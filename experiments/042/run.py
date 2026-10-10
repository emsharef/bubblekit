"""Experiment 042 (D29): intraday evaluation at scale on Alpaca SIP 5-minute bars (Deviations 1-3).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/042/run.py [inventory | smoke | run]      (start from inside .worktrees/analyst)

Reads data/d29/sip/ (and data/d29/iex/, data/d29/massive/) written by fetch.py, experiment 039's Yahoo daily closes
in data/d24/ for forward outcomes, and experiment 021's DJIA membership and daily data for the control rule.
`inventory` builds every window and prints counts and lengths (no score); `smoke` scores the registered smoke tier
(2 positives and 2 controls at 2 checkpoints, timed); `run` is the full experiment.
"""
import csv
import datetime as dt
import gzip
import importlib.util
import io
import json
import math
import os
import sys
import time
from fractions import Fraction as F
from multiprocessing import Pool
from zoneinfo import ZoneInfo

import numpy as np
from scipy.stats import rankdata

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)
D29 = os.path.join(ROOT, "data", "d29")


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


r021 = _load("r021", "experiments/021/run.py")
r027 = _load("r027", "experiments/027/run.py")
r032 = _load("r032", "experiments/032/run.py")
r033 = _load("r033", "experiments/033/run.py")
r035 = _load("r035", "experiments/035/run.py")
r039 = _load("r039", "experiments/039/run.py")
neg = r021.negatives
fetch = _load("f042", "experiments/042/fetch.py")
cev = r032.cev
psy = r021.psy
WORKERS = r021.WORKERS
NY = ZoneInfo("America/New_York")

DAYS, BARS = 252, 78
DELTA_BAR = (5 / 60) / (24 * DAYS)              # experiment 027's calendar durations
DELTA_ON = 17.5 / (24 * DAYS)
U_SHAPE, U_PHI = r027.session_clock(1.5), 0.25   # experiment 027's published U(1.5, 0.25)
IEX_FIRST = dt.date(2020, 7, 27)
PRIOR_RULE_FROM = dt.date(2021, 7, 27)           # the PM's labelled subset
ROLL_FIRST = dt.date(2017, 1, 1)
WINDOW_MONTHS = 6
MIN_CLOCK_SESSIONS = 100                         # Deviation 3: fewer complete prior-year sessions -> U-shape clock
MIN_PRICES = 1000                                # Deviation 3: fewer closes in a window -> untestable
ALPHA, Q = 0.05, 0.05
TICK = F(1, 100)
BOX = (F("-2"), F("2"), F("0.01"), F("16"))
CERT = dict(count=4, max_count=64, max_evaluations=256, factor=2)
POWERS = (F(1), F(3, 2), F(2))
KAPPAS = ("0.10", "0.20", "0.30", "0.45", "0.70", "1.00", "1.50", "2.00", "3.00", "4.00")
WALL_CAP = 12 * 3600
CV_SEED, CV_REPS, CV_STEP = r021.CV_SEED, r021.CV_REPS, 1000
HORIZONS = r039.HORIZONS


# ---- bars ---------------------------------------------------------------------------------------------------------
_ses = {}


_splits = None


def splits(sym):
    global _splits
    if _splits is None:
        _splits = json.load(open(os.path.join(D29, "splits.json")))
    return [(dt.date.fromisoformat(e["date"]), e["numerator"] / e["denominator"]) for e in _splits.get(sym, [])]


def sessions(sym, feed="sip", adjusted=True):
    """{date: array of 78 slot closes (NaN where no bar)} for one symbol and feed; cached per process. SIP and IEX bars
    are raw prices; `adjusted` divides every close before each Yahoo split date by that split's ratio (Deviation 3)."""
    key = (sym, feed, adjusted)
    if key not in _ses:
        path = os.path.join(D29, feed, f"{sym}.csv.gz")
        out = {}
        if os.path.exists(path):
            rows = list(csv.reader(io.StringIO(gzip.decompress(open(path, "rb").read()).decode())))[1:]
            for t, c, _, _ in rows:
                x = dt.datetime.strptime(t, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=dt.timezone.utc).astimezone(NY)
                j = ((x.hour * 60 + x.minute) - (9 * 60 + 30)) // 5
                if 0 <= j < BARS:
                    out.setdefault(x.date(), np.full(BARS, np.nan))[j] = float(c)
        if adjusted:
            for sd, ratio in splits(sym):
                for d in out:
                    if d < sd:
                        out[d] = out[d] / ratio
        if len(_ses) > 40:
            _ses.clear()
        _ses[key] = out
    return _ses[key]


def daily_close(ses):
    """Last regular-session close of each day (for peak and onset only)."""
    ds = sorted(ses)
    px = []
    for d in ds:
        v = ses[d][np.isfinite(ses[d])]
        px.append(v[-1] if v.size else np.nan)
    return np.array(ds), np.array(px)


# ---- clocks -------------------------------------------------------------------------------------------------------
def u_clock():
    """Per-slot variance increments of experiment 027's U(1.5, 0.25); slot 0 carries the overnight share."""
    v = (1 - U_PHI) * U_SHAPE / DAYS
    v[0] += U_PHI / DAYS
    return v


def prior_year_clock(ses, start):
    """The name's own clock from the 12 months of bars before `start` (Deviation 1): per-slot mean squared log return
    over complete regular sessions (all 78 slots, previous session's last slot present), normalized; slot 0 is the
    overnight return plus the first bar. Returns (per-slot increments, sessions used) or (None, sessions used)."""
    a = _minus_months(start, 12)
    days = sorted(d for d in ses if a <= d < start)
    sq, prev = [], None
    for d in days:
        x = ses[d]
        if prev is not None and np.isfinite(x).all() and np.isfinite(ses[prev][-1]):
            path = np.concatenate([[ses[prev][-1]], x])
            sq.append(np.diff(np.log(path)) ** 2)
        prev = d
    if len(sq) < MIN_CLOCK_SESSIONS:
        return None, len(sq)
    m = np.mean(sq, axis=0)
    return m / m.sum() / DAYS, len(sq)


def _minus_months(d, k):
    import calendar
    y, m = divmod(d.year * 12 + d.month - 1 - k, 12)
    return dt.date(y, m + 1, min(d.day, calendar.monthrange(y, m + 1)[1]))


def _plus_months(d, k):
    return _minus_months(d, -k)


# ---- records ------------------------------------------------------------------------------------------------------
def record(ses, a, b, vslot):
    """Closes, calendar durations d and declared clock increments vU over sessions in [a, b]. A slot without a bar is
    merged into the next bar of the same session (032's rule); trailing empty slots of a session add nothing; the
    first bar of each session carries the overnight duration."""
    P, d, v = [], [], []
    acc_d = acc_v = 0.0
    started = False
    for day in sorted(x for x in ses if a <= x <= b):
        x = ses[day]
        for j in range(BARS):
            if started:
                acc_d += DELTA_BAR + (DELTA_ON if j == 0 else 0.0)
                acc_v += vslot[j]
            if not np.isfinite(x[j]) or not x[j] > 0:
                continue
            if not started:
                P.append(x[j])
                started = True
                acc_d = acc_v = 0.0
                continue
            P.append(x[j])
            d.append(acc_d)
            v.append(acc_v)
            acc_d = acc_v = 0.0
        acc_d = acc_v = 0.0                  # trailing empty slots add nothing; the next slot 0 adds the overnight
    return np.array(P), np.array(d), np.array(v)


def window_record(sym, a, b, feed="sip", clock="prior", adjusted=True):
    """One window: its record under the primary clock (prior year, U-shape fallback) or the U-shape. The clock is
    always declared from split-adjusted bars; the record's closes are raw only for column (iii)."""
    ses = sessions(sym, feed, adjusted)
    if clock == "U":
        vs, used, label = u_clock(), None, "U"
    else:
        vs, used = prior_year_clock(sessions(sym, feed), a)
        label = "prior-year" if vs is not None else "U-fallback"
        if vs is None:
            vs = u_clock()
    P, d, v = record(ses, a, b, vs)
    return P, d, v, {"clock": label, "clock_sessions": used}


# ---- windows ------------------------------------------------------------------------------------------------------
def month_ends(first, last):
    """Last SPY session of each month in [first, last]."""
    ds = sorted(d for d in sessions("SPY") if first <= d <= last)
    out = []
    for i, d in enumerate(ds):
        if i == len(ds) - 1 or ds[i + 1].month != d.month:
            out.append(d)
    return out


def positives():
    """(name, group, record start, record end): 021's E5 and E9 windows; 033's class-B list with 033's windows."""
    out = []
    for e, names in (("E5", ["GME", "AMC", "KOSS", "BB"]), ("E9", ["ARKK", "TSLA", "ZM", "PTON"])):
        a, b = neg.EPISODES[e][:2]
        out += [(n, e, dt.date.fromisoformat(a), dt.date.fromisoformat(b)) for n in names]
    for n, c, e in r033.NAMES:
        if c == "B":
            end = dt.date.fromisoformat(e)
            out.append((n, "033-B", max(r033.month_start_12_before(end), r033.ARCHIVE_FIRST), end))
    return out


def calm_members(start, end, mem, cache):
    """021's member rule at `start` (lowest trailing vol + drawdown rank sum; ties by price weight, then name), keeping
    members whose SIP bars cover [start, end] within a week; replacements recorded (033's rule on SIP bars)."""
    ranked = []
    for n in neg.members_at(mem, start):
        sym = neg.LINEAGE.get(n)
        if not isinstance(sym, str):
            continue
        if sym not in cache:
            cache[sym] = neg.load(sym)
        md, madj, _, mraw = cache[sym]
        t = neg.trailing(md, madj, start)
        if t is None:
            continue
        k = np.searchsorted(md, start) - 1
        ranked.append({"name": n, "symbol": sym, "sigma_tr": t[0], "drawdown_tr": t[1], "price_weight": float(mraw[k])})
    rs = rankdata([m["sigma_tr"] for m in ranked], method="min")
    rd = rankdata([m["drawdown_tr"] for m in ranked], method="min")
    for m, x, y in zip(ranked, rs, rd):
        m["score"] = int(x + y)
    ranked.sort(key=lambda m: (m["score"], -m["price_weight"], m["name"]))
    picked, replaced = [], []
    for m in ranked:
        if len(picked) == 5:
            break
        ds = sorted(sessions(m["symbol"]))
        ok = bool(ds) and ds[0] <= start + dt.timedelta(days=7) and ds[-1] >= end - dt.timedelta(days=7)
        (picked if ok else replaced).append(m["symbol"])
    return picked, replaced


def monitored():
    """Checkpoint windows for positives and their time-matched controls: every month-end m inside the record, scored on
    the trailing six months of bars (m - 6 months, m]."""
    pos = positives()
    mem = neg.membership()
    cache, ctrl = {}, {}
    wins = []
    for name, grp, a, b in pos:
        for m in month_ends(a, b):
            wins.append({"kind": "positive", "group": grp, "name": name, "record": [str(a), str(b)],
                         "checkpoint": str(m), "a": _minus_months(m, WINDOW_MONTHS) + dt.timedelta(days=1), "b": m})
        if (a, b) not in ctrl:
            picked, replaced = calm_members(a, b, mem, cache)
            ctrl[(a, b)] = {"members": picked, "replaced": replaced}
    for (a, b), c in sorted(ctrl.items()):
        for sym in ["SPY", "DIA"] + c["members"]:
            for m in month_ends(a, b):
                wins.append({"kind": "control", "group": f"ctrl|{a}|{b}", "name": sym, "record": [str(a), str(b)],
                             "checkpoint": str(m), "a": _minus_months(m, WINDOW_MONTHS) + dt.timedelta(days=1), "b": m})
    return wins, {f"{a}|{b}": c for (a, b), c in ctrl.items()}


def rolling():
    """The seeded 100-name draw: six-month windows starting on each month's first SPY session from 2017-01, while 126
    forward trading days of Yahoo closes remain (039's coverage rule on the forward path)."""
    syms = fetch.symbols()["rolling_draw"]["drawn"]
    gd, _ = r039.load("^GSPC")
    spy = sorted(sessions("SPY"))
    starts = []
    y, mo = ROLL_FIRST.year, ROLL_FIRST.month
    while True:
        k = int(np.searchsorted(spy, dt.date(y, mo, 1)))
        if k >= len(spy):
            break
        starts.append(spy[k])
        y, mo = (y + 1, 1) if mo == 12 else (y, mo + 1)
    wins = []
    for s in starts:
        e = _plus_months(dt.date(s.year, s.month, 1), WINDOW_MONTHS) - dt.timedelta(days=1)
        ke = int(np.searchsorted(gd, e, side="right")) - 1
        if ke + max(HORIZONS) >= len(gd):
            continue
        for sym in syms:
            wins.append({"kind": "rolling", "group": f"roll|{s}", "name": sym, "checkpoint": str(gd[ke]),
                         "a": s, "b": gd[ke], "forward_end": str(gd[ke + max(HORIZONS)])})
    return wins


# ---- columns ------------------------------------------------------------------------------------------------------
def cols(P, d, v):
    o = {"n": int(P.size), "v1": r032.col_v1(P, d)["log_e"],
         "c033": r035.c033_score(P, d, v, r035.FC_WIDE, r035.NULL_ORIG)["log_e"]}
    s = r032.col_sadf(P)
    o.update(sadf=s["sadf"], gsadf=s["gsadf"])
    return o


def forward_outcomes(sym, b, fe):
    d, p = r039.load(sym.replace(".", "-"))
    i1 = int(np.searchsorted(d, b, side="right"))
    f1 = int(np.searchsorted(d, fe, side="right"))
    if i1 == 0 or f1 - i1 < r039.COVERAGE * max(HORIZONS):
        return None
    return r039.forward(p[i1 - 1:f1])


def window_job(w):
    """Columns (i), (ii), (iv) on SIP (primary clock), column (ii) under the U-shape for windows before 2021-07-27,
    and the IEX secondary for windows starting on or after 2020-07-27."""
    t0 = time.time()
    out = {k: (str(v) if isinstance(v, dt.date) else v) for k, v in w.items()}
    P, d, v, meta = window_record(w["name"], w["a"], w["b"])
    out.update(meta)
    if P.size < MIN_PRICES:
        out["untestable"] = f"{P.size} closes"
        return out
    out["sip"] = cols(P, d, v)
    if w["a"] < PRIOR_RULE_FROM:
        _, _, vU, _ = window_record(w["name"], w["a"], w["b"], clock="U")
        out["sip"]["c033_U"] = r035.c033_score(P, d, vU, r035.FC_WIDE, r035.NULL_ORIG)["log_e"]
    if w["a"] >= IEX_FIRST:
        Pi, di, vi, mi = window_record(w["name"], w["a"], w["b"], feed="iex",
                                       clock="prior" if w["a"] >= PRIOR_RULE_FROM else "U")
        out["iex"] = cols(Pi, di, vi) | {"clock": mi["clock"]} if Pi.size >= MIN_PRICES else {"untestable": int(Pi.size)}
    if w["kind"] == "rolling":
        out["forward"] = forward_outcomes(w["name"], w["b"], dt.date.fromisoformat(w["forward_end"]))
    out["sec"] = time.time() - t0
    return out


_fc = _cert = None


def cert_job(w):
    """Column (iii): D22's certified lower numerator (expanding fit) over claim 038's certified upper denominator,
    with the declared box, on cent-labelled SIP closes; split at floor(N/2)."""
    global _fc, _cert
    if _fc is None:
        _fc = _load("d22fc", "checks/d22-predictable-forecast/forecast.py")
        _cert = _load("cert038", "checks/038/certify.py")
    t0 = time.time()
    rec = {"key": w["key"]}
    if any(w["a"] < sd <= w["b"] for sd, _ in splits(w["name"])):
        return rec | {"status": "not covered (split inside the window)", "log_e_bound": float("-inf")}
    P, d, v, _ = window_record(w["name"], w["a"], w["b"], adjusted=False)
    labels = [int(round(F(str(x)) / TICK)) for x in P[1:]]
    if any(z == 0 for z in labels) or not np.all(np.abs(np.round(P * 100) - P * 100) < 1e-6):
        return rec | {"status": "not covered (zero label or sub-cent tick)", "log_e_bound": float("-inf")}
    start = F(str(P[0]))
    gaps = tuple(F(float(x)) for x in d)
    vU = tuple(F(float(x)) for x in v)
    N = len(labels)
    cat = [_fc.Candidate(p, F(k), clk) for clk in (gaps, vU) for p in POWERS for k in KAPPAS]
    lg = lambda f: (math.log(f.numerator) - math.log(f.denominator)) if f > 0 else float("-inf")
    try:
        steps = _fc.evaluate(labels, cat, start, TICK, N // 2)
        rec["log_q_lower"] = lg(steps[-1].joint_lower)
    except Exception as e:
        rec["log_q_lower"], rec["forecast_error"] = float("-inf"), type(e).__name__
    try:
        res = _cert.enclose(labels, list(gaps), [list(gaps), list(vU)], TICK, start, BOX, N // 2, **CERT)
        rec.update(status=res.status, log_D_lower=lg(res.lower), log_D_upper=lg(res.upper),
                   evaluations=res.evaluations)
    except Exception as e:
        rec.update(status=f"error: {type(e).__name__}", log_D_upper=0.0)
    rec["log_e_bound"] = rec["log_q_lower"] - rec["log_D_upper"]
    rec["sec"] = time.time() - t0
    return rec


def cv_grid(lengths):
    """SADF/GSADF null quantiles at a grid of lengths every CV_STEP closes spanning the observed lengths, interpolated
    linearly in n (Deviation 3); 021's simulation and seed scheme at each grid length."""
    lo = int(min(lengths) // CV_STEP * CV_STEP)
    hi = int(-(-max(lengths) // CV_STEP) * CV_STEP)
    grid = list(range(max(lo, CV_STEP), hi + 1, CV_STEP))
    root = np.random.SeedSequence(CV_SEED)
    jobs = [(N, s.generate_state(2).tolist()) for N, ss in zip(grid, root.spawn(len(grid)))
            for s in ss.spawn(CV_REPS // 50)]
    with Pool(WORKERS) as pool:
        st = {N: [] for N in grid}
        for N, o in pool.imap_unordered(r021.cv_job, jobs):
            st[N] += o
    return {N: {k: {"5%": float(np.quantile(np.array(st[N])[:, j], 0.95))} for j, k in enumerate(("sadf", "gsadf"))}
            for N in grid}


def cv_at(cvs, n, k):
    g = sorted(cvs)
    return float(np.interp(n, g, [cvs[x][k]["5%"] for x in g]))


# ---- summaries ----------------------------------------------------------------------------------------------------
def flags_of(o, cvs, feed="sip"):
    x = o.get(feed)
    if not x or "v1" not in x:
        return None
    thr = -math.log(ALPHA)
    f = {"v1": x["v1"] > thr, "c033": x["c033"] > thr,
         "sadf": x["sadf"] > cv_at(cvs, x["n"], "sadf"), "gsadf": x["gsadf"] > cv_at(cvs, x["n"], "gsadf")}
    if "c033_U" in x:
        f["c033_U"] = x["c033_U"] > thr
    if feed == "sip" and "cert" in o:
        f["cert"] = o["cert"].get("log_e_bound", float("-inf")) > thr
    return f


def ebh(rows, feed, col):
    """Original-m e-BH at q = 0.05 within each (group, checkpoint) panel."""
    out = {}
    panels = {}
    for o in rows:
        panels.setdefault((o["group"], o["checkpoint"]), []).append(o)
    for (g, c), R in panels.items():
        if col == "cert":
            logs = [o.get("cert", {}).get("log_e_bound", float("-inf")) for o in R]
        else:
            logs = [o.get(feed, {}).get(col, float("-inf")) if o.get(feed) and "v1" in o.get(feed, {}) else
                    float("-inf") for o in R]
        rej = cev.ebh(np.exp(np.nan_to_num(np.array(logs, float), nan=-np.inf)), Q)
        for o, r_ in zip(R, rej):
            out[(o["group"], o["name"], o["checkpoint"])] = bool(r_)
    return out


def time_to_flag(rows, cvs, feed, spy_days):
    """Per positive record: first flagged checkpoint per column, offset from the record's peak and from its stated
    onset (minimum daily close before the peak, within the record; Deviation 2)."""
    out = []
    recs = {}
    for o in rows:
        if o["kind"] == "positive":
            recs.setdefault((o["group"], o["name"], tuple(o["record"])), []).append(o)
    for (g, name, rec), R in sorted(recs.items()):
        R.sort(key=lambda o: o["checkpoint"])
        a, b = (dt.date.fromisoformat(x) for x in rec)
        dd, dp = daily_close(sessions(name, feed))
        m = (dd >= a) & (dd <= b) & np.isfinite(dp)
        if not m.any():
            out.append({"group": g, "name": name, "record": rec, "untestable": "no bars in the record"})
            continue
        dd, dp = dd[m], dp[m]
        kp = int(np.argmax(dp))
        peak, onset = dd[kp], dd[int(np.argmin(dp[:kp + 1]))]
        tdays = lambda x, y: int(np.searchsorted(spy_days, y) - np.searchsorted(spy_days, x))
        cols_ = {}
        for c in ("v1", "c033", "c033_U", "sadf", "gsadf", "cert"):
            hit = next((o for o in R if (flags_of(o, cvs, feed) or {}).get(c)), None)
            if not any(c in (flags_of(o, cvs, feed) or {}) for o in R):
                continue
            cols_[c] = None if hit is None else {
                "first_flag": hit["checkpoint"],
                "from_peak_trading_days": tdays(peak, dt.date.fromisoformat(hit["checkpoint"])),
                "from_onset_trading_days": tdays(onset, dt.date.fromisoformat(hit["checkpoint"])),
                "from_peak_months": round((dt.date.fromisoformat(hit["checkpoint"]) - peak).days / 30.44, 2)}
        out.append({"group": g, "name": name, "record": rec, "peak": str(peak), "onset": str(onset),
                    "checkpoints": len(R), "clocks": sorted({o.get("clock") for o in R}),
                    "scores": [{"checkpoint": o["checkpoint"], **{k: o.get(feed, {}).get(k) for k in
                                ("v1", "c033", "c033_U", "sadf", "gsadf", "n")},
                                "cert": o.get("cert", {}).get("log_e_bound")} for o in R],
                    "first_flag": cols_})
    return out


def false_alarms(rows, cvs, feed):
    out = {}
    C = [o for o in rows if o["kind"] == "control" and flags_of(o, cvs, feed)]
    for lab, sel in (("all", C), ("from_2021-07-27", [o for o in C if dt.date.fromisoformat(o["a"]) >= PRIOR_RULE_FROM])):
        if not sel:
            continue
        cs = sorted(set().union(*[flags_of(o, cvs, feed).keys() for o in sel]))
        recs = {}
        for o in sel:
            recs.setdefault((o["group"], o["name"]), []).append(flags_of(o, cvs, feed))
        out[lab] = {"windows": len(sel), "records": len(recs),
                    "per_window": {c: float(np.mean([flags_of(o, cvs, feed).get(c, False) for o in sel
                                                     if c in flags_of(o, cvs, feed)])) for c in cs},
                    "per_record_ever": {c: float(np.mean([any(f.get(c, False) for f in fl) for fl in recs.values()]))
                                        for c in cs}}
    return out


def roll_regressions(rows, feed):
    R = [o for o in rows if o["kind"] == "rolling" and o.get(feed) and "v1" in o[feed] and o.get("forward")]
    if len(R) < 50:
        return {"n": len(R)}
    starts = np.array([o["a"] for o in R])
    names = np.array([o["name"] for o in R])
    smonth = np.array([dt.date.fromisoformat(s).year * 12 + dt.date.fromisoformat(s).month for s in starts])
    ranks = {}
    for sc in ("v1", "c033", "gsadf"):
        v = np.array([o[feed][sc] if math.isfinite(o[feed][sc]) else -1e300 for o in R], float)
        ranks[sc] = r039.pct_rank(v, starts)
    lag = math.ceil(1.5 * WINDOW_MONTHS)
    res = {"n": len(R), "start_months": int(len(np.unique(smonth))), "dk_lag_months": lag}
    for out_ in [f"mdd{h}" for h in HORIZONS] + [f"ret{h}" for h in HORIZONS]:
        y = np.array([o["forward"][out_] for o in R])
        blk = {}
        for spec in (["v1"], ["c033"], ["gsadf"], ["v1", "c033", "gsadf"]):
            X = np.column_stack([np.ones(len(y))] + [ranks[s] for s in spec])
            b, u = r039.ols(y, X)
            blk["+".join(spec)] = {"coef": b[1:].tolist(), "se_dk": r039.dk_se(X, u, smonth, lag)[1:].tolist(),
                                   "se_twoway": r039.twoway_se(X, u, starts, names)[1:].tolist()}
        res[out_] = blk
    return res


def period_table(rows, cvs, feed):
    out = {}
    R = [o for o in rows if o["kind"] == "rolling" and flags_of(o, cvs, feed)]
    for y in sorted({o["a"][:4] for o in R}):
        S = [o for o in R if o["a"][:4] == y]
        fl = [flags_of(o, cvs, feed) for o in S]
        out[y] = {"windows": len(S),
                  "flag_rate": {c: float(np.mean([f[c] for f in fl if c in f])) for c in ("v1", "c033", "sadf", "gsadf")},
                  "quantiles": {c: dict(zip(("5%", "50%", "95%"), np.quantile(
                      [o[feed][c] for o in S if math.isfinite(o[feed][c])] or [np.nan], (0.05, 0.5, 0.95)).tolist()))
                      for c in ("v1", "c033", "gsadf")}}
    return out


def massive_check():
    out = {}
    for sym in fetch.CROSS:
        p = os.path.join(D29, "massive", f"{sym}.csv.gz")
        if not os.path.exists(p):
            out[sym] = {"missing": True}
            continue
        m = {r[0]: float(r[1]) for r in csv.reader(io.StringIO(gzip.decompress(open(p, "rb").read()).decode()))
             if r[0] != "t"}
        q = os.path.join(D29, "sip", f"{sym}.csv.gz")
        s = {r[0]: float(r[1]) for r in csv.reader(io.StringIO(gzip.decompress(open(q, "rb").read()).decode()))
             if r[0] != "t" and r[0] >= min(m)}
        both = sorted(set(m) & set(s))
        out[sym] = {"both": len(both), "sip_only": len(set(s) - set(m)), "massive_only": len(set(m) - set(s)),
                    "within_one_cent": float(np.mean([abs(m[t] - s[t]) <= 0.01 + 1e-9 for t in both])) if both else None}
    return out


def build_all():
    mon, ctrl = monitored()
    roll = rolling()
    return mon, ctrl, roll


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "run"
    mon, ctrl, roll = build_all()
    if mode == "inventory":
        lens = []
        for w in mon[:: max(1, len(mon) // 60)] + roll[:: max(1, len(roll) // 60)]:
            P, _, _, meta = window_record(w["name"], w["a"], w["b"])
            lens.append((w["kind"], w["name"], str(w["a"]), int(P.size), meta["clock"]))
        print(json.dumps({"monitored": len(mon), "positives": sum(w["kind"] == "positive" for w in mon),
                          "controls": sum(w["kind"] == "control" for w in mon), "rolling": len(roll),
                          "control_sets": ctrl, "sample_lengths": lens}, indent=1, default=str))
        return
    if mode == "smoke":
        P2 = [w for w in mon if w["kind"] == "positive" and w["name"] in ("GME", "NVDA")]
        C2 = [w for w in mon if w["kind"] == "control" and w["name"] in ("SPY", "KO")]
        pick = []
        for grp in (P2, C2):
            for nm in sorted({w["name"] for w in grp}):
                ws = [w for w in grp if w["name"] == nm]
                pick += ws[len(ws) // 2: len(ws) // 2 + 2]
        for i, w in enumerate(pick):
            w["key"] = f"smoke{i}"
        t0 = time.time()
        with Pool(WORKERS) as pool:
            a = pool.map(window_job, pick, chunksize=1)
            c = pool.map(cert_job, pick, chunksize=1)
        res = {"windows": [x | {"cert": y} for x, y in zip(a, c)], "wall_s": time.time() - t0,
               "per_window_sec": float(np.mean([x["sec"] for x in a if "sec" in x])),
               "per_cert_sec": float(np.mean([y["sec"] for y in c if "sec" in y])),
               "n_windows": {"monitored": len(mon), "rolling": len(roll)}}
        res["projected_hours_columns_i_ii_iv"] = res["per_window_sec"] * (len(mon) + len(roll)) / WORKERS / 3600
        res["projected_hours_column_iii_all"] = res["per_cert_sec"] * (len(mon) + len(roll)) / WORKERS / 3600
        with open(os.path.join(HERE, "smoke.json"), "w") as fh:
            json.dump(res, fh, indent=1, default=float)
        print(json.dumps({k: v for k, v in res.items() if k != "windows"}, indent=1))
        return
    t_start = time.time()
    allw = mon + roll
    for i, w in enumerate(allw):
        w["key"] = f"{w['kind']}|{w['group']}|{w['name']}|{w['checkpoint']}"
    order = sorted(range(len(allw)), key=lambda i: (allw[i]["name"], allw[i]["checkpoint"]))
    with Pool(WORKERS) as pool:
        res = [None] * len(allw)
        for i, o in zip(order, pool.imap(window_job, [allw[i] for i in order], chunksize=8)):
            res[i] = o
    print("columns (i), (ii), (iv) done", round((time.time() - t_start) / 3600, 2), "h", flush=True)
    lengths = [o[f]["n"] for o in res for f in ("sip", "iex") if o.get(f) and "n" in o[f]]
    cvs = cv_grid(lengths)
    print("critical values done", flush=True)
    # column (iii): fixed order positives, controls, rolling; 12-hour wall cap
    certs, t0 = {}, time.time()
    with Pool(WORKERS) as pool:
        futs = [(w["key"], pool.apply_async(cert_job, (w,))) for w, o in zip(allw, res) if "untestable" not in o]
        for key, fut in futs:                      # submitted in the fixed order; the pool runs them in that order
            left = WALL_CAP - (time.time() - t0)
            if left <= 0 and not fut.ready():
                certs[key] = {"status": "not attempted or unfinished at the wall cap", "log_e_bound": float("-inf")}
                continue
            try:
                certs[key] = fut.get(timeout=max(0.01, left))
            except Exception as e:
                certs[key] = {"status": "not attempted or unfinished at the wall cap" if time.time() - t0 >= WALL_CAP
                              else f"error: {type(e).__name__}", "log_e_bound": float("-inf")}
        pool.terminate()
    cert_wall = time.time() - t0
    for w, o in zip(allw, res):
        if w["key"] in certs and "untestable" not in o:
            o["cert"] = certs[w["key"]]
    spy_days = np.array(sorted(sessions("SPY")))
    out = {"clock_rule": "prior 12 months of SIP bars (U(1.5, 0.25) fallback below 100 complete sessions)",
           "control_sets": ctrl, "critical_values_grid": cvs, "cert_wall_s": cert_wall,
           "seconds": time.time() - t_start}
    for feed in ("sip", "iex"):
        out[feed] = {"time_to_flag": time_to_flag(res, cvs, feed, spy_days),
                     "false_alarms": false_alarms(res, cvs, feed),
                     "rolling_regressions": roll_regressions(res, feed),
                     "period_table": period_table(res, cvs, feed),
                     "ebh": {c: {"|".join(k): v for k, v in ebh(res, feed, c).items() if v}
                             for c in (("v1", "c033", "cert") if feed == "sip" else ("v1", "c033"))}}
    out["massive_cross_check"] = massive_check()
    out["cert_status_counts"] = {}
    for o in res:
        st = o.get("cert", {}).get("status")
        if st:
            out["cert_status_counts"][st] = out["cert_status_counts"].get(st, 0) + 1
    out["untestable"] = [(o["kind"], o["name"], o["checkpoint"], o["untestable"]) for o in res if "untestable" in o]
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(out, fh, indent=1, default=float)
    with gzip.open(os.path.join(HERE, "windows.json.gz"), "wt") as fh:
        json.dump(res, fh, default=float)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        wr = csv.writer(fh)
        wr.writerow(["group", "name", "peak", "onset", "column", "first_flag", "from_peak_trading_days",
                     "from_onset_trading_days"])
        for r in out["sip"]["time_to_flag"]:
            for c, v in r.get("first_flag", {}).items():
                wr.writerow([r["group"], r["name"], r.get("peak"), r.get("onset"), c] +
                            ([v["first_flag"], v["from_peak_trading_days"], v["from_onset_trading_days"]] if v else
                             ["", "", ""]))
    print("done")


if __name__ == "__main__":
    main()
