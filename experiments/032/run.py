"""Experiment 032: D6's first real-data intraday application (hourly bars; E6 = SK Hynix, N24m-3 calm negative).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/032/run.py [inventory|smoke]      (start from inside .worktrees/analyst)

`inventory` prints the data-only record inventory and the declared clock shares, and runs no test. `smoke [n]` runs
column (iii) on an n-increment (default 300) synthetic GBM record only, to time it. Reads the gitignored archive
data/d6-intraday/bars/60m/ (experiments/data/intraday_archive.py).
"""
import csv
import datetime as dt
import importlib.util
import json
import math
import os
import sys
import time
from fractions import Fraction as F
from multiprocessing import Pool
from zoneinfo import ZoneInfo

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)
BARS = os.path.join(ROOT, "data", "d6-intraday", "bars", "60m")


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


r021 = _load("r021", "experiments/021/run.py")
r027 = _load("r027", "experiments/027/run.py")
r028 = _load("r028", "experiments/028/run.py")
total = r021.total
psy = r021.psy
cev = r027.cev

DAYS = 252
OVERNIGHT_H = 17.5
EXCH = {"US": ("America/New_York", dt.time(9, 30), dt.time(16, 0)), "KRX": ("Asia/Seoul", dt.time(9, 0), dt.time(15, 30))}
ROWS = {
    "E6": {"names": ["000660.KS"], "exch": "KRX", "declare": ("2023-10-06", "2023-12-28"),
           "full": ("2024-01-02", "2026-10-05"), "to_peak": ("2024-01-02", "2026-06-22")},
    "N24m-3": {"names": ["^GSPC", "^DJI", "V", "PG", "WMT", "KO", "TRV"], "exch": "US",
               "declare": ("2023-11-07", "2024-06-28"),
               "full": ("2024-07-01", "2026-06-30"), "to_peak": ("2024-07-01", "2026-06-02")},
}
ALPHAS = (0.05, 0.10)
QS = (0.05, 0.10)
BOX = (F("-0.5"), F("0.5"), F("0.01"), F("0.64"))
TICK = F(1, 100)
CERT = dict(count=4, max_count=64, max_evaluations=256, factor=2)
WALL_CAP = 6 * 3600
WORKERS = r021.WORKERS


# ---- data -----------------------------------------------------------------------------------------------------
def sessions(sym, exch):
    """{local date: [(start datetime, close)]} with null closes kept as None; stray bars at or after the close dropped."""
    tzname, _, close_t = EXCH[exch]
    tz = ZoneInfo(tzname)
    out = {}
    with open(os.path.join(BARS, sym.replace("^", "_") + ".csv"), newline="") as fh:
        for r in csv.DictReader(fh):
            t = dt.datetime.fromtimestamp(int(r["timestamp_utc"]), tz)
            c = float(r["close"]) if r["close"] not in ("", "nan") else None
            out.setdefault(t.date(), []).append((t, c))
    res, stray, half = {}, 0, 0
    for d, bars in sorted(out.items()):
        bars.sort()
        starts = [b[0].time() for b in bars]
        # US half days: a bar starting 13:00 and none at 13:30 -> the session closed at 13:00
        close = close_t
        if exch == "US" and dt.time(13, 0) in starts and dt.time(13, 30) not in starts:
            close, half = dt.time(13, 0), half + 1
        keep = [b for b in bars if b[0].time() < close]
        stray += len(bars) - len(keep)
        res[d] = (keep, close)
    return res, {"stray_bars_dropped": stray, "half_days": half}


def bar_minutes(keep, close):
    """Length of each bar: next start minus start, the last up to the session close."""
    out = []
    for i, (t, _) in enumerate(keep):
        end = keep[i + 1][0] if i + 1 < len(keep) else t.replace(hour=close.hour, minute=close.minute)
        out.append((end - t).total_seconds() / 60.0)
    return out


def regular_minutes(exch):
    _, open_t, close_t = EXCH[exch]
    n = 6 if exch == "KRX" else 7
    starts = [open_t.hour * 60 + open_t.minute + 60 * j for j in range(n)]
    end = close_t.hour * 60 + close_t.minute
    return [min(60, end - s) if j < n - 1 else end - s for j, s in enumerate(starts)]


def declare_shares(row):
    """Per-slot variance shares from regular, complete sessions in the declaration period (data strictly before)."""
    info = ROWS[row]
    exch = info["exch"]
    nslot = len(regular_minutes(exch))
    a, b = (dt.date.fromisoformat(x) for x in info["declare"])
    per_name = []
    for sym in info["names"]:
        ses, _ = sessions(sym, exch)
        days = sorted(d for d in ses if d <= b)
        sq = [[] for _ in range(nslot)]
        prev_close = None
        for d in days:
            keep, close = ses[d]
            closes = [c for _, c in keep]
            regular = len(keep) == nslot and all(c is not None and c > 0 for c in closes)
            if regular and d >= a and prev_close is not None:
                path = [prev_close] + closes
                for j in range(nslot):
                    sq[j].append(math.log(path[j + 1] / path[j]) ** 2)
            last = [c for c in closes if c is not None and c > 0]
            prev_close = last[-1] if last else prev_close
        m = np.array([np.mean(x) for x in sq])
        per_name.append(m / m.sum())
    shares = np.mean(per_name, axis=0)
    return shares / shares.sum(), [p.tolist() for p in per_name]


def record(sym, row, variant, shares):
    """Prices (closes), calendar durations d and declared clock vU for one tested span."""
    info = ROWS[row]
    exch = info["exch"]
    reg = regular_minutes(exch)
    ses, meta = sessions(sym, exch)
    a, b = (dt.date.fromisoformat(x) for x in info[variant])
    prices, d, v = [], [], []
    acc_d = acc_v = 0.0
    nulls = irregular = 0
    started = False
    for day in sorted(x for x in ses if a <= x <= b):
        keep, close = ses[day]
        mins = bar_minutes(keep, close)
        if len(keep) != len(reg) or close != EXCH[exch][2]:
            irregular += 1
        if started:
            acc_d += OVERNIGHT_H / (24 * DAYS)
        for j, ((t, c), mn) in enumerate(zip(keep, mins)):
            share = shares[min(j, len(reg) - 1)] * (mn / reg[min(j, len(reg) - 1)])
            if started:
                acc_d += (mn / 60.0) / (24 * DAYS)
                acc_v += share / DAYS
            if c is None or not c > 0:
                nulls += 1
                continue
            if not started:                     # the first valid close of the span is the start
                prices.append(c)
                started = True
                acc_d = acc_v = 0.0
                continue
            prices.append(c)
            d.append(acc_d)
            v.append(acc_v)
            acc_d = acc_v = 0.0
    return np.array(prices), np.array(d), np.array(v), {"null_bars_dropped": nulls, "irregular_sessions": irregular,
                                                         **meta}


# ---- columns --------------------------------------------------------------------------------------------------
def col_v1(P, d):
    X = P / P[0]
    times = np.concatenate([[0.0], np.cumsum(d)])
    N = len(d)
    t0 = time.time()
    r = total.score_total_path(r021.CATALOGUE, [float(x) for x in times], [float(x) for x in X], N // 2)
    return {"log_e": float(r["log_e"]), "raw_log_e": float(r["raw_log_e"]), "status": list(r["status"]),
            "fit": None if r["fit"] is None else int(r["fit"]), "sec": time.time() - t0}


def col_033(P, d, vU):
    S = (P / P[0])[None, :]
    t0 = time.time()
    out, _, k = r027.scores(S, d, vU)
    return {"log_e": float(out["c033"][0]), "fail": bool(out["fail"][0]), "unbounded": bool(out["unbounded033"][0]),
            "k": int(k), "sec": time.time() - t0}


def col_sadf(P):
    X = P / P[0]
    L0 = r021.r0_window(X.size)
    t0 = time.time()
    s, g = psy.sadf_gsadf(X, [L0])[L0]
    return {"sadf": float(s), "gsadf": float(g), "n": int(X.size), "sec": time.time() - t0}


def cert_job(args):
    """Column (iii) for one record: certified log D interval (claims 036-038) and the diagnostic numerator."""
    key, P, d, vU = args
    t0 = time.time()
    cert = _load("cert038", "checks/038/certify.py")
    start = F(str(P[0]))
    labels = [int(round(F(str(x)) / TICK)) for x in P[1:]]
    Z = np.array([[int(round(F(str(x)) / TICK)) for x in P]], float)
    rec = {"key": key}
    try:
        lq, floored = r028.forecast034(Z, d, vU, float(P[0]))
        rec["log_q"], rec["floored"] = float(lq[0]), int(floored[0])
    except Exception as e:                           # forecast failure: score zero, kept
        rec["log_q"], rec["floored"], rec["forecast_error"] = float("-inf"), -1, type(e).__name__
    gaps = [F(float(x)) for x in d]
    clocks = [gaps, [F(float(x)) for x in vU]]
    try:
        res = cert.enclose(labels, gaps, clocks, TICK, start, BOX, len(labels) // 2, **CERT)
        lg = lambda f: (math.log(f.numerator) - math.log(f.denominator)) if f > 0 else float("-inf")
        rec.update({"status": res.status, "log_D_lower": lg(res.lower), "log_D_upper": lg(res.upper),
                    "evaluations": res.evaluations, "leaves": len(res.leaves), "prunable": res.prunable,
                    "failed_leaves": sum(l.failed for l in res.leaves)})
    except Exception as e:
        rec.update({"status": f"error: {type(e).__name__}", "log_D_upper": 0.0})
    ok = rec.get("floored", -1) == 0 and math.isfinite(rec["log_q"])
    rec["log_e_bound"] = rec["log_q"] - rec["log_D_upper"] if ok else float("-inf")
    rec["sec"] = time.time() - t0
    return rec


def ebh_flags(logs, q):
    e = np.exp(np.nan_to_num(np.array(logs, float), nan=-np.inf))
    return cev.ebh(e, q).tolist()


# ---- main -----------------------------------------------------------------------------------------------------
def build():
    shares = {row: declare_shares(row) for row in ROWS}
    recs = []
    for row, info in ROWS.items():
        for variant in ("full", "to_peak"):
            for sym in info["names"]:
                P, d, vU, meta = record(sym, row, variant, shares[row][0])
                recs.append({"row": row, "variant": variant, "name": sym, "P": P, "d": d, "vU": vU, "meta": meta})
    return shares, recs


def smoke():
    rng = np.random.default_rng(12345)                 # throwaway synthetic record, not archive data
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    d = np.full(n, 1 / (DAYS * 7))
    P = np.round(50 * np.exp(np.concatenate([[0], np.cumsum(0.3 * np.sqrt(d) * rng.standard_normal(n))])), 2)
    r = cert_job(("synthetic", P, d, d * 1.0))
    print(json.dumps(r, indent=1, default=str))


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "run"
    if mode == "smoke":
        smoke()
        return
    shares, recs = build()
    if mode == "inventory":
        print(json.dumps({"shares": {k: v[0].tolist() for k, v in shares.items()},
                          "per_name_shares": {k: v[1] for k, v in shares.items()},
                          "records": [{k: (r[k] if k not in ("P", "d", "vU") else int(len(r[k]))) for k in r}
                                      | {"first_price": float(r["P"][0])} for r in recs]}, indent=1, default=str))
        return
    # columns (i), (ii), (iv) per record; critical values for SADF/GSADF at each length (021's procedure)
    out = []
    for r in recs:
        o = {k: r[k] for k in ("row", "variant", "name", "meta")}
        o["n_increments"] = int(len(r["d"]))
        o["v1"] = col_v1(r["P"], r["d"])
        o["c033"] = col_033(r["P"], r["d"], r["vU"])
        o["sadf"] = col_sadf(r["P"])
        out.append(o)
    Ns = sorted({o["sadf"]["n"] for o in out})
    root = np.random.SeedSequence(r021.CV_SEED)
    cv_jobs = [(N, s.generate_state(2).tolist()) for N, ss in zip(Ns, root.spawn(len(Ns)))
               for s in ss.spawn(r021.CV_REPS // 50)]
    with Pool(WORKERS) as pool:
        stats = {N: [] for N in Ns}
        for N, o_ in pool.map(r021.cv_job, cv_jobs, chunksize=4):
            stats[N] += o_
    cvs = {N: {k: {"5%": float(np.quantile(np.array(stats[N])[:, j], 0.95)),
                   "10%": float(np.quantile(np.array(stats[N])[:, j], 0.90))} for j, k in enumerate(("sadf", "gsadf"))}
           for N in Ns}
    # column (iii): N24m-3 only (SK Hynix not covered: variable KRX tick), fixed order, wall cap
    order = [r for r in recs if r["row"] == "N24m-3" and r["variant"] == "full"] + \
            [r for r in recs if r["row"] == "N24m-3" and r["variant"] == "to_peak"]
    certs = {}
    t0 = time.time()
    with Pool(WORKERS) as pool:
        pending = {}
        it = iter(order)
        for r in it:
            key = f"{r['row']}|{r['variant']}|{r['name']}"
            pending[key] = pool.apply_async(cert_job, ((key, r["P"], r["d"], r["vU"]),))
        for key, fut in pending.items():
            left = WALL_CAP - (time.time() - t0)
            try:
                certs[key] = fut.get(timeout=max(1.0, left))
            except Exception as e:
                certs[key] = {"key": key, "status": f"not finished within the wall cap ({type(e).__name__})",
                              "log_e_bound": float("-inf")}
        pool.terminate()
    cert_wall = time.time() - t0
    for o in out:
        key = f"{o['row']}|{o['variant']}|{o['name']}"
        o["cert"] = certs.get(key, {"status": "not covered: variable KRX tick" if o["row"] == "E6" else
                                     "not attempted", "log_e_bound": float("-inf")})
        o["flags"] = {f"v1_{a}": o["v1"]["log_e"] > -math.log(a) for a in ALPHAS} | \
                     {f"c033_{a}": o["c033"]["log_e"] > -math.log(a) for a in ALPHAS} | \
                     {f"cert_{a}": o["cert"]["log_e_bound"] > -math.log(a) for a in ALPHAS} | \
                     {f"sadf_{lv}": o["sadf"]["sadf"] > cvs[o["sadf"]["n"]]["sadf"][lv] for lv in ("5%", "10%")} | \
                     {f"gsadf_{lv}": o["sadf"]["gsadf"] > cvs[o["sadf"]["n"]]["gsadf"][lv] for lv in ("5%", "10%")}
        o["cv"] = cvs[o["sadf"]["n"]]
    ebh = {}
    for row in ROWS:
        for variant in ("full", "to_peak"):
            grp = [o for o in out if o["row"] == row and o["variant"] == variant]
            for col, get in (("v1", lambda o: o["v1"]["log_e"]), ("c033", lambda o: o["c033"]["log_e"]),
                             ("cert", lambda o: o["cert"]["log_e_bound"])):
                for q in QS:
                    rej = ebh_flags([get(o) for o in grp], q)
                    ebh[f"{row}|{variant}|{col}|{q}"] = dict(zip([o["name"] for o in grp], rej))
    res = {"shares": {k: v[0].tolist() for k, v in shares.items()},
           "per_name_shares": {k: v[1] for k, v in shares.items()}, "records": out, "ebh": ebh,
           "critical_values": cvs, "cert_settings": {k: (str(v) if isinstance(v, F) else v) for k, v in CERT.items()}
           | {"box": [str(x) for x in BOX], "tick": str(TICK), "wall_cap_s": WALL_CAP, "wall_s": cert_wall}}
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump({f"{o['row']}|{o['variant']}|{o['name']}": {"v1": o["v1"]["status"], "c033_fail": o["c033"]["fail"],
                                                              "cert": o["cert"]["status"]} for o in out}, fh, indent=0)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["row", "variant", "name", "n", "v1_log_e", "c033_log_e", "cert_log_e_bound", "cert_status",
                    "sadf", "gsadf"] + sorted(out[0]["flags"]))
        for o in out:
            w.writerow([o["row"], o["variant"], o["name"], o["n_increments"], o["v1"]["log_e"], o["c033"]["log_e"],
                        o["cert"]["log_e_bound"], o["cert"]["status"], o["sadf"]["sadf"], o["sadf"]["gsadf"]]
                       + [o["flags"][k] for k in sorted(o["flags"])])
    print("done")


if __name__ == "__main__":
    main()
