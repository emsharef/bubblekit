"""Experiment 033: D21 recent run-ups on free hourly data (experiment 032's design plus JKP; GME/AMC jump diagnostics).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/033/run.py [inventory]      (start from inside .worktrees/analyst)

`inventory` prints the data-only record inventory (windows, sizes, negatives selection) and runs no test.
Reuses experiments 021 (negatives, critical values, JKP wrapper), 027/028 (via 032) and 032 (sessions, columns).
"""
import csv
import datetime as dt
import importlib.util
import json
import math
import os
import sys
import time
from multiprocessing import Pool

import numpy as np
from scipy.stats import rankdata

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


r032 = _load("r032", "experiments/032/run.py")
r021 = r032.r021
neg = r021.negatives
jkp = r021.jkp
ALPHAS, QS = r032.ALPHAS, r032.QS
WORKERS = r032.WORKERS
U_US = np.array([0.595, 0.0947, 0.0564, 0.0492, 0.0713, 0.0645, 0.069])      # experiment 032's N24m-3 shares
ARCHIVE_FIRST = dt.date(2023, 11, 7)
ARCHIVE_LAST = dt.date(2026, 10, 6)

# (name, class, window end) from the registration; window = 12 calendar months ending there, truncated
NAMES = [("GME", "B", "2024-05-31"), ("AMC", "B", "2024-05-31"), ("DJT", "B", "2024-04-30"),
         ("SMCI", "B", "2024-11-29"), ("PLTR", "B", "2025-08-29"), ("CRWV", "B", "2025-12-31"),
         ("NVDA", "B", "2025-12-31"), ("OPEN", "B", "2025-10-31"), ("BYND", "B", "2025-10-31"),
         ("KSS", "B", "2025-07-31"), ("DNUT", "B", "2025-07-31"), ("GPRO", "B", "2025-07-31"),
         ("IONQ", "B", "2025-03-31"), ("RGTI", "B", "2025-03-31"), ("QBTS", "B", "2025-03-31"),
         ("OKLO", "B", "2026-07-31"), ("MSTR", "B", "2025-09-30"), ("BMNR", "B", "2025-10-31"),
         ("SBET", "B", "2025-10-31"), ("NAKA", "B", "2025-10-31"), ("CRCL", "B", "2025-07-31"),
         ("ORCL", "C", "2025-12-31"),
         ("RDDT", "W", "2024-03-31"), ("COIN", "W", "2025-10-31"), ("MARA", "W", "2025-12-31"),
         ("RIOT", "W", "2025-12-31"), ("CLSK", "W", "2025-12-31"), ("IREN", "W", "2025-12-31"),
         ("CIFR", "W", "2025-12-31"), ("HUT", "W", "2025-12-31")]


def month_start_12_before(end):
    y, m = end.year, end.month - 11
    while m < 1:
        y, m = y - 1, m + 12
    return dt.date(y, m, 1)


def record_window(sym, start, end, shares=U_US):
    """Hourly closes, calendar durations and declared clock over [start, end] (032's rules, US sessions)."""
    exch = "US"
    reg = r032.regular_minutes(exch)
    ses, meta = r032.sessions(sym, exch)
    prices, d, v = [], [], []
    acc_d = acc_v = 0.0
    nulls = irregular = 0
    started = False
    for day in sorted(x for x in ses if start <= x <= end):
        keep, close = ses[day]
        mins = r032.bar_minutes(keep, close)
        if len(keep) != len(reg) or close != r032.EXCH[exch][2]:
            irregular += 1
        if started:
            acc_d += r032.OVERNIGHT_H / (24 * r032.DAYS)
        for j, ((t, c), mn) in enumerate(zip(keep, mins)):
            share = shares[min(j, len(reg) - 1)] * (mn / reg[min(j, len(reg) - 1)])
            if started:
                acc_d += (mn / 60.0) / (24 * r032.DAYS)
                acc_v += share / r032.DAYS
            if c is None or not c > 0:
                nulls += 1
                continue
            if not started:
                prices.append(c)
                started = True
                acc_d = acc_v = 0.0
                continue
            prices.append(c)
            d.append(acc_d)
            v.append(acc_v)
            acc_d = acc_v = 0.0
    days = sorted(x for x in ses if start <= x <= end)
    return (np.array(prices), np.array(d), np.array(v),
            {"null_bars_dropped": nulls, "irregular_sessions": irregular, "first_session": str(days[0]) if days else None,
             "last_session": str(days[-1]) if days else None, **meta})


def has_bars(sym):
    return os.path.exists(os.path.join(r032.BARS, sym.replace("^", "_") + ".csv"))


def positive_records():
    recs = []
    for sym, cls, e in NAMES:
        end = dt.date.fromisoformat(e)
        start = max(month_start_12_before(end), ARCHIVE_FIRST)
        rec = {"name": sym, "class": cls, "window": [start.isoformat(), end.isoformat()], "group": "positive" if cls == "B" else cls}
        if not has_bars(sym):
            rec["untestable"] = "no archived hourly bars"
        else:
            P, d, v, meta = record_window(sym, start, end)
            if len(P) < 30:
                rec["untestable"] = f"{len(P)} closes in the window"
            rec.update({"P": P, "d": d, "vU": v, "meta": meta})
        recs.append(rec)
    return recs


def windows_of(recs):
    """Actual tested windows (first to last session) of every positive-list record with data."""
    out = []
    for r in recs:
        if "untestable" in r or "meta" not in r:
            continue
        out.append((dt.date.fromisoformat(r["meta"]["first_session"]), dt.date.fromisoformat(r["meta"]["last_session"])))
    return out


def primary_negatives(pos_windows):
    """The entry's rule: L = 12 months, quarterly starts inside the archive, no overlap with any positive window."""
    gd, gadj, _, _ = neg.load("^GSPC")
    cands = []
    for y in range(2023, 2027):
        for m in (1, 4, 7, 10):
            k = np.searchsorted(gd, dt.date(y, m, 1))
            if k >= len(gd):
                continue
            s = gd[k]
            if s < ARCHIVE_FIRST:
                continue
            e = neg.add_months(s, 12)
            ke = np.searchsorted(gd, e) - 1
            if e > ARCHIVE_LAST or ke >= len(gd):
                continue
            end = gd[ke]
            overlap = any(s <= pe and ps <= end for ps, pe in pos_windows)
            cands.append({"start": s.isoformat(), "end": end.isoformat(), "overlaps_positive": overlap})
    return [c for c in cands if not c["overlaps_positive"]], cands


def calm_members(start, end, mem, cache):
    """021's member rule at `start`: 5 DJIA members with the lowest trailing vol + drawdown rank sum (ties: price, name),
    requiring hourly bars over [start, end]; replacements recorded."""
    names = neg.members_at(mem, start)
    ranked = []
    for n in names:
        v = neg.LINEAGE.get(n)
        sym = v if isinstance(v, str) else None
        if sym is None:
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
        ok = has_bars(m["symbol"])
        if ok:
            ses, _ = r032.sessions(m["symbol"], "US")
            ds = sorted(ses)
            ok = ds[0] <= start + dt.timedelta(days=7) and ds[-1] >= end - dt.timedelta(days=7)
        (picked if ok else replaced).append(m["symbol"])
    return picked, replaced


def secondary_negatives(pos_recs):
    mem = neg.membership()
    cache = {}
    wins = {}
    for r in pos_recs:
        if "untestable" in r:
            continue
        w = (r["meta"]["first_session"], r["meta"]["last_session"])
        wins.setdefault(w, []).append(r["name"])
    out = []
    for (a, b), who in sorted(wins.items()):
        s, e = dt.date.fromisoformat(a), dt.date.fromisoformat(b)
        picked, replaced = calm_members(s, e, mem, cache)
        for sym in ["^GSPC", "^DJI"] + picked:
            P, d, v, meta = record_window(sym, s, e)
            out.append({"name": sym, "class": "negative (time-matched)", "group": f"neg|{a}|{b}", "window": [a, b],
                        "matched_to": who, "replaced": replaced, "P": P, "d": d, "vU": v, "meta": meta})
    return out


# ---- per-record work ------------------------------------------------------------------------------------------
def cols_job(r):
    P, d, vU = r["P"], r["d"], r["vU"]
    o = {"v1": r032.col_v1(P, d), "c033": r032.col_033(P, d, vU), "sadf": r032.col_sadf(P)}
    t0 = time.time()
    m2, m1 = r021.jkp_verdicts(P / P[0], jkp.MIN_OBS)
    o["jkp"] = {"m2": m2, "m1": m1, "sec": time.time() - t0}
    o["tick_to_price_median"] = float(np.median(0.01 / P))
    return o


def jump_diag(P, d):
    r = np.diff(np.log(P))
    rv = float((r ** 2).sum())
    bv = float((math.pi / 2) * (np.abs(r[1:]) * np.abs(r[:-1])).sum())
    s = np.sort(r ** 2)[::-1]
    return {"RV": rv, "BV": bv, "jump_share": max(0.0, 1 - bv / rv), "largest_share": float(s[0] / rv),
            "top5_share": float(s[:5].sum() / rv), "n": int(r.size)}


def gme_job(args):
    name, P, d = args
    out = {"name": name, "window": jump_diag(P, d)}
    times = np.concatenate([[0.0], np.cumsum(d)])
    tail = times >= times[-1] - 2 * 21 * 24 / (24 * r032.DAYS)          # about the last two months of sessions
    k0 = int(np.argmax(tail))
    out["last_two_months"] = jump_diag(P[k0:], d[k0:])
    sc = _load("score061", "checks/061/scoring.py")
    t0 = time.time()
    try:
        res = sc.score_total_path(r021.CATALOGUE, [float(x) for x in times], [float(x) for x in P / P[0]], len(d) // 2,
                                  0.10, 252, max_boxes=128)
        out["claim061"] = {"log_e_prof": float(res["log_e"]), "log_e_drift": float(res["drift_log_e"]),
                           "status": list(res["status"]), "detail": res.get("detail")}
    except Exception as e:
        out["claim061"] = {"error": f"{type(e).__name__}: {e}"}
    out["claim061"]["sec"] = time.time() - t0
    return out


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "run"
    pos = positive_records()
    pw = windows_of(pos)
    prim, allc = primary_negatives(pw)
    sec = secondary_negatives([r for r in pos if r["class"] == "B" or r["class"] in ("C", "W")])
    if mode == "inventory":
        print(json.dumps({"positives": [{k: (r[k] if k not in ("P", "d", "vU") else int(len(r[k]))) for k in r} for r in pos],
                          "primary_candidates": allc, "primary_selected": prim,
                          "secondary": [{"window": s["window"], "name": s["name"], "n": int(len(s["d"])),
                                         "replaced": s["replaced"]} for s in sec]}, indent=1, default=str))
        return
    recs = [r for r in pos if "untestable" not in r] + sec
    with Pool(WORKERS) as pool:
        cols = pool.map(cols_job, recs, chunksize=1)
        gm = pool.map(gme_job, [(r["name"], r["P"], r["d"]) for r in pos if r["name"] in ("GME", "AMC")])
    for r, c in zip(recs, cols):
        r.update(c)
    Ns = sorted({r["sadf"]["n"] for r in recs})
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
    # column (iii): fixed order B, C, W, negatives; 6-hour cap
    order = [r for c in ("B", "C", "W") for r in recs if r["class"] == c] + [r for r in recs if r["group"].startswith("neg")]
    certs, t0 = {}, time.time()
    with Pool(WORKERS) as pool:
        futs = [(id(r), pool.apply_async(r032.cert_job, ((r["name"], r["P"], r["d"], r["vU"]),))) for r in order]
        for rid, fut in futs:
            try:
                certs[rid] = fut.get(timeout=max(1.0, r032.WALL_CAP - (time.time() - t0)))
            except Exception as e:
                certs[rid] = {"status": f"not finished within the wall cap ({type(e).__name__})", "log_e_bound": float("-inf")}
        pool.terminate()
    cert_wall = time.time() - t0
    out = []
    for r in pos + sec:
        o = {k: r[k] for k in ("name", "class", "group", "window") if k in r}
        for k in ("meta", "matched_to", "replaced", "untestable"):
            if k in r:
                o[k] = r[k]
        if "untestable" in r:
            o["flags"] = {f"{c}_{a}": False for c in ("v1", "c033", "cert") for a in ALPHAS}
            out.append(o)
            continue
        o["n_increments"] = int(len(r["d"]))
        for k in ("v1", "c033", "sadf", "jkp", "tick_to_price_median"):
            o[k] = r[k]
        o["cert"] = certs.get(id(r), {"status": "not attempted", "log_e_bound": float("-inf")})
        cv = cvs[r["sadf"]["n"]]
        o["cv"] = cv
        o["flags"] = {f"v1_{a}": o["v1"]["log_e"] > -math.log(a) for a in ALPHAS} | \
                     {f"c033_{a}": o["c033"]["log_e"] > -math.log(a) for a in ALPHAS} | \
                     {f"cert_{a}": o["cert"]["log_e_bound"] > -math.log(a) for a in ALPHAS} | \
                     {f"sadf_{lv}": o["sadf"]["sadf"] > cv["sadf"][lv] for lv in ("5%", "10%")} | \
                     {f"gsadf_{lv}": o["sadf"]["gsadf"] > cv["gsadf"][lv] for lv in ("5%", "10%")} | \
                     {"jkp_m2": o["jkp"]["m2"] == "bubble", "jkp_m1": o["jkp"]["m1"] == "bubble"}
        out.append(o)
    ebh = {}
    groups = {"B": [o for o in out if o["class"] == "B"], "C+W": [o for o in out if o["class"] in ("C", "W")]}
    for o in out:
        if o.get("group", "").startswith("neg"):
            groups.setdefault(o["group"], []).append(o)
    for g, grp in groups.items():
        for col, get in (("v1", lambda o: o.get("v1", {}).get("log_e", -np.inf)),
                         ("c033", lambda o: o.get("c033", {}).get("log_e", -np.inf)),
                         ("cert", lambda o: o.get("cert", {}).get("log_e_bound", -np.inf))):
            for q in QS:
                rej = r032.ebh_flags([get(o) for o in grp], q)
                ebh[f"{g}|{col}|{q}"] = dict(zip([o["name"] for o in grp], rej))
    res = {"clock_shares": U_US.tolist(), "records": out, "ebh": ebh, "gme_amc": gm, "primary_negative_candidates": allc,
           "primary_negatives_selected": prim, "critical_values": cvs, "cert_wall_s": cert_wall}
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump({f"{o.get('group')}|{o['name']}": {"untestable": o.get("untestable"), "v1": o.get("v1", {}).get("status"),
                                                     "cert": o.get("cert", {}).get("status")} for o in out}, fh, indent=0)
    keys = sorted(next(o for o in out if "v1" in o)["flags"])
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["group", "class", "name", "window_start", "window_end", "n", "v1_log_e", "c033_log_e", "cert_bound",
                    "cert_status", "sadf", "gsadf", "jkp_m2", "jkp_m1", "tick_to_price"] + keys)
        for o in out:
            if "v1" not in o:
                w.writerow([o.get("group"), o["class"], o["name"], o["window"][0], o["window"][1], 0] + [""] * 9 +
                           [False] * len(keys))
                continue
            w.writerow([o["group"], o["class"], o["name"], o["window"][0], o["window"][1], o["n_increments"],
                        o["v1"]["log_e"], o["c033"]["log_e"], o["cert"]["log_e_bound"], o["cert"]["status"],
                        o["sadf"]["sadf"], o["sadf"]["gsadf"], o["jkp"]["m2"], o["jkp"]["m1"],
                        o["tick_to_price_median"]] + [o["flags"][k] for k in keys])
    print("done")


if __name__ == "__main__":
    main()
