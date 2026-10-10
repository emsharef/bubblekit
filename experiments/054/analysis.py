"""Experiment 054 analysis: calibration with mathb's monitor.py, first alarms, time-to-alarm, controls, forward
regressions. Called by run.py (full/analyze)."""
import csv
import datetime as dt
import gzip
import json
import math
import os

import numpy as np

RUN = mon = r039 = r042 = None


def _bind(module):
    """The caller passes its own run module: importing 'run' by name can resolve to another experiment's run.py
    (042/050 put their directories first on sys.path)."""
    global RUN, mon, r039, r042
    RUN, mon, r039, r042 = module, module.mon, module.r039, module.r042
DK_LAG = 9
SPLIT = dt.date(2023, 1, 1)


def alarm_time(cal, k, t):
    """Replay availability of checkpoint t: the bar end of slot j in session offset d, plus the assumed 60 s."""
    d, j = (t - 1) // 77, (t - 1) % 77 + 1
    day = cal[k + d]
    minutes = 9 * 60 + 30 + 5 * (j + 1)
    return day, f"{day} {minutes // 60:02d}:{minutes % 60:02d}:00 ET + 60 s (assumed)", d


def ols(y, X):
    b, *_ = np.linalg.lstsq(X, y, rcond=None)
    return b, y - X @ b


def regressions(rows):
    month = np.array([r["launch"][:7] for r in rows])
    date = np.array([r["launch"] for r in rows])
    rk = {s: r039.pct_rank(np.array([r[s] for r in rows], float), date) for s in ("monitor", "gsadf")}
    out = {}
    for h in RUN.H_FWD:
        for oc in (f"mdd{h}", f"ret{h}"):
            y = np.array([r[oc] for r in rows], float)
            for spec in (["monitor"], ["gsadf"], ["monitor", "gsadf"]):
                X = np.column_stack([np.ones(len(y))] + [rk[s] for s in spec])
                b, u = ols(y, X)
                se = r039.dk_se(X, u, month, DK_LAG)
                key = f"{oc}|{'+'.join(spec)}"
                out[key] = {"coef": b[1:].tolist(), "se_dk": se[1:].tolist(), "n": int(y.size),
                            "r2": float(1 - u.var() / y.var())}
                tr = np.array([r[f"out_end{h}"] < str(SPLIT) for r in rows])
                te = np.array([r["launch"] >= str(SPLIT) for r in rows])
                if tr.sum() > 30 and te.sum() > 30:
                    bt, _ = ols(y[tr], X[tr])
                    pred = X[te] @ bt
                    base = y[tr].mean()
                    oos = 1 - np.sum((y[te] - pred) ** 2) / np.sum((y[te] - base) ** 2)
                    tm = month[te]
                    um = np.unique(tm)
                    rng = np.random.default_rng(np.random.SeedSequence([RUN.BOOT_SEED, h, len(spec)]))
                    blocks = [um[i:i + 12] for i in range(len(um))]
                    boots = []
                    for _ in range(1000):
                        pick = []
                        while len(pick) < len(um):
                            pick += list(blocks[rng.integers(len(blocks))])
                        idx = np.concatenate([np.flatnonzero(tm == m) for m in pick[:len(um)]])
                        boots.append(1 - np.sum((y[te][idx] - pred[idx]) ** 2) / np.sum((y[te][idx] - base) ** 2))
                    out[key].update(oos_r2=float(oos), oos_se=float(np.std(boots)), n_train=int(tr.sum()),
                                    n_test=int(te.sum()))
    return out


def record_peak_onset(sym, a, b, cal):
    ses = r042.sessions(sym)
    ds = [d for d in cal if a <= d <= b and RUN.daily_close(ses, d) is not None]
    if not ds:
        return None, None
    px = np.array([RUN.daily_close(ses, d) for d in ds])
    kp = int(np.argmax(px))
    ko = int(np.argmin(px[:kp + 1]))
    return ds[ko], ds[kp]


def run(man, module):
    _bind(module)
    cal, _ = RUN.calendar()
    ci = {d: i for i, d in enumerate(cal)}
    with gzip.open(os.path.join(RUN.ARCH, "launches.json.gz"), "rt") as fh:
        L = json.load(fh)
    by = {(o["sym"], o["k"], o["tag"]): o for o in L["launches"]}
    refs = [by[(r["sym"], r["k"], "ref")] for r in man["reference"]]
    cut, summ = mon.calibrate([RUN.prefix_logs(o["archive"]) for o in refs], RUN.SCHEDULE, RUN.ALPHA)
    raw = mon.base.rank_cutoff([s.maximum for s in summ], RUN.ALPHA)
    gref = [max(o["gsadf"]) for o in refs]
    gcut = mon.base.rank_cutoff(gref, RUN.ALPHA)
    res = {"wall_h": L["wall"] / 3600, "code": L["code"],
           "calibration": {"reference_count": len(refs), "monitor_cutoff": cut, "monitor_raw_rank_value": raw,
                           "gsadf_cutoff": gcut,
                           "reference_fit_failures": sum(o["fit"] is None for o in refs),
                           "reference_clock_fallbacks": sum(o["clock"] == "SPY-fallback" for o in refs),
                           "reference_max_quantiles": np.quantile([s.maximum for s in summ], (0.5, 0.9, 0.95, 0.99)).tolist(),
                           "reference_alarms_at_cutoff": sum(mon.base.flag(s.maximum, cut) for s in summ)}}
    rows = []
    for t in man["targets"]:
        o = by[(t["sym"], t["k"], t["kind"])]
        m = mon.summarize(RUN.prefix_logs(o["archive"]), RUN.SCHEDULE, cutoff=cut)
        g = o["gsadf"]
        ga = RUN.first_alarm_gsadf(g, gcut)
        row = {**t, "monitor": m.maximum, "monitor_alarm": m.first_alarm, "gsadf": max(g), "gsadf_alarm_session": ga,
               "fit_ok": o["fit"] is not None, "clock": o["clock"], "factors": o.get("factors", 0),
               "status_counts": o["status_counts"]}
        if m.first_alarm is not None:
            day, stamp, dd = alarm_time(cal, t["k"], m.first_alarm)
            row.update(monitor_alarm_day=str(day), monitor_alarm_time=stamp, monitor_alarm_session=dd)
        rows.append(row)
    # positives: time to alarm against record peak and onset
    P = [r for r in rows if r["kind"] == "positive"]
    recs = {}
    for r in P:
        key = (r["sym"], r["group"], tuple(r["record"]))
        recs.setdefault(key, []).append(r)
    pos_out = []
    for (sym, grp, rec), R in sorted(recs.items()):
        a, b = dt.date.fromisoformat(rec[0]), dt.date.fromisoformat(rec[1])
        onset, peak = record_peak_onset(sym, a, b, cal)
        def earliest(kind):
            days = []
            for r in R:
                if kind == "monitor" and r.get("monitor_alarm_day"):
                    days.append(dt.date.fromisoformat(r["monitor_alarm_day"]))
                if kind == "gsadf" and r["gsadf_alarm_session"] is not None:
                    days.append(cal[r["k"] + r["gsadf_alarm_session"]])
            return min(days) if days else None
        e = {}
        for kind in ("monitor", "gsadf"):
            day = earliest(kind)
            e[kind] = {"first_alarm": str(day) if day else None,
                       "sessions_from_peak": (ci[day] - ci[peak]) if day and peak in ci else None,
                       "sessions_from_onset": (ci[day] - ci[onset]) if day and onset in ci else None,
                       "launches_alarmed": sum(1 for r in R if (r.get("monitor_alarm") is not None if kind == "monitor"
                                                                else r["gsadf_alarm_session"] is not None))}
        pos_out.append({"sym": sym, "group": grp, "record": list(rec), "onset": str(onset), "peak": str(peak),
                        "launches": len(R), "fit_failures": sum(not r["fit_ok"] for r in R), **e})
    res["positives"] = pos_out

    def shares(R):
        n = len(R)
        return {"launches": n, "monitor_alarm_share": sum(r["monitor_alarm"] is not None for r in R) / n if n else None,
                "gsadf_alarm_share": sum(r["gsadf_alarm_session"] is not None for r in R) / n if n else None,
                "fit_failures": sum(not r["fit_ok"] for r in R)}
    C = [r for r in rows if r["kind"] == "control"]
    res["controls"] = {"all": shares(C), "SPY/DIA": shares([r for r in C if r["sym"] in ("SPY", "DIA")]),
                       "members": shares([r for r in C if r["sym"] not in ("SPY", "DIA")]),
                       "by_window": {g: shares([r for r in C if r["group"] == g]) for g in sorted({r["group"] for r in C})}}
    res["positive_launches"] = {"all": shares(P), **{g: shares([r for r in P if r["group"] == g])
                                                     for g in sorted({r["group"] for r in P})}}
    U = [r for r in rows if r["kind"] == "unselected"]
    res["unselected"] = {"all": shares(U), "unexposed": shares([r for r in U if not r["overlap_052"]]),
                         "by_year": {y: shares([r for r in U if r["launch"][:4] == y])
                                     for y in sorted({r["launch"][:4] for r in U})}}
    # forward outcomes (Yahoo adjusted closes; 039's coverage rule)
    gd, _ = r039.load("^GSPC")
    fwd = []
    for r in U:
        end = cal[r["k"] + RUN.NSES - 1]
        ke = int(np.searchsorted(gd, end, side="right")) - 1
        d, p = r039.load(r["sym"])
        i1 = np.searchsorted(d, gd[ke], side="right")
        f1 = np.searchsorted(d, gd[ke + max(RUN.H_FWD)], side="right")
        if i1 == 0 or f1 - i1 < 0.99 * max(RUN.H_FWD):
            continue
        out = r039.forward(p[i1 - 1:f1])
        row = {"launch": r["launch"], "sym": r["sym"], "monitor": r["monitor"], "gsadf": r["gsadf"],
               "overlap_052": r["overlap_052"], **out}
        for h in RUN.H_FWD:
            row[f"out_end{h}"] = str(gd[min(ke + h, len(gd) - 1)])
        fwd.append(row)
    res["forward"] = {"n": len(fwd), "of_unselected": len(U), "full": regressions(fwd),
                      "unexposed": regressions([r for r in fwd if not r["overlap_052"]])}
    with open(os.path.join(RUN.HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=str)
    with gzip.open(os.path.join(RUN.HERE, "targets.json.gz"), "wt") as fh:
        json.dump(rows, fh, default=str)
    with open(os.path.join(RUN.HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["block", "name", "launches", "monitor_alarm_share", "gsadf_alarm_share", "fit_failures"])
        for blk in ("controls", "positive_launches"):
            for k, v in res[blk].items():
                if k != "by_window" and isinstance(v, dict) and "launches" in v:
                    w.writerow([blk, k, v["launches"], v["monitor_alarm_share"], v["gsadf_alarm_share"], v["fit_failures"]])
        for k, v in res["unselected"]["by_year"].items():
            w.writerow(["unselected", k, v["launches"], v["monitor_alarm_share"], v["gsadf_alarm_share"], v["fit_failures"]])
    print(json.dumps(res["calibration"], default=str))
