"""Experiment 047 (D28 index data): claim 042's IV-scaled score on SPX/VIX and NDX/VXN.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/047/run.py      (start from inside .worktrees/analyst; single process)

Reads data/d28/ (fetch.py). Scores with checks/d28-predictable-iv/evaluate.py unchanged. Writes results.json and
summary.csv.
"""
import csv
import datetime as dt
import importlib.util
import json
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)
DATA = os.path.join(ROOT, "data", "d28")


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


ev = _load("d28eval", "checks/d28-predictable-iv/evaluate.py")
r021 = _load("r021", "experiments/021/run.py")
DAYS, TRAIN, SCORED = 252, 126, 252
DT = 1.0 / DAYS
END = dt.date(2026, 10, 7)
BANDS = ((0.3, 1.0), (0.25, 1.25), (0.5, 1.0))
BAND_NAMES = ("primary [0.3,1.0]", "band M [0.25,1.25]", "sensitivity [0.5,1.0]")
ALPHAS = (0.05, 0.10)
NBER = [(dt.date(1990, 7, 1), dt.date(1991, 3, 31)), (dt.date(2001, 3, 1), dt.date(2001, 11, 30)),
        (dt.date(2007, 12, 1), dt.date(2009, 6, 30)), (dt.date(2020, 2, 1), dt.date(2020, 4, 30))]
VXN_CBOE_FROM = dt.date(2009, 9, 14)
EPISODES = [("SPX dot-com", "SPX", dt.date(1998, 7, 1), dt.date(1999, 1, 4), dt.date(2001, 12, 31)),
            ("SPX 2020-21", "SPX", dt.date(2019, 7, 1), dt.date(2020, 1, 2), dt.date(2021, 12, 31)),
            ("NDX 2020-21", "NDX", dt.date(2019, 7, 1), dt.date(2020, 1, 2), dt.date(2021, 12, 31))]


def yahoo(name):
    r = json.load(open(os.path.join(DATA, f"yahoo_{name}.json")))["chart"]["result"][0]
    tz = r["meta"].get("gmtoffset", 0)
    out = {}
    for t, c in zip(r["timestamp"], r["indicators"]["quote"][0]["close"]):
        d = dt.datetime.fromtimestamp(t + tz, dt.timezone.utc).date()
        if c is not None and c > 0 and d <= END:
            out[d] = float(c)
    return out


def cboe(name):
    out = {}
    with open(os.path.join(DATA, f"cboe_{name}.csv")) as fh:
        for row in csv.DictReader(fh):
            d = dt.datetime.strptime(row["DATE"], "%m/%d/%Y").date()
            c = float(row["CLOSE"])
            if c > 0 and d <= END:
                out[d] = c
    return out


def agreement(a, b):
    common = sorted(set(a) & set(b))
    diffs = np.array([abs(a[d] - b[d]) for d in common])
    return {"common_days": len(common), "within_0.01": float(np.mean(diffs <= 0.01 + 1e-9)) if common else None,
            "max_abs_diff": float(diffs.max()) if common else None}


def iv_series(index, iv, lag):
    """For each return t (dates[t-1] -> dates[t]) the IV close of index-trading day t-lag (lag 2 primary), carried
    forward from the latest earlier IV close if that day has none. Returns dates, prices, iv per return, carried."""
    dates = sorted(index)
    ivd = sorted(iv)
    P = np.array([index[d] for d in dates])
    out, carried = [], 0
    j = 0
    for t in range(1, len(dates)):
        k = t - lag
        if k < 0:
            out.append(np.nan)
            continue
        target = dates[k]
        while j + 1 < len(ivd) and ivd[j + 1] <= target:
            j += 1
        if ivd[j] > target:
            out.append(np.nan)
            continue
        carried += ivd[j] != target
        out.append(iv[ivd[j]] / 100.0)
    return dates, P, np.array(out), carried


def score_record(P, IV):
    rows = ev.evaluate([float(x) for x in P], [float(x) for x in IV], [DT] * len(IV), TRAIN, bands=BANDS)
    out = {"status": rows[-1]["status"]}
    for bi, bn in enumerate(BAND_NAMES):
        sc = np.array([r_["log_scores"][bi] for r_ in rows], float)
        k = int(np.argmax(np.where(np.isfinite(sc), sc, -np.inf)))
        out[bn] = {"final": float(sc[-1]), "max": float(sc[k]), "argmax_index": int(rows[k]["index"]),
                   "cross": {str(a): ev.first_crossing(rows, a, band=bi) for a in ALPHAS}}
    R = np.diff(np.log(P))[TRAIN:]
    v = (np.asarray(IV[TRAIN:]) ** 2) * DT
    out["realized_implied_ratio"] = float((R ** 2).sum() / v.sum())
    return out


def gsadf(P):
    X = P / P[0]
    L0 = r021.r0_window(X.size)
    return float(r021.psy.sadf_gsadf(X, [L0])[L0][1])


def cvs(lengths):
    out = {}
    root = np.random.SeedSequence(r021.CV_SEED)
    for N, ss in zip(sorted(lengths), root.spawn(len(lengths))):
        st = []
        for s in ss.spawn(r021.CV_REPS // 50):
            st += [g for _, g in r021.cv_job((N, s.generate_state(2).tolist()))[1]]
        out[N] = float(np.quantile(st, 0.95))
    return out


def max_drawdown(p):
    return float(np.max(1 - p / np.maximum.accumulate(p)))


def main():
    spx, ndx = yahoo("GSPC"), yahoo("NDX")
    vix_c, vix_y, vxn_y, vxn_c = cboe("VIX"), yahoo("VIX"), yahoo("VXN"), cboe("VXN")
    vxn = {d: v for d, v in vxn_y.items() if d < VXN_CBOE_FROM} | {d: v for d, v in vxn_c.items()}
    res = {"agreement": {"VIX cboe vs yahoo": agreement(vix_c, vix_y), "VXN cboe vs yahoo": agreement(vxn_c, vxn_y)},
           "first_dates": {"SPX": str(min(spx)), "NDX": str(min(ndx)), "VIX": str(min(vix_c)), "VXN": str(min(vxn))}}
    series = {"SPX": (spx, vix_c), "NDX": (ndx, vxn)}
    windows, lengths = [], set()
    for lag in (2, 1):
        for name, (idx, iv) in series.items():
            dates, P, IV, carried = iv_series(idx, iv, lag)
            res.setdefault("carried_iv_days", {})[f"{name}|lag{lag}"] = carried
            first_ok = int(np.argmax(np.isfinite(IV)))        # first return with an IV
            starts = []
            for y in range(dates[0].year, END.year + 1):
                for m in (1, 4, 7, 10):
                    k = int(np.searchsorted(np.array(dates), dt.date(y, m, 1)))
                    if k >= first_ok + 1 and k + TRAIN + SCORED < len(dates):
                        starts.append(k)
            for k in sorted(set(starts)):
                Pw = P[k:k + TRAIN + SCORED + 1]
                IVw = IV[k:k + TRAIN + SCORED]
                if not np.isfinite(IVw).all():
                    continue
                sd = dates[k + TRAIN]
                ed = dates[k + TRAIN + SCORED]
                calm = (max_drawdown(Pw[TRAIN:]) < 0.10) and not any(a <= ed and sd <= b for a, b in NBER)
                rec = {"index": name, "lag": lag, "train_start": str(dates[k]), "score_start": str(sd),
                       "score_end": str(ed), "calm": calm, **score_record(Pw, IVw)}
                if lag == 2:
                    rec["gsadf"], rec["gsadf_n"] = gsadf(Pw), int(Pw.size)
                    lengths.add(Pw.size)
                windows.append(rec)
    episodes = []
    for lab, name, a, s, e in EPISODES:
        idx, iv = series[name]
        for lag in (2, 1):
            dates, P, IV, _ = iv_series(idx, iv, lag)
            da = np.array(dates)
            k0 = int(np.searchsorted(da, a))
            ks = int(np.searchsorted(da, s))
            ke = int(np.searchsorted(da, e, side="right")) - 1
            ktrain = ks - TRAIN                                  # exactly 126 training returns before scoring
            Pw, IVw = P[ktrain:ke + 1], IV[ktrain:ke]
            rec = {"episode": lab, "lag": lag, "train_start": str(dates[ktrain]), "requested_train_start": str(a),
                   "score_start": str(dates[ks]), "score_end": str(dates[ke]), **score_record(Pw, IVw)}
            for bn in BAND_NAMES:
                for al in ALPHAS:
                    c = rec[bn]["cross"][str(al)][0]
                    rec[bn][f"first_cross_date_{al}"] = str(dates[ktrain + c]) if c is not None else None
                rec[bn]["argmax_date"] = str(dates[ktrain + rec[bn]["argmax_index"]])
            if lag == 2:
                rec["gsadf"], rec["gsadf_n"] = gsadf(Pw), int(Pw.size)
                lengths.add(Pw.size)
            episodes.append(rec)
    cv = cvs(lengths)
    for r in windows + episodes:
        if "gsadf" in r:
            r["gsadf_cv_5%"] = cv[r["gsadf_n"]]
    summ = {}
    for name in series:
        for lag in (2, 1):
            W = [w for w in windows if w["index"] == name and w["lag"] == lag]
            C = [w for w in W if w["calm"]]
            blk = {"windows": len(W), "calm_windows": len(C)}
            for bn in BAND_NAMES:
                for al in ALPHAS:
                    kc = sum(w[bn]["cross"][str(al)][0] is not None for w in C)
                    ka = sum(w[bn]["cross"][str(al)][0] is not None for w in W)
                    blk[f"{bn}|{al}"] = {"calm_cross": kc, "calm_rate": kc / len(C) if C else None,
                                         "all_cross": ka, "all_rate": ka / len(W) if W else None,
                                         "unresolved": sum(bool(w[bn]["cross"][str(al)][1]) for w in W)}
            if lag == 2:
                blk["gsadf_5%"] = {"calm_rate": float(np.mean([w["gsadf"] > w["gsadf_cv_5%"] for w in C])) if C else None,
                                   "all_rate": float(np.mean([w["gsadf"] > w["gsadf_cv_5%"] for w in W]))}
            blk["ratio_quantiles"] = np.quantile([w["realized_implied_ratio"] for w in W], (0.05, 0.25, 0.5, 0.75, 0.95)).tolist()
            blk["by_year_primary_0.05"] = {}
            for w in W:
                y = w["score_end"][:4]
                b = blk["by_year_primary_0.05"].setdefault(y, [0, 0])
                b[0] += 1
                b[1] += w[BAND_NAMES[0]]["cross"]["0.05"][0] is not None
            summ[f"{name}|lag{lag}"] = blk
    res.update(summary=summ, episodes=episodes, windows=windows, gsadf_cv_5pct=cv,
               labels={"pre-2003-09-22 VIX": "retrospective reconstructed-scale analysis",
                       "lag1": "sensitivity; published after the return interval begins; not deployable",
                       "calm": "empirical flag frequencies on overlapping windows, not a proven size"})
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=str)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["index", "lag", "band", "alpha", "windows", "calm_windows", "calm_cross", "all_cross"])
        for k, b in summ.items():
            for bn in BAND_NAMES:
                for al in ALPHAS:
                    x = b[f"{bn}|{al}"]
                    w.writerow([*k.split("|"), bn, al, b["windows"], b["calm_windows"], x["calm_cross"], x["all_cross"]])
    print(json.dumps({"summary_keys": list(summ), "episodes": len(episodes), "windows": len(windows)}))


if __name__ == "__main__":
    main()
