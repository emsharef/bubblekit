"""Experiment 045: experiment 040's calibrated GSADF thresholds on experiment 039's unselected universe.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/045/run.py

Reads 039's stored windows.csv.gz and results.json and 040's results.json; recomputes no statistic. Writes
results.json and summary.csv.
"""
import csv
import datetime as dt
import gzip
import importlib.util
import json
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


r039 = _load("r039", "experiments/039/run.py")
SEED = 20261045
OUTS = ("mdd63", "mdd126", "ret63", "ret126")
PERIODS = {"1995-99": (1995, 1999), "2003-07": (2003, 2007), "2009-19": (2009, 2019), "2023-26": (2023, 2026)}


def load():
    rows = []
    with gzip.open(os.path.join(EXP, "039", "windows.csv.gz"), "rt") as fh:
        for r in csv.DictReader(fh):
            rows.append({"L": int(r["L"]), "sym": r["sym"], "start": r["start"], "end_year": int(r["end"][:4]),
                         "n": int(r["n"]), "gsadf": float(r["gsadf"]), "p": float(r["gsadf_p"]),
                         **{o: float(r[o]) for o in OUTS}})
    return rows


def regress(R, flag, L):
    starts = np.array([r["start"] for r in R])
    names = np.array([r["sym"] for r in R])
    smonth = np.array([int(s[:4]) * 12 + int(s[5:7]) for s in starts])
    train = np.array([dt.date.fromisoformat(s) < r039.OOS_SPLIT for s in starts])
    X = np.column_stack([np.ones(len(R)), flag.astype(float)])
    out = {"flag_share": float(flag.mean()), "n": len(R)}
    for o in OUTS:
        y = np.array([r[o] for r in R])
        b, u = r039.ols(y, X)
        sedk = r039.dk_se(X, u, smonth, math.ceil(1.5 * L))
        se2 = r039.twoway_se(X, u, starts, names)
        xd, yd = X[:, 1].copy(), y.copy()
        for g in np.unique(starts):
            m = starts == g
            xd[m] -= xd[m].mean()
            yd[m] -= yd[m].mean()
        bfe, ufe = r039.ols(yd, xd[:, None])
        sefe = r039.dk_se(xd[:, None], ufe, smonth, math.ceil(1.5 * L))
        bt, _ = r039.ols(y[train], X[train])
        ybar = y[train].mean()
        yh = X[~train] @ bt
        r2 = 1 - ((y[~train] - yh) ** 2).sum() / ((y[~train] - ybar) ** 2).sum()
        tm = np.unique(smonth[~train])
        rng = np.random.default_rng(np.random.SeedSequence([SEED, L]))
        nb = max(1, len(tm) // L)
        boots = []
        for _ in range(1000):
            pick = []
            for _b in range(nb):
                s0 = rng.integers(0, max(1, len(tm) - L + 1))
                pick.extend(tm[s0:s0 + L])
            m = np.isin(smonth, pick) & ~train
            if m.sum() < 10:
                continue
            boots.append(1 - ((y[m] - X[m] @ bt) ** 2).sum() / ((y[m] - ybar) ** 2).sum())
        out[o] = {"coef": float(b[1]), "intercept": float(b[0]), "se_dk": float(sedk[1]), "se_twoway": float(se2[1]),
                  "coef_fe": float(bfe[0]), "se_fe_dk": float(sefe[0]), "oos_r2": float(r2),
                  "oos_r2_boot_se": float(np.std(boots, ddof=1)) if boots else None,
                  "flagged_mean": float(y[flag].mean()) if flag.any() else None,
                  "unflagged_mean": float(y[~flag].mean())}
    return out


def main():
    rows = load()
    res039 = json.load(open(os.path.join(EXP, "039", "results.json")))
    cv = {int(k): v for k, v in res039["critical_values_95"].items()}
    thr = json.load(open(os.path.join(EXP, "040", "results.json")))["results"]
    T = {"daily|full": {a: thr["daily|full"][a]["threshold_p_all_calm"] for a in ("0.05", "0.1")},
         "daily|to_peak (sensitivity)": {a: thr["daily|to_peak"][a]["threshold_p_all_calm"] for a in ("0.05", "0.1")}}
    res = {"thresholds_p": T, "rates": {}, "regressions": {}}
    for L in r039.LENGTHS:
        R = [r for r in rows if r["L"] == L]
        p = np.array([r["p"] for r in R])
        nom = np.array([r["gsadf"] > cv[r["n"]] for r in R])
        ey = np.array([r["end_year"] for r in R])
        blk = {}
        for setname, th in T.items():
            for a, t in th.items():
                f = p <= t + 1e-12
                blk[f"{setname}|{a}"] = {
                    "pooled": float(f.mean()),
                    "by_year": {str(y): float(f[ey == y].mean()) for y in sorted(set(ey.tolist()))},
                    "by_period": {k: float(f[(ey >= lo) & (ey <= hi)].mean()) for k, (lo, hi) in PERIODS.items()
                                  if ((ey >= lo) & (ey <= hi)).any()}}
        blk["nominal"] = {"pooled": float(nom.mean()),
                          "by_period": {k: float(nom[(ey >= lo) & (ey <= hi)].mean()) for k, (lo, hi) in PERIODS.items()
                                        if ((ey >= lo) & (ey <= hi)).any()}}
        res["rates"][str(L)] = blk
        res["regressions"][str(L)] = {a: regress(R, p <= T["daily|full"][a] + 1e-12, L) for a in ("0.05", "0.1")}
        res["regressions"][str(L)]["rank_039"] = {o: {"coef": res039["regressions"][str(L)][o]["gsadf"]["coef"][0],
                                                     "se_dk": res039["regressions"][str(L)][o]["gsadf"]["se_dk"][0],
                                                     "oos_r2": res039["regressions"][str(L)][o]["gsadf"]["oos_r2"]}
                                                 for o in OUTS}
        print("L", L, "done", flush=True)
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["L", "alpha", "flag_share", "outcome", "coef", "se_dk", "se_twoway", "oos_r2", "oos_r2_boot_se"])
        for L, b in res["regressions"].items():
            for a in ("0.05", "0.1"):
                for o in OUTS:
                    x = b[a][o]
                    w.writerow([L, a, b[a]["flag_share"], o, x["coef"], x["se_dk"], x["se_twoway"], x["oos_r2"],
                                x["oos_r2_boot_se"]])
    print("done")


if __name__ == "__main__":
    main()
