"""Experiment 015: size and power of GSADF/SADF, JKP, the Liu-Phillips-Yu panel test and OPY on known-answer models.

    uv run python experiments/015/run.py      (start from inside .worktrees/analyst)
"""
import csv
import json
import os
import sys
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
for d in ("002", "003", "004", "005"):
    sys.path.insert(0, os.path.join(EXP, d))
sys.path.insert(0, HERE)
import jkp  # noqa: E402
import models  # noqa: E402
import opy  # noqa: E402
import panel  # noqa: E402
import psy  # noqa: E402

WORKERS = max(1, (os.cpu_count() or 4) - 3)
SINGLE_PATHS, OPY_PATHS, PANEL_SIZE = 1000, 400, 20
CV_REPS, CV_SEED = 2000, 20261016
PANEL_CV = {"5%": 1.64, "10%": 1.28}
MONTH = 21 * models.BARS_PER_DAY            # 1,638 increments
SIGNAL_DAYS = models.TAIL_DAYS - 21         # 63


def r0_window(N):
    return int(np.floor((0.01 + 1.8 / np.sqrt(N)) * N))


def cv_job(args):
    N, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    L0 = r0_window(N)
    out = []
    for y in psy.null_paths(rng, 50, N):
        s, g = psy.sadf_gsadf(y, [L0])[L0]
        out.append((s, g))
    return N, out


def jkp_verdicts(S, min_obs):
    """Method 2 verdict and Method 1 (strict) verdict, as in experiment 003; failures are 'failed'."""
    if (S <= 0).any():
        S = S[:int(np.argmax(S <= 0))]
    try:
        xs, h = jkp.grid(S)
        if xs.size == 0:
            return "failed", "failed"
        fz, jk, N = jkp.nonparametric(S, xs, h)
        jk[N < min_obs] = np.nan
        good = np.isfinite(jk) & (jk > 0)
        if not good.any():
            return "failed", "failed"
        m2 = jkp.method2(xs, jk, S.min(), S.max())["verdict"]
        try:
            s0, a1 = jkp.gcj(S, "f1")
            m1 = jkp.method1(xs[good], np.sqrt(jk[good]), s0, a1)
        except Exception:
            m1 = "failed"
        return m2, m1
    except Exception:
        return "failed", "failed"


def opy_path(tail):
    nu, indet = [], 0
    for k in range(SIGNAL_DAYS):
        win = tail[k * models.BARS_PER_DAY: (k + 21) * models.BARS_PER_DAY + 1]
        v, _ = jkp_verdicts(win, 100)
        nu.append(v == "bubble")
        indet += v in ("inconclusive", "failed")
    nu = np.array(nu)
    h = opy.viterbi(nu, opy.B_TABLE2)
    closes = tail[21 * models.BARS_PER_DAY::models.BARS_PER_DAY][1:]          # close of each signal day
    _, kinds = opy.lifetimes(closes, h)
    return {"bubble": "birth" in kinds, "indet_share": indet / SIGNAL_DAYS, "plus_share": float(nu.mean())}


def job(args):
    model, T, b, cvs = args
    daily, tail = models.batch(model, T, b)
    month = tail[:, -(MONTH + 1):]
    out = {"model": model, "T": T, "b": b, "single": [], "panel": [], "opy": []}
    first = b * models.BATCH
    for i in range(daily.shape[0]):
        if first + i >= SINGLE_PATHS:
            break
        rec = {"absorbed": bool(daily[i, -1] <= 0)}
        for name, S in (("daily", daily[i]), ("month", month[i])):
            N = S.size
            L0 = r0_window(N)
            s, g = psy.sadf_gsadf(S, [L0])[L0]
            rec[name] = {"sadf": float(s), "gsadf": float(g), "sadf_rej": {lv: bool(s > cvs[N]["sadf"][lv]) for lv in ("5%", "10%")},
                         "gsadf_rej": {lv: bool(g > cvs[N]["gsadf"][lv]) for lv in ("5%", "10%")}}
            rec[name]["jkp_m2"], rec[name]["jkp_m1"] = jkp_verdicts(S, jkp.MIN_OBS)
        out["single"].append(rec)
    for p in range(0, daily.shape[0], PANEL_SIZE):
        pr = {}
        for name, Y in (("daily", daily[p:p + PANEL_SIZE]), ("month", month[p:p + PANEL_SIZE])):
            _, J, _, tinv = panel.panel_tests(Y, np.arange(Y.shape[0]))
            pr[name] = {"t": float(tinv), "J": float(J)}
        out["panel"].append(pr)
    for i in range(daily.shape[0]):
        if first + i >= OPY_PATHS:
            break
        out["opy"].append(opy_path(tail[i]))
    return out


def rate(x):
    x = np.asarray(x, float)
    p = float(x.mean()) if x.size else float("nan")
    return {"rate": p, "se": float(np.sqrt(p * (1 - p) / x.size)) if x.size else None, "n": int(x.size)}


def main():
    Ns = sorted({models.DAYS_PER_YEAR * T + 1 for T in models.HORIZONS} | {MONTH + 1})
    root = np.random.SeedSequence(CV_SEED)
    cv_jobs = [(N, s.generate_state(2).tolist()) for N, ss in zip(Ns, root.spawn(len(Ns)))
               for s in ss.spawn(CV_REPS // 50)]
    with Pool(WORKERS) as pool:
        stats = {N: [] for N in Ns}
        for N, o in pool.map(cv_job, cv_jobs):
            stats[N] += o
        cvs = {}
        for N in Ns:
            a = np.array(stats[N])
            cvs[N] = {k: {"5%": float(np.quantile(a[:, j], 0.95)), "10%": float(np.quantile(a[:, j], 0.90))}
                      for j, k in enumerate(("sadf", "gsadf"))}
        print("critical values", json.dumps(cvs), flush=True)
        jobs = [(m, T, b, cvs) for b in range(models.BATCHES) for T in models.HORIZONS[::-1] for m in models.MODELS]
        parts = pool.map(job, jobs, chunksize=1)
    res = {"critical_values": {str(N): v for N, v in cvs.items()}, "cells": {}}
    rows = []
    for m, (kind, prm, mart) in models.MODELS.items():
        for T in models.HORIZONS:
            ps = [p for p in parts if p["model"] == m and p["T"] == T]
            single = [r for p in ps for r in p["single"]]
            pan = [r for p in ps for r in p["panel"]]
            op = [r for p in ps for r in p["opy"]]
            cell = {"label": "size" if mart else "power", "absorbed": rate([r["absorbed"] for r in single])}
            for s in ("daily", "month"):
                c = {}
                for t in ("sadf", "gsadf"):
                    c[t] = {lv: rate([r[s][f"{t}_rej"][lv] for r in single]) for lv in ("5%", "10%")}
                for meth in ("jkp_m2", "jkp_m1"):
                    v = [r[s][meth] for r in single]
                    c[meth] = {"bubble": rate([x == "bubble" for x in v]),
                               "indeterminate": rate([x in ("inconclusive", "failed") for x in v]),
                               "failed": rate([x == "failed" for x in v])}
                for t in ("t", "J"):
                    c["panel_" + t] = {lv: rate([r[s][t] > cv for r in pan]) for lv, cv in PANEL_CV.items()}
                cell[s] = c
                rows.append([m, T, s, cell["label"]] + [c[t][lv]["rate"] for t in ("sadf", "gsadf") for lv in ("5%", "10%")]
                            + [c["jkp_m2"]["bubble"]["rate"], c["jkp_m2"]["indeterminate"]["rate"], c["jkp_m1"]["bubble"]["rate"]]
                            + [c["panel_" + t][lv]["rate"] for t in ("t", "J") for lv in ("5%", "10%")])
            cell["opy"] = {"bubble": rate([r["bubble"] for r in op]),
                           "indet_share_mean": float(np.mean([r["indet_share"] for r in op])),
                           "plus_share_mean": float(np.mean([r["plus_share"] for r in op]))}
            res["cells"][f"{m}|{T}"] = cell
            print(m, T, "opy", cell["opy"]["bubble"]["rate"], flush=True)
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(res, f, indent=1)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["model", "T", "sampling", "label", "sadf5", "sadf10", "gsadf5", "gsadf10", "jkp_m2_bubble",
                    "jkp_m2_indeterminate", "jkp_m1_bubble", "panel_t5", "panel_t10", "panel_J5", "panel_J10"])
        w.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
