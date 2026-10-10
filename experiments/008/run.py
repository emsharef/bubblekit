"""Experiment 008: discretely rebalanced fixed-share fund vs pi*delta and D1's continuous limit; inverse breaches.

    uv run python experiments/008/run.py
"""
import csv
import json
import os
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "001"))
from defect import exact_defect  # noqa: E402
from rebal import (breach_horizon, breach_one_interval, continuous_defect, fund_defects, log_a_cev,  # noqa: E402
                   log_a_quad)

WORKERS = max(1, (os.cpu_count() or 4) - 3)       # leave at least 3 cores free for Lean CI
PIS = [-3, -2, -1, 0.25, 0.75, 2, 3]
DELTAS = {"day": (1 / 252, 40, 252), "week": (1 / 52, 40, 52), "month": (1 / 12, 160, 12)}   # (Delta, m, per year)
KS = (4, 5, 6)
H, H2 = 0.01, 0.005
CASES = {
    "cev0.5": dict(log_a=log_a_cev(0.5), beta=0.5, cuts=lambda k: (10.0 ** -(2 ** k), 1e8)),
    "cev1.5": dict(log_a=log_a_cev(1.5), beta=1.5, cuts=lambda k: (1e-8, 10.0 ** (2 ** k))),
    "cev2": dict(log_a=log_a_cev(2.0), beta=2.0, cuts=lambda k: (1e-8, 10.0 ** (2 ** k))),
    "1+x^2": dict(log_a=log_a_quad, beta=None, cuts=lambda k: (10.0 ** -(2 ** k), 10.0 ** (2 ** k))),
}


def job(args):
    case, pi, dname = args
    spec = CASES[case]
    Delta, m, per_year = DELTAS[dname]
    n_rec = [1, per_year, 5 * per_year]
    T_of = {1: Delta, per_year: 1.0, 5 * per_year: 5.0}
    lad, cont = {}, {}
    for k in KS:
        d, delta1, a1 = fund_defects(spec["log_a"], pi, *spec["cuts"](k), H, Delta, m, n_rec)
        lad[k] = (d, delta1, a1)
        cont[k] = continuous_defect(spec["log_a"], pi, *spec["cuts"](k), H, Delta / m, list(T_of.values()))
    d2, delta2, a2 = fund_defects(spec["log_a"], pi, *spec["cuts"](6), H2, Delta, 2 * m, n_rec)
    c2 = continuous_defect(spec["log_a"], pi, *spec["cuts"](6), H2, Delta / (2 * m), list(T_of.values()))
    rows = []
    for n in n_rec:
        T = T_of[n]
        D = d2[n]
        e = abs(d2[n] - lad[6][0][n]) + abs(lad[6][0][n] - lad[5][0][n])
        Dc = c2[T]
        ec = abs(c2[T] - cont[6][T]) + abs(cont[6][T] - cont[5][T])
        exact_c = exact_defect(spec["beta"], pi, T) if (spec["beta"] is not None and pi > 0) else None
        rows.append(dict(case=case, pi=pi, Delta=dname, T=round(T, 6), intervals=n, D_discrete=D, err_discrete=e,
                         D_continuous=Dc, err_continuous=ec, D_continuous_exact=exact_c))
    exact_delta = exact_defect(spec["beta"], 1.0, Delta) if spec["beta"] is not None else None
    one = dict(case=case, pi=pi, Delta=dname, delta_num=delta2, delta_err=abs(delta2 - lad[6][1]) + abs(lad[6][1] - lad[5][1]),
               delta_exact=exact_delta, A_one_interval=a2, D_one=d2[1], pi_delta=pi * delta2,
               D_one_minus_pi_delta=d2[1] - pi * delta2)
    return rows, one


def bjob(args):
    case, pi, dname = args
    spec = CASES[case]
    Delta, m, per_year = DELTAS[dname]
    out = dict(case=case, pi=pi, Delta=dname,
               one_interval=breach_one_interval(spec["log_a"], pi, Delta, m),
               one_interval_fine=breach_one_interval(spec["log_a"], pi, Delta, 2 * m, h_target=0.0025))
    if dname in ("week", "month"):
        bh = breach_horizon(spec["log_a"], pi, Delta, max(10, m // 4), [per_year, 5 * per_year])
        out["horizon_T1"], out["horizon_T5"] = bh[per_year], bh[5 * per_year]
    return out


def main():
    jobs = [(c, p, d) for c in CASES for p in PIS for d in DELTAS]
    bjobs = [(c, p, d) for c in CASES for p in PIS if p < 0 for d in DELTAS]
    with Pool(WORKERS) as pool:
        res = pool.map(job, jobs)
        bres = pool.map(bjob, bjobs)
    rows = [r for rs, _ in res for r in rs]
    ones = [o for _, o in res]
    for name, data in (("summary.csv", rows), ("one_interval.csv", ones), ("breach.csv", bres)):
        with open(os.path.join(HERE, name), "w", newline="") as f:
            keys = sorted({k for r in data for k in r}, key=lambda k: list(data[0]).index(k) if k in data[0] else 99)
            w = csv.DictWriter(f, fieldnames=keys)
            w.writeheader()
            w.writerows(data)
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump({"workers": WORKERS, "rows": rows, "one_interval": ones, "breach": bres}, f, indent=1, default=float)
    print("done", len(rows), len(ones), len(bres))


if __name__ == "__main__":
    main()
