"""Experiment 001: run the registered grid, write results_ladder.csv and summary.csv, print the tables.

    uv run python experiments/001/run.py
"""
import csv
import os
import sys
from multiprocessing import Pool

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from defect import exact_defect, pde_defect  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
BETAS = [0.5, 1.0, 1.5, 2.0]
H0_PIS = [0.25, 0.4, 0.5, 0.6, 0.75, 1.0, 1.5, 2.0]
NEAR_PIS = [0.45, 0.49, 0.499, 0.501, 0.51, 0.55]
TIMES = (1.0, 5.0)
KS = range(1, 9)
G2 = (0.01, 0.002)
G3 = (0.005, 0.001)
POSITIVE = 1e-5          # "clearly positive" threshold
CONVERGED = 1e-6         # e_trunc bound for method P to count as converged


def cuts(beta, k):
    if beta > 1.0:
        return 1e-6, 10.0 ** (2**k)
    if beta < 1.0:
        return 10.0 ** -(2**k), 1e6
    return 10.0 ** -(2**k), 10.0 ** (2**k)


def extra_cut(beta):
    """The registered extra run at k = 8 that moves the fixed cut, or None (beta = 1)."""
    if beta > 1.0:
        return 1e-12, 10.0**256
    if beta < 1.0:
        return 10.0**-256, 1e12
    return None


def cell(args):
    beta, pi = args
    rows = []

    def run(k, grid, eps, M, tag):
        res, e_used, m_used = pde_defect(beta, pi, eps, M, *grid, times=TIMES)
        for T, d in res.items():
            rows.append(dict(beta=beta, pi=pi, T=T, k=k, run=tag, h=grid[0], dt=grid[1],
                             eps=e_used, M=m_used, D_P=d))
        return res

    for k in KS:
        run(k, G2, *cuts(beta, k), "ladder")
    run(8, G3, *cuts(beta, 8), "fine")
    if extra_cut(beta):
        run(8, G2, *extra_cut(beta), "extra-cut")
    return rows


def predicted(beta, pi, hyp):
    if hyp == "H0":
        return beta > 1.0 and pi > 0.5
    return (beta > 1.0 and pi > 0.5) or (beta < 1.0 and pi < 0.5)


def summarize(rows):
    out = []
    keys = sorted({(r["beta"], r["pi"], r["T"]) for r in rows})
    for beta, pi, T in keys:
        rs = [r for r in rows if (r["beta"], r["pi"], r["T"]) == (beta, pi, T)]
        get = lambda k, run: next(r["D_P"] for r in rs if r["k"] == k and r["run"] == run)  # noqa: E731
        d8, d7, fine = get(8, "ladder"), get(7, "ladder"), get(8, "fine")
        extra = [r["D_P"] for r in rs if r["run"] == "extra-cut"]
        e_disc = abs(fine - d8)
        e_trunc = abs(d8 - d7) + (abs(extra[0] - d8) if extra else 0.0)
        e = e_disc + e_trunc
        converged = e_trunc <= CONVERGED
        dx = exact_defect(beta, pi, T)
        if fine - e > POSITIVE:
            reading = "positive"
        elif converged:
            reading = "zero"
        else:
            reading = "upper bound only"
        agree = (abs(fine - dx) <= 2 * e + 1e-6) if converged else None
        # The verdict reading: P where converged, X where not.
        positive = (reading == "positive") if converged else dx > POSITIVE
        row = dict(beta=beta, pi=pi, T=T, D_P=fine, e_disc=e_disc, e_trunc=e_trunc, D_X=dx,
                   P_reading=reading, P_X_agree=agree, positive=positive,
                   h0_grid=pi in H0_PIS)
        for hyp in ("H0", "H1"):
            row[f"against_{hyp}"] = (pi in H0_PIS) and (positive != predicted(beta, pi, hyp))
        out.append(row)
    return out


def write(path, rows):
    with open(path, "w", newline="") as f:
        wr = csv.DictWriter(f, fieldnames=list(rows[0]))
        wr.writeheader()
        wr.writerows(rows)


def fmt(x, col=""):
    if x is None:
        return "n/a"
    if isinstance(x, (bool, np.bool_)):
        return "yes" if x else "no"
    if col in ("beta", "pi", "T"):
        return f"{x:g}"
    if isinstance(x, float):
        return "0" if x == 0.0 else f"{x:.3e}"
    return str(x)


def threshold_ladder(rows):
    """D_P(k) * 2^k on the G2 ladder near pi = 1/2: constant means a 1/log M (or 1/log(1/eps)) leak."""
    print("\n| beta | pi | T | D_P(k)·2^k, k = 1..8 |")
    print("|---|---|---|---|")
    for beta in (0.5, 1.5, 2.0):
        for pi in (0.499, 0.5, 0.501):
            for T in TIMES:
                lad = sorted((r["k"], r["D_P"]) for r in rows if (r["beta"], r["pi"], r["T"], r["run"])
                             == (beta, pi, T, "ladder"))
                print(f"| {beta:g} | {pi:g} | {T:g} | " + " ".join(f"{d * 2**k:.3e}" for k, d in lad) + " |")


def main():
    tasks = [(b, p) for b in BETAS for p in sorted(H0_PIS + NEAR_PIS)]
    with Pool() as pool:
        rows = [r for rs in pool.map(cell, tasks) for r in rs]
    write(os.path.join(HERE, "results_ladder.csv"), rows)
    summary = summarize(rows)
    write(os.path.join(HERE, "summary.csv"), summary)

    cols = ["beta", "pi", "T", "D_P", "e_disc", "e_trunc", "D_X", "P_reading", "P_X_agree",
            "against_H0", "against_H1"]
    print("| " + " | ".join(cols) + " |")
    print("|" + "---|" * len(cols))
    for r in summary:
        print("| " + " | ".join(fmt(r[c], c) for c in cols) + " |")
    threshold_ladder(rows)
    for hyp in ("H0", "H1"):
        bad = [(r["beta"], r["pi"], r["T"]) for r in summary if r[f"against_{hyp}"]]
        print(f"{hyp}: {'against in cells ' + str(bad) if bad else 'no cell against'}")
    dis = [(r["beta"], r["pi"], r["T"]) for r in summary if r["P_X_agree"] is False]
    print(f"P/X disagreements in converged cells: {dis if dis else 'none'}")


if __name__ == "__main__":
    main()
