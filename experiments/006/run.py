"""Experiment 006: D1 zero endpoint for sigma = 1 (Case A) and sigma = 1 + x^2 (Case B). Single process.

    uv run python experiments/006/run.py

Method P is experiment 001's backward equation with a supplied log a(y); method X (Case A) is experiment 001's
exact_defect at beta = 0.  Decision rules are experiment 001's.
"""
import csv
import math
import os
import sys

import numpy as np
from scipy.sparse import diags
from scipy.sparse.linalg import splu

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "001"))
from defect import exact_defect  # noqa: E402

TIMES = (1.0, 5.0)
KS = range(1, 9)
G2, G3 = (0.01, 0.002), (0.005, 0.001)
POSITIVE, CONVERGED = 1e-5, 1e-6


def log_a_A(y):                       # sigma = 1: a = e^{-2y}
    return -2.0 * y


def log_a_B(y):                       # sigma = 1 + x^2: a = (e^{-y} + e^{y})^2 = 4 cosh^2 y
    ay = np.abs(y)
    return 2.0 * (ay + np.log1p(np.exp(-2.0 * ay)))


CASES = {
    "A": dict(log_a=log_a_A, pis=[0.1, 0.25, 0.4, 0.45, 0.49, 0.5, 0.51, 0.55, 0.6, 0.75, 1.0, 1.5, 2.0],
              cuts=lambda k: (10.0 ** -(2 ** k), 1e6), extra=(10.0 ** -256, 1e12), beta=0.0),
    "B": dict(log_a=log_a_B, pis=[0.25, 0.4, 0.5, 0.6, 0.75, 1.0],
              cuts=lambda k: (10.0 ** -(2 ** k), 10.0 ** (2 ** k)), extra=None, beta=None),
}


def pde_defect(log_a, pi, eps, M, h, dt, times=TIMES):
    """Experiment 001's method P with rows divided by a(y) = exp(log_a(y))."""
    jlo, jhi = math.floor(math.log(eps) / h), math.ceil(math.log(M) / h)
    y = h * np.arange(jlo + 1, jhi)
    i0, n = -jlo - 1, y.size
    w = np.exp(np.clip(-log_a(y), -745.0, 700.0))
    c = pi - 0.5
    L = diags([np.full(n - 1, 0.5 / h**2 - c / (2 * h)), np.full(n, -1.0 / h**2),
               np.full(n - 1, 0.5 / h**2 + c / (2 * h))], [-1, 0, 1], format="csc")
    euler = splu((diags(w) - dt * L).tocsc())
    bdf2 = splu((diags(3.0 * w) - 2.0 * dt * L).tocsc())
    record = {round(T / dt): T for T in times}
    out, u_prev = {}, np.ones(n)
    u = euler.solve(w * u_prev)
    for step in range(2, round(max(times) / dt) + 1):
        u, u_prev = bdf2.solve(w * (4.0 * u - u_prev)), u
        if step in record:
            out[record[step]] = 1.0 - u[i0]
    return out


def main():
    ladder, summary = [], []
    for case, spec in CASES.items():
        for pi in spec["pis"]:
            lad = {k: pde_defect(spec["log_a"], pi, *spec["cuts"](k), *G2) for k in KS}
            fine = pde_defect(spec["log_a"], pi, *spec["cuts"](8), *G3)
            extra = pde_defect(spec["log_a"], pi, *spec["extra"], *G2) if spec["extra"] else None
            for k, res in lad.items():
                for T, d in res.items():
                    ladder.append(dict(case=case, pi=pi, T=T, k=k, run="ladder", D_P=d))
            for T in TIMES:
                ladder.append(dict(case=case, pi=pi, T=T, k=8, run="fine", D_P=fine[T]))
                d8, d7 = lad[8][T], lad[7][T]
                e_disc = abs(fine[T] - d8)
                e_trunc = abs(d8 - d7) + (abs(extra[T] - d8) if extra else 0.0)
                e = e_disc + e_trunc
                conv = e_trunc <= CONVERGED
                if fine[T] - e > POSITIVE:
                    reading = "positive"
                elif conv:
                    reading = "zero"
                else:
                    reading = "upper bound only"
                dx = exact_defect(spec["beta"], pi, T) if spec["beta"] is not None else None
                agree = (abs(fine[T] - dx) <= 2 * e + 1e-6) if (dx is not None and conv) else None
                summary.append(dict(case=case, pi=pi, T=T, D_P=fine[T], e_disc=e_disc, e_trunc=e_trunc,
                                    D_X=dx, P_reading=reading, P_X_agree=agree,
                                    scaled_ladder=" ".join(f"{lad[k][T] * 2**k:.3e}" for k in KS)))
            print(case, pi, "done", flush=True)
    for name, rows in (("results_ladder.csv", ladder), ("summary.csv", summary)):
        with open(os.path.join(HERE, name), "w", newline="") as f:
            wr = csv.DictWriter(f, fieldnames=list(rows[0]))
            wr.writeheader()
            wr.writerows(rows)
    print("| case | π | T | D_P | e_disc | e_trunc | D_X | P reading | P/X agree |")
    print("|---|---|---|---|---|---|---|---|---|")
    for r in summary:
        dx = "—" if r["D_X"] is None else f"{r['D_X']:.6f}"
        ag = "—" if r["P_X_agree"] is None else ("yes" if r["P_X_agree"] else "NO")
        print(f"| {r['case']} | {r['pi']:g} | {r['T']:g} | {r['D_P']:.6f} | {r['e_disc']:.1e} | {r['e_trunc']:.1e} "
              f"| {dx} | {r['P_reading']} | {ag} |")


if __name__ == "__main__":
    main()
