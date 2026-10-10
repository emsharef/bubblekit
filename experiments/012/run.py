"""Experiment 012: uniform integrability of the finite-grid fund W^(N)_T and its mean vs the continuous E V_T.

    uv run python experiments/012/run.py      (start from inside .worktrees/analyst)
"""
import csv
import json
import os
import sys
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "008"))
from rebal import continuous_defect, fund_defects, log_a_cev  # noqa: E402

WORKERS = max(1, (os.cpu_count() or 4) - 3)
SEED = 20261012
F = 4032
BETAS = (1.0, 1.5, 2.0)
PIS = (-1.0, 0.25, 0.75, 2.0, 3.0)
NS = (4, 16, 64, 252, 1008)
KS = (2, 5, 10, 50)
PATHS, BATCH = 400_000, 1000
TOP = 10


def sim_grid(rng, beta, reps):
    dt = 1.0 / F
    if beta == 1.0:
        Wb = np.concatenate([np.zeros((reps, 1)), np.cumsum(np.sqrt(dt) * rng.standard_normal((reps, F)), 1)], 1)
        return np.exp(Wb - 0.5 * np.arange(F + 1) * dt)
    d = 3 if beta == 2.0 else 4
    x0 = 1.0 if beta == 2.0 else 2.0
    X = np.concatenate([np.zeros((reps, 1, d)), np.cumsum(np.sqrt(dt) * rng.standard_normal((reps, F, d)), 1)], 1)
    X[:, :, 0] += x0
    R = np.linalg.norm(X, axis=2)
    return 1.0 / R if beta == 2.0 else 4.0 / R**2


def fund_T(S, pi, N):
    Si = S[:, :: F // N]
    W = np.ones(S.shape[0])
    for i in range(N):
        W = W * ((1 - pi) + pi * Si[:, i + 1] / Si[:, i])
    return W


def batch(args):
    beta, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    S = sim_grid(rng, beta, BATCH)
    out = {}
    for pi in PIS:
        for N in NS:
            W = fund_T(S, pi, N)
            A = np.abs(W)
            rec = {"n": W.size, "sW": W.sum(), "sW2": (W * W).sum(), "sA": A.sum(), "sA2": (A * A).sum(),
                   "top": np.sort(A)[-TOP:].tolist()}
            for K in KS:
                t = A * (A > K)
                rec[f"sT{K}"], rec[f"sT2{K}"] = t.sum(), (t * t).sum()
            out[f"{pi}|{N}"] = rec
    return beta, out


def cuts(beta, k=6):
    return (10.0 ** -(2 ** k), 10.0 ** (2 ** k)) if beta == 1.0 else (1e-8, 10.0 ** (2 ** k))


def targeted(args):
    beta, pi = args
    la = log_a_cev(beta)
    r = {"EV": 1.0 - continuous_defect(la, pi, *cuts(beta), 0.005, 1.0 / F, [1.0])[1.0]}
    stable_ns = NS if 0.0 <= pi <= 1.0 else (4, 16)
    r["EW_recursion"] = {}
    for N in stable_ns:
        d1 = fund_defects(la, pi, *cuts(beta), 0.01, 1.0 / N, 40, [N])[0][N]
        d2 = fund_defects(la, pi, *cuts(beta), 0.005, 1.0 / N, 80, [N])[0][N]
        r["EW_recursion"][N] = {"EW": 1.0 - d2, "err": abs(d2 - d1)}
    return beta, pi, r


def mean_se(s, s2, n):
    m = s / n
    return m, float(np.sqrt(max(s2 / n - m * m, 0.0) / n))


def main():
    root = np.random.SeedSequence(SEED)
    jobs = []
    for beta, ss in zip(BETAS, root.spawn(len(BETAS))):
        jobs += [(beta, s.generate_state(2).tolist()) for s in ss.spawn(PATHS // BATCH)]
    with Pool(WORKERS) as pool:
        parts = pool.map(batch, jobs)
        tg = pool.map(targeted, [(b, p) for b in BETAS for p in PIS])
    tmap = {(b, p): r for b, p, r in tg}
    res, rows = {"paths": PATHS, "F": F, "cases": {}}, []
    for beta in BETAS:
        bp = [o for b, o in parts if b == beta]
        for pi in PIS:
            case = {"EV_continuous": tmap[(beta, pi)]["EV"], "N": {}}
            sup = {K: (-1.0, None) for K in KS}
            for N in NS:
                recs = [o[f"{pi}|{N}"] for o in bp]
                n = sum(r["n"] for r in recs)
                tot = lambda k: float(sum(r[k] for r in recs))  # noqa: E731
                EW, seW = mean_se(tot("sW"), tot("sW2"), n)
                EA, seA = mean_se(tot("sA"), tot("sA2"), n)
                top = sorted(sum((r["top"] for r in recs), []))[-TOP:]
                e = {"EW": EW, "se_EW": seW, "EabsW": EA, "se_EabsW": seA,
                     "top10_share_of_EabsW": float(sum(top) / tot("sA")) if tot("sA") > 0 else None,
                     "max_absW": top[-1], "tail": {}}
                for K in KS:
                    m, se = mean_se(tot(f"sT{K}"), tot(f"sT2{K}"), n)
                    e["tail"][K] = {"E": m, "se": se}
                    if m > sup[K][0]:
                        sup[K] = (m, N)
                rc = tmap[(beta, pi)]["EW_recursion"].get(N)
                if rc:
                    e["EW_recursion"] = rc["EW"]
                    e["recursion_err"] = rc["err"]
                    e["agree"] = bool(abs(rc["EW"] - EW) <= 3 * seW + rc["err"])
                case["N"][N] = e
                rows.append([beta, pi, N, EW, seW, EA, seA, case["EV_continuous"]] +
                            [e["tail"][K]["E"] for K in KS] + [e["top10_share_of_EabsW"], e.get("EW_recursion"),
                                                               e.get("agree")])
            case["ui_sup_over_N"] = {K: {"E": v, "at_N": N_} for K, (v, N_) in sup.items()}
            res["cases"][f"{beta}|{pi}"] = case
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(res, f, indent=1, default=float)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["beta", "pi", "N", "EW", "se_EW", "EabsW", "se_EabsW", "EV_cont"] + [f"tail_K{K}" for K in KS] +
                   ["top10_share", "EW_recursion", "agree"])
        w.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
