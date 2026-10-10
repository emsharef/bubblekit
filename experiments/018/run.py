"""Experiment 018: claim 020's clipped lower bounds d_F on experiment 017's exact paths, nested monitoring sets.

    uv run python experiments/018/run.py      (start from inside .worktrees/analyst)
"""
import csv
import json
import os
from multiprocessing import Pool

import importlib.util

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
_spec = importlib.util.spec_from_file_location("e017", os.path.join(EXP, "017", "run.py"))
e017 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(e017)

WORKERS = max(1, (os.cpu_count() or 4) - 3)
KS = (64, 16, 4, 1)
CONFIGS = [c for c in e017.CONFIGS if c[0] > 1]
F = e017.F


def monitor_idx(k, n):
    """F_k: every k-th fine point together with every rebalancing time of an N = n grid (both include 0 and F)."""
    return np.union1d(np.arange(0, F + 1, k), np.arange(0, F + 1, F // n))


def clipped(X, k):
    """Z_F for every config on paths X (P, F + 1): claim 020 (1). Returns Z (C, P) and breach flags."""
    C, P = len(CONFIGS), X.shape[0]
    Z = np.empty((C, P))
    hit = np.zeros((C, P), bool)
    for ci, (pi, a, n) in enumerate(CONFIGS):
        idx = monitor_idx(k, n)
        reb = F // n
        Wi = np.ones(P)
        Xi = X[:, 0].copy()
        alive = np.ones(P, bool)
        Wn = Wi
        for j in idx[1:]:
            Wn = Wi * (1 - pi + pi * X[:, j] / Xi)
            br = alive & (Wn < a)
            Z[ci, br] = a
            hit[ci, br] = True
            alive &= ~br
            if j % reb == 0:
                Wi = np.where(alive, Wn, Wi)
                Xi = np.where(alive, X[:, j], Xi)
        Z[ci, alive] = Wn[alive]
    return Z, hit


def batch(args):
    model, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    X = e017.paths(model, rng, e017.BATCH)                 # 017's Q paths
    rng.random(X.shape)                                    # 017's bridge uniforms, consumed and discarded
    Xp, alive = e017.px_paths(model, rng, e017.BATCH)      # 017's P^X paths
    Xp = np.where(np.isfinite(Xp), Xp, 1e300)
    w = np.where(alive, 1.0 / np.where(alive, Xp[:, -1], 1.0), 0.0)
    out = {}
    for k in KS:
        Zq, hq = clipped(X, k)
        with np.errstate(invalid="ignore", over="ignore"):
            Zp, hp = clipped(Xp, k)
        out[k] = {"Zq": Zq, "hq": hq, "Zw": np.where(alive[None, :], Zp * w[None, :], 0.0), "hp": hp & alive[None, :]}
    return model, out


def stats(v):
    return float(1 - v.mean()), float(v.std(ddof=1) / np.sqrt(v.size))


def main():
    root = np.random.SeedSequence(e017.SEED)
    jobs = []
    for m, ss in zip(e017.MODELS, root.spawn(len(e017.MODELS))):
        jobs += [(m, s.generate_state(2).tolist()) for s in ss.spawn(e017.PATHS // e017.BATCH)]
    with Pool(WORKERS) as pool:
        parts = pool.map(batch, jobs)
    ref = json.load(open(os.path.join(EXP, "017", "results.json")))["cells"]
    res, rows = {"KS": KS, "cells": {}}, []
    for m in e017.MODELS:
        ps = [o for mm, o in parts if mm == m]
        res["cells"][m] = {}
        for ci, (pi, a, n) in enumerate(CONFIGS):
            cell = {"d_H_017_bridge_primary": ref[m][f"{pi}|{a}|{n}"]["px_bridge"]["d_H"],
                    "d_H_017_se": ref[m][f"{pi}|{a}|{n}"]["px_bridge"]["se"]}
            for k in KS:
                Zq = np.concatenate([o[k]["Zq"][ci] for o in ps])
                Zw = np.concatenate([o[k]["Zw"][ci] for o in ps])
                dq, sq = stats(Zq)
                dp, sp = stats(Zw)
                cell[f"k{k}"] = {"d_F_px": dp, "se_px": sp, "d_F_q": dq, "se_q": sq,
                                 "breach_q": float(np.concatenate([o[k]["hq"][ci] for o in ps]).mean()),
                                 "top10_q": float(np.sort(Zq)[-10:].sum() / Zq.sum()),
                                 "ess_px": float(Zw.sum() ** 2 / (Zw ** 2).sum())}
                rows.append([m, pi, a, n, k, dp, sp, dq, sq, cell[f"k{k}"]["breach_q"], cell[f"k{k}"]["top10_q"],
                             cell[f"k{k}"]["ess_px"], cell["d_H_017_bridge_primary"]])
            res["cells"][m][f"{pi}|{a}|{n}"] = cell
        print(m, "done", flush=True)
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(res, f, indent=1)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as f:
        wr = csv.writer(f)
        wr.writerow(["model", "pi", "a", "N", "k", "d_F_px", "se_px", "d_F_q", "se_q", "breach_frac_q", "top10_q",
                     "ess_px", "d_H_017"])
        wr.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
