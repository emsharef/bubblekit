"""Experiment 017: defect of floor-liquidated leveraged (and inverse) funds under refinement, claims 011 and 018.

    uv run python experiments/017/run.py      (start from inside .worktrees/analyst)
"""
import csv
import json
import math
import os
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
WORKERS = max(1, (os.cpu_count() or 4) - 3)
SEED = 20261017
F = 19656                      # 78 steps a day x 252 days; every N divides it
COARSE = 6                     # refinement check on every 6th point (Deviation 1)
PATHS, BATCH = 20000, 250
PIS = (1.5, 2.0, 3.0, -1.0, -3.0)
FLOORS = (0.0, 0.5)
NS = (1, 4, 12, 52, 252)
MODELS = ("bes3", "cev1.5", "gbm")
DELTA = {"bes3": 1 - math.erf(1 / math.sqrt(2)), "cev1.5": math.exp(-2), "gbm": 0.0}
CONFIGS = [(p, a, n) for p in PIS for a in FLOORS for n in NS]


def paths(model, rng, n):
    dt = 1.0 / F
    if model == "gbm":
        W = np.concatenate([np.zeros((n, 1)), np.cumsum(np.sqrt(dt) * rng.standard_normal((n, F)), 1)], 1)
        return np.exp(W - 0.5 * np.arange(F + 1) * dt)
    d, x0 = (3, 1.0) if model == "bes3" else (4, 2.0)
    B = np.cumsum(np.sqrt(dt) * rng.standard_normal((n, F, d)), 1)
    B = np.concatenate([np.zeros((n, 1, d)), B], 1)
    B[:, :, 0] += x0
    r2 = np.einsum("ijk,ijk->ij", B, B)
    return 1.0 / np.sqrt(r2) if model == "bes3" else 4.0 / r2


def px_paths(model, rng, n):
    """Paths under P^X (X as numeraire, Deviation 2), exact on the fine grid; returns X and the survival flag.

    E_Q[F] = E_{P^X}[F / X_T ; survival]. BES3: beta = 1/X is a 1-d Brownian motion from 1 absorbed at 0 (bridge test
    between grid points). CEV 1.5: Z = 4/X is BESQ(0) from 4, absorbed at 0. GBM: ln X = W + t/2."""
    dt = 1.0 / F
    if model == "gbm":
        W = np.concatenate([np.zeros((n, 1)), np.cumsum(np.sqrt(dt) * rng.standard_normal((n, F)), 1)], 1)
        return np.exp(W + 0.5 * np.arange(F + 1) * dt), np.ones(n, bool)
    if model == "bes3":
        b = np.concatenate([np.ones((n, 1)), 1 + np.cumsum(np.sqrt(dt) * rng.standard_normal((n, F)), 1)], 1)
        u = rng.random((n, F))
        hit = (b[:, 1:] <= 0) | (u < np.exp(-2 * np.maximum(b[:, :-1], 0) * np.maximum(b[:, 1:], 0) / dt))
        dead = np.concatenate([np.zeros((n, 1), bool), np.logical_or.accumulate(hit, 1)], 1)
        b = np.where(dead | (b <= 0), np.nan, b)
        X = 1.0 / b
        return np.where(np.isnan(X), np.inf, X), ~dead[:, -1]
    Z = np.empty((n, F + 1))
    Z[:, 0] = 4.0
    for k in range(F):
        P = rng.poisson(Z[:, k] / (2 * dt))
        Z[:, k + 1] = np.where(P > 0, 2 * dt * rng.gamma(np.maximum(P, 1), 1.0), 0.0)
    with np.errstate(divide="ignore"):
        X = 4.0 / Z
    return X, Z[:, -1] > 0


def logvar(model, x):
    if model == "gbm":
        return np.ones_like(x)
    return x * x if model == "bes3" else x


def engine(model, X, U, stride, bridge):
    """Run all CONFIGS on the grid X[:, ::stride]; returns H_T (C, P), liquidated flags, breach sizes, X at stop."""
    Xg = X[:, ::stride]
    Ug = U[:, ::stride]
    K = Xg.shape[1] - 1
    dt = stride / F
    pi = np.array([c[0] for c in CONFIGS])[:, None]
    a = np.array([c[1] for c in CONFIGS])[:, None]
    reb = np.array([F // c[2] // stride for c in CONFIGS])[:, None]
    C, P = len(CONFIGS), Xg.shape[0]
    Wi = np.ones((C, P))
    Xi = np.repeat(Xg[None, :, 0], C, 0)
    alive = np.ones((C, P), bool)
    H = np.empty((C, P))
    breach = np.zeros((C, P))
    xstop = np.empty((C, P))
    Wn = Wi.copy()
    for k in range(1, K + 1):
        xk, xp = Xg[:, k], Xg[:, k - 1]
        Wn = Wi * (1 - pi + pi * xk[None, :] / Xi)
        liq = alive & (Wn < a)
        if bridge:
            with np.errstate(divide="ignore", invalid="ignore"):
                b = Xi * (1 - (1 - a / Wi) / pi)
                lb = np.log(b)
                prod = (np.log(xp)[None, :] - lb) * (np.log(xk)[None, :] - lb)
                v = logvar(model, np.sqrt(xp * xk))[None, :]
                p = np.where(prod > 0, np.exp(-2 * prod / (v * dt)), 1.0)
            liq |= alive & (Ug[None, :, k] < p)
            H[liq] = np.broadcast_to(a, (C, P))[liq]
            xstop[liq] = b[liq]
        else:
            H[liq] = Wn[liq]
            breach[liq] = (np.broadcast_to(a, (C, P)) - Wn)[liq]
            xstop[liq] = np.broadcast_to(xk, (C, P))[liq]
        alive &= ~liq
        rb = (k % reb == 0) & alive
        Wi = np.where(rb, Wn, Wi)
        Xi = np.where(rb, xk[None, :], Xi)
    H[alive] = Wn[alive]
    xstop[alive] = np.broadcast_to(Xg[:, -1], (C, P))[alive]
    return H, ~alive, breach, xstop


def batch(args):
    model, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    out = {}
    X = paths(model, rng, BATCH)
    U = rng.random(X.shape)
    for tag, stride, bridge in (("bridge", 1, True), ("discrete", 1, False), ("bridge_coarse", COARSE, True)):
        H, liq, br, xs = engine(model, X, U, stride, bridge)
        out[tag] = {"H": H, "liq": liq, "breach": br, "xstop": xs}
    out["XT"] = X[:, -1]
    Xp, alive = px_paths(model, rng, BATCH)
    Up = rng.random(Xp.shape)
    wts = np.where(alive, 1.0 / np.where(alive, Xp[:, -1], 1.0), 0.0)
    for tag, stride in (("px_bridge", 1), ("px_bridge_coarse", COARSE)):
        with np.errstate(invalid="ignore", divide="ignore", over="ignore"):
            H, liq, _, _ = engine(model, np.where(np.isfinite(Xp), Xp, 1e300), Up, stride, True)
        out[tag] = {"Hw": np.where(alive[None, :], H * wts[None, :], 0.0), "liq": liq & alive[None, :]}
    out["px_alive"], out["px_w"] = alive, wts
    return model, out


def main():
    root = np.random.SeedSequence(SEED)
    jobs = []
    for m, ss in zip(MODELS, root.spawn(len(MODELS))):
        jobs += [(m, s.generate_state(2).tolist()) for s in ss.spawn(PATHS // BATCH)]
    with Pool(WORKERS) as pool:
        parts = pool.map(batch, jobs)
    res, rows = {"F": F, "coarse": COARSE, "paths": PATHS, "delta": DELTA, "cells": {}}, []
    for m in MODELS:
        ps = [o for mm, o in parts if mm == m]
        XT = np.concatenate([o["XT"] for o in ps])
        alive = np.concatenate([o["px_alive"] for o in ps])
        wq = np.concatenate([o["px_w"] for o in ps])
        res["cells"][m] = {"mc_delta": float(1 - XT.mean()), "mc_delta_se": float(XT.std(ddof=1) / np.sqrt(XT.size)),
                           "px_delta": float(1 - alive.mean()), "px_E_one": float(wq.mean())}
        for ci, (pi, a, n) in enumerate(CONFIGS):
            cell = {}
            for tag in ("bridge", "discrete", "bridge_coarse"):
                H = np.concatenate([o[tag]["H"][ci] for o in ps])
                liq = np.concatenate([o[tag]["liq"][ci] for o in ps])
                top = np.sort(H)[-10:].sum() / H.sum() if H.sum() > 0 else None
                cell[tag] = {"d_H": float(1 - H.mean()), "se": float(H.std(ddof=1) / np.sqrt(H.size)),
                             "liq_prob": float(liq.mean()), "top10_share": top}
                if tag == "discrete":
                    cell[tag]["breach_mean"] = float(np.concatenate([o[tag]["breach"][ci] for o in ps]).mean())
                if tag == "bridge" and n == 1:
                    xs = np.concatenate([o[tag]["xstop"][ci] for o in ps])
                    cell["n1_formula_d_H"] = float(pi * (1 - xs.mean()))
            for tag in ("px_bridge", "px_bridge_coarse"):
                Hw = np.concatenate([o[tag]["Hw"][ci] for o in ps])
                ess = float(Hw.sum() ** 2 / (Hw ** 2).sum()) if (Hw ** 2).sum() > 0 else None
                cell[tag] = {"d_H": float(1 - Hw.mean()), "se": float(Hw.std(ddof=1) / np.sqrt(Hw.size)), "ess": ess,
                             "liq_prob": float(np.concatenate([o[tag]["liq"][ci] for o in ps]).mean())}
            cell["primary"] = "px_bridge" if pi > 1 else "bridge"
            cell["pi_delta"] = pi * DELTA[m]
            cell["log10_bound"] = (n * math.log10(abs(pi)) + math.log10(DELTA[m])) if DELTA[m] > 0 and pi > 1 else None
            res["cells"][m][f"{pi}|{a}|{n}"] = cell
            b = cell[cell["primary"]]
            rows.append([m, pi, a, n, cell["primary"], b["d_H"], b["se"], b["liq_prob"], cell["pi_delta"],
                         cell["log10_bound"], cell["bridge"]["d_H"], cell["bridge"]["se"], cell["px_bridge"]["d_H"],
                         cell["px_bridge"]["se"], cell["px_bridge"]["ess"], cell["discrete"]["d_H"],
                         cell["discrete"]["breach_mean"], cell["bridge_coarse"]["d_H"], cell["px_bridge_coarse"]["d_H"],
                         cell["bridge"]["top10_share"]])
        print(m, "done", flush=True)
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(res, f, indent=1)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["model", "pi", "a", "N", "primary", "d_H", "se", "liq_prob", "pi_delta", "log10_piN_delta",
                    "d_H_Q", "se_Q", "d_H_PX", "se_PX", "ess_PX", "d_H_discrete_Q", "breach_mean_Q", "d_H_coarse_Q",
                    "d_H_coarse_PX", "top10_share_Q"])
        w.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
