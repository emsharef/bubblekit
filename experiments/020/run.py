"""Experiment 020: claim 021's outer sets for delta_T under four option information sets (the human's data rule).

    uv run python experiments/020/run.py      (start from inside .worktrees/analyst)
"""
import csv
import importlib.util
import json
import math
import os
from multiprocessing import Pool

import numpy as np
from scipy import integrate, stats
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
_spec = importlib.util.spec_from_file_location("e017", os.path.join(EXP, "017", "run.py"))
e017 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(e017)

WORKERS = max(1, (os.cpu_count() or 4) - 3)
MODELS = ("bes3", "cev1.5", "gbm")
DELTA = e017.DELTA
OTM = [round(1.00 + 0.05 * i, 2) for i in range(10)]
ITM = [0.50, 0.60, 0.70, 0.80, 0.90, 0.95]
K_PUT, K_FUND = 1.0, 1.0
TICK = 0.01 / 450
WIDTHS = (0.0, 1e-4, 1e-3, 1e-2, 0.05, 0.10)
PANELS = 1000
FUNDS = [(pi, a, n) for pi in (2.0, 3.0) for a in (0.0, 0.5) for n in (1, 252)]
FUND_SEED, PANEL_SEED = 20261021, 20261022
FUND_PATHS, FUND_BATCH = 20000, 250
F = e017.F


# ---- exact underlying targets ----------------------------------------------------------------------------------
def terminal(model):
    """Return (pdf of s, X(s), support upper) for the terminal law in a 1-d variable s, or None for GBM."""
    if model == "bes3":
        d = stats.ncx2(3, 1.0)
        return d.pdf, lambda s: s ** -0.5
    d = stats.ncx2(4, 4.0)
    return d.pdf, lambda s: 4.0 / s


def call(model, K):
    if model == "gbm":
        d1 = (-math.log(K) + 0.5) if K > 0 else math.inf
        return stats.norm.cdf(d1) - K * stats.norm.cdf(d1 - 1.0) if K > 0 else 1.0
    pdf, X = terminal(model)
    s_star = (1 / K ** 2) if model == "bes3" else 4.0 / K
    v, _ = integrate.quad(lambda s: (X(s) - K) * pdf(s), 0, s_star, epsrel=1e-10, limit=400)
    return v


def put(model, K):
    m = mean(model)
    return call(model, K) - m + K                       # parity under expectation pricing (AX-18)


def mean(model):
    if model == "gbm":
        return 1.0
    pdf, X = terminal(model)
    v, _ = integrate.quad(lambda s: X(s) * pdf(s), 0, np.inf, epsrel=1e-10, limit=400)
    return v


# ---- fund option targets by Monte Carlo (claim 020 clipping, P^X estimator) -------------------------------------
def clipped(X, pi, a, n):
    P = X.shape[0]
    reb = F // n
    Wi = np.ones(P)
    Xi = X[:, 0].copy()
    alive = np.ones(P, bool)
    Z = np.empty(P)
    Wn = Wi
    for j in range(1, F + 1):
        Wn = Wi * (1 - pi + pi * X[:, j] / Xi)
        br = alive & (Wn < a)
        Z[br] = a
        alive &= ~br
        if j % reb == 0:
            Wi = np.where(alive, Wn, Wi)
            Xi = np.where(alive, X[:, j], Xi)
    Z[alive] = Wn[alive]
    return Z


def fund_batch(args):
    model, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    Xp, alive = e017.px_paths(model, rng, FUND_BATCH)
    Xp = np.where(np.isfinite(Xp), Xp, 1e300)
    w = np.where(alive, 1.0 / np.where(alive, Xp[:, -1], 1.0), 0.0)
    out = {}
    with np.errstate(invalid="ignore", over="ignore"):
        for f in FUNDS:
            Z = clipped(Xp, *f)
            out[f] = (np.maximum(Z - K_FUND, 0) * w, np.maximum(K_FUND - Z, 0) * w)
    return model, out


# ---- claim 021 outer set ---------------------------------------------------------------------------------------
def b_call(Ks, lo, hi, put_iv=None):
    """Interval [1 - m_max, 1 - m_min] from (2), or None if infeasible. Variables (m, c_1..c_r), Ks ascending."""
    r = len(Ks)
    Kfull = np.r_[0.0, Ks]
    A, b = [], []

    def slope(i):                                   # s_i = (c_i - c_{i-1})/(K_i - K_{i-1}) as a row over (m, c)
        row = np.zeros(r + 1)
        row[i] += 1 / (Kfull[i] - Kfull[i - 1])
        row[i - 1] -= 1 / (Kfull[i] - Kfull[i - 1])
        return row
    A.append(-slope(1)); b.append(1.0)               # s_1 >= -1
    for i in range(1, r):
        A.append(slope(i) - slope(i + 1)); b.append(0.0)  # s_i <= s_{i+1}
    A.append(slope(r)); b.append(0.0)                # s_r <= 0
    if put_iv is not None:                           # Plo <= c_j - m + K <= Phi
        j = Ks.index(K_PUT) + 1
        row = np.zeros(r + 1); row[j] = 1.0; row[0] = -1.0
        A.append(row); b.append(put_iv[1] - K_PUT)
        A.append(-row); b.append(-(put_iv[0] - K_PUT))
    bounds = [(0.0, 1.0)] + [(max(0.0, l), h) for l, h in zip(lo, hi)]
    if any(l > h + 1e-15 for l, h in bounds):
        return None
    res = []
    for sign in (1.0, -1.0):
        c = np.zeros(r + 1); c[0] = sign
        sol = linprog(c, A_ub=np.array(A), b_ub=np.array(b), bounds=bounds, method="highs")
        if sol.status != 0:
            return None
        res.append(sol.x[0])
    m_min, m_max = res
    return (1 - m_max, 1 - m_min)


def quote_interval(rng, target, w, floor=None, extra=0.0):
    e = rng.uniform(-w, w) if w > 0 else 0.0
    q = target + e
    if floor is not None and q <= floor:
        return (0.0, floor + w)
    return (q - w - extra, q + w + extra)


def panel_job(args):
    model, w, seed, calls, put_t, fund = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    out = []
    for _ in range(PANELS // 10):
        rec = {}
        civ = {K: quote_interval(rng, calls[K], w, floor=TICK) for K in sorted(calls)}
        piv = quote_interval(rng, put_t, w)
        fiv = {f: (quote_interval(rng, fund[f]["C"], w, extra=3 * fund[f]["C_se"]),
                   quote_interval(rng, fund[f]["P"], w, extra=3 * fund[f]["P_se"])) for f in FUNDS}
        lo = lambda Ks: [civ[K][0] for K in Ks]
        hi = lambda Ks: [civ[K][1] for K in Ks]
        rec["a"] = b_call(OTM, lo(OTM), hi(OTM))
        rec["c"] = b_call(OTM, lo(OTM), hi(OTM), put_iv=piv)
        dK = sorted(ITM + OTM)
        rec["d"] = b_call(dK, lo(dK), hi(dK))
        Ls = {}
        for f in FUNDS:
            pi, a, n = f
            (clo, chi), (plo, phi) = fiv[f]
            Ls[f] = 1 - K_FUND - chi + plo
        rec["L"] = {f"{f[0]}|{f[1]}|{f[2]}": Ls[f] for f in FUNDS}
        for (a, n) in ((0.0, 252), (0.5, 252), (0.0, 1), (0.5, 1)):
            group = [f for f in FUNDS if f[1] == a and f[2] == n]
            ell = {f: max(0.0, Ls[f]) for f in group}
            u = {f: min(1.0, 1 - f[1]) for f in group}         # U_j from trivial Clo = 0, Phi = K (Design)
            key = f"b|{a}|{n}"
            if rec["a"] is None or any(ell[f] > u[f] for f in group):
                rec[key] = None
                continue
            blev = max(math.exp(math.log(ell[f]) - n * math.log(f[0])) if ell[f] > 0 else 0.0 for f in group)
            lo_e = max(rec["a"][0], blev)
            rec[key] = (lo_e, rec["a"][1]) if lo_e <= rec["a"][1] else None
            rec[key + "|blev"] = blev
        out.append(rec)
    return model, w, out


def summarize(sets):
    ne = [s for s in sets if s is not None]
    r = {"incompatible": len(sets) - len(ne), "n": len(sets)}
    excl = np.array([s is not None and s[0] > 0 for s in sets], float)
    p = float(excl.mean())
    r["exclude_zero"] = {"rate": p, "se": float(np.sqrt(p * (1 - p) / len(sets)))}
    if ne:
        lo = np.array([s[0] for s in ne]); wd = np.array([s[1] - s[0] for s in ne])
        r["lower"] = {"mean": float(lo.mean()), "p5": float(np.percentile(lo, 5)), "p95": float(np.percentile(lo, 95))}
        r["width"] = {"mean": float(wd.mean()), "p5": float(np.percentile(wd, 5)), "p95": float(np.percentile(wd, 95))}
    return r


def main():
    targets = {}
    for m in MODELS:
        mm = mean(m)
        targets[m] = {"mean": mm, "delta_check": 1 - mm, "calls": {K: call(m, K) for K in sorted(OTM + ITM)},
                      "put": put(m, K_PUT)}
        print(m, "E X_T", mm, "delta", DELTA[m], flush=True)
    root = np.random.SeedSequence(FUND_SEED)
    fjobs = []
    for m, ss in zip(MODELS, root.spawn(len(MODELS))):
        fjobs += [(m, s.generate_state(2).tolist()) for s in ss.spawn(FUND_PATHS // FUND_BATCH)]
    with Pool(WORKERS) as pool:
        fparts = pool.map(fund_batch, fjobs)
        fund = {}
        for m in MODELS:
            fund[m] = {}
            for f in FUNDS:
                C = np.concatenate([o[f][0] for mm, o in fparts if mm == m])
                P = np.concatenate([o[f][1] for mm, o in fparts if mm == m])
                fund[m][f] = {"C": float(C.mean()), "C_se": float(C.std(ddof=1) / np.sqrt(C.size)),
                              "P": float(P.mean()), "P_se": float(P.std(ddof=1) / np.sqrt(P.size)),
                              "d_F": float(1 - K_FUND - C.mean() + P.mean())}
            print(m, {f"{f}": round(fund[m][f]["d_F"], 4) for f in FUNDS}, flush=True)
        proot = np.random.SeedSequence(PANEL_SEED)
        pjobs = []
        for (m, w), ss in zip([(m, w) for m in MODELS for w in WIDTHS], proot.spawn(len(MODELS) * len(WIDTHS))):
            pjobs += [(m, w, s.generate_state(2).tolist(), targets[m]["calls"], targets[m]["put"], fund[m])
                      for s in ss.spawn(10)]
        pparts = pool.map(panel_job, pjobs)
    res = {"targets": {m: {"mean": t["mean"], "delta_exact": DELTA[m], "calls": {str(k): v for k, v in t["calls"].items()},
                           "put": t["put"]} for m, t in targets.items()},
           "fund": {m: {f"{f[0]}|{f[1]}|{f[2]}": v for f, v in d.items()} for m, d in fund.items()},
           "tick": TICK, "cells": {}}
    rows = []
    for m in MODELS:
        for w in WIDTHS:
            recs = [r for mm, ww, o in pparts if mm == m and ww == w for r in o]
            cell = {s: summarize([r[s] for r in recs]) for s in ("a", "c", "d", "b|0.0|252", "b|0.5|252", "b|0.0|1", "b|0.5|1")}
            for key in ("b|0.0|252", "b|0.5|252", "b|0.0|1", "b|0.5|1"):
                bl = np.array([r.get(key + "|blev", np.nan) for r in recs], float)
                cell[key]["blev_median"] = float(np.nanmedian(bl)) if np.isfinite(bl).any() else None
            cell["L"] = {k: {"mean": float(np.mean([r["L"][k] for r in recs])),
                             "p5": float(np.percentile([r["L"][k] for r in recs], 5)),
                             "p95": float(np.percentile([r["L"][k] for r in recs], 95))} for k in recs[0]["L"]}
            res["cells"][f"{m}|{w}"] = cell
            for s in ("a", "b|0.0|252", "b|0.0|1", "c", "d"):
                c = cell[s]
                rows.append([m, w, s, c["exclude_zero"]["rate"], c["exclude_zero"]["se"], c["incompatible"],
                             c.get("lower", {}).get("mean"), c.get("width", {}).get("mean")])
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        wr = csv.writer(fh)
        wr.writerow(["model", "w", "info_set", "exclude_zero", "se", "incompatible", "mean_lower", "mean_width"])
        wr.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
