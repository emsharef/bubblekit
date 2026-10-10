"""Experiment 028: keeping power on cent-rounded intraday prices (claim 034 refinement and boxes; claim 033 on rounded).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/028/run.py          (start from inside .worktrees/analyst)

Reuses experiment 027's code (`experiments/027/run.py`): clock grids, clocked GBM/CEV simulation, claim 033's
vectorized profile and the exact-price scores.
"""
import csv
import heapq
import importlib.util
import json
import math
import os
import time
from multiprocessing import Pool

import numpy as np
from scipy import special
from scipy.stats import ncx2

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


r027 = _load("r027", "experiments/027/run.py")
r023, cev = r027.r023, r027.cev

WORKERS = r027.WORKERS
SEED = 20261028
BATCH = 100
ALPHAS = (0.05, 0.10)
TICK = 0.01
BOXES = {"W": (-0.50, 0.50, 0.01, 0.64), "N": (-0.20, 0.20, 0.04, 0.2025)}
HL_HOURLY = [(2, 2), (2, 4), (4, 2), (4, 4)]
HL_5M60 = [(2, 2), (4, 2)]
U = ("U", 1.5, 0.25)
# (name, kind, clock, b-or-p, kappa, start price, n paths for 033, 034 batches hourly-250, 034 batches 5m-60)
TRUTHS = [("N-in", "gbm", U, 0.0, 0.30, 50.0, 2000, 6, 2),
          ("N-k60", "gbm", U, 0.0, 0.60, 50.0, 2000, 6, 2),
          ("N-b40", "gbm", U, 0.40, 0.30, 50.0, 2000, 6, 2),
          ("N-outU", "gbm", ("U", 2.0, 0.25), 0.0, 0.30, 50.0, 2000, 6, 2),
          ("N-in-$5", "gbm", U, 0.0, 0.30, 5.0, 2000, 6, 2),
          ("A-15-30", "cev", U, 1.5, 0.30, 50.0, 1000, 4, 2),
          ("A-15-45", "cev", U, 1.5, 0.45, 50.0, 1000, 4, 2),
          ("A-20-30", "cev", U, 2.0, 0.30, 50.0, 1000, 4, 2),
          ("A-20-45", "cev", U, 2.0, 0.45, 50.0, 1000, 4, 2),
          ("A-20-45-$5", "cev", U, 2.0, 0.45, 5.0, 1000, 4, 2)]
HORIZONS = (60, 250)
COVER = {  # coverage of claim 034 columns by box (both boxes share the clock set)
    "N-in": {"W": True, "N": True}, "N-k60": {"W": True, "N": False}, "N-b40": {"W": True, "N": False},
    "N-outU": {"W": False, "N": False}, "N-in-$5": {"W": True, "N": True}}


def col34(box, h, l):
    return f"E034_{box}_h{h}_l{l}"


# ---- claim 034: transition bound, state recursion, branch and bound -------------------------------------------
def log_w(a, dS, c, dT, dt, v, B):
    """Vectorized log W_clock (claim 034 (2)-(3)) from source cell [a, dS) to target cell [c, dT); a, c > 0."""
    bL, bH, wL, wH = B
    with np.errstate(divide="ignore", invalid="ignore"):
        Mm = np.log(a) + bL * dt - wH * v / 2
        Mp = np.log(dS) + bH * dt - wL * v / 2
        sm, sp = np.sqrt(wL * v), np.sqrt(wH * v)
        L, R = np.log(c), np.log(dT)
        m = np.clip((L + R) / 2, Mm, Mp)
        inside = (L <= m) & (m <= R)
        e1, e2 = np.abs(L - m), np.abs(R - m)
        lo, hi = np.minimum(e1, e2), np.maximum(e1, e2)
        ss = np.sqrt((hi * hi - lo * lo) / (2 * np.log(hi / lo)))
        s = np.where(inside, sm, np.clip(np.nan_to_num(ss, nan=np.inf), sm, sp))
        u, l = (R - m) / s, (L - m) / s
        val = np.where(l > 0,
                       special.log_ndtr(-l) + np.log1p(-np.exp(special.log_ndtr(-u) - special.log_ndtr(-l))),
                       special.log_ndtr(u) + np.log1p(-np.exp(special.log_ndtr(l) - special.log_ndtr(u))))
    return np.minimum(val, 0.0)


def logD_box(Z, d, v, B, lmax):
    """Claim 034 (4) in log space for one label path Z (cents), one box and clock, state levels 0..lmax."""
    n = len(Z) - 1
    parent = None
    for lev in range(lmax + 1):
        k = 2 ** lev
        edges = TICK * (Z[:, None] - 0.5) + TICK * (np.arange(k + 1) / k)[None, :]
        A, Dd = edges[:, :-1], edges[:, 1:]
        lw = log_w(A[:-1, :, None], Dd[:-1, :, None], A[1:, None, :], Dd[1:, None, :], d[:, None, None],
                   v[:, None, None], B)
        suf = np.zeros(k)
        sufs = [None] * (n + 1)
        sufs[n] = suf
        for j in range(n - 1, -1, -1):
            x = lw[j] + suf[None, :]
            mx = x.max(1)
            t = mx + np.log(np.exp(x - mx[:, None]).sum(1))
            cap = 0.0 if parent is None else np.repeat(parent[j], 2)
            suf = np.minimum(np.minimum(0.0, cap), t)
            sufs[j] = suf
        parent = sufs
    return float(np.max(parent[0]))


def children(B):
    b0, b1, w0, w1 = B
    bm, wm = (b0 + b1) / 2, (w0 + w1) / 2
    return [(bl, bh, wl, wh) for bl, bh in ((b0, bm), (bm, b1)) for wl, wh in ((w0, wm), (wm, w1))]


def logD_bb(Z, d, clocks, box, h, lmax):
    """Exact maximum of claim 034's bound over the depth-h dyadic cover of `box` and the clock set, by best-first
    branch and bound (a child's bound never exceeds its parent's). Returns (log D, boxes evaluated)."""
    best, evals, heap = -np.inf, 0, []
    for ci, v in enumerate(clocks):
        val = logD_box(Z, d, v, box, lmax)
        evals += 1
        heapq.heappush(heap, (-val, 0, ci, box))
    while heap:
        negval, depth, ci, B = heapq.heappop(heap)
        if -negval <= best:
            break
        if depth == h:
            best = -negval
            continue
        for C in children(B):
            val = logD_box(Z, d, clocks[ci], C, lmax)
            evals += 1
            if val > best:
                heapq.heappush(heap, (-val, depth + 1, ci, C))
    return best, evals


def logD_full(Z, d, clocks, box, h, lmax):
    boxes = [box]
    for _ in range(h):
        boxes = [c for B in boxes for c in children(B)]
    return max(logD_box(Z, d, v, B, lmax) for B in boxes for v in clocks)


# ---- claim 034 forecast (027's CEV cell forecast with the start price as a parameter) ----------------------------
def cell_logprob(z0, z1, dt, p, kap, P0):
    x = TICK * z0 / P0
    lo, hi = TICK * (z1 - 0.5) / P0, TICK * (z1 + 0.5) / P0
    if p == 1:
        mu = np.log(x) - 0.5 * kap * kap * dt
        sd = kap * np.sqrt(dt)
        a, b = (np.log(lo) - mu) / sd, (np.log(hi) - mu) / sd
        pr = special.ndtr(b) - special.ndtr(a)
        return np.log(np.maximum(pr, 1e-300)), (pr < 1e-300).sum(1)
    q = 1.0 - p
    c = kap * kap * q * q
    delta = (1 - 2 * p) / (1 - p)
    nc = (x ** (2 * q) / c) / dt
    ylo, yhi = (lo ** (2 * q) / c) / dt, (hi ** (2 * q) / c) / dt
    pr = ncx2.cdf(ylo, delta, nc) - ncx2.cdf(yhi, delta, nc)
    return np.log(np.maximum(pr, 1e-300)), (pr < 1e-300).sum(1)


def forecast034(Z, d, vU, P0):
    """Training-selected CEV cell forecast (p >= 1 on both clocks) over the evaluation labels; returns log q (P,)."""
    P, N1 = Z.shape
    k = (N1 - 1) // 2
    clocks = {"F": d, "U": vU}
    cand = [(c, i) for c in clocks for i, (p, _) in enumerate(cev.CATALOGUE) if p >= 1]
    xr = TICK * Z / P0
    trl = np.full((P, len(cand)), -np.inf)
    for j, (cname, i) in enumerate(cand):
        p, kap = cev.CATALOGUE[i]
        lk = cev.log_kernel(p, kap, clocks[cname][None, :k], xr[:, :k], xr[:, 1:k + 1])
        trl[:, j] = np.where(np.isnan(lk).any(1), -np.inf, lk.sum(1))
    best = np.argmax(trl, axis=1)
    logq = np.zeros(P)
    floored = np.zeros(P, int)
    for j in np.unique(best):
        rows = best == j
        cname, i = cand[j]
        p, kap = cev.CATALOGUE[i]
        lp, fl = cell_logprob(Z[rows, k:-1], Z[rows, k + 1:], clocks[cname][None, k:], p, kap, P0)
        logq[rows] = lp.sum(1)
        floored[rows] = fl
    return logq, floored


# ---- jobs ---------------------------------------------------------------------------------------------------------
def truth027(t):
    name, kind, clock, a, k = t[:5]
    return (name, kind, clock, a, k, 0)


def score033_both(S, d, vU, P0):
    ex, _, _ = r027.scores(S, d, vU)
    Zr = np.rint(P0 * S / TICK)
    X = np.where(Zr > 0, TICK * Zr / P0, 0.0)
    ro, _, _ = r027.scores(X, d, vU)
    return ex["c033"], ro["c033"], int(ex["unbounded033"].sum()), int(ro["unbounded033"].sum())


def score034_cols(S, d, vU, P0, hl_list):
    Z = np.rint(P0 * S / TICK)
    P, N1 = Z.shape
    k = (N1 - 1) // 2
    logq, floored = forecast034(Z, d, vU, P0)
    out, evals, secs = {}, {}, {}
    edge = {"zero_label_paths": int((Z <= 0).any(1).sum()), "forecast_nonfinite": int((~np.isfinite(logq)).sum()),
            "forecast_floored_paths": int((floored > 0).sum()), "forecast_floored_steps": int(floored.sum()),
            "bound_nonfinite": {}}
    clocks = [d[k:], vU[k:]]
    for bname, box in BOXES.items():
        for h, l in hl_list:
            col = col34(bname, h, l)
            t0 = time.time()
            vals, ev = [], []
            for i in range(P):
                if (Z[i, k:] <= 0).any():
                    vals.append(np.nan)
                    ev.append(0)
                    continue
                lv, e = logD_bb(Z[i, k:], d[k:], clocks, box, h, l)
                vals.append(lv)
                ev.append(e)
            vals = np.array(vals)
            edge["bound_nonfinite"][col] = int((~np.isfinite(vals) | (vals > 1e-12)).sum())
            ok = np.isfinite(logq) & np.isfinite(vals) & (vals <= 1e-12)
            out[col] = np.where(ok, logq - vals, -np.inf)
            evals[col] = float(np.mean(ev))
            secs[col] = (time.time() - t0) / P
    return out, evals, secs, Z, k, edge


def checks034(Z, d, vU, k):
    """First paths of each cell: branch and bound equals the full cover at h = 2 (l = 2, wide box); and claim 034's
    reference denominator on the first 100 evaluation increments at h = 2, l = 2."""
    sc34 = _load("score034", "checks/034/scoring.py")
    mp = sc34.clock.cells.cell.mp if hasattr(sc34.clock.cells.cell, "mp") else __import__("mpmath").mp
    res = []
    for i in range(min(3, Z.shape[0])):
        ck = {"path": i}
        clocks = [d[k:], vU[k:]]
        bb, _ = logD_bb(Z[i, k:], d[k:], clocks, BOXES["W"], 2, 2)
        full = logD_full(Z[i, k:], d[k:], clocks, BOXES["W"], 2, 2)
        ck["bb_vs_full"] = abs(bb - full)
        if i < 2:
            m = 100
            zz = [int(z) for z in Z[i, k:k + m + 1]]
            dd, vv = [float(x) for x in d[k:k + m]], [float(x) for x in vU[k:k + m]]
            ref = sc34.denominator(zz, dd, [dd, vv], TICK, BOXES["W"], 2, 2)
            mine = logD_full(Z[i, k:k + m + 1], d[k:k + m], [d[k:k + m], vU[k:k + m]], BOXES["W"], 2, 2)
            ck["ref_logD_100"] = abs(float(__import__("mpmath").log(ref)) - mine)
        res.append(ck)
    return res


def job(args):
    t, H, b, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    P0 = t[5]
    S5 = r027.simulate(truth027(t), rng, BATCH, H)
    d5, vU5 = r027.grid(H, U)
    out = {"truth": t[0], "H": H, "b": b, "freq": {}}
    t0 = time.time()
    ex, ro, ue, ur = score033_both(S5, d5, vU5, P0)
    rec5 = {"E033_exact": ex.tolist(), "E033_round": ro.tolist(), "unbounded_exact": ue, "unbounded_round": ur,
            "sec_per_path_033": (time.time() - t0) / BATCH}
    if H == 60 and b < t[8]:
        cols, ev, secs, Z, k, edge = score034_cols(S5, d5, vU5, P0, HL_5M60)
        rec5.update({c: v.tolist() for c, v in cols.items()})
        rec5["evals"], rec5["sec_per_path_034"], rec5["edge"] = ev, secs, edge
    out["freq"]["5m"] = rec5
    if H == 250 and b < t[7]:
        hidx = r027.hourly_index(H)
        S, d, vU = S5[:, hidx], r027.coarsen(d5, hidx), r027.coarsen(vU5, hidx)
        t0 = time.time()
        ex, ro, ue, ur = score033_both(S, d, vU, P0)
        rec = {"E033_exact": ex.tolist(), "E033_round": ro.tolist(), "unbounded_exact": ue, "unbounded_round": ur,
               "sec_per_path_033": (time.time() - t0) / BATCH}
        cols, ev, secs, Z, k, edge = score034_cols(S, d, vU, P0, HL_HOURLY)
        rec.update({c: v.tolist() for c, v in cols.items()})
        rec["evals"], rec["sec_per_path_034"], rec["edge"] = ev, secs, edge
        rec["checks"] = checks034(Z, d, vU, k) if b == 0 else []
        out["freq"]["60m"] = rec
    return out


def summarize(t, recs, cols):
    c = {"paths": len(np.concatenate([np.asarray(r[cols[0]]) for r in recs]))}
    L = {col: np.concatenate([np.asarray(r[col], float) for r in recs]) for col in cols}
    for a in ALPHAS:
        thr = -math.log(a)
        rj = {col: L[col] > thr for col in cols}
        c[str(a)] = {col: r023.rate(v) for col, v in rj.items()}
        if "E033_exact" in cols:
            c[str(a)]["paired_vs_E033_exact"] = {col: r023.paired(rj[col], rj["E033_exact"]) for col in cols
                                                 if col != "E033_exact" and len(rj[col]) == len(rj["E033_exact"])}
    c["failures"] = {col: int(np.sum(~np.isfinite(L[col]) & (L[col] != -np.inf)) + np.sum(np.isnan(L[col])))
                     for col in cols}
    c["zero_scores"] = {col: int(np.sum(L[col] == -np.inf)) for col in cols}
    return c


def main():
    root = np.random.SeedSequence(SEED)
    cells = [(t, H) for t in TRUTHS for H in HORIZONS]
    jobs = []
    for (t, H), ss in zip(cells, root.spawn(len(cells))):
        for b, s in enumerate(ss.spawn(t[6] // BATCH)):
            jobs.append((t, H, b, s.generate_state(2).tolist()))
    heavy = lambda j: (j[1] == 250 and j[2] < j[0][7]) * 10 + (j[1] == 60 and j[2] < j[0][8]) * 3
    with Pool(WORKERS) as pool:
        parts = pool.map(job, sorted(jobs, key=lambda j: -heavy(j)), chunksize=1)
    res, rows, STAT = {"boxes": BOXES, "cells": {}}, [], {}
    for t, H in cells:
        ps = sorted([p for p in parts if p["truth"] == t[0] and p["H"] == H], key=lambda p: p["b"])
        cell = {}
        recs5 = [p["freq"]["5m"] for p in ps]
        c = summarize(t, recs5, ["E033_exact", "E033_round"])
        c["unbounded"] = {"exact": sum(r["unbounded_exact"] for r in recs5), "round": sum(r["unbounded_round"] for r in recs5)}
        c["sec_per_path_033"] = float(np.mean([r["sec_per_path_033"] for r in recs5]))
        cell["5m"] = c
        if H == 60:
            sub = [r for r in recs5 if "evals" in r]
            cols = ["E033_exact", "E033_round"] + [col34(bx, h, l) for bx in BOXES for h, l in HL_5M60]
            sub2 = [{k_: (v if k_ in cols[2:] else v[:len(r[cols[2]])]) for k_, v in r.items() if k_ in cols}
                    for r in sub]
            c34 = summarize(t, sub2, cols)
            c34["evals"] = {col: float(np.mean([r["evals"][col] for r in sub])) for col in cols[2:]}
            c34["sec_per_path_034"] = {col: float(np.mean([r["sec_per_path_034"][col] for r in sub])) for col in cols[2:]}
            c34["edge"] = {k_: (sum(r["edge"][k_] for r in sub) if k_ != "bound_nonfinite" else
                              {cc: sum(r["edge"]["bound_nonfinite"][cc] for r in sub) for cc in cols[2:]})
                         for k_ in ("zero_label_paths", "forecast_nonfinite", "forecast_floored_paths",
                                    "forecast_floored_steps", "bound_nonfinite")}
            cell["5m_034_subset"] = c34
        if H == 250:
            rh = [p["freq"]["60m"] for p in ps if "60m" in p["freq"]]
            cols = ["E033_exact", "E033_round"] + [col34(bx, h, l) for bx in BOXES for h, l in HL_HOURLY]
            ch = summarize(t, rh, cols)
            ch["unbounded"] = {"exact": sum(r["unbounded_exact"] for r in rh), "round": sum(r["unbounded_round"] for r in rh)}
            ch["evals"] = {col: float(np.mean([r["evals"][col] for r in rh])) for col in cols[2:]}
            ch["sec_per_path_034"] = {col: float(np.mean([r["sec_per_path_034"][col] for r in rh])) for col in cols[2:]}
            ch["sec_per_path_033"] = float(np.mean([r["sec_per_path_033"] for r in rh]))
            ch["checks"] = [ck for r in rh for ck in r.get("checks", [])]
            ch["edge"] = {k_: (sum(r["edge"][k_] for r in rh) if k_ != "bound_nonfinite" else
                              {cc: sum(r["edge"]["bound_nonfinite"][cc] for r in rh) for cc in cols[2:]})
                         for k_ in ("zero_label_paths", "forecast_nonfinite", "forecast_floored_paths",
                                    "forecast_floored_steps", "bound_nonfinite")}
            cell["60m"] = ch
        for f, c_ in cell.items():
            for col, v in c_["0.05"].items():
                if col.startswith("paired"):
                    continue
                rows.append([t[0], H, f, col, v["rate"], v["se"], c_["0.1"][col]["rate"], v["n"]])
            STAT[f"{t[0]}|{H}|{f}"] = {"failures": c_["failures"], "zero_scores": c_["zero_scores"]}
        cell["coverage_034"] = COVER.get(t[0])
        res["cells"][f"{t[0]}|{H}"] = cell
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump(STAT, fh, indent=0)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["truth", "sessions", "sampling", "column", "rate_a05", "se_a05", "rate_a10", "n"])
        w.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
