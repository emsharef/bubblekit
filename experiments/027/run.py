"""Experiment 027: power and false alarms at 5-minute and hourly sampling under a declared intraday variance clock.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/027/run.py          (start from inside .worktrees/analyst)

Reuses experiment 023's code (experiment 022's CEV kernel with the large-argument Bessel fix, and reporting helpers).
"""
import csv
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


r023 = _load("r023", "experiments/023/run.py")        # patches scipy's ive (023's Deviation 1)
cev = r023.cev

WORKERS = r023.WORKERS
SEED = 20261027
DAYS = 252
BATCH = 100
HORIZONS = (60, 250)
ALPHAS = (0.05, 0.10)
P0, TICK = 50.0, 0.01
BOX = (-0.50, 0.50, 0.01, 0.64)                       # b-, b+, w-, w+
H_DEPTH = 2
BARS = 78                                             # 5-minute bars per 6.5-hour session
HOUR_GROUPS = [12] * 6 + [6]                          # hourly bars: six full hours and the final half hour
DELTA_BAR = (5 / 60) / (24 * DAYS)
DELTA_ON = 17.5 / (24 * DAYS)

TRUTHS = [("G-in-0", "gbm", ("U", 1.5, 0.25), 0.0, 0.30, 2000),
          ("G-in-b", "gbm", ("U", 1.5, 0.25), 0.10, 0.30, 2000),
          ("G-flat", "gbm", ("F",), 0.0, 0.30, 2000),
          ("G-out-U", "gbm", ("U", 2.0, 0.25), 0.0, 0.30, 2000),
          ("G-out-ON", "gbm", ("U", 1.5, 0.50), 0.0, 0.30, 2000)] + \
         [(f"CEV-p{p}-k{k}", "cev", ("U", 1.5, 0.25), p, k, 1000) for p in (1.5, 2.0) for k in (0.30, 0.45)]
COVER = {"G-in-0": {"v1flat": False, "raw": False, "d055": False, "c033": True, "c034": True},
         "G-in-b": {"v1flat": False, "raw": False, "d055": False, "c033": True, "c034": True},
         "G-flat": {"v1flat": True, "raw": False, "d055": True, "c033": True, "c034": True},
         "G-out-U": {"v1flat": False, "raw": False, "d055": False, "c033": False, "c034": False},
         "G-out-ON": {"v1flat": False, "raw": False, "d055": False, "c033": False, "c034": False}}
COLS = ["v1flat", "raw", "d055", "c033"]


def session_clock(speed_hi):
    """Integrated squared speed over each 5-minute bar of a session, normalized to sum 1 (shape only)."""
    edges = np.arange(BARS + 1) * (6.5 / BARS)
    hi = lambda a, b: max(0.0, min(b, 1.0) - max(a, 0.0)) + max(0.0, min(b, 6.5) - max(a, 5.5))
    raw = np.array([hi(a, b) * speed_hi ** 2 + (b - a - hi(a, b)) * 0.75 ** 2 for a, b in zip(edges, edges[1:])])
    return raw / raw.sum()


def grid(n_sessions, clock):
    """5-minute calendar durations and variance increments for n sessions with overnight returns between them."""
    d, v = [], []
    if clock[0] == "F":
        shape, phi = None, None
    else:
        shape, phi = session_clock(clock[1]), clock[2]
    for s in range(n_sessions):
        for j in range(BARS):
            d.append(DELTA_BAR)
            v.append(DELTA_BAR if shape is None else (1 - phi) / DAYS * shape[j])
        if s < n_sessions - 1:
            d.append(DELTA_ON)
            v.append(DELTA_ON if shape is None else phi / DAYS)
    return np.array(d), np.array(v)


def hourly_index(n_sessions):
    """Indices into the 5-minute price grid that give hourly closes and session opens."""
    idx, pos = [0], 0
    for s in range(n_sessions):
        for g in HOUR_GROUPS:
            pos += g
            idx.append(pos)
        if s < n_sessions - 1:
            pos += 1
            idx.append(pos)
    return np.array(idx)


def coarsen(x, idx):
    c = np.concatenate([[0.0], np.cumsum(x)])
    return np.diff(c[idx])


def cev_clock(rng, p, k, n, dts):
    """Exact CEV (p > 1) from S_0 = 1 over per-step durations dts (experiment 022's sampler, step by step)."""
    q = 1.0 - p
    c = k * k * q * q
    delta = (1 - 2 * p) / (1 - p)
    S = np.empty((n, len(dts) + 1))
    S[:, 0] = 1.0
    Y = np.full(n, 1.0 / c)
    for j, dt in enumerate(dts):
        Y = dt * rng.noncentral_chisquare(delta, Y / dt)
        S[:, j + 1] = (c * Y) ** (1.0 / (2 * q))
    return S


def simulate(t, rng, n, H):
    name, kind, clock, a, k, _ = t
    d, v = grid(H, clock)
    if kind == "gbm":
        inc = a * d - 0.5 * k * k * v + k * np.sqrt(v) * rng.standard_normal((n, len(d)))
        return np.concatenate([np.ones((n, 1)), np.exp(np.cumsum(inc, axis=1))], axis=1)
    return cev_clock(rng, a, k, n, v)


def gauss_logsup(R, d, v):
    """Claim 033's closed profile (2)-(3) on log returns R (P, n) with calendar d and clock v; +inf if singular."""
    n = R.shape[1]
    A = (d * d / v).sum()
    B = (R * (d / v)).sum(1)
    T = d.sum()
    res = R - (B / A)[:, None] * d
    Q = (res * res / v).sum(1)
    K = res.sum(1)
    Hh = ((v - (T / A) * d) ** 2 / v).sum()
    with np.errstate(divide="ignore", invalid="ignore"):
        w = 2 * Q / (n + np.sqrt(n * n + Hh * Q))
        val = -n * np.log(2 * np.pi * w) / 2 - 0.5 * np.log(v).sum() - Q / (2 * w) - K / 2 - w * Hh / 8
    return np.where(Q > 0, val, np.inf)


def scores(S, d, vU):
    """Raw 054, claim 055 (flat Gaussian), claim 033 (catalogue {F, U}) on exact prices S (P, N + 1)."""
    P, N1 = S.shape
    N = N1 - 1
    k = N // 2
    clocks = {"F": d, "U": vU}
    x, y = S[:, :-1], S[:, 1:]
    tr, ev = [], []
    for cname, v in clocks.items():
        for (p, kap) in cev.CATALOGUE:
            lk = cev.log_kernel(p, kap, v[None, :], x, y)
            tr.append(lk[:, :k].sum(1))
            ev.append(lk[:, k:].sum(1))
    tr, ev = np.array(tr).T, np.array(ev).T                           # (P, 36)
    fail = np.isnan(tr).any(1) | np.isnan(ev).any(1)
    sel = np.argmax(np.where(np.isnan(tr), -np.inf, tr), axis=1)
    logG = ev[np.arange(P), sel]
    nullidx = [i for i in range(36) if cev.CATALOGUE[i % 18][0] <= 1]
    logG0 = np.where(np.isnan(ev[:, nullidx]), -np.inf, ev[:, nullidx]).max(1)
    yv = S[:, k:]
    pos = (yv > 0).all(1)
    Rv = np.diff(np.log(np.where(pos[:, None], yv, 1.0)), axis=1)
    jac = np.log(np.where(pos[:, None], yv[:, 1:], 1.0)).sum(1)
    dG = gauss_logsup(Rv, d[k:], d[k:]) - jac                          # flat clock: claim 055
    dU = gauss_logsup(Rv, d[k:], vU[k:]) - jac
    dG = np.where(pos, dG, -np.inf)
    dU = np.where(pos, dU, -np.inf)
    out = {"sel": sel, "fail": fail, "unbounded055": dG == np.inf, "unbounded033": np.maximum(dG, dU) == np.inf}
    # usable test v1 exactly as in experiment 021: flat-clock numerator (first 18) and flat-clock CEV null only
    selF = np.argmax(np.where(np.isnan(tr[:, :18]), -np.inf, tr[:, :18]), axis=1)
    logGF = ev[np.arange(P), selF]
    nullF = [i for i in range(18) if cev.CATALOGUE[i][0] <= 1]
    logG0F = np.where(np.isnan(ev[:, nullF]), -np.inf, ev[:, nullF]).max(1)
    with np.errstate(invalid="ignore"):
        D1 = np.maximum(logG0F, dG)
        out["v1flat"] = np.where(fail | (logGF == -np.inf) | (D1 == np.inf), -np.inf, logGF - D1)
    with np.errstate(invalid="ignore"):
        bad = fail | (logG == -np.inf)
        out["raw"] = np.where(bad, -np.inf, logG - logG0)
        D55 = np.maximum(logG0, dG)
        out["d055"] = np.where(bad | (D55 == np.inf), -np.inf, logG - D55)
        D33 = np.maximum(D55, dU)
        out["c033"] = np.where(bad | (D33 == np.inf), -np.inf, logG - D33)
    return out, tr, k


# ---- claim 034 (hourly, rounded to the cent) ------------------------------------------------------------------
def boxes(depth):
    out = [BOX]
    for _ in range(depth):
        nxt = []
        for b0, b1, w0, w1 in out:
            bm, wm = (b0 + b1) / 2, (w0 + w1) / 2
            nxt += [(bl, bh, wl, wh) for bl, bh in ((b0, bm), (bm, b1)) for wl, wh in ((w0, wm), (wm, w1))]
        out = list(dict.fromkeys(nxt))
    return out


def log_w_clock(z0, z1, dt, v, B):
    """log W_clock (claim 034 (2)-(3)) for positive labels z0 -> z1 (arrays), one step, one box."""
    bL, bH, wL, wH = B
    a, dS = TICK * (z0 - 0.5), TICK * (z0 + 0.5)
    c, dT = TICK * (z1 - 0.5), TICK * (z1 + 0.5)
    Mm = np.log(a) + bL * dt - wH * v / 2
    Mp = np.log(dS) + bH * dt - wL * v / 2
    sm, sp = np.sqrt(wL * v), np.sqrt(wH * v)
    L, R = np.log(c), np.log(dT)
    m = np.clip((L + R) / 2, Mm, Mp)
    inside = (L <= m) & (m <= R)
    e1, e2 = np.abs(L - m), np.abs(R - m)
    lo, hi = np.minimum(e1, e2), np.maximum(e1, e2)
    with np.errstate(divide="ignore", invalid="ignore"):
        sstar = np.sqrt((hi * hi - lo * lo) / (2 * np.log(hi / lo)))
    s = np.where(inside, sm, np.clip(np.nan_to_num(sstar, nan=sm), sm, sp))
    u, l = (R - m) / s, (L - m) / s
    # log(Phi(u) - Phi(l)) stably: both arguments on the same side use the matching tail
    with np.errstate(divide="ignore", invalid="ignore"):
        upper_tail = l > 0
        val = np.where(upper_tail,
                       special.log_ndtr(-l) + np.log1p(-np.exp(special.log_ndtr(-u) - special.log_ndtr(-l))),
                       special.log_ndtr(u) + np.log1p(-np.exp(special.log_ndtr(l) - special.log_ndtr(u))))
    return np.minimum(val, 0.0)


def cev_cell_logprob(z0, z1, dt, p, kap):
    """log P(next label z1 | model price at representative TICK*z0/P0) under CEV (p >= 1) over duration dt."""
    x = TICK * z0 / P0
    lo, hi = TICK * (z1 - 0.5) / P0, TICK * (z1 + 0.5) / P0
    if p == 1:
        mu = np.log(x) - 0.5 * kap * kap * dt
        sd = kap * np.sqrt(dt)
        a, b = (np.log(lo) - mu) / sd, (np.log(hi) - mu) / sd
        return np.log(np.maximum(special.ndtr(b) - special.ndtr(a), 1e-300))
    q = 1.0 - p
    c = kap * kap * q * q
    delta = (1 - 2 * p) / (1 - p)
    nc = (x ** (2 * q) / c) / dt
    # S = (c Y)^(1/(2q)) with q < 0 is decreasing in Y: P(lo <= S < hi) = F_Y(lo-image) - F_Y(hi-image)
    ylo, yhi = (lo ** (2 * q) / c) / dt, (hi ** (2 * q) / c) / dt
    pr = ncx2.cdf(ylo, delta, nc) - ncx2.cdf(yhi, delta, nc)
    return np.log(np.maximum(pr, 1e-300))


def score034(S, d, vU, sel_train_density):
    """Claim 034 on hourly cent labels: CEV cell forecast (training-selected, p >= 1) over D_clock at h = 2, l = 0."""
    P = S.shape[0]
    Z = np.rint(P0 * S / TICK)
    N = Z.shape[1] - 1
    k = N // 2
    clocks = {"F": d, "U": vU}
    # forecast candidate: p >= 1 kernels on both clocks, chosen by training likelihood at label representatives
    cand = [(c, i) for c in clocks for i, (p, _) in enumerate(cev.CATALOGUE) if p >= 1]
    xr = TICK * Z / P0
    trl = np.full((P, len(cand)), -np.inf)
    for j, (cname, i) in enumerate(cand):
        p, kap = cev.CATALOGUE[i]
        lk = cev.log_kernel(p, kap, clocks[cname][None, :k], xr[:, :k], xr[:, 1:k + 1])
        trl[:, j] = np.where(np.isnan(lk).any(1), -np.inf, lk.sum(1))
    best = np.argmax(trl, axis=1)
    logq = np.zeros(P)
    for j in np.unique(best):
        rows = best == j
        cname, i = cand[j]
        p, kap = cev.CATALOGUE[i]
        lp = cev_cell_logprob(Z[rows, k:-1], Z[rows, k + 1:], clocks[cname][None, k:], p, kap)
        logq[rows] = lp.sum(1)
    logD = np.full(P, -np.inf)
    for B in boxes(H_DEPTH):
        for v in clocks.values():
            lw = log_w_clock(Z[:, k:-1], Z[:, k + 1:], d[None, k:], v[None, k:], B)
            logD = np.maximum(logD, lw.sum(1))
    return np.where(np.isfinite(logq) & (logD <= 0), logq - logD, -np.inf), best


def checks(S, d, vU, k, f, b):
    """Reference checks on the first paths of each cell: claim 033's profile against checks/033/profile.py (70 digits)
    for both clocks, and at hourly sampling claim 034's denominator against checks/034/scoring.py (first 2 paths)."""
    out = []
    prof = _load("prof033", "checks/033/profile.py")
    mp = prof.mp
    for i in range(3):
        mp.dps = 70
        ck = {"path": i}
        R = np.diff(np.log(S[i:i + 1, k:]), axis=1)
        jac = np.log(S[i, k + 1:]).sum()
        for name, v in (("F", d), ("U", vU)):
            ref = prof.log_null_sup([float(x) for x in d[k:]], [float(x) for x in v[k:]], [float(x) for x in S[i, k:]])
            mine = gauss_logsup(R, d[k:], v[k:])[0] - jac
            ck[f"c033_{name}"] = r023.diff(ref, mine)
        mp.dps = 15
        if f == "60m" and i < 2:
            sc34 = _load("score034", "checks/034/scoring.py")
            Z = np.rint(P0 * S[i] / TICK).astype(int)
            ref = sc34.denominator([int(z) for z in Z[k:]], [float(x) for x in d[k:]],
                                   [[float(x) for x in d[k:]], [float(x) for x in vU[k:]]], TICK, BOX, H_DEPTH, 0)
            mine = -np.inf
            for B in boxes(H_DEPTH):
                for v in (d, vU):
                    mine = max(mine, float(log_w_clock(Z[None, k:-1], Z[None, k + 1:], d[None, k:], v[None, k:], B).sum()))
            ck["c034_logD"] = r023.diff(mp.log(ref), mine)
        out.append(ck)
    return out


def job(args):
    t, H, b, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    S5 = simulate(t, rng, BATCH, H)
    d5, vU5 = grid(H, ("U", 1.5, 0.25))
    hidx = hourly_index(H)
    out = {"truth": t[0], "H": H, "b": b, "freq": {}}
    for f in ("5m", "60m"):
        if f == "5m":
            S, d, vU = S5, d5, vU5
        else:
            S, d, vU = S5[:, hidx], coarsen(d5, hidx), coarsen(vU5, hidx)
        t0 = time.time()
        sc, tr, k = scores(S, d, vU)
        rec = {c: sc[c].tolist() for c in COLS}
        rec.update(sel=sc["sel"].tolist(), fail=int(sc["fail"].sum()), unbounded055=int(sc["unbounded055"].sum()),
                   unbounded033=int(sc["unbounded033"].sum()), sec_per_path=(time.time() - t0) / S.shape[0])
        if f == "60m":
            t0 = time.time()
            s34, best = score034(S, d, vU, None)
            rec["c034"] = s34.tolist()
            rec["sec_per_path_034"] = (time.time() - t0) / S.shape[0]
        rec["checks"] = checks(S, d, vU, k, f, b) if b == 0 else []
        out["freq"][f] = rec
    return out


def main():
    root = np.random.SeedSequence(SEED)
    cells = [(t, H) for t in TRUTHS for H in HORIZONS]
    jobs = []
    for (t, H), ss in zip(cells, root.spawn(len(cells))):
        for b, s in enumerate(ss.spawn(t[5] // BATCH)):
            jobs.append((t, H, b, s.generate_state(2).tolist()))
    with Pool(WORKERS) as pool:
        parts = pool.map(job, sorted(jobs, key=lambda j: -j[1]), chunksize=1)
    res, rows, STAT = {"cells": {}}, [], {}
    for t, H in cells:
        ps = sorted([p for p in parts if p["truth"] == t[0] and p["H"] == H], key=lambda p: p["b"])
        cell = {}
        for f in ("5m", "60m"):
            recs = [p["freq"][f] for p in ps]
            cols = COLS + (["c034"] if f == "60m" else [])
            L = {c: np.concatenate([np.asarray(r[c], float) for r in recs]) for c in cols}
            cks = [ck for r in recs for ck in r["checks"]]
            c = {"paths": int(L["raw"].size), "fail": sum(r["fail"] for r in recs),
                 "checks": cks, "max_check_absdiff": max([max(v for kk, v in ck.items() if kk != "path") for ck in cks], default=None),
                 "unbounded055": sum(r["unbounded055"] for r in recs), "unbounded033": sum(r["unbounded033"] for r in recs),
                 "sec_per_path": float(np.mean([r["sec_per_path"] for r in recs])),
                 "coverage": COVER.get(t[0], {cc: False for cc in cols})}
            if f == "60m":
                c["sec_per_path_034"] = float(np.mean([r["sec_per_path_034"] for r in recs]))
            for a in ALPHAS:
                thr = -math.log(a)
                rj = {cc: L[cc] > thr for cc in cols}
                c[str(a)] = {cc: r023.rate(v) for cc, v in rj.items()}
                c[str(a)]["paired_vs_d055"] = {cc: r023.paired(rj[cc], rj["d055"]) for cc in cols if cc != "d055"}
            cell[f] = c
            STAT[f"{t[0]}|{H}|{f}"] = {"fail": c["fail"], "unbounded055": c["unbounded055"], "unbounded033": c["unbounded033"]}
            for cc in cols:
                rows.append([t[0], H, f, cc, c[str(0.05)][cc]["rate"], c[str(0.05)][cc]["se"], c[str(0.1)][cc]["rate"]])
        res["cells"][f"{t[0]}|{H}"] = cell
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump(STAT, fh, indent=0)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["truth", "sessions", "freq", "column", "rate_a05", "se_a05", "rate_a10"])
        w.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
