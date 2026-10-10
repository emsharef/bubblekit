"""Experiment 026: claim 059's single-switch score against claims 055 and 054 (D15/D5).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/026/run.py          (start from inside .worktrees/analyst)

Reuses experiment 023's code (`experiments/023/run.py`): experiment 022's exact CEV sampler and vectorized score, the
large-argument Bessel fix, and the reporting and e-BH helpers.
"""
import csv
import importlib.util
import json
import math
import os
from multiprocessing import Pool

import numpy as np
from mpmath import mp

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
sw059 = _load("sw059", "checks/059/scoring.py")

WORKERS, DAYS, PATHS, BATCH, HORIZONS, FREQ, ALPHAS = (r023.WORKERS, r023.DAYS, r023.PATHS, r023.BATCH, r023.HORIZONS,
                                                       r023.FREQ, r023.ALPHAS)
SEED = 20261026
CUTSETS = ("K1", "K40", "K25", "K10")
PHI = {"K40": 0.40, "K25": 0.25, "K10": 0.10}
COLS = ["raw", "d055"] + [f"sw_{k}" for k in CUTSETS]

G1 = [("const", b, k, None, None) for b in (0.0, 0.10) for k in (0.20, 0.35)]
G2 = [("switch", 0.0, kl, kr, s) for (kl, kr) in ((0.20, 0.45), (0.45, 0.20)) for s in (0.15, 0.30, 0.50)]
G3 = [("cevnull", p, 0.30, None, None) for p in (0.5, 0.75)]
G4 = [("cevalt", p, k, None, None) for p in (1.25, 1.5, 2.0) for k in (0.20, 0.30, 0.45)]
TRUTHS = G1 + G2 + G3 + G4


def tname(t):
    kind, a, k, kr, s = t
    if kind == "const":
        return f"const_b{a:+.2f}_k{k:.2f}"
    if kind == "switch":
        return f"switch_k{k:.2f}to{kr:.2f}_s{s:.2f}"
    return f"{kind}_p{a:.2f}_k{k:.2f}"


def switch_month(T, s):
    """Evaluation months from the evaluation start to the switch (registered rounding)."""
    ne_m = 12 * T - (12 * T) // 2
    return int(round(s * ne_m))


def simulate(t, rng, n, T):
    kind, a, k, kr, s = t
    steps = DAYS * T
    dt = 1.0 / DAYS
    if kind in ("cevnull", "cevalt"):
        return cev.sample_cev(rng, a, k, n, steps, dt)
    kap = np.full(steps, k)
    if kind == "switch":
        start = steps // 2 + 21 * switch_month(T, s)          # first daily increment after the switch
        kap[start:] = kr
    z = rng.standard_normal((n, steps))
    inc = (a - kap ** 2 / 2)[None, :] * dt + kap[None, :] * math.sqrt(dt) * z
    return np.concatenate([np.ones((n, 1)), np.exp(np.cumsum(inc, axis=1))], axis=1)


def cutset(name, ne):
    if name == "K1":
        c = [ne // 2]
    else:
        lo = math.ceil(PHI[name] * ne)
        c = list(range(lo, ne - lo + 1))
    clipped = [x for x in c if 2 <= x <= ne - 2]
    return clipped, len(clipped) != len(c)


def switch_logsup(Ss, times, k, cuts):
    """Claim 059 (4)-(5), vectorized: max over cuts of the two segment Gaussian profiles; strata as in claim 055."""
    P = Ss.shape[0]
    yv = Ss[:, k:]
    y0 = yv[:, 0]
    logD = np.full(P, -np.inf)
    best = np.full(P, -1)
    trapped = (y0 == 0) & (yv == 0).all(1)
    logD[trapped] = 0.0
    pos = (y0 > 0) & (yv > 0).all(1)
    if not pos.any():
        return logD, best
    R = np.diff(np.log(yv[pos]), axis=1)
    d = np.diff(times[k:])
    ne = R.shape[1]
    cR, cR2, cD, cL = (np.cumsum(R, 1), np.cumsum(R * R / d[None, :], 1), np.cumsum(d), np.cumsum(np.log(d)))
    totR, totR2, totD, totL = cR[:, -1], cR2[:, -1], cD[-1], cL[-1]
    vals = []
    for c in cuts:
        segs = []
        for (sR, sR2, tau, sl, n) in ((cR[:, c - 1], cR2[:, c - 1], cD[c - 1], cL[c - 1], c),
                                       (totR - cR[:, c - 1], totR2 - cR2[:, c - 1], totD - cD[c - 1], totL - cL[c - 1],
                                        ne - c)):
            Q = sR2 - sR * sR / tau
            with np.errstate(divide="ignore", invalid="ignore"):
                v = np.where(Q > 0, -n / 2 * (np.log(2 * np.pi * Q / n) + 1) - 0.5 * sl, np.inf)
            segs.append(v)
        vals.append(segs[0] + segs[1])
    V = np.vstack(vals)
    j = np.argmax(V, axis=0)
    logD[pos] = V[j, np.arange(V.shape[1])] - np.log(yv[pos][:, 1:]).sum(1)
    bp = np.full(pos.sum(), -1)
    bp[:] = np.array(cuts)[j]
    best[pos] = bp
    return logD, best


def scores(Ss, times):
    k = (Ss.shape[1] - 1) // 2
    ne = Ss.shape[1] - 1 - k
    base = cev.score(Ss, times, ALPHAS, 0.0)
    P = Ss.shape[0]
    dt = np.diff(times)[None, :]
    x, y = Ss[:, :-1], Ss[:, 1:]
    ev = np.empty((P, len(cev.CATALOGUE)))
    for c, (p, kap) in enumerate(cev.CATALOGUE):
        ev[:, c] = cev.log_kernel(p, kap, dt, x, y)[:, k:].sum(1)
    logG = ev[np.arange(P), base["sel"]]
    logG0 = ev[:, cev.NULL].max(1)
    ok = np.isin(base["status"], ("ok", "resurrection"))
    out = {"raw": base["logE"], "d055": base["logEd"], "status": base["status"], "sel": base["sel"],
           "margin_small": base["margin_small"], "clipped": {}}
    for name in CUTSETS:
        cuts, clipped = cutset(name, ne)
        out["clipped"][name] = clipped
        logDS, bc = switch_logsup(Ss, times, k, cuts)
        logD = np.maximum(logG0, logDS)
        with np.errstate(invalid="ignore"):
            le = np.where((logG == -np.inf) | (logD == np.inf) | ~ok, -np.inf, logG - logD)
        out[f"sw_{name}"] = le
        out[f"sw_{name}_unbounded"] = (logDS == np.inf) & ok
        out[f"sw_{name}_cut"] = bc
    return out


def admitted(t, T, freq, name):
    """Coverage of a switch row by cut set `name` at this frequency (registered rule)."""
    st = FREQ[freq]
    N = DAYS * T // st
    ne = N - N // 2
    cm = switch_month(T, t[4])
    c_star = cm if freq == "monthly" else 21 * cm
    return c_star in cutset(name, ne)[0]


def covered(t, T, freq, col):
    kind, a, k, kr, s = t
    if kind == "cevnull":
        return True
    if kind == "cevalt":
        return False
    if kind == "const":
        return {"raw": a == 0.0 and k in (0.20, 0.30, 0.45), "d055": True}.get(col, True)
    return False if col in ("raw", "d055") else admitted(t, T, freq, col[3:])


def job(args):
    t, T, b, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    S = simulate(t, rng, BATCH, T)
    out = {"truth": tname(t), "T": T, "b": b, "freq": {}}
    for f, st in FREQ.items():
        idx = r023.grid(T, st)
        Ss, times = S[:, idx], idx / DAYS
        sc = scores(Ss, times)
        rec = {key: (v.tolist() if isinstance(v, np.ndarray) else v) for key, v in sc.items()}
        k = (len(times) - 1) // 2
        ne = len(times) - 1 - k
        amb = np.asarray(sc["margin_small"], bool).copy()
        for col in COLS:
            for a in ALPHAS:
                amb |= np.abs(np.asarray(sc[col], float) + math.log(a)) < 1e-6
        rows = sorted(set((list(range(5)) if b == 0 else []) + [int(i) for i in np.flatnonzero(amb)]))
        checks = []
        for i in rows:
            tt, pp = [float(x) for x in times], [float(x) for x in Ss[i]]
            ck = {"path": i, "ambiguous": bool(amb[i]), "score_absdiff": {}, "cut_match": {}}
            mp.dps = 15
            tr = sw059.score_total_path(cev.CATALOGUE, tt, pp, k, cutset("K10", ne)[0])
            ck["status_adapter"] = list(tr["status"])
            ck["score_absdiff"]["raw"] = r023.diff(tr["raw_log_e"], sc["raw"][i])
            ck["score_absdiff"]["d055"] = r023.diff(tr["drift_log_e"], sc["d055"][i])
            ck["score_absdiff"]["sw_K10_adapter"] = r023.diff(tr["log_e"], sc["sw_K10"][i])
            ck["fit_match"] = tr["fit"] is not None and int(tr["fit"]) == int(sc["sel"][i])
            if "numerical_failure" not in tr["status"] and "outside_domain" not in tr["status"]:
                nulls = [c for c, (p_, _) in enumerate(cev.CATALOGUE) if p_ <= 1]
                num, old = tr["evaluation"][tr["fit"]], max(tr["evaluation"][c] for c in nulls)
                mp.dps = 70
                for name in CUTSETS:
                    cuts = cutset(name, ne)[0]
                    lp = sw059.log_null_sup(tt[k:], pp[k:], cuts)
                    ck["score_absdiff"][f"sw_{name}"] = r023.diff(
                        sw059.gaussian.enlarged_log_score(num, old, lp), sc[f"sw_{name}"][i])
                    if Ss[i, k:].min() > 0:
                        r_ = [mp.log(mp.mpf(pp[j + 1]) / mp.mpf(pp[j])) for j in range(k, len(pp) - 1)]
                        d_ = [mp.mpf(tt[j + 1]) - mp.mpf(tt[j]) for j in range(k, len(tt) - 1)]
                        ck["cut_match"][name] = int(sw059.profile.profile_returns(r_, d_, cuts)["cut"]) == \
                            int(sc[f"sw_{name}_cut"][i])
                mp.dps = 15
            checks.append(ck)
        rec["checks"] = checks
        out["freq"][f] = rec
    return out


def main():
    root = np.random.SeedSequence(SEED)
    cells = [(t, T) for t in TRUTHS for T in HORIZONS]
    jobs = []
    for (t, T), ss in zip(cells, root.spawn(len(cells))):
        for b, s in enumerate(ss.spawn(PATHS // BATCH)):
            jobs.append((t, T, b, s.generate_state(2).tolist()))
    with Pool(WORKERS) as pool:
        parts = pool.map(job, jobs, chunksize=1)
    res = {"cutsets": {"K1": "midpoint", **{k: f"min segment {v}" for k, v in PHI.items()}}, "columns": COLS,
           "cells": {}, "panels": {}, "admission": {}}
    rows, LOG, STAT = [], {}, {}
    for t, T in cells:
        n = tname(t)
        ps = sorted([p for p in parts if p["truth"] == n and p["T"] == T], key=lambda p: p["b"])
        cell = {}
        for f in FREQ:
            recs = [p["freq"][f] for p in ps]
            cat = lambda key: np.concatenate([np.asarray(r[key]) for r in recs])
            L = {col: cat(col).astype(float) for col in COLS}
            LOG[(n, T, f)] = L
            st = cat("status")
            STAT[f"{n}|{T}|{f}"] = {"n": int(st.size),
                                    "not_ok": [[int(i), str(st[i])] for i in np.flatnonzero(st != "ok")]}
            cks = [ck for r in recs for ck in r["checks"]]
            c = {"status_counts": {s: int((st == s).sum()) for s in set(st.tolist())},
                 "fit_counts": {str(cev.CATALOGUE[i]): int((cat("sel") == i).sum()) for i in set(cat("sel").tolist())},
                 "train_margin_small": int(cat("margin_small").sum()),
                 "clipped": recs[0]["clipped"],
                 "coverage": {col: covered(t, T, f, col) for col in COLS},
                 "unbounded": {name: int(cat(f"sw_{name}_unbounded").sum()) for name in CUTSETS},
                 "checks": cks,
                 "checks_summary": {
                     "n": len(cks), "ambiguous": sum(ck["ambiguous"] for ck in cks),
                     "max_score_absdiff": max([max(ck["score_absdiff"].values()) for ck in cks], default=None),
                     "fit_mismatch": sum(not ck["fit_match"] for ck in cks),
                     "cut_mismatch": sum(not v for ck in cks for v in ck["cut_match"].values())}}
            for name in CUTSETS:
                bc = cat(f"sw_{name}_cut")
                vals, cnt = np.unique(bc, return_counts=True)
                c[f"sw_{name}_cut_quantiles"] = (np.quantile(bc[bc >= 0], [0.1, 0.5, 0.9]).tolist()
                                                 if (bc >= 0).any() else None)
            for a in ALPHAS:
                thr = -math.log(a)
                rj = {col: L[col] > thr for col in COLS}
                c[str(a)] = {col: r023.rate(v) for col, v in rj.items()}
                for ref in ("raw", "d055"):
                    c[str(a)][f"paired_vs_{ref}"] = {col: r023.paired(rj[col], rj[ref]) for col in COLS[2:]}
            for col in COLS:
                E = np.exp(np.minimum(L[col], 700))
                c[f"{col}_summary"] = {"mean_E": float(E.mean()), "mean_E_se": float(E.std(ddof=1) / math.sqrt(E.size)),
                                       "median_logE": float(np.median(L[col])), "zero_count": int((L[col] == -np.inf).sum())}
            seq = [L["sw_K10"], L["sw_K25"], L["sw_K40"], L["sw_K1"], L["d055"], L["raw"]]
            c["ordering_violations"] = sum(int(np.sum((seq[i] > seq[i + 1] + 1e-9) & np.isfinite(seq[i])))
                                           for i in range(len(seq) - 1))
            cell[f] = c
            if t[0] == "switch":
                res["admission"][f"{n}|{T}|{f}"] = {name: admitted(t, T, f, name) for name in CUTSETS}
            for col in COLS:
                rows.append([n, T, f, col, "covered" if c["coverage"][col] else
                             ("alternative" if t[0] == "cevalt" else "uncovered_null"),
                             c["0.05"][col]["rate"], c["0.05"][col]["se"], c["0.1"][col]["rate"]])
        res["cells"][f"{n}|{T}"] = cell
    alt = tname(("cevalt", 1.5, 0.30, None, None))
    for T in HORIZONS:
        for s in (0.50, 0.15):
            nul = ("switch", 0.0, 0.20, 0.45, s)
            En_all, Ea_all = LOG[(tname(nul), T, "daily")], LOG[(alt, T, "daily")]
            for col in COLS:
                En, Ea = np.exp(np.minimum(En_all[col], 700)), np.exp(np.minimum(Ea_all[col], 700))
                for q in (0.05, 0.10):
                    fa, da, na, fm, td, fd, nm = [], [], [], [], [], [], []
                    for g in range(50):
                        rj = r023.ebh(En[g * 20:(g + 1) * 20], q)
                        fa.append(rj.sum() / max(rj.sum(), 1)); da.append(rj.sum()); na.append(rj.any())
                        rj2 = r023.ebh(np.r_[En[g * 20:g * 20 + 10], Ea[g * 20:g * 20 + 10]], q)
                        fm.append(rj2[:10].sum() / max(rj2.sum(), 1)); td.append(rj2[10:].sum())
                        fd.append(rj2[:10].sum()); nm.append(rj2.any())
                    res["panels"][f"{T}|s{s:.2f}|{col}|q{q}"] = {
                        "covered": covered(nul, T, "daily", col),
                        "allnull": {"mean_FDP": float(np.mean(fa)), "FDP_se": float(np.std(fa, ddof=1) / math.sqrt(50)),
                                    "mean_false": float(np.mean(da)), "nonempty": float(np.mean(na))},
                        "mixed": {"mean_FDP": float(np.mean(fm)), "FDP_se": float(np.std(fm, ddof=1) / math.sqrt(50)),
                                  "mean_true": float(np.mean(td)), "mean_false": float(np.mean(fd)),
                                  "nonempty": float(np.mean(nm))}}
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump(STAT, fh, indent=0)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["truth", "T", "freq", "column", "label", "rate_a05", "se_a05", "rate_a10"])
        w.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
