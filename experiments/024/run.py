"""Experiment 024: prespecified scale-interval sensitivity of claim 057's rectangle score, drift fixed at [-0.20, 0.20].

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/024/run.py          (start from inside .worktrees/analyst)

Reuses experiment 023's code (experiments/023/run.py): the exact Gaussian and CEV samplers, the large-argument Bessel
fix, claim 056's bounded profile and the reporting helpers. Fresh paths from SeedSequence(20261057).
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


r023 = _load("r023", "experiments/023/run.py")       # also patches scipy's ive (023's Deviation 1)
cev = r023.cev
prof057 = _load("prof057", "checks/057/profile.py")
score057 = _load("score057", "checks/057/scoring.py")

WORKERS = r023.WORKERS
SEED = 20261057
DAYS, PATHS, BATCH, HORIZONS, FREQ, ALPHAS = r023.DAYS, r023.PATHS, r023.BATCH, r023.HORIZONS, r023.FREQ, r023.ALPHAS
LO, HI = -0.20, 0.20
SCALES = ((0.30, 0.30), (0.25, 0.35), (0.20, 0.45), (0.15, 0.60), (0.10, 1.00))
PRIMARY = (0.20, 0.45)
GRID_K = (0.20, 0.30, 0.45)

G1 = [("gauss", b, k) for b in (-0.40, -0.20, -0.05, 0.0, 0.05, 0.20, 0.40)
      for k in (0.15, 0.20, 0.25, 0.30, 0.35, 0.45, 0.60)]
G2 = [("cevnull", p, 0.30) for p in (0.5, 0.75)]
G3 = [("cevalt", p, k) for p in (1.25, 1.5, 2.0) for k in (0.20, 0.30, 0.45)]
TRUTHS = G1 + G2 + G3
tname = r023.tname


def ckey(c):
    return f"r{c[0]:.2f}-{c[1]:.2f}"


COLS = ["raw", "d055", "b056"] + [ckey(c) for c in SCALES]


def covered(t, col):
    """Coverage label (Design): rectangle membership OR the retained p = 1 catalogue null; CEV nulls always."""
    kind, a, k = t
    if kind == "cevnull":
        return True
    if kind == "cevalt":
        return False
    grid_null = a == 0.0 and k in GRID_K
    if col == "raw":
        return grid_null
    if col == "d055":
        return True
    inb = LO - 1e-12 <= a <= HI + 1e-12
    if col == "b056":
        return inb
    c = SCALES[[ckey(s) for s in SCALES].index(col)]
    return (inb and c[0] - 1e-12 <= k <= c[1] + 1e-12) or grid_null


def rect_logsup(Ss, times, k, lo, hi, slo, shi, tol=1e-9):
    """Claim 057's exact rectangle maximum on each path's evaluation block (vectorized), and the active category set.

    Candidates as in checks/057/profile.py: both drift edges with the clipped variance root, both scale edges with the
    clipped drift, and the interior stationary point when feasible. Categories: interior, drift_edge, scale_edge, corner
    (an edge candidate whose other coordinate is clipped). Every category within tol of the maximum is reported."""
    P = Ss.shape[0]
    yv = Ss[:, k:]
    y0 = yv[:, 0]
    logD = np.full(P, -np.inf)
    kind = np.full(P, "zero", dtype=object)
    trapped = (y0 == 0) & (yv == 0).all(1)
    logD[trapped] = 0.0
    kind[trapped] = "trapped"
    pos = (y0 > 0) & (yv > 0).all(1)
    if not pos.any():
        return logD, kind
    R = np.diff(np.log(yv[pos]), axis=1)
    d = np.diff(times[k:])[None, :]
    n = R.shape[1]
    tau = d.sum()
    mean = R.sum(1) / tau
    Q = ((R - mean[:, None] * d) ** 2 / d).sum(1) if n > 1 else np.zeros(R.shape[0])
    const = -n * math.log(2 * math.pi) / 2 - 0.5 * np.log(d).sum()
    lw, hw = slo * slo, shi * shi

    def loglik(b, w):
        return const - n * np.log(w) / 2 - (Q + tau * (mean - (b - w / 2)) ** 2) / (2 * w)
    cands, cats = [], []
    for b in (lo, hi):
        A = Q + tau * (mean - b) ** 2
        root = 2 * A / (n + np.sqrt(n * n + tau * A))
        w = np.clip(root, lw, hw)
        cands.append(loglik(b, w))
        cats.append(np.where((root < lw) | (root > hw), "corner", "drift_edge"))
    for w in (lw, hw):
        b0 = mean + w / 2
        b = np.clip(b0, lo, hi)
        cands.append(loglik(b, np.full_like(b, w)))
        cats.append(np.where((b0 < lo) | (b0 > hi), "corner", "scale_edge"))
    wi = Q / n
    bi = mean + wi / 2
    feas = (wi >= lw) & (wi <= hw) & (bi >= lo) & (bi <= hi)
    with np.errstate(divide="ignore", invalid="ignore"):
        cands.append(np.where(feas, loglik(bi, np.where(wi > 0, wi, 1.0)), -np.inf))
    cats.append(np.full(R.shape[0], "interior", dtype=object))
    C = np.vstack(cands)
    best = C.max(0)
    act = np.abs(C - best[None, :]) <= tol * np.maximum(1.0, np.abs(best[None, :]))
    labels = np.array(["+".join(sorted({str(cats[j][i]) for j in range(C.shape[0]) if act[j, i]}))
                       for i in range(C.shape[1])], dtype=object)
    logD[pos] = best - np.log(yv[pos][:, 1:]).sum(1)
    kind[pos] = labels
    return logD, kind


def scores(Ss, times):
    k = (Ss.shape[1] - 1) // 2
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
           "margin_small": base["margin_small"], "fail": {}}

    def enlarged(logDB):
        logD = np.maximum(logG0, logDB)
        with np.errstate(invalid="ignore"):
            return np.where((logG == -np.inf) | (logD == np.inf) | ~ok, -np.inf, logG - logD)
    logDB, kindB = r023.bounded_logsup(Ss, times, k, LO, HI)
    out["b056"], out["b056_kind"] = enlarged(logDB), kindB
    for c in SCALES:
        logDR, kindR = rect_logsup(Ss, times, k, LO, HI, c[0], c[1])
        bad = ~np.isfinite(logDR) & (logDR > 0) | np.isnan(logDR)     # a computed +inf or NaN is a failure (Design)
        logDR = np.where(bad, np.inf, logDR)
        le = enlarged(logDR)
        out[ckey(c)] = np.where(bad, -np.inf, le)
        out[ckey(c) + "_kind"] = np.where(bad, "numerical_failure", kindR)
        out["fail"][ckey(c)] = int(bad.sum())
    return out


def job(args):
    t, T, b, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    S = r023.simulate(t, rng, BATCH, T)
    out = {"truth": tname(t), "T": T, "b": b, "freq": {}}
    for f, st in FREQ.items():
        idx = r023.grid(T, st)
        Ss, times = S[:, idx], idx / DAYS
        sc = scores(Ss, times)
        rec = {key: (v.tolist() if isinstance(v, np.ndarray) else v) for key, v in sc.items()}
        checks = []
        k = (len(times) - 1) // 2
        amb = np.asarray(sc["margin_small"], bool).copy()
        for col in COLS:
            for a in ALPHAS:
                amb |= np.abs(np.asarray(sc[col], float) + math.log(a)) < 1e-6
        rows = sorted(set((list(range(5)) if b == 0 else []) + [int(i) for i in np.flatnonzero(amb)]))
        for i in rows:
            ck = {"path": i, "ambiguous": bool(amb[i]), "profile_absdiff": {}, "score_absdiff": {}}
            tt, pp = [float(x) for x in times], [float(x) for x in Ss[i]]
            mp.dps = 70
            for c in SCALES:
                mpv = prof057.log_null_sup(tt[k:], pp[k:], LO, HI, c[0], c[1])
                fv = rect_logsup(Ss[i:i + 1], times, k, LO, HI, c[0], c[1])[0][0]
                ck["profile_absdiff"][ckey(c)] = r023.diff(mpv, fv)
            mp.dps = 15
            tr = score057.score_total_path(cev.CATALOGUE, tt, pp, k, LO, HI, PRIMARY[0], PRIMARY[1])
            ck["status_adapter"] = list(tr["status"])
            ck["score_absdiff"]["raw"] = r023.diff(tr["raw_log_e"], sc["raw"][i])
            ck["score_absdiff"][ckey(PRIMARY) + "_adapter"] = r023.diff(tr["log_e"], sc[ckey(PRIMARY)][i])
            if tr["fit"] is not None and "numerical_failure" not in tr["status"] and "outside_domain" not in tr["status"]:
                nulls = [c for c, (p_, _) in enumerate(cev.CATALOGUE) if p_ <= 1]
                num = tr["evaluation"][tr["fit"]]
                old = max(tr["evaluation"][c] for c in nulls)
                g = prof057.gaussian
                ck["score_absdiff"]["d055"] = r023.diff(
                    g.enlarged_log_score(num, old, g.log_null_sup(tt[k:], pp[k:])), sc["d055"][i])
                ck["score_absdiff"]["b056"] = r023.diff(
                    g.enlarged_log_score(num, old, prof057.bounded.log_null_sup(tt[k:], pp[k:], LO, HI)), sc["b056"][i])
                for c in SCALES:
                    ck["score_absdiff"][ckey(c)] = r023.diff(g.enlarged_log_score(
                        num, old, prof057.log_null_sup(tt[k:], pp[k:], LO, HI, c[0], c[1])), sc[ckey(c)][i])
                ck["fit_match"] = int(tr["fit"]) == int(sc["sel"][i])
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
    res = {"drift_interval": [LO, HI], "scale_intervals": SCALES, "primary_scale": PRIMARY, "columns": COLS,
           "cells": {}, "panels": {}}
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
                 "rect_failures": {col: int(sum(r["fail"][col] for r in recs)) for col in COLS[3:]},
                 "coverage": {col: covered(t, col) for col in COLS},
                 "checks": cks,
                 "checks_summary": {
                     "n": len(cks), "ambiguous": sum(ck["ambiguous"] for ck in cks),
                     "max_profile_absdiff": max([max(ck["profile_absdiff"].values()) for ck in cks], default=None),
                     "max_score_absdiff": max([max(ck["score_absdiff"].values()) for ck in cks], default=None),
                     "fit_mismatch": sum(not ck.get("fit_match", True) for ck in cks)}}
            kinds = cat("b056_kind")
            c["b056_profile_kind"] = {s: int((kinds == s).sum()) for s in set(kinds.tolist())}
            for sc_ in SCALES:
                kinds = cat(ckey(sc_) + "_kind")
                c[ckey(sc_) + "_profile_kind"] = {s: int((kinds == s).sum()) for s in set(kinds.tolist())}
            for a in ALPHAS:
                thr = -math.log(a)
                rj = {col: L[col] > thr for col in COLS}
                c[str(a)] = {col: r023.rate(v) for col, v in rj.items()}
                for ref in ("raw", "d055", "b056"):
                    c[str(a)][f"paired_vs_{ref}"] = {col: r023.paired(rj[col], rj[ref]) for col in COLS[3:]}
            for col in COLS:
                E = np.exp(np.minimum(L[col], 700))
                c[f"{col}_summary"] = {"mean_E": float(E.mean()), "mean_E_se": float(E.std(ddof=1) / math.sqrt(E.size)),
                                       "median_logE": float(np.median(L[col])), "zero_count": int((L[col] == -np.inf).sum())}
            # pointwise ordering: d055 <= b056 <= rect(widest) <= ... <= rect(narrowest) <= raw
            seq = [L["d055"], L["b056"]] + [L[ckey(s)] for s in SCALES[::-1]] + [L["raw"]]
            c["ordering_violations"] = sum(int(np.sum((seq[i] > seq[i + 1] + 1e-9) & np.isfinite(seq[i])))
                                           for i in range(len(seq) - 1))
            cell[f] = c
            for col in COLS:
                rows.append([n, T, f, col, "covered" if covered(t, col) else ("alternative" if t[0] == "cevalt" else
                                                                             "uncovered_null"),
                             c["0.05"][col]["rate"], c["0.05"][col]["se"], c["0.1"][col]["rate"]])
        res["cells"][f"{n}|{T}"] = cell
    alt = tname(("cevalt", 1.5, 0.30))
    for T in HORIZONS:
        for b_ in (-0.40, -0.20, -0.05, 0.0, 0.05, 0.20, 0.40):
            nul = ("gauss", b_, 0.35)
            En_all = LOG[(tname(nul), T, "daily")]
            Ea_all = LOG[(alt, T, "daily")]
            for col in COLS:
                En, Ea = np.exp(np.minimum(En_all[col], 700)), np.exp(np.minimum(Ea_all[col], 700))
                for q in (0.05, 0.10):
                    fdp_all, disc_all, ne_all, fdp_mix, td, fd, ne_mix = [], [], [], [], [], [], []
                    for g in range(50):
                        rj = r023.ebh(En[g * 20:(g + 1) * 20], q)
                        fdp_all.append(rj.sum() / max(rj.sum(), 1)); disc_all.append(rj.sum()); ne_all.append(rj.any())
                        rj2 = r023.ebh(np.r_[En[g * 20:g * 20 + 10], Ea[g * 20:g * 20 + 10]], q)
                        fdp_mix.append(rj2[:10].sum() / max(rj2.sum(), 1)); td.append(rj2[10:].sum())
                        fd.append(rj2[:10].sum()); ne_mix.append(rj2.any())
                    res["panels"][f"{T}|b{b_:+.2f}|{col}|q{q}"] = {
                        "covered": covered(nul, col),
                        "allnull": {"mean_FDP": float(np.mean(fdp_all)), "FDP_se": float(np.std(fdp_all, ddof=1) / math.sqrt(50)),
                                    "mean_false": float(np.mean(disc_all)), "nonempty": float(np.mean(ne_all))},
                        "mixed": {"mean_FDP": float(np.mean(fdp_mix)), "FDP_se": float(np.std(fdp_mix, ddof=1) / math.sqrt(50)),
                                  "mean_true": float(np.mean(td)), "mean_false": float(np.mean(fd)),
                                  "nonempty": float(np.mean(ne_mix))}}
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
