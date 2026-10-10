"""Experiment 023: prespecified sensitivity of claim 056's bounded-drift score to its annual drift interval.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/023/run.py          (start from inside .worktrees/analyst)

Reuses experiment 022's exact CEV kernel and sampler (experiments/022/cev.py), with scipy's ive patched by the
large-argument series of experiment 022's Deviation 4 (Deviation 1 here).
"""
import csv
import importlib.util
import json
import math
import os
import sys
from multiprocessing import Pool

import numpy as np
from mpmath import mp
from scipy import special

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


cev = _load("cev022", "experiments/022/cev.py")
prof056 = _load("prof056", "checks/056/profile.py")
score056 = _load("score056", "checks/056/scoring.py")

_ive = special.ive


def ive_fixed(a, z):
    """Copied from experiments/022/failures_sensitivity.py: scipy ive, with the exact 4-term large-z series where
    scipy returns NaN (z of order 1e9). Verified there against mpmath to machine precision."""
    v = _ive(a, z)
    z = np.asarray(z, float)
    bad = ~np.isfinite(v) & (z > 1e6)
    if np.any(bad):
        zb = z[bad] if np.ndim(z) else z
        mu = 4.0 * a * a
        t = 1.0 / (8.0 * zb)
        s = 1 - (mu - 1) * t + (mu - 1) * (mu - 9) * t ** 2 / 2 - (mu - 1) * (mu - 9) * (mu - 25) * t ** 3 / 6
        val = s / np.sqrt(2 * np.pi * zb)
        if np.ndim(v):
            v = np.array(v, float)
            v[bad] = val
        else:
            v = val
    return v


special.ive = ive_fixed

WORKERS = max(1, (os.cpu_count() or 4) - 3)
SEED = 20261056
DAYS = 252
PATHS, BATCH = 1000, 100
HORIZONS = (2, 5)
FREQ = {"monthly": 21, "daily": 1}
ALPHAS = (0.05, 0.10)
HS = (0.0, 0.025, 0.05, 0.10, 0.20, 0.40, 1.00)
PRIMARY_H = 0.20

# truths in the registered order: group 1 (b, kappa) lexicographic, group 2 p, group 3 (p, kappa)
G1 = [("gauss", b, k) for b in (-0.40, -0.20, -0.05, 0.0, 0.05, 0.20, 0.40) for k in (0.20, 0.30, 0.35, 0.45, 0.60)]
G2 = [("cevnull", p, 0.30) for p in (0.5, 0.75)]
G3 = [("cevalt", p, k) for p in (1.25, 1.5, 2.0) for k in (0.20, 0.30, 0.45)]
TRUTHS = G1 + G2 + G3


def tname(t):
    kind, a, k = t
    return f"gauss_b{a:+.2f}_k{k:.2f}" if kind == "gauss" else f"{kind}_p{a:.2f}_k{k:.2f}"


def simulate(t, rng, n, T):
    kind, a, k = t
    steps = DAYS * T
    dt = 1.0 / DAYS
    if kind == "gauss":
        tt = np.arange(steps + 1) * dt
        W = np.concatenate([np.zeros((n, 1)), np.cumsum(np.sqrt(dt) * rng.standard_normal((n, steps)), 1)], 1)
        return np.exp(k * W + (a - 0.5 * k * k) * tt)
    return cev.sample_cev(rng, a, k, n, steps, dt)


def grid(T, stride):
    steps = DAYS * T
    idx = np.arange(0, steps + 1, stride)
    return idx if idx[-1] == steps else np.r_[idx, steps]


def bounded_logsup(Ss, times, k, lo, hi):
    """Claim 056's exact constrained Gaussian log supremum on each path's evaluation block (vectorized).

    Returns (logD, kind) with kind in {'lower', 'upper', 'interior', 'unbounded', 'zero', 'trapped'}."""
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

    def loglik(b, w):
        squares = Q + tau * (mean - (b - w / 2)) ** 2
        return const - n * np.log(w) / 2 - squares / (2 * w)
    cands, labels = [], []
    for b, lab in ((lo, "lower"), (hi, "upper")):
        A = Q + tau * (mean - b) ** 2
        w = 2 * A / (n + np.sqrt(n * n + tau * A))
        with np.errstate(divide="ignore", invalid="ignore"):
            cands.append(np.where(w > 0, loglik(b, w), np.inf))
        labels.append(lab)
    with np.errstate(divide="ignore", invalid="ignore"):
        wi = Q / n
        bi = mean + wi / 2
        feas = (Q > 0) & (bi >= lo) & (bi <= hi)
        cands.append(np.where(feas, loglik(bi, np.where(wi > 0, wi, 1.0)), -np.inf))
    labels.append("interior")
    C = np.vstack(cands)
    best = np.argmax(C, axis=0)
    val = C[best, np.arange(C.shape[1])]
    unb = (Q == 0) & (mean >= lo) & (mean <= hi)
    val = np.where(unb, np.inf, val)
    kk = np.array(labels, dtype=object)[best]
    kk = np.where(unb, "unbounded", kk)
    logD[pos] = val - np.log(yv[pos][:, 1:]).sum(1)
    kind[pos] = kk
    return logD, kind


def scores(Ss, times):
    """Raw claim-054 log E, claim-055 log E^drift, and claim-056 log E_h for every h; plus fit and statuses."""
    k = (Ss.shape[1] - 1) // 2
    base = cev.score(Ss, times, ALPHAS, 0.0)
    logE, logEd = base["logE"], base["logEd"]
    # recover log G-hat and log G0 consistently with cev.score
    P = Ss.shape[0]
    dt = np.diff(times)[None, :]
    x, y = Ss[:, :-1], Ss[:, 1:]
    ev = np.empty((P, len(cev.CATALOGUE)))
    for c, (p, kap) in enumerate(cev.CATALOGUE):
        ev[:, c] = cev.log_kernel(p, kap, dt, x, y)[:, k:].sum(1)
    logG = ev[np.arange(P), base["sel"]]
    logG0 = ev[:, cev.NULL].max(1)
    ok = np.isin(base["status"], ("ok", "resurrection"))       # as cev.score keeps them
    out = {"raw": logE, "d055": logEd, "status": base["status"], "sel": base["sel"],
           "margin_small": base["margin_small"]}
    for h in HS:
        logDB, kind = bounded_logsup(Ss, times, k, -h, h)
        logD = np.maximum(logG0, logDB)
        with np.errstate(invalid="ignore"):
            le = np.where((logG == -np.inf) | (logD == np.inf) | ~ok, -np.inf, logG - logD)
        out[f"h{h}"] = le
        out[f"h{h}_kind"] = kind
    return out


def diff(mpv, fv):
    """|mp - float| when both finite; 0 when equal infinities; inf on a finite/infinite mismatch."""
    mpv, fv = float(mpv), float(fv)
    if np.isfinite(mpv) and np.isfinite(fv):
        return abs(mpv - fv)
    return 0.0 if mpv == fv else float("inf")


def job(args):
    t, T, b, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    S = simulate(t, rng, BATCH, T)
    out = {"truth": tname(t), "T": T, "b": b, "freq": {}}
    for f, st in FREQ.items():
        idx = grid(T, st)
        Ss, times = S[:, idx], idx / DAYS
        sc = scores(Ss, times)
        rec = {key: (v.tolist() if isinstance(v, np.ndarray) else v) for key, v in sc.items()}
        # preregistered checks: the first five paths of every cell/frequency (batch 0), and any ambiguous decision or
        # training margin < 1e-6 anywhere. The bounded profile is checked against checks/056/profile.py at 70 digits
        # for every h; every score column against the total adapter checks/056/scoring.py (primary h, which runs the
        # D14 CEV adapter) and, from that adapter's fit and evaluation likelihoods, the claim-055 and other-h scores.
        checks = []
        k = (len(times) - 1) // 2
        amb = np.asarray(sc["margin_small"], bool).copy()
        for h in HS:
            for a in ALPHAS:
                amb |= np.abs(np.asarray(sc[f"h{h}"]) + math.log(a)) < 1e-6
        for a in ALPHAS:
            amb |= np.abs(np.asarray(sc["raw"]) + math.log(a)) < 1e-6
            amb |= np.abs(np.asarray(sc["d055"]) + math.log(a)) < 1e-6
        rows = sorted(set((list(range(5)) if b == 0 else []) + [int(i) for i in np.flatnonzero(amb)]))
        for i in rows:
            ck = {"path": i, "ambiguous": bool(amb[i]), "profile_absdiff": {}, "score_absdiff": {}}
            tt, pp = [float(x) for x in times], [float(x) for x in Ss[i]]
            mp.dps = 70
            for h in HS:
                mpv = prof056.log_null_sup(tt[k:], pp[k:], -h, h)
                fv = bounded_logsup(Ss[i:i + 1], times, k, -h, h)[0][0]
                ck["profile_absdiff"][str(h)] = diff(mpv, fv)
            mp.dps = 15
            tr = score056.score_total_path(cev.CATALOGUE, tt, pp, k, -PRIMARY_H, PRIMARY_H)
            ck["status_adapter"] = list(tr["status"])
            ck["score_absdiff"]["raw"] = diff(tr["raw_log_e"], sc["raw"][i])
            ck["score_absdiff"][f"h{PRIMARY_H}"] = diff(tr["log_e"], sc[f"h{PRIMARY_H}"][i])
            if tr["fit"] is not None and "numerical_failure" not in tr["status"] and "outside_domain" not in tr["status"]:
                nulls = [c for c, (p_, _) in enumerate(cev.CATALOGUE) if p_ <= 1]
                num = tr["evaluation"][tr["fit"]]
                old = max(tr["evaluation"][c] for c in nulls)
                g = prof056.gaussian
                ck["score_absdiff"]["d055"] = diff(g.enlarged_log_score(num, old, g.log_null_sup(tt[k:], pp[k:])),
                                                   sc["d055"][i])
                for h in HS:
                    ck["score_absdiff"][f"h{h}"] = diff(
                        g.enlarged_log_score(num, old, prof056.log_null_sup(tt[k:], pp[k:], -h, h)), sc[f"h{h}"][i])
                ck["fit_match"] = int(tr["fit"]) == int(sc["sel"][i])
            checks.append(ck)
        rec["checks"] = checks
        out["freq"][f] = rec
    return out


def wilson(p, n, z=1.96):
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    hw = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return [c - hw, c + hw]


def rate(x):
    x = np.asarray(x, float)
    p = float(x.mean())
    return {"rate": p, "se": float(math.sqrt(p * (1 - p) / x.size)), "wilson95": wilson(p, x.size), "n": int(x.size)}


def paired(a, b):
    d = np.asarray(a, float) - np.asarray(b, float)
    return {"diff": float(d.mean()), "se": float(d.std(ddof=1) / math.sqrt(d.size))}


def ebh(e, q):
    m = e.size
    order = np.argsort(-e)
    es = e[order]
    ks = np.arange(1, m + 1)
    ok = es >= m / (q * ks)
    rej = np.zeros(m, bool)
    if ok.any():
        rej[order[:ks[ok].max()]] = True
    return rej


def main():
    root = np.random.SeedSequence(SEED)
    cells = [(t, T) for t in TRUTHS for T in HORIZONS]
    jobs = []
    for (t, T), ss in zip(cells, root.spawn(len(cells))):
        for b, s in enumerate(ss.spawn(PATHS // BATCH)):
            jobs.append((t, T, b, s.generate_state(2).tolist()))
    with Pool(WORKERS) as pool:
        parts = pool.map(job, jobs, chunksize=1)
    res, rows = {"hs": HS, "primary_h": PRIMARY_H, "cells": {}, "panels": {}}, []
    LOG, STAT = {}, {}
    for t, T in cells:
        n = tname(t)
        ps = sorted([p for p in parts if p["truth"] == n and p["T"] == T], key=lambda p: p["b"])
        cell = {}
        for f in FREQ:
            recs = [p["freq"][f] for p in ps]
            cat = lambda key: np.concatenate([np.asarray(r[key]) for r in recs])
            raw, d055 = cat("raw").astype(float), cat("d055").astype(float)
            Lh = {h: cat(f"h{h}").astype(float) for h in HS}
            LOG[(n, T, f)] = (raw, d055, Lh)
            st = cat("status")
            STAT[f"{n}|{T}|{f}"] = {"n": int(st.size),
                                    "not_ok": [[int(i), str(st[i])] for i in np.flatnonzero(st != "ok")]}
            c = {"status_counts": {s: int((st == s).sum()) for s in set(st.tolist())},
                 "fit_counts": {str(cev.CATALOGUE[i]): int((cat("sel") == i).sum()) for i in set(cat("sel").tolist())},
                 "train_margin_small": int(cat("margin_small").sum()),
                 "checks": [ck for r in recs for ck in r["checks"]]}
            cks = c["checks"]
            c["checks_summary"] = {
                "n": len(cks), "ambiguous": sum(ck["ambiguous"] for ck in cks),
                "max_profile_absdiff": max([max(ck["profile_absdiff"].values()) for ck in cks], default=None),
                "max_score_absdiff": max([max(ck["score_absdiff"].values()) for ck in cks], default=None),
                "fit_mismatch": sum(not ck.get("fit_match", True) for ck in cks)}
            for h in HS:
                kinds = cat(f"h{h}_kind")
                c[f"h{h}_profile_kind"] = {s: int((kinds == s).sum()) for s in set(kinds.tolist())}
            for a in ALPHAS:
                thr = -math.log(a)
                rj = {"raw": raw > thr, "d055": d055 > thr}
                rj.update({f"h{h}": Lh[h] > thr for h in HS})
                c[str(a)] = {key: rate(v) for key, v in rj.items()}
                c[str(a)]["paired_vs_055"] = {f"h{h}": paired(rj[f"h{h}"], rj["d055"]) for h in HS}
                c[str(a)]["paired_vs_raw"] = {f"h{h}": paired(rj[f"h{h}"], rj["raw"]) for h in HS}
            for key, L in [("raw", raw), ("d055", d055)] + [(f"h{h}", Lh[h]) for h in HS]:
                E = np.exp(np.minimum(L, 700))
                c[f"{key}_summary"] = {"mean_E": float(E.mean()), "mean_E_se": float(E.std(ddof=1) / math.sqrt(E.size)),
                                       "median_logE": float(np.median(L)), "zero_count": int((L == -np.inf).sum())}
            # pointwise ordering raw >= h_small >= ... >= h_large >= d055 (finite comparisons)
            seq = [raw] + [Lh[h] for h in HS] + [d055]
            viol = sum(int(np.sum((seq[i + 1] > seq[i] + 1e-9) & np.isfinite(seq[i]))) for i in range(len(seq) - 1))
            c["ordering_violations"] = viol
            cell[f] = c
            for h in HS:
                kind, a_, k_ = t
                label = ("in-bound" if abs(a_) <= h + 1e-12 else "out-of-bound") if kind == "gauss" else kind
                rows.append([n, T, f, h, label, c["0.05"][f"h{h}"]["rate"], c["0.05"][f"h{h}"]["se"],
                             c["0.05"]["d055"]["rate"], c["0.05"]["raw"]["rate"]])
        res["cells"][f"{n}|{T}"] = cell
    # panel secondary: daily, Gaussian kappa = 0.35 rows (each b) and CEV p = 1.5, kappa = 0.30
    alt = tname(("cevalt", 1.5, 0.30))
    for T in HORIZONS:
        for b_ in (-0.40, -0.20, -0.05, 0.0, 0.05, 0.20, 0.40):
            nul = tname(("gauss", b_, 0.35))
            for key in ["raw", "d055"] + [f"h{h}" for h in HS]:
                def getE(name):
                    raw, d055, Lh = LOG[(name, T, "daily")]
                    L = raw if key == "raw" else d055 if key == "d055" else Lh[float(key[1:])]
                    return np.exp(np.minimum(L, 700))
                En, Ea = getE(nul), getE(alt)
                for q in (0.05, 0.10):
                    fdp_all, disc_all, ne_all = [], [], []
                    fdp_mix, td, fd, ne_mix = [], [], [], []
                    for g in range(50):
                        e = En[g * 20:(g + 1) * 20]
                        rj = ebh(e, q)
                        fdp_all.append(rj.sum() / max(rj.sum(), 1)); disc_all.append(rj.sum()); ne_all.append(rj.any())
                        e2 = np.r_[En[g * 20:g * 20 + 10], Ea[g * 20:g * 20 + 10]]
                        rj2 = ebh(e2, q)
                        fdp_mix.append(rj2[:10].sum() / max(rj2.sum(), 1)); td.append(rj2[10:].sum()); fd.append(rj2[:10].sum())
                        ne_mix.append(rj2.any())
                    res["panels"][f"{T}|b{b_:+.2f}|{key}|q{q}"] = {
                        "allnull": {"mean_FDP": float(np.mean(fdp_all)), "FDP_se": float(np.std(fdp_all, ddof=1) / math.sqrt(50)),
                                    "mean_false": float(np.mean(disc_all)), "nonempty": float(np.mean(ne_all))},
                        "mixed": {"mean_FDP": float(np.mean(fdp_mix)), "FDP_se": float(np.std(fdp_mix, ddof=1) / math.sqrt(50)),
                                  "mean_true": float(np.mean(td)), "mean_false": float(np.mean(fd)), "nonempty": float(np.mean(ne_mix))},
                        "in_bound": (abs(b_) <= float(key[1:]) + 1e-12) if key.startswith("h") else (key == "d055")}
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump(STAT, fh, indent=0)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["truth", "T", "freq", "h", "label", "rate_a05", "se", "d055_rate_a05", "raw_rate_a05"])
        w.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
