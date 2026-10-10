"""Experiment 013: claim 008's visited-range identity computed from n equally spaced samples.

    uv run python experiments/013/run.py      (start from inside .worktrees/analyst)
"""
import csv
import json
import os
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
WORKERS = max(1, (os.cpu_count() or 4) - 3)
SEED = 20261013
F = 491_400
NS = (252, 1950, 8190, 98280)
QS = (0.01, 0.05, 0.10)
PS = (0.01, 0.05, 0.10)
HMULT = (1.0, 2.0, 0.5)
PATHS, BATCH = 400, 25
SIGMAS = ("one", "x075", "x2")


def primitive(sig, x):
    if sig == "one":
        return 0.5 * x * x
    if sig == "x075":
        return 2.0 * np.sqrt(x)
    return -0.5 / (x * x)


def exact(sig, lo, hi, m, M):
    a, b = max(lo, m, 0.0), min(hi, M)
    if b <= a:
        return 0.0
    if sig == "x2" and a <= 0:
        return np.inf
    return float(primitive(sig, b) - primitive(sig, a))


def simulate(rng, sig, reps):
    dt = 1.0 / F
    if sig == "x2":
        X = np.concatenate([np.zeros((reps, 1, 3)), np.cumsum(np.sqrt(dt) * rng.standard_normal((reps, F, 3)), 1)], 1)
        X[:, :, 0] += 1.0
        return 1.0 / np.linalg.norm(X, axis=2)
    S = np.empty((reps, F + 1))
    if sig == "one":
        s = np.ones(reps)
        dead = np.zeros(reps, bool)
        S[:, 0] = 1.0
        for j in range(F):
            nxt = s + np.sqrt(dt) * rng.standard_normal(reps)
            u = rng.random(reps)
            dead |= (nxt <= 0) | ((s > 0) & (u < np.exp(-2.0 * s * np.maximum(nxt, 0) / dt)))
            s = np.where(dead, 0.0, nxt)
            S[:, j + 1] = s
        return S
    r = np.full(reps, 4.0)                                       # R = 4 S^{1/4}, S_0 = 1
    dead = np.zeros(reps, bool)
    S[:, 0] = 1.0
    for j in range(F):
        nxt = r - 1.5 / np.where(r > 0, r, 1.0) * dt + np.sqrt(dt) * rng.standard_normal(reps)
        dead |= nxt <= 0
        r = np.where(dead, 0.0, nxt)
        S[:, j + 1] = (r / 4.0) ** 4
    return S


def estimate(Ssamp, h):
    """L-hat at every sample point (box kernel on squared increments) and the per-sample terms of H-hat."""
    n = Ssamp.size - 1
    X, q = Ssamp[:-1], np.diff(Ssamp) ** 2
    order = np.argsort(X)
    xs, cq = X[order], np.concatenate([[0.0], np.cumsum(q[order])])
    lo = np.searchsorted(xs, X - h, side="right")
    hi = np.searchsorted(xs, X + h, side="left")
    Lhat = (cq[hi] - cq[lo]) / (2.0 * h)
    cnt = hi - lo
    with np.errstate(divide="ignore", invalid="ignore"):
        term = np.where((X > 0) & (Lhat > 0), (1.0 / n) * X / Lhat, 0.0)
    return X, term, cnt


def one_path(sig, Sf, n, hm):
    m, M = float(Sf.min()), float(Sf.max())
    Ss = Sf[:: F // n]
    mh, Mh = float(Ss.min()), float(Ss.max())
    R = Mh - mh
    h = hm * 0.5 * R * n ** (-1 / 3) if R > 0 else 1e-12
    X, term, cnt = estimate(Ss, h)
    Hhat, Hex = float(term.sum()), exact(sig, -np.inf, np.inf, m, M)
    # delta-method variance over bins of width 2h
    nb = max(1, int(np.ceil(R / (2 * h)))) if R > 0 else 1
    b = np.minimum(((X - mh) / (2 * h)).astype(int), nb - 1) if R > 0 else np.zeros_like(X, int)
    contrib = np.bincount(b, weights=term, minlength=nb)
    nbin = np.bincount(b, minlength=nb)
    var = float(np.sum(np.where(nbin > 0, contrib ** 2 * 2.0 / np.maximum(nbin, 1), 0.0)))
    out = {"err": Hhat - Hex, "exact": Hex, "cover": abs(Hhat - Hex) <= 1.96 * np.sqrt(var), "absorbed": m <= 0}
    if hm != 1.0:
        return out
    for q in QS:
        a, bq = np.quantile(X, q), np.quantile(X, 1 - q)
        sel = (X > a) & (X < bq)
        out[f"trim{q}"] = float(term[sel].sum()) - exact(sig, a, bq, m, M)
        out[f"trim{q}_exact"] = exact(sig, a, bq, m, M)
    for p in PS:
        lo_b, hi_b = mh + p * R, Mh - p * R
        selb = (X <= lo_b) | (X >= hi_b)
        est_band = float(term[selb].sum())
        ex_band = exact(sig, -np.inf, lo_b, m, M) + exact(sig, hi_b, np.inf, m, M)
        out[f"band{p}"] = est_band - ex_band
    return out


def batch(args):
    sig, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    S = simulate(rng, sig, BATCH)
    res = []
    for Sf in S:
        res.append({f"{n}|{hm}": one_path(sig, Sf, n, hm) for n in NS for hm in HMULT})
    return sig, res


def summarize(rows, key):
    e = np.array([r[key] for r in rows], float)
    ok = np.isfinite(e)
    e = e[ok]
    k = e.size
    return {"n": int(k), "bias": float(e.mean()), "bias_se": float(e.std(ddof=1) / np.sqrt(k)),
            "rmse": float(np.sqrt(np.mean(e * e)))}


def main():
    root = np.random.SeedSequence(SEED)
    jobs = []
    for sig, ss in zip(SIGMAS, root.spawn(len(SIGMAS))):
        jobs += [(sig, s.generate_state(2).tolist()) for s in ss.spawn(PATHS // BATCH)]
    with Pool(WORKERS) as pool:
        parts = pool.map(batch, jobs)
    res, rows = {"F": F, "paths": PATHS, "cases": {}}, []
    for sig in SIGMAS:
        paths = [p for s, ps in parts if s == sig for p in ps]
        absorbed = int(sum(p[f"{NS[0]}|1.0"]["absorbed"] for p in paths))
        case = {"absorbed_paths": absorbed}
        for n in NS:
            for hm in HMULT:
                rr = [p[f"{n}|{hm}"] for p in paths]
                ex = np.array([r["exact"] for r in rr])
                s = summarize(rr, "err")
                s["mean_exact"] = float(np.mean(ex[np.isfinite(ex)]))
                s["rel_rmse"] = s["rmse"] / s["mean_exact"]
                cov = np.array([r["cover"] for r in rr], float)
                s["coverage"] = [float(cov.mean()), float(np.sqrt(cov.mean() * (1 - cov.mean()) / cov.size))]
                if hm == 1.0:
                    for q in QS:
                        t = summarize(rr, f"trim{q}")
                        t["mean_exact"] = float(np.mean([r[f"trim{q}_exact"] for r in rr]))
                        t["rel_rmse"] = t["rmse"] / t["mean_exact"] if t["mean_exact"] else None
                        s[f"trim{q}"] = t
                    e = np.array([r["err"] for r in rr])
                    for p in PS:
                        eb = np.array([r[f"band{p}"] for r in rr])
                        s[f"band{p}"] = {"bias_share": float(eb.mean() / e.mean()) if e.mean() else None,
                                         "mse_share": float(np.mean(eb * e) / np.mean(e * e)) if np.mean(e * e) else None}
                    if sig != "x2":
                        ab = np.array([r["absorbed"] for r in rr])
                        for tag, msk in (("absorbed", ab), ("not_absorbed", ~ab)):
                            if msk.any():
                                s[tag] = {"n": int(msk.sum()), "bias": float(e[msk].mean()),
                                          "rmse": float(np.sqrt(np.mean(e[msk] ** 2)))}
                case[f"{n}|{hm}"] = s
                rows.append([sig, n, hm, s["mean_exact"], s["bias"], s["bias_se"], s["rmse"], s["rel_rmse"],
                             s["coverage"][0]] + ([s[f"trim{q}"]["rel_rmse"] for q in QS] if hm == 1.0 else [None] * 3))
        res["cases"][sig] = case
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(res, f, indent=1, default=float)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["sigma", "n", "h_mult", "mean_exact", "bias", "bias_se", "rmse", "rel_rmse", "coverage"] +
                   [f"rel_rmse_trim{q}" for q in QS])
        w.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
