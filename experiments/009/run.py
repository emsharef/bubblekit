"""Experiment 009: sup_t |W^(N) - V| for claim 005's grid fund vs claim 001's continuous wealth.

    uv run python experiments/009/run.py      (start from inside .worktrees/analyst)
"""
import json
import os
import sys
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from conv import F, fund_W, refine_bes3, refine_bm, sim_bm, sim_inv_bes3, stop_at, wealth_V  # noqa: E402

WORKERS = max(1, (os.cpu_count() or 4) - 3)
SEED = 20261011
PATHS, BATCH = 4000, 250
PIS = (0.25, 0.5, 0.75, 1.0)
NS = (4, 16, 64, 252, 1008)
STOPS = (None, 5, 20)
ETAS = (0.01, 0.05, 0.2)
CHECK = 200


def batch(args):
    sigma, b, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    if sigma == "one":
        S = sim_bm(rng, BATCH)
        X = None
    else:
        S, X = sim_inv_bes3(rng, BATCH, return_X=True)
    hit = (S[:, -1] <= 0) if sigma == "one" else np.zeros(BATCH, bool)
    out = {"hit": hit.tolist(), "D": {}, "check": {}}
    for m in STOPS:
        Ss, mov = stop_at(S, m)
        for pi in PIS:
            V = wealth_V(Ss, mov, pi, sigma)
            for N in NS:
                W = fund_W(Ss, pi, N)
                out["D"][f"{m}|{pi}|{N}"] = np.nanmax(np.abs(W - V), axis=1).tolist()
    if b == 0:                                                 # quadrature accuracy of V on CHECK paths
        rng2 = np.random.default_rng(np.random.SeedSequence([seed[0], 99]))
        Sr = refine_bm(rng2, S[:CHECK]) if sigma == "one" else refine_bes3(rng2, X[:CHECK])
        for m in STOPS:
            Ss, mov = stop_at(S[:CHECK], m)
            Sr_s, mov_r = stop_at(Sr, m)
            for pi in PIS:
                V1 = wealth_V(Ss, mov, pi, sigma)
                V2 = wealth_V(Sr_s, mov_r, pi, sigma)[:, ::2]
                d = np.abs(V1 - V2)
                d = d[np.isfinite(d)]
                out["check"][f"{m}|{pi}"] = float(d.max()) if d.size else None
    return sigma, b, out


def qci(x, q):
    x = np.sort(x)
    n = x.size
    k = q * n
    h = 1.96 * np.sqrt(n * q * (1 - q))
    lo, hi = int(max(0, np.floor(k - h))), int(min(n - 1, np.ceil(k + h)))
    return [float(np.quantile(x, q)), float(x[lo]), float(x[hi])]


def stats(x):
    x = np.asarray(x, float)
    r = {"n": int(x.size)}
    if x.size == 0:
        return r
    for q in (0.5, 0.9, 0.99):
        r[f"q{int(q * 100)}"] = qci(x, q)
    for eta in ETAS:
        p = float(np.mean(x > eta))
        r[f"P>{eta}"] = [p, float(np.sqrt(p * (1 - p) / x.size))]
    return r


def main():
    root = np.random.SeedSequence(SEED)
    jobs = []
    for sigma, ss in zip(("one", "x2"), root.spawn(2)):
        jobs += [(sigma, b, s.generate_state(2).tolist()) for b, s in enumerate(ss.spawn(PATHS // BATCH))]
    with Pool(WORKERS) as pool:
        parts = pool.map(batch, jobs)
    res = {"F": F, "paths": PATHS, "workers": WORKERS, "cases": {}, "V_quadrature_check": {}}
    for sigma in ("one", "x2"):
        ps = [o for s, b, o in parts if s == sigma]
        hit = np.concatenate([np.array(o["hit"]) for o in ps])
        res["cases"][sigma] = {"hit_zero_before_T": int(hit.sum())}
        for key in ps[0]["D"]:
            D = np.concatenate([np.array(o["D"][key]) for o in ps])
            entry = {"all": stats(D)}
            if sigma == "one" and key.startswith("None|"):
                entry["hit"] = stats(D[hit])
                entry["no_hit"] = stats(D[~hit])
            res["cases"][sigma][key] = entry
        res["V_quadrature_check"][sigma] = next(o["check"] for s, b, o in parts if s == sigma and b == 0)
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(res, f, indent=1)
    rows = []
    for sigma in ("one", "x2"):
        for key, e in res["cases"][sigma].items():
            if "|" not in key:
                continue
            m, pi, N = key.split("|")
            for sub in ("all", "hit", "no_hit"):
                if sub in e and e[sub].get("n"):
                    s = e[sub]
                    rows.append([sigma, m, pi, N, sub, s["n"], s["q50"][0], s["q90"][0], s["q99"][0],
                                 s["P>0.01"][0], s["P>0.05"][0], s["P>0.2"][0]])
    with open(os.path.join(HERE, "summary.csv"), "w") as f:
        f.write("sigma,stop_m,pi,N,subset,n,median,q90,q99,P_gt_0.01,P_gt_0.05,P_gt_0.2\n")
        for r in rows:
            f.write(",".join(str(round(v, 6)) if isinstance(v, float) else str(v) for v in r) + "\n")
    print("done", len(rows), "hits", {s: res["cases"][s]["hit_zero_before_T"] for s in ("one", "x2")})
    print("V check", res["V_quadrature_check"])


if __name__ == "__main__":
    main()
