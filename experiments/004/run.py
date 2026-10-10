"""Experiment 004: reproduce the panel entries of [liu2022panel] Table 4.

    uv run python experiments/004/run.py
"""
import json
import os
import sys
from multiprocessing import Pool

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from panel import cluster, panel_tests, simulate  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
SEED = 20261008
REPS = 5000
CHUNK = 250
CV = 1.64
DGPS = {"DGP3": (0.5, 0.0), "DGP4": (0.5, 0.01)}
# Table 4, panel rows: (n, T) -> DGP -> (g1 t, g1 J, g2 t, g2 J)
PUB = {
    (32, 150): {"DGP3": (1.0, 1.0, 0.063, 0.070), "DGP4": (1.0, 1.0, 0.326, 0.166)},
    (32, 200): {"DGP3": (1.0, 1.0, 0.049, 0.051), "DGP4": (1.0, 1.0, 0.564, 0.278)},
    (32, 250): {"DGP3": (1.0, 1.0, 0.056, 0.052), "DGP4": (1.0, 1.0, 0.888, 0.611)},
    (48, 150): {"DGP3": (1.0, 1.0, 0.053, 0.058), "DGP4": (1.0, 1.0, 0.418, 0.238)},
    (48, 200): {"DGP3": (1.0, 1.0, 0.049, 0.054), "DGP4": (1.0, 1.0, 0.703, 0.425)},
    (48, 250): {"DGP3": (1.0, 1.0, 0.056, 0.063), "DGP4": (1.0, 1.0, 0.958, 0.828)},
    (64, 150): {"DGP3": (1.0, 1.0, 0.063, 0.061), "DGP4": (1.0, 1.0, 0.477, 0.295)},
    (64, 200): {"DGP3": (1.0, 1.0, 0.041, 0.049), "DGP4": (1.0, 1.0, 0.797, 0.562)},
    (64, 250): {"DGP3": (1.0, 1.0, 0.058, 0.057), "DGP4": (1.0, 1.0, 0.985, 0.914)},
}
LABELS = ("g1 t", "g1 J", "g2 t", "g2 J")


def chunk(job):
    dgp, n, T, seed = job
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    rows = []
    for _ in range(CHUNK):
        Y, g = simulate(rng, n, T, DGPS[dgp])
        lab = cluster(Y)
        o1 = panel_tests(Y, np.where(lab == 0)[0])
        o2 = panel_tests(Y, np.where(lab == 1)[0])
        rows.append([o1[0] > CV, o1[1] > CV, o2[0] > CV, o2[1] > CV, o1[3] > CV, o2[3] > CV, np.mean(lab != g)])
    return dgp, n, T, np.array(rows, dtype=float)


def tol(p):
    return 3 * np.sqrt(p * (1 - p) / REPS + p * (1 - p) / 1000) + 0.0005


def main():
    root = np.random.SeedSequence(SEED)
    cells = [(d, n, T) for (n, T) in PUB for d in DGPS]
    jobs = []
    for (d, n, T), ss in zip(cells, root.spawn(len(cells))):
        jobs += [(d, n, T, s.generate_state(4).tolist()) for s in ss.spawn(REPS // CHUNK)]
    with Pool() as pool:
        parts = pool.map(chunk, jobs)
    agg = {}
    for d, n, T, arr in parts:
        agg.setdefault((d, n, T), []).append(arr)

    res = {"reps": REPS, "cells": {}}
    n_ok = n_tot = 0
    n_ok_inv = 0
    print("| n | T | DGP | target | published | ours (as printed) | tol | reproduced | ours, t scale-invariant | reproduced |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for (n, T), pubs in PUB.items():
        for d in DGPS:
            a = np.concatenate(agg[(d, n, T)])
            rates = a[:, :4].mean(0)
            inv = {"g1 t": a[:, 4].mean(), "g2 t": a[:, 5].mean()}
            cell = {"clustering_error": float(a[:, 6].mean())}
            for k, lab in enumerate(LABELS):
                p, pub = float(rates[k]), pubs[d][k]
                ok = bool(abs(p - pub) <= tol(p))
                n_ok += ok
                n_tot += 1
                e = dict(published=pub, ours=round(p, 4), tol=round(float(tol(p)), 4), reproduced=ok)
                p_cmp = p
                if lab in inv:
                    pi = float(inv[lab])
                    e["ours_t_scale_invariant"] = round(pi, 4)
                    e["reproduced_t_scale_invariant"] = bool(abs(pi - pub) <= tol(pi))
                    p_cmp = pi
                n_ok_inv += bool(abs(p_cmp - pub) <= tol(p_cmp))
                cell[lab] = e
                print(f"| {n} | {T} | {d} | {lab} | {pub} | {p:.4f} | {tol(p):.4f} | {'yes' if ok else 'NO'} | "
                      f"{e.get('ours_t_scale_invariant', '')} | "
                      f"{'' if lab not in inv else ('yes' if e['reproduced_t_scale_invariant'] else 'NO')} |")
            res["cells"][f"n={n} T={T} {d}"] = cell
    res["reproduced_as_printed"] = f"{n_ok}/{n_tot}"
    res["reproduced_with_scale_invariant_t"] = f"{n_ok_inv}/{n_tot}"
    res["max_clustering_error"] = max(c["clustering_error"] for c in res["cells"].values())
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1)
    print("\nreproduced (as printed):", res["reproduced_as_printed"],
          "| with scale-invariant t:", res["reproduced_with_scale_invariant_t"],
          "| max clustering error:", res["max_clustering_error"])


if __name__ == "__main__":
    main()
