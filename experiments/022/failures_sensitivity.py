"""Experiment 022, Deviation 4 (post hoc): recompute the numerical-failure records with a large-argument Bessel fix.

scipy.special.ive(nu, z) returns NaN for z of order 1e9 (e.g. nu = 0.5, z = 1.08e9). The registered run kept those
records as zero evidence (claim 054's contract). This script regenerates the affected cells from their seeds,
replaces log ive by its exact large-z asymptotic series where scipy fails, and reports how the failed records'
decisions would change. The primary (registered) results are not altered.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/022/failures_sensitivity.py
"""
import json
import os
import sys
from multiprocessing import Pool

import numpy as np
from scipy import special

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cev  # noqa: E402
import run as r022  # noqa: E402

_ive = special.ive


def ive_fixed(a, z):
    """ive with an exact asymptotic replacement where scipy returns NaN (large z); 4 terms of the series."""
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


def job(args):
    name, T, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    S = r022.simulate(name, rng, r022.BATCH, T)
    out = []
    for f, st in r022.FREQ.items():
        idx = r022.grid(T, st)
        Ss, times = S[:, idx], idx / r022.STEPS_YEAR
        eps, _, _ = r022.eps_for(times)
        special.ive = _ive
        base = cev.score(Ss, times, r022.ALPHAS, eps)
        failed = base["status"] == "numerical_failure"
        if not failed.any():
            continue
        special.ive = ive_fixed
        fixed = cev.score(Ss[failed], times, r022.ALPHAS, eps)
        special.ive = _ive
        for j, i in enumerate(np.flatnonzero(failed)):
            out.append({"cell": f"{name}|{T}|{f}", "fixed_status": str(fixed["status"][j]),
                        "S1_05": bool(fixed[0.05]["S1"][j]), "S3_05": bool(fixed[0.05]["S3"][j]),
                        "S1_10": bool(fixed[0.1]["S1"][j]), "S3_10": bool(fixed[0.1]["S3"][j]),
                        "logE": float(fixed["logE"][j])})
    return out


def main():
    res = json.load(open(os.path.join(HERE, "results.json")))
    affected = sorted({(k.split("|")[0], int(k.split("|")[1])) for k, c in res["cells"].items()
                       for f in r022.FREQ if c[f]["status_counts"].get("numerical_failure", 0)})
    affected = [(m, T) for m, T in affected if m in r022.MODELS]
    root = np.random.SeedSequence(r022.SEED)
    cells = [(m, T) for m in r022.MODELS for T in r022.HORIZONS]
    spawned = dict(zip(cells, root.spawn(len(cells))))
    jobs = [(m, T, s.generate_state(2).tolist()) for m, T in affected for s in spawned[(m, T)].spawn(r022.PATHS // r022.BATCH)]
    with Pool(r022.WORKERS) as pool:
        rows = [x for part in pool.map(job, jobs, chunksize=1) for x in part]
    summary = {}
    for x in rows:
        s = summary.setdefault(x["cell"], {"records": 0, "still_failed": 0, "S1_05": 0, "S3_05": 0, "S1_10": 0, "S3_10": 0})
        s["records"] += 1
        s["still_failed"] += x["fixed_status"] == "numerical_failure"
        for key in ("S1_05", "S3_05", "S1_10", "S3_10"):
            s[key] += x[key]
    with open(os.path.join(HERE, "failures_sensitivity.json"), "w") as fh:
        json.dump({"cells": summary, "records": len(rows)}, fh, indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
