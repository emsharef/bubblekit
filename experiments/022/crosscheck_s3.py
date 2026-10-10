"""Experiment 022, Deviation 3: S3 (claim 055 drift-robust score) against mathb's total adapter, numerical evidence only.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/022/crosscheck_s3.py      (after run.py; regenerates batch 0 from its seed)
"""
import importlib.util
import json
import os
import sys
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cev  # noqa: E402
import run as r022  # noqa: E402

drift_total = r022._load("drift055", "checks/d13-drift-total/total.py")
NPATHS = 5
FREQS = ("monthly", "weekly", "daily")


def job(args):
    name, T, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    S = r022.simulate(name, rng, r022.BATCH, T)
    out = []
    for tag, X in ([(name, S)] + [(rn, np.round(S / r022.TICK) * r022.TICK)
                                  for rn, base in r022.ROUNDED.items() if base == name]):
        for f in FREQS:
            idx = r022.grid(T, r022.FREQ[f])
            Ss, times = X[:NPATHS, idx], idx / r022.STEPS_YEAR
            eps, _, _ = r022.eps_for(times)
            mine = cev.score(Ss, times, r022.ALPHAS, eps)["logEd"]
            for i in range(NPATHS):
                rec = drift_total.score_total_path(cev.CATALOGUE, list(times), list(Ss[i]), (len(times) - 1) // 2)
                theirs = float(rec["log_e"])
                same_inf = (not np.isfinite(theirs)) and (not np.isfinite(mine[i])) and np.sign(theirs) == np.sign(mine[i])
                diff = 0.0 if same_inf else abs(theirs - mine[i])
                dec = [(theirs > -np.log(a)) == (mine[i] > -np.log(a)) for a in r022.ALPHAS]
                out.append({"cell": f"{tag}|{T}|{f}", "diff": diff, "decisions_agree": all(dec),
                            "status": list(rec["status"])})
    return out


def main():
    root = np.random.SeedSequence(r022.SEED)
    cells = [(m, T) for m in r022.MODELS for T in r022.HORIZONS]
    jobs = [(m, T, ss.spawn(r022.PATHS // r022.BATCH)[0].generate_state(2).tolist())
            for (m, T), ss in zip(cells, root.spawn(len(cells)))]
    with Pool(r022.WORKERS) as pool:
        rows = [x for part in pool.map(job, jobs, chunksize=1) for x in part]
    finite = [x["diff"] for x in rows if np.isfinite(x["diff"])]
    statuses = {}
    for x in rows:
        for s in x["status"]:
            statuses[s] = statuses.get(s, 0) + 1
    res = {"paths_checked": len(rows), "max_abs_diff_finite": max(finite) if finite else None,
           "infinite_diffs": sum(1 for x in rows if not np.isfinite(x["diff"])),
           "decision_mismatches": sum(1 for x in rows if not x["decisions_agree"]),
           "status_counts": statuses}
    with open(os.path.join(HERE, "crosscheck_s3.json"), "w") as fh:
        json.dump(res, fh, indent=1)
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
