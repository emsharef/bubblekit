"""Experiment 005: Obayashi-Protter-Yang Steps 6-8 and lifetime fit against the paper's stated estimates.

    uv run python experiments/005/run.py
"""
import json
import os
import sys
from multiprocessing import Pool

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from opy import (B_TABLE2, brute_force, gg_fit, gg_sample, lifetimes, path_logprob, profile_mle,  # noqa: E402
                 simulate_hmm, viterbi)

HERE = os.path.dirname(os.path.abspath(__file__))
SEED = 20261009
R = 200
STOCKS, DAYS = 500, 756
N_LIFE = 13060
WORKERS = max(1, (os.cpu_count() or 4) - 3)   # leave at least 3 cores free for Lean CI
GG = (5.2478868, 0.9016828, -0.2339065)


def hb_job(seed):
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    _, nu = simulate_hmm(rng, STOCKS, DAYS)
    return profile_mle(nu)


def hg_job(seed):
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    return gg_fit(gg_sample(rng, N_LIFE, *GG)).tolist()


def viterbi_check(rng, cases=500, T=12):
    worst, mismatches = 0.0, 0
    for _ in range(cases):
        b = (rng.uniform(0.5, 0.99), rng.uniform(0.01, 0.5))
        nu = rng.random(T) < rng.uniform(0.1, 0.9)
        hv = viterbi(nu, b)
        hb, lb = brute_force(nu, b)
        gap = lb - path_logprob(hv, nu, b)               # ties allowed: compare attained log-probabilities
        worst = max(worst, gap)
        mismatches += gap > 1e-9
    return mismatches, worst


def filter_checks():
    """Hand-worked Steps 7-8 cases: (prices, smoothed states with 0 = B) -> expected lifetimes and period kinds."""
    B, N = 0, 1
    cases = [
        # birth (+10%), N stretch, death (-10%): one bubble from day 1 to day 8 -> 8 days
        ([100, 100, 110, 110, 108, 107, 110, 105, 99, 99], [N, B, B, N, N, N, B, B, B, N], [8],
         ["birth", "death"]),
        # suppressed period (+2%) then nothing
        ([100, 100, 102, 102], [N, B, B, N], [], ["suppressed"]),
        # birth with no subsequent death: open at sample end, no lifetime
        ([100, 100, 106, 106], [N, B, B, N], [], ["birth"]),
        # death without a prior birth is ignored; a second birth while open is absorbed
        ([100, 90, 90, 100, 106, 106, 112, 112, 100], [B, B, N, B, B, N, B, B, B], [6],
         ["death", "birth", "death"]),
        ([100, 106, 106, 106, 113, 113, 113, 100], [B, B, N, B, B, N, B, B], [8], ["birth", "birth", "death"]),
    ]
    results = []
    for X, h, exp_life, exp_kinds in cases:
        life, kinds = lifetimes(np.array(X, float), np.array(h))
        results.append(dict(lifetimes=life, expected=exp_life, kinds=kinds, expected_kinds=exp_kinds,
                            ok=(life == exp_life and kinds == exp_kinds)))
    return results


def main():
    rng = np.random.default_rng(SEED)
    mism, worst = viterbi_check(rng)
    fchk = filter_checks()
    root = np.random.SeedSequence(SEED)
    sb, sg = root.spawn(2)
    with Pool(WORKERS) as pool:
        hb = np.array(pool.map(hb_job, [s.generate_state(4).tolist() for s in sb.spawn(R)]))
        hg = np.array(pool.map(hg_job, [s.generate_state(4).tolist() for s in sg.spawn(R)]))

    res = {"viterbi": {"cases": 500, "T": 12, "mismatches": int(mism), "max_logprob_gap": float(worst)},
           "filter_checks": fchk, "H_B": {}, "H_G": {}}
    for j, (name, pub) in enumerate(zip(("b11", "b21"), B_TABLE2)):
        m, sd = hb[:, j].mean(), hb[:, j].std(ddof=1)
        tol = 3 * sd / np.sqrt(R) + 0.0005
        res["H_B"][name] = dict(published=pub, mean=round(float(m), 5), sd=round(float(sd), 5), tol=round(float(tol), 5),
                                reproduced=bool(abs(m - pub) <= tol))
    for j, (name, pub) in enumerate(zip(("alpha", "sigma", "q"), GG)):
        m, sd = hg[:, j].mean(), hg[:, j].std(ddof=1)
        tol = 3 * sd / np.sqrt(R)
        res["H_G"][name] = dict(published=pub, mean=round(float(m), 5), sd=round(float(sd), 5), tol=round(float(tol), 5),
                                reproduced=bool(abs(m - pub) <= tol))
    res["all_filter_checks_ok"] = all(c["ok"] for c in fchk)
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1)

    print(f"Viterbi vs brute force: {mism} mismatches in 500 cases (max log-prob gap {worst:.1e})")
    print("Steps 7-8 hand cases:", ["ok" if c["ok"] else f"FAIL {c}" for c in fchk])
    print("\n| quantity | published | mean of R=200 estimates | MC SD per estimate | tol | reproduced |\n|---|---|---|---|---|---|")
    for blk in ("H_B", "H_G"):
        for k, e in res[blk].items():
            print(f"| {k} | {e['published']} | {e['mean']} | {e['sd']} | {e['tol']} | {'yes' if e['reproduced'] else 'NO'} |")


if __name__ == "__main__":
    main()
