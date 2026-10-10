"""Diagnostic for experiment 009 Deviations (added after the run): resolution sensitivity of Delta_N itself.

On the first 200 paths of batch 0 for each sigma (same seeds as run.py), Delta_N is computed at the fine resolution F
and at 2F (Brownian-bridge refinement of the same path) and the quantiles are compared, per subset.
    uv run python experiments/009/resolution_check.py
"""
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from conv import fund_W, refine_bes3, refine_bm, sim_bm, sim_inv_bes3, stop_at, wealth_V  # noqa: E402
from run import BATCH, CHECK, NS, PIS, SEED, STOPS  # noqa: E402


def deltas(S, m, pi, sigma):
    Ss, mov = stop_at(S, m)
    V = wealth_V(Ss, mov, pi, sigma)
    return {N: np.nanmax(np.abs(fund_W(Ss, pi, N) - V), axis=1) for N in NS}


def main():
    root = np.random.SeedSequence(SEED)
    out = {}
    for sigma, ss in zip(("one", "x2"), root.spawn(2)):
        seed = ss.spawn(1)[0].generate_state(2).tolist()           # batch 0's seed, as in run.py
        rng = np.random.default_rng(np.random.SeedSequence(seed))
        if sigma == "one":
            S = sim_bm(rng, BATCH)[:CHECK]
        else:
            S, X = sim_inv_bes3(rng, BATCH, return_X=True)
            S, X = S[:CHECK], X[:CHECK]
        rng2 = np.random.default_rng(np.random.SeedSequence([seed[0], 99]))
        Sr = refine_bm(rng2, S) if sigma == "one" else refine_bes3(rng2, X)
        hit = (S[:, -1] <= 0)
        for m in STOPS:
            for pi in PIS[:3]:
                d1, d2 = deltas(S, m, pi, sigma), deltas(Sr, m, pi, sigma)
                for N in NS:
                    for sub, mask in (("all", np.ones(CHECK, bool)), ("hit", hit), ("no_hit", ~hit)):
                        if sigma == "x2" and sub != "all" or not mask.any():
                            continue
                        a, b = d1[N][mask], d2[N][mask]
                        out[f"{sigma}|{m}|{pi}|{N}|{sub}"] = {
                            "n": int(mask.sum()), "median_F": float(np.median(a)), "median_2F": float(np.median(b)),
                            "q90_F": float(np.quantile(a, 0.9)), "q90_2F": float(np.quantile(b, 0.9)),
                            "median_abs_change": float(np.median(np.abs(a - b)))}
    with open(os.path.join(HERE, "resolution_check.json"), "w") as f:
        json.dump(out, f, indent=1)
    for k, v in out.items():
        if k.split("|")[3] in ("64", "1008"):
            print(k, v["n"], "med %.4f->%.4f q90 %.4f->%.4f |chg| %.4f" % (v["median_F"], v["median_2F"], v["q90_F"],
                                                                         v["q90_2F"], v["median_abs_change"]))


if __name__ == "__main__":
    main()
