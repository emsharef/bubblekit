"""Experiment 036, supplementary: cross-check the run's own evaluator against math's checks/d22-predictable-forecast/compare.py.

    uv run python experiments/036/compare_check.py      (writes experiments/036/compare_check.json)

Regenerates the first path of batch 0 in the N-in and L-20 cells from the registered seeds (no new simulation), runs
compare.evaluate with the run's settings (max_count 32, max_evaluations 64, factor 2, count 4), and compares its lower
scores at the run's 20 checkpoints with the stored per-path scores in results.json, for both fitting modes.
"""
import json
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import importlib.util  # noqa: E402

spec = importlib.util.spec_from_file_location("r036", os.path.join(HERE, "run.py"))
r036 = importlib.util.module_from_spec(spec)
sys.modules["r036"] = r036
spec.loader.exec_module(r036)
from fractions import Fraction as F  # noqa: E402


def lg(f):
    return -math.inf if f == 0 else math.log(f.numerator) - math.log(f.denominator)


def main():
    cmp_ = r036._load("cmp_d22", "checks/d22-predictable-forecast/compare.py")
    fcm, _ = r036.mods()
    stored = json.load(open(os.path.join(HERE, "results.json")))
    root = np.random.SeedSequence(r036.SEED)
    out = []
    for cell, ss in zip(r036.CELLS, root.spawn(len(r036.CELLS))):
        if cell[0] not in ("N-in", "L-20"):
            continue
        seed = ss.spawn(r036.PATHS // r036.BATCH)[0].generate_state(2).tolist()
        rng = np.random.default_rng(np.random.SeedSequence(seed))
        idx, d5, v5, sess5, sess_h = r036.grids()
        d, v = r036.r027.coarsen(d5, idx), r036.r027.coarsen(v5, idx)
        gaps = tuple(F(float(x)) for x in d)
        vU = tuple(F(float(x)) for x in v)
        cat = [fcm.Candidate(p, F(k), clk) for clk in (gaps, vU) for p in r036.POWERS for k in r036.KAPPAS]
        train = int(np.searchsorted(sess_h, r036.TRAIN_S))
        checks = [int(np.searchsorted(sess_h, s, side="right")) for s in range(r036.TRAIN_S, r036.H)]
        S = r036.simulate(cell, rng, r036.BATCH)
        Z = [int(round(F(str(50.0 * x)) / r036.TICK)) for x in S[0, 1:]]
        rows = cmp_.evaluate(Z, gaps, (gaps, vU), r036.TICK, r036.START, r036.BOX, train, cat,
                             count=4, max_count=32, max_evaluations=64, factor=2)
        by = {r.prefix_length: r for r in rows}
        part = next(p for p in stored["parts"] if p["cell"] == cell[0] and p["b"] == 0)["paths"][0]
        diffs = {}
        for mode, attr in (("expanding", "adaptive_score_lower"), ("frozen", "frozen_score_lower")):
            mine = part["modes"][mode]["score"]
            theirs = [lg(getattr(by[t], attr)) for t in checks]
            diffs[mode] = max(abs(a - b) for a, b in zip(mine, theirs))
        den = max(abs(part["log_D_upper"][j] - lg(min(F(1), by[t].denominator_upper))) for j, t in enumerate(checks))
        out.append({"cell": cell[0], "max_abs_score_diff": diffs, "max_abs_log_denominator_diff": den,
                    "statuses_match": [by[t].status for t in checks] == part["den_status"]})
        print(out[-1], flush=True)
    with open(os.path.join(HERE, "compare_check.json"), "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
