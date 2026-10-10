"""Experiment 029, supplementary to the registered spot checks: mathb's conservative reference-clock selector.

    uv run python experiments/029/certified_spotcheck.py      (writes experiments/029/certified_spotcheck.json)

Regenerates exactly the registered spot-check panels (the first panel of batch 0 in each cell, from the registered
seeds; no new simulation) and compares experiment 029's ordinary floating-point retained set with
`checks/d20-clock-certificate/certify.py`'s `select` on the same reference evaluation prices and the same
training-fixed forecast (equal weights 1/15, the fitted (b, w) per reference, as exact rationals of the float values).
This certifies the reference set only, not a target numerator, denominator or score.
"""
import importlib.util
import json
import math
import os
import sys
import time
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


r029 = _load("r029", "experiments/029/run.py")
cert = _load("clockcert", "checks/d20-clock-certificate/certify.py")


def lf(x):
    return None if x is None else float(x)


def main():
    root = np.random.SeedSequence(r029.SEED)
    out = []
    for ci, ss in enumerate(root.spawn(len(r029.CELLS))):
        seed = ss.spawn(r029.BATCHES)[0].generate_state(2).tolist()
        rng = np.random.default_rng(np.random.SeedSequence(seed))
        cell = r029.CELLS[ci]
        ref, _, _ = r029.simulate(cell, rng)
        ro = r029.reference_side(ref)
        prices = [[F(float(x)) for x in row[r029.NTR:]] for row in ref]
        dur = [F(float(x)) for x in r029.D[r029.NTR:]]
        clocks = [[F(float(x)) for x in c[r029.NTR:]] for c in r029.CLOCKS]
        cands = [(F(1, 15), c, [(F(float(ro["b"][a])), F(float(ro["w"][a]))) for a in range(r029.R)])
                 for c in range(15)]
        t0 = time.time()
        sel = cert.select(prices, dur, clocks, cands, F(1, 100000), calendar=0)
        sec = time.time() - t0
        ordinary = np.flatnonzero(ro["keep"]).tolist()
        excluded = [j for j in range(15) if j not in sel.retained]
        finite = [lf(sel.exclusion_margins[j]) for j in excluded]
        out.append({"cell": cell[0], "ordinary_retained": ordinary, "certified_retained": list(sel.retained),
                    "match": sorted(sel.retained) == ordinary,
                    "reasons": sorted(set(sel.reasons)), "min_exclusion_margin": min(finite) if finite else None, "excluded": excluded,
                    "ordinary_logq": ro["logq"], "certified_logq_bounds": [lf(x) for x in sel.log_forecast]
                    if sel.log_forecast else None, "seconds": sec})
        print(cell[0], "match", out[-1]["match"], "ordinary", ordinary, "certified", list(sel.retained),
              "min margin", out[-1]["min_exclusion_margin"], f"{sec:.1f}s", flush=True)
    with open(os.path.join(HERE, "certified_spotcheck.json"), "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
