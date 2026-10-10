"""Deterministic integration witnesses for experiment 043; never runs a simulation.

Not a CI check: this reports the current run adapter's behavior, so a later
repair can change the report without preserving a known defect as a test.
Run with the repository's single-thread BLAS environment prefix.
"""
import importlib.util
import json
import math
from pathlib import Path
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("d28_run_input_witness", ROOT / "experiments/043/run.py")
run = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = run
spec.loader.exec_module(run)

# Enumerate the real run's seeds. No generated price path or model draw.
groups = {}
for cell, horizon, batch, seed, count, v1_count in run.jobs_for(run.SEED, run.BATCH, 0):
    if cell["type"] == "alternative":
        key = (cell["p"], cell["k"], horizon, batch)
        groups.setdefault(key, {})[cell["track"]] = tuple(seed)
unpaired = [key for key, seeds in groups.items() if len(set(seeds.values())) > 1]

# Feed a fixed nonfinite-price record to the public wrapper. The evaluator
# records its failure; a comparator should not receive the nonfinite path.
# A guard substitutes for the expensive comparator and records the call.
class NonfiniteComparatorInput(Exception):
    pass


seen = []

def guarded_comparator(prices, windows):
    finite = bool(np.isfinite(prices).all())
    seen.append(finite)
    if not finite:
        raise NonfiniteComparatorInput("nonfinite prices reached GSADF")
    return {window: (0., 0.) for window in windows}


prices = np.ones(run.TRAIN+4)
prices[-1] = math.inf
iv = np.full(len(prices)-1, .2)
saved = run.r021.psy.sadf_gsadf
wrapper_returned = False
try:
    run.r021.psy.sadf_gsadf = guarded_comparator
    run.score_path(prices, iv, False)
    wrapper_returned = True
except NonfiniteComparatorInput:
    pass
finally:
    run.r021.psy.sadf_gsadf = saved
evaluator_status = run.ev.evaluate(prices, iv, [run.DT]*len(iv), run.TRAIN, bands=run.BANDS)[-1]["status"]

# A near-threshold checkpoint followed by a resolved crossing. Detection by
# the later date is certain for the numeric rule, but its FIRST date is not.
threshold = -math.log(.05)
rows = [dict(index=run.TRAIN+2, status="ok", log_scores=(threshold,)*3),
        dict(index=run.TRAIN+7, status="ok", log_scores=(threshold+.01,)*3)]
cross = {str(a): run.ev.first_crossing(rows, a) for a in run.ALPHAS}
path = dict(status="ok", gsadf=None)
for bi in range(len(run.BANDS)):
    path[f"b{bi}"] = dict(final=threshold+.01, max=threshold+.01, cross=cross)
N = 8
summary = run.summarize({("fixed timing witness", N): [path]},
                        {run.TRAIN+N+1: {"gsadf": {"5%": 1.}}})
timing = summary[f"fixed timing witness|N={N}"][run.BAND_NAMES[0]]["0.05"]

print(json.dumps({
    "no_simulation_run": True,
    "absorption_groups": len(groups),
    "groups_with_different_tracking_seeds": len(unpaired),
    "first_group_seeds": {k: list(v) for k, v in next(iter(groups.values())).items()},
    "nonfinite_record": {"evaluator_status": evaluator_status,
                         "comparator_called_on_nonfinite": False in seen,
                         "wrapper_returned_with_guard": wrapper_returned},
    "timing_witness": {"unresolved_possible_first_delay": 2,
                       "resolved_crossing_delay": 7,
                       "reported": timing},
}, indent=2))
