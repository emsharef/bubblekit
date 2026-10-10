"""D19 bounded feasibility assessment (not an experiment) of math's adaptive evaluator.

Uses `checks/d19-adaptive-filter/certify.py` (reviewed claims 036/037 bounds, budgeted adaptive cover) on the same
throwaway cent-rounded hourly GBM records as `d19_adaptive_probe.py` (experiment 027's clocked simulator, seed 5,
records of 5, 20, 63 and 250 sessions drawn in that order, $50 start, narrow box, clocks {flat, U(1.5, 0.25)}).
Run from the repository root:

    uv run python experiments/data/d19_adaptive_eval_probe.py [max_sessions]

Prints, per record and setting: stop status (tolerance met, budget exhausted, resolution or arithmetic limit),
centre evaluations, transition terms, leaves, prunable leaves, failed leaves, largest M used, log lower, log upper,
log width and seconds. No score, power or runtime-at-scale claim follows from these rows.
"""
import importlib.util
import math
import os
import sys
import time
from fractions import Fraction as F

import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))


def load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


ad = load("adaptive_eval", "checks/d19-adaptive-filter/certify.py")
r027 = load("r027", "experiments/027/run.py")

BOX = (F("-0.2"), F("0.2"), F("0.04"), F("0.2025"))
SESSIONS = (5, 20, 63, 250)
# (factor, max_count, max_evaluations) per record length; factor 2 is math's benchmark tolerance (log 2 = 0.693 nats),
# factor e is the human's 1-nat target.
SETTINGS = {5: [(2, 64, 128), ("e", 64, 128)], 20: [(2, 64, 128), ("e", 64, 128)],
            63: [(2, 128, 256)], 250: [(2, 256, 128)]}
E_RAT = F(27182818284, 10 ** 10)          # a rational just below e


def lg(f):
    return math.log(f.numerator) - math.log(f.denominator) if f > 0 else float("-inf")


def records(max_sessions):
    rng = np.random.default_rng(5)
    for H in SESSIONS:
        S = r027.simulate(("G", "gbm", ("U", 1.5, 0.25), 0.0, 0.30, 0), rng, 1, H)
        if H > max_sessions:
            continue
        d5, v5 = r027.grid(H, ("U", 1.5, 0.25))
        hidx = r027.hourly_index(H)
        S, d, v = S[:, hidx][0], r027.coarsen(d5, hidx), r027.coarsen(v5, hidx)
        Z = [int(z) for z in np.rint(50 * S / 0.01)]
        gaps = [F(float(x)) for x in d]
        yield H, Z[1:], gaps, [gaps, [F(float(x)) for x in v]]


def main():
    max_sessions = int(sys.argv[1]) if len(sys.argv) > 1 else max(SESSIONS)
    for H, labels, gaps, clocks in records(max_sessions):
        N = len(labels)
        for factor, max_count, budget in SETTINGS[H]:
            t0 = time.time()
            res = ad.enclose(labels, gaps, clocks, F(1, 100), F(50), BOX, N // 2, count=4, max_count=max_count,
                             max_evaluations=budget, factor=(E_RAT if factor == "e" else factor))
            lo, hi = lg(res.lower), lg(res.upper)
            print(f"sessions {H} N {N} factor {factor} max_count {max_count} budget {budget}: {res.status}; "
                  f"evaluations {res.evaluations}, transition terms {res.transition_terms}, leaves {len(res.leaves)}, "
                  f"prunable {res.prunable}, failed {sum(l.failed for l in res.leaves)}, largest M "
                  f"{max(l.count for l in res.leaves)}; log lower {lo:.3f}, log upper {hi:.3f}, width {hi - lo:.3f} "
                  f"nats; {time.time() - t0:.1f}s", flush=True)


if __name__ == "__main__":
    main()
