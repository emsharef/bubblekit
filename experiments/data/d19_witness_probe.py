"""D19 feasibility probe (not an experiment): math's adaptive evaluator with and without certified search witnesses.

Answers math's note `2026-10-07-d19-certified-witnesses.md`. Same throwaway records and settings as
`d19_adaptive_eval_probe.py` (seed 5; 5, 20, 63, 250 sessions; narrow box; clocks {flat, U(1.5, 0.25)}; factor 2).
Runs the evaluator with cache_bounds=False, the pathwise mode in which the retained output was produced (before the
allowance cache existed). Run from the repository root:

    uv run python experiments/data/d19_witness_probe.py [max_sessions]

Per record:
1. Plain numerical search: `d19_adaptive_probe.numerical_max` (float64 midpoint filter, M = 32, L-BFGS-B from 5
   starts per clock). Only the parameter location (clock, b, w) is passed on, as decimal strings; its value is not.
2. Unseeded: `enclose` exactly as in `d19_adaptive_eval_probe.py`.
3. Seeded: the same call plus one witness at the search location with integration count M = max_count. The
   evaluator re-evaluates the point with outward bounds; only its certified lower endpoint can seed pruning.
Printed separately: search seconds; witness work (evaluations, transition terms M + (N - 1) M^2, certified log lower,
failed flag); cover work (the remaining evaluations and terms); final status, log width, prunable leaves and seconds.
"""
import importlib.util
import math
import os
import sys
import time
from fractions import Fraction as F

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))


def load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


ev = load("adaptive_eval_probe", "experiments/data/d19_adaptive_eval_probe.py")
search = load("adaptive_probe", "experiments/data/d19_adaptive_probe.py")
ad = ev.ad


def lg(f):
    return math.log(f.numerator) - math.log(f.denominator) if f > 0 else float("-inf")


def run(labels, gaps, clocks, N, max_count, budget, witnesses):
    t0 = time.time()
    res = ad.enclose(labels, gaps, clocks, F(1, 100), F(50), ev.BOX, N // 2, count=4, max_count=max_count,
                     max_evaluations=budget, factor=2, witnesses=witnesses,
                     cache_bounds=False)                      # the pre-cache pathwise mode of the retained output
    return res, time.time() - t0


def main():
    max_sessions = int(sys.argv[1]) if len(sys.argv) > 1 else max(ev.SESSIONS)
    for H, labels, gaps, clocks in ev.records(max_sessions):
        N = len(labels)
        _, max_count, budget = ev.SETTINGS[H][0]
        t0 = time.time()
        num, (ci, b, w) = search.numerical_max(labels, gaps, clocks, N // 2)
        t_search = time.time() - t0
        bs, ws = f"{b:.12g}", f"{w:.12g}"
        print(f"sessions {H} N {N}: plain search {t_search:.1f}s, value {num:.3f} (uncertified, not passed on) at "
              f"clock {ci} b {bs} w {ws}", flush=True)
        for label, wit in (("unseeded", ()), ("seeded", ((ci, bs, ws, max_count),))):
            res, sec = run(labels, gaps, clocks, N, max_count, budget, wit)
            wterms = sum(m + (N - 1) * m * m for _, _, _, m in wit)
            wl = res.witnesses
            wtxt = ("none" if not wit else
                    f"{len(wit)} point(s), {wterms} terms, certified log lower "
                    f"{lg(wl[0].lower) if wl else float('nan'):.3f}, failed {sum(x.failed for x in wl)}")
            lo, hi = lg(res.lower), lg(res.upper)
            print(f"  {label}: witness work {wtxt}; cover evaluations {res.evaluations - len(wit)}, cover terms "
                  f"{res.transition_terms - wterms}; {res.status}; leaves {len(res.leaves)}, prunable {res.prunable}, "
                  f"failed leaves {sum(l.failed for l in res.leaves)}, largest M {max(l.count for l in res.leaves)}; "
                  f"log lower {lo:.3f}, log upper {hi:.3f}, width {hi - lo:.3f} nats; {sec:.1f}s", flush=True)


if __name__ == "__main__":
    main()
