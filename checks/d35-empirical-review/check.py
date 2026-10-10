"""Independent deterministic model checks and finite-law adapter checks.

No new fitted record, simulated path, experimental outcome or global optimizer.
Run with the repository's four numerical-library thread limits set to one.
"""
from fractions import Fraction as F
from itertools import combinations_with_replacement
import json
import math
from pathlib import Path

from calibrate import FitPair, flag, rank_cutoff, score_fit, score_window


def loglik_on_ray(returns, mu, nu, B, initial_x=0.0):
    """Independent log-domain calculation; baseline h=1 throughout."""
    constant = (math.lgamma((nu+1)/2)-math.lgamma(nu/2)
                - .5*math.log(math.pi*(nu-2)))
    x, total, slope = initial_x, 0.0, 0.0
    for r in returns:
        e = r-mu
        log_scale = -B*x
        if e == 0:
            correction = 0.0
        else:
            z = 2*math.log(abs(e))-2*log_scale-math.log(nu-2)
            correction = max(z, 0.0)+math.log1p(math.exp(-abs(z)))
        total += constant-log_scale-.5*(nu+1)*correction
        slope += x if x <= 0 or e == 0 else -nu*x
        x += r
    return total, slope


ray_cases = 0
for nu in (4, 6, 10):
    fixtures = [([.1, .2], .2, 0.0), ([.1, .2, .3], .2, 0.0),
                ([.01, .5, .2], .2, 0.0), ([-.1, .2, .3], .3, 0.0),
                ([.1, .2], .2, .4), ([.1, .2], .2, -.2)]
    for n in range(2, 9):
        record = [.01]*(n-2)+[10.0, .2]
        assert loglik_on_ray(record, .2, nu, 100)[1] > 0
        fixtures.append((record, .2, 0.0))
    for record, mu, x0 in fixtures:
        first, slope = loglik_on_ray(record, mu, nu, 10000, x0)
        second, _ = loglik_on_ray(record, mu, nu, 20000, x0)
        assert math.isclose(second-first, 10000*slope, rel_tol=1e-10, abs_tol=1e-8)
        ray_cases += 1
assert math.isclose(loglik_on_ray([.1,.2], .2, 6, 1)[1], .1)
assert math.isclose(loglik_on_ray([.1,.2,.3], .2, 6, 1)[1], -1.7)
assert math.isclose(loglik_on_ray([.01,.5,.2], .2, 6, 1)[1], .45)

# All invalid optima are retained below successful scores; never evaluate inf-inf.
failures = [None, FitPair(math.inf, math.inf), FitPair(-math.inf, 0),
            FitPair(0, math.inf), FitPair(math.nan, 1), FitPair(0, 1, False),
            FitPair(0, 1, True, False), FitPair(-1e308, 1e308)]
for fit in failures:
    result = score_fit(fit)
    assert result.value == -1 and result.signed_gap is None
finite = [score_fit(FitPair(10, 10+x)) for x in (-2, 0, .01, 1, 10)]
assert [s.signed_gap for s in finite][:2] == [-2, 0]
assert [s.value for s in finite] == sorted(s.value for s in finite)
assert finite[0].value == finite[1].value == 0

# Requested failures/missing checkpoints remain in the fixed list. An endpoint
# does not inherit an earlier failure that is outside its declared score map.
fits = {2: FitPair(math.inf, math.inf), 5: FitPair(0, 1)}
endpoint, ep_details = score_window(fits, [5])
maximum, details = score_window(fits, [2, 3, 5], mode="maximum")
assert endpoint == maximum == score_fit(fits[5]).value
assert list(details) == [2, 3, 5] and details[2].status == "nonfinite_fit"
assert details[3].status == "missing_fit" and list(ep_details) == [5]
assert score_window({}, [2, 5], mode="maximum")[0] == -1

# Exhaust exchangeable laws obtained by uniformly designating each member of a
# fixed multiset as test score; ties and failures are part of the population.
rank_cases = 0
for n in range(1, 6):
    for scores in combinations_with_replacement((-1.0, 0.0, .25, 1.0), n+1):
        for alpha in (F(1,20), F(1,n+1), F(1,2), F(3,4)):
            flags = 0
            for i, test in enumerate(scores):
                cal = scores[:i]+scores[i+1:]
                flags += flag(test, rank_cutoff(cal, alpha))
            assert F(flags, n+1) <= alpha
            rank_cases += 1
assert rank_cutoff([0.0]*18, F(1,20)) == math.inf
assert rank_cutoff([0.0]*19, F(1,20)) == 0
assert not flag(0, rank_cutoff([0.0]*19, F(1,20)))
assert flag(.25, rank_cutoff([0.0]*19, F(1,20)))
assert not flag(-1, rank_cutoff([-1.0]*19, F(1,20)))

# Recount archived oracle diagnostics only; no experiment or optimizer imported.
root = Path(__file__).resolve().parents[2]
records = json.loads((root/"experiments/049/results.json").read_text())["records"]
counts = {}
for group in ("positive", "negative", "universe"):
    subset = [r for r in records if r["group"] == group]
    assert subset and all(math.isfinite(r["oracle_b2"]) for r in subset)
    counts[group] = (sum(r["oracle_b2"] > math.log(20) for r in subset), len(subset))
subset = [r for r in records if r["group"] == "universe" and r["runup"]]
counts["run-ups"] = (sum(r["oracle_b2"] > math.log(20) for r in subset), len(subset))
print(f"PASS: {ray_cases} asymptotic ray checks; {rank_cases} exchangeable finite-law checks;")
print("retained failure, cutoff, tie and checkpoint checks.")
print("049 archive b2 gains > log(20), count/records (diagnostic only):", counts)
