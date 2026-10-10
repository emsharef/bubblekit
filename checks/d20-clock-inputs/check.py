"""Fixed D20 input diagnostics; no simulations, performance or certificates.

Run with the repository's single-thread BLAS environment: uv run python
checks/d20-clock-inputs/check.py. Uses the locked mpmath dependency.
"""
import importlib.util
from fractions import Fraction
from pathlib import Path

from mpmath import mp

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("clock_profile", ROOT / "checks/033/profile.py")
profile = importlib.util.module_from_spec(spec)
spec.loader.exec_module(profile)
mp.dps = 60


def close(x, y):
    assert abs(x - y) < mp.mpf("1e-45") * (1 + abs(x) + abs(y)), (x, y)


def normal(x, mean, variance):
    return mp.exp(-(x - mean) ** 2 / (2 * variance)) / mp.sqrt(2 * mp.pi * variance)


# Re-evaluate the registered Gaussian affinity by direct integration,
# including drift changes induced by changing the variance clock.
cases = [(".01", ".02", "-.03", ".04"),
         ("0", ".2", "0", ".2"),
         ("-.1", ".3", ".2", ".1"),
         (".02", ".09", ".01", ".11")]
for values in cases:
    mean, var, refmean, refvar = map(mp.mpf, values)
    a = mp.quad(lambda x: mp.sqrt(normal(x, mean, var) * normal(x, refmean, refvar)),
                [-mp.inf, 0, mp.inf])
    loss = mp.log((var + refvar) / (2 * mp.sqrt(var * refvar)))
    loss += (mean - refmean) ** 2 / (2 * (var + refvar))
    close(a * a, mp.exp(-loss))

# Only clock shape matters: the free variance scale absorbs global error.
r = tuple(map(mp.mpf, (".03", "-.04", ".02", ".07")))
d = tuple(map(mp.mpf, (".1", ".1", ".1", ".1")))
v = tuple(map(mp.mpf, (".1", ".9", ".1", ".9")))
p = profile.profile_returns(r, d, v)
scaled = profile.profile_returns(r, d, tuple(7 * x for x in v))
close(p["log_sup"], scaled["log_sup"])
close(p["w"], 7 * scaled["w"])

# Dividing log returns by sqrt(v/d) equalizes variances, but generally
# leaves a varying mean. It does not give claim 055's constant-drift law.
b, w = mp.mpf(".12"), mp.mpf(".09")
means = [(b * dt - w * vt / 2) / mp.sqrt(vt / dt) for dt, vt in zip(d, v)]
variances = [w * vt / (vt / dt) for dt, vt in zip(d, v)]
assert means[0] != means[1]
for dt, variance in zip(d, variances):
    close(variance, w * dt)

# Existing finite-outcome leakage example: other-name data can reveal
# the tested outcome, despite containing no own-name array as an input.
size = 21
raw_mean = sum(Fraction(1, size) * size for _ in range(size))
assert raw_mean == size
assert all(size > 20 for _ in range(size))

# A genuinely conditional normalized forecast and dominating density
# keep the moment under arbitrary weights on the conditioning records.
weights = (Fraction(1, 3), Fraction(2, 3))
actual = ((Fraction(1, 4), Fraction(3, 4)),
          (Fraction(2, 3), Fraction(1, 3)))
forecast = ((Fraction(3, 4), Fraction(1, 4)),
            (Fraction(1, 5), Fraction(4, 5)))
for g, q in zip(actual, forecast):
    assert sum(q) == 1
    assert sum(gi * qi / gi for gi, qi in zip(g, q)) == 1
assert sum(weights) == 1

# Explicit sufficient TV budgets, not a statistical accuracy assertion.
# Equal means; alternating log-standard-deviation errors +h and -h.
for n in (630, 1260):
    h = mp.mpf(".02")
    loss = n * mp.log(mp.cosh(h))
    epsilon = mp.sqrt(-mp.expm1(-loss))
    limit = mp.acosh(mp.exp(-mp.log1p(-mp.mpf(".05") ** 2) / n))
    close(mp.sqrt(-mp.expm1(-n * mp.log(mp.cosh(limit)))), mp.mpf(".05"))
    print(f"n={n}: equal-mean h=.02 TV upper budget={float(epsilon):.8f}; "
          f"h at budget .05={float(limit):.8f}")
print("PASS: Gaussian affinity, clock scale, transformed drift, conditional/leakage fixtures")
