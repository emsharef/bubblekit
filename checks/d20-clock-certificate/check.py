"""Fixed enclosure checks; no simulation, power estimate or fitted-law claim."""
from fractions import Fraction as F
import importlib.util
from pathlib import Path
from unittest.mock import patch

from flint import ctx
from mpmath import mp

import certify

_spec = importlib.util.spec_from_file_location(
    "diagnostic067", Path(__file__).resolve().parents[1] / "067/clock.py")
diagnostic = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(diagnostic)
mp.dps = 160


def m(x):
    x = F(x)
    return mp.mpf(x.numerator) / x.denominator


def enclosed(x, pair):
    assert pair is not None and m(pair[0]) <= x <= m(pair[1]), (x, pair)


# Exact endpoint comparisons: strict exclusion, equality, overlapping balls,
# unresolved profiles and unconditional calendar retention.
result = certify.decide((F(2), F(2)), [(F(0), F(0))]*3 + [None],
                        (F(-1), F(-1)), 0)
assert result.retained == (0, 3)
assert all(result.exclusion_margins[j] > 0 for j in (1, 2))
assert certify.decide((F(1), F(1)), [(F(0), F(0))]*2,
                      (F(-1), F(-1)), 0).retained == (0, 1)
assert certify.decide((F(0), F(3)), [(F(0), F(0))]*2,
                      (F(-1), F(-1)), 0).retained == (0, 1)

n = 64
gaps = (F(1, 252),) * n
raw = [tuple(gaps[j] * (9 if (k >> (3-j//16)) & 1 else 1)
             for j in range(n)) for k in range(15)]
clocks = tuple(tuple(x*sum(gaps)/sum(v) for x in v) for v in raw)
params = ((F(0), F(9, 100)),) * 4
candidates = tuple((F(1, 15), k, params) for k in range(15))
delta = F(1, 100000)
for truth in (0, 5):
    # Round a deterministic algebra fixture to 90 decimal significant digits.
    # Those decimal rationals ARE the exact observations for this check.
    prices = []
    for phase in range(4):
        current, row = mp.mpf(1), [F(1)]
        for j, v in enumerate(clocks[truth]):
            increment = -m(F(9, 100)*v)/2 + (-1 if (j+phase)%2 == 0 else 1)*mp.sqrt(m(F(9, 100)*v))
            current *= mp.exp(increment)
            row.append(F(mp.nstr(current, 90)))
        prices.append(tuple(row))
    result = certify.select(prices, gaps, clocks, candidates, delta, bits=256)
    rows = tuple(tuple(mp.log(m(b)/m(a)) for a, b in zip(y, y[1:])) for y in prices)
    dd = tuple(map(m, gaps))
    vv = tuple(tuple(map(m, v)) for v in clocks)
    cc = tuple((m(weight), k, tuple((m(b), m(w)) for b, w in pp))
               for weight, k, pp in candidates)
    logq = diagnostic.reference_forecast(rows, dd, vv, cc)
    logds = diagnostic.reference_profiles(rows, dd, vv)
    enclosed(logq, result.log_forecast)
    for x, interval in zip(logds, result.log_profiles):
        enclosed(x, interval)
    exact_diagnostic = diagnostic.retain(logds, logq, m(delta), 0)
    assert set(exact_diagnostic) <= set(result.retained)
    assert result.retained == ((0,) if truth == 0 else (0, 5))
    for j in set(range(15)) - set(result.retained):
        assert result.exclusion_margins[j] > 0
        assert logq + mp.log(m(delta)) > logds[j]
    # Multiplying each peer's entire price path by its own positive constant
    # leaves every exact return, and therefore the certificate, unchanged.
    scaled = [tuple((a+2)*y for y in row) for a, row in enumerate(prices)]
    assert certify.select(scaled, gaps, clocks, candidates, delta, bits=256) == result
    print(f"truth fixture={truth:04b}: certified retained={result.retained}")

simple_clocks = ((F(1),)*3, (F(1), F(9), F(1)))
simple_candidates = ((F(1), 0, ((F(0), F(1)),)),)
exact_singular = ((F(1), F(2), F(4), F(8)),)
assert certify.select(exact_singular, simple_clocks[0], simple_clocks,
                      simple_candidates, delta).log_profiles == (None, None)
near_singular = ((F(1), F(2), F(4)+F(1, 10**50), F(8)),)
low = certify.select(near_singular, simple_clocks[0], simple_clocks,
                     simple_candidates, delta, bits=64)
high = certify.select(near_singular, simple_clocks[0], simple_clocks,
                      simple_candidates, delta, bits=512)
assert low.log_profiles == (None, None) and low.retained == (0, 1)
assert all(x is not None for x in high.log_profiles)
single = certify.select(((1, 2),), (1,), ((1,), (9,)), simple_candidates, delta)
assert single.retained == (0, 1) and single.log_profiles == (None, None)

for bad in (None, (), ((1, 2),), ((1, 2, 0, 8),), ((1, 2, "nan", 8),), ((1, 2, -4, 8),)):
    result = certify.select(bad, simple_clocks[0], simple_clocks, simple_candidates, delta)
    assert result.retained == (0, 1) and result.log_forecast is None
with patch.object(certify, "log_density", side_effect=ArithmeticError("forced failure")):
    assert certify.select(exact_singular, simple_clocks[0], simple_clocks,
                          simple_candidates, delta).retained == (0, 1)
with patch.object(certify, "log_profile", side_effect=ArithmeticError("forced failure")):
    assert certify.select(exact_singular, simple_clocks[0], simple_clocks,
                          simple_candidates, delta).retained == (0, 1)

# Design failures must not be silently mistaken for statistical nonrejections.
for change in ({"delta": 1}, {"calendar": 1}, {"bits": 0},
               {"candidates": ((F(1, 2), 0, ((0, 1),)),)}):
    kwargs = dict(prices=exact_singular, durations=simple_clocks[0], clocks=simple_clocks,
                  candidates=simple_candidates, delta=delta)
    kwargs.update(change)
    try:
        certify.select(**kwargs)
    except ValueError:
        pass
    else:
        raise AssertionError("invalid design accepted")
assert ctx.prec == 53
print("PASS: strict/equality comparisons, independent high-precision enclosures, "
      "nontrivial exclusions, price scaling, singular/near-singular and failure retention")
