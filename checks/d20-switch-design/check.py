"""D20 fixed-path design diagnostics: no random draws or performance estimates.

Run with single-thread BLAS settings: uv run python checks/d20-switch-design/check.py.
The constructed paths are algebra fixtures, not labelled bubble realizations.
"""
import importlib.util
from fractions import Fraction
from pathlib import Path

from mpmath import mp

spec = importlib.util.spec_from_file_location(
    "clock067", Path(__file__).resolve().parents[1] / "067/clock.py")
clock = importlib.util.module_from_spec(spec)
spec.loader.exec_module(clock)
mp.dps = 70

n = 64
d = (mp.mpf(1) / 252,) * n
# Four equal blocks; normalize each clock to the same total variance time.
# All-high is the same normalized clock as all-low, so retain 15 patterns.
raw_clocks = tuple(tuple(d[j] * (9 if (index >> (3 - j // 16)) & 1 else 1)
                         for j in range(n)) for index in range(15))
clocks = tuple(tuple(x * mp.fsum(d) / mp.fsum(v) for x in v) for v in raw_clocks)
delta, cap = mp.mpf(".00001"), mp.mpf(10000)
b, w = mp.mpf(0), mp.mpf(".09")


def fixture(v, phase):
    return tuple(b * dt - w * step / 2
                 + (1 if (j + phase) % 2 else -1) * mp.sqrt(w * step)
                 for j, (dt, step) in enumerate(zip(d, v)))


def selected_set(truth):
    rows = tuple(fixture(clocks[truth], phase) for phase in range(4))
    candidates = tuple((mp.mpf(1) / len(clocks), k, ((b, w),) * len(rows))
                       for k in range(len(clocks)))
    profiles = clock.reference_profiles(rows, d, clocks)
    q = clock.reference_forecast(rows, d, clocks, candidates)
    return clock.retain(profiles, q, delta, 0)


penalty = mp.log1p((cap - 1) * delta)
for truth, target_shape in ((0, 5), (5, 10)):
    retained = selected_set(truth)
    assert truth in retained and 0 in retained
    assert target_shape not in retained
    target = fixture(clocks[target_shape], 0)
    profiles = tuple(clock.profile.profile_returns(target, d, v)["log_sup"] for v in clocks)
    full, selected = max(profiles), max(profiles[k] for k in retained)
    gain = full - selected
    assert gain > penalty
    print(f"reference clock={truth:04b}, target fixture={target_shape:04b}, "
          f"retained={[f'{k:04b}' for k in retained]}, "
          f"Gaussian log-denominator reduction={float(gain):.8f}")
    # If the retained finite CEV maximum dominates the full Gaussian profile,
    # the complete denominator gain vanishes. No CEV dominance is assumed here.
    g0 = full + 1
    assert max(g0, full) - max(g0, selected) == 0

# Shape ambiguity is removed before forming this catalogue: all-high and
# all-low would normalize to the same vector, so they are not two hypotheses.
all_high = tuple(9 * x for x in d)
normalized_high = tuple(x * mp.fsum(d) / mp.fsum(all_high) for x in all_high)
assert all(abs(x - y) < mp.mpf("1e-60") for x, y in zip(normalized_high, clocks[0]))
for v in clocks:
    assert abs(mp.fsum(v) - mp.fsum(d)) < mp.mpf("1e-60")
cost = Fraction(1) + (Fraction(10000) - 1) * Fraction(1, 100000)
assert cost == Fraction(109999, 100000)
ceiling = Fraction(10000) / cost
for names in (20, 100):
    assert ceiling > names / Fraction(1, 20)  # one-discovery e-BH threshold, q=.05
print(f"cap denominator={cost}; log penalty={float(penalty):.8f}; "
      f"safe ceiling={float(ceiling):.8f}")
print("PASS: possible Gaussian gain, CEV obstruction, shape ambiguity and cap thresholds; "
      "no power conclusion")
