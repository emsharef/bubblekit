"""Deterministic tests for claim 064, with independent likelihood integrals.

No simulated observations, fitted empirical parameters or power measurements.
"""
import math
from itertools import product

from mpmath import mp
from scipy.integrate import quad

from noise import bounds, diagnostic_score, edges, emission, emission_upper, fixed

mp.dps = 45
TOL = mp.mpf('1e-35')


def integrate_step(start, z, noise, mode, suffix=lambda x: 1.):
    """Independent standard-normal integration, not interval-max recursion."""
    tick, dt, drift, kappa = .01, .5, .02, .6
    lo, hi = max(0., tick * max(0., z - .5) - noise), tick * (z + .5) + noise
    if start == 0:
        weight = float(emission(0, tick, z, noise)) if mode == 'uniform' else float(lo == 0)
        return weight * suffix(0.)
    mu, sd = (drift - kappa * kappa / 2) * dt, kappa * math.sqrt(dt)
    def standard(x):
        return (math.log(x / start) - mu) / sd if x > 0 else -math.inf
    # Emission kinks and central normal mass, to avoid missed narrow peaks.
    price_cuts = [lo, hi] + [tick * max(0., z - .5) + s * noise for s in (-1, 1)] + [tick * (z + .5) + s * noise for s in (-1, 1)]
    cuts = sorted(set([standard(lo), standard(hi)] + [standard(x) for x in price_cuts if lo < x < hi]
                      + [t for t in (-8., -4., 0., 4., 8.) if standard(lo) < t < standard(hi)]))
    def integrand(t):
        x = start * math.exp(mu + sd * t)
        if mode == 'support':
            weight = 1.
        elif noise == 0:
            weight = 1.
        elif z == 0:
            weight = min(1., max(0., (tick / 2 - x + noise) / (2 * noise)))
        else:
            weight = max(0., min(noise, tick * (z + .5) - x) - max(-noise, tick * (z - .5) - x)) / (2 * noise)
        return math.exp(-t * t / 2) / math.sqrt(2 * math.pi) * weight * suffix(x)
    return sum(quad(integrand, a, b, epsabs=2e-10, epsrel=2e-9)[0] for a, b in zip(cuts, cuts[1:]))


suprema = 0
for noise, z in product(map(mp.mpf, ('.0025', '.005', '.01')), (0, 1, 2, 10)):
    grid = edges('.01', z, noise, 8)
    for lo, hi in zip(grid, grid[1:]):
        top = emission_upper((lo, hi), '.01', z, noise)
        assert 0 < top <= 1
        for j in range(9):
            x = lo + (hi - lo) * j / 8
            assert emission(x, '.01', z, noise) <= top + TOL
        suprema += 1
    # Conditional emission normalization retains both zero and positive labels.
    for x in map(mp.mpf, ('0', '.001', '.005', '.01', '.05')):
        assert abs(mp.fsum(emission(x, '.01', label, noise) for label in range(12)) - 1) < TOL

# Bounded errors need not have the independent-uniform likelihood. The support
# mode dominates the expanded latent-path event itself, without that assumption.
fixtures = ((0, .0025, 0, 1, .005), (0, .0049, 1, 0, .01),
            (1, .01, 1, 2, .005), (1, .006, 0, 0, .0025),
            (2, .02, 2, 1, .01))
for z0, start, z1, z2, noise in fixtures:
    results = {}
    for mode in ('support', 'uniform'):
        actual = integrate_step(start, z1, noise, mode,
                                lambda x: integrate_step(x, z2, noise, mode))
        values = bounds((z0, z1, z2), ('.5', '.5'), '.01', str(noise), '.02', '.6', 3, mode)
        assert actual > 0 and all(actual <= float(v) + 2e-8 for v in values)
        assert all(0 < b <= a <= 1 for a, b in zip(values, values[1:]))
        results[mode] = values
    assert all(u <= s + TOL for u, s in zip(results['uniform'], results['support']))

# a=0 is exactly the pre-existing ordinary-cell recursion, in either mode.
for labels in ((0, 1, 0), (1, 2, 1), (0, 0, 0)):
    original = fixed.bounds(labels, ('.5', '.2'), '.01', '.02', '.6', 2)
    for mode in ('support', 'uniform'):
        assert max(abs(a - b) for a, b in zip(original, bounds(labels, ('.5', '.2'), '.01', 0, '.02', '.6', 2, mode))) < TOL

# Trapped zero may produce positive quotes. For all-zero labels, the uniform
# likelihood at X0=0 attains the global emission maximum at every date.
assert emission(0, '.01', 1, '.01') == mp.mpf('.25')
for noise in ('.0025', '.005', '.01'):
    p0 = emission(0, '.01', 0, noise)
    for mode, exact in (('support', mp.mpf(1)), ('uniform', p0 ** 3)):
        values = bounds((0, 0, 0, 0), ('.5',) * 3, '.01', noise, '.02', '.6', 3, mode)
        assert max(abs(v - exact) for v in values) < TOL
# At a=tick/2 the adversarial bounded-error law can round zero to label 1,
# although a continuous uniform error does not put mass at that endpoint.
assert all(v == 1 for v in bounds((0, 1, 0, 1), ('.5',) * 3, '.01', '.005', '.02', '.6', 2))
assert emission(0, '.01', 1, '.005') == 0

# A normalized point-mass forecast demonstrates the cost of using the wrong
# contract: actual trapped zero with zero errors is bounded but not uniform.
wrong = bounds((0,) * 13, ('.5',) * 12, '.01', '.01', '.02', '.6', 0, 'uniform')[0]
assert abs(wrong - (mp.mpf(3) / 4) ** 12) < TOL
assert 4 ** 12 > 20 * 3 ** 12
assert 1 / wrong > 20

# Existing normalized numerator, finite-null maximization and unit invariance.
labels, gaps = (1, 2, 1), ('.5', '.2')
catalogue = (('.02', '.6'), ('0', '.4'))
forecast = ('.03', '.5')
for mode in ('support', 'uniform'):
    level = 2
    score = diagnostic_score(labels, gaps, '.01', '.005', catalogue, forecast, level, mode)
    denominator = max(bounds(labels, gaps, '.01', '.005', *pair, level, mode)[-1] for pair in catalogue)
    assert abs(score * denominator - fixed.forecast(labels, gaps, '.01', *forecast)) < TOL
    rescaled = diagnostic_score(labels, gaps, 1, '.5', catalogue, forecast, level, mode)
    assert abs(score - rescaled) < TOL
    finer = diagnostic_score(labels, gaps, '.01', '.005', catalogue, forecast, level + 1, mode)
    assert finer >= score - TOL

# One-step moment upper sum over a finite set, plus omitted forecast mass.
# Support mode uses expanded-event probabilities, which bound actual label
# masses but need not sum to one. This does not drop unobserved labels.
for mode in ('support', 'uniform'):
    subtotal, forecast_mass = 0., 0.
    for z in range(8):
        q = float(fixed.forecast((1, z), ('.5',), '.01', *forecast))
        d = float(bounds((1, z), ('.5',), '.01', '.005', '.02', '.6', 1, mode)[-1])
        actual = integrate_step(.01, z, .005, mode)
        subtotal += q * actual / d
        forecast_mass += q
    assert subtotal + (1 - forecast_mass) <= 1 + 1e-8

base = [(0, 1), ('.5',), '.01', '.005', '.02', '.6', 1, 'uniform']
invalid = {0: ((0, -1), (0, 1.5), (0,)), 1: ((0,), ()), 2: (0, -1),
           3: (-1, mp.inf), 4: (mp.nan,), 5: (0,), 6: (-1, 1.5), 7: ('iid-returns',)}
for index, choices in invalid.items():
    for value in choices:
        args = base.copy()
        args[index] = value
        try:
            bounds(*args)
        except ValueError:
            pass
        else:
            raise AssertionError(f'accepted invalid design at {index}')

print(f'PASS: {suprema} emission suprema; 10 independent two-step likelihood integrals; '
      'normalization, refinement, zero-radius recovery, zero-state noise, unit scaling, '
      'finite-null scores, tail-accounted one-step moments and invalid designs.')
print('Diagnostic arithmetic only; no certified score, simulated power or real-noise guarantee.')
