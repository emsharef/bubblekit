"""Fixed deterministic checks, not simulations, proofs, or error certificates."""
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
from pathlib import Path
import math
import numpy as np
from scipy.optimize import minimize_scalar
from mpmath import mp


def load(name, path):
    spec = spec_from_file_location(name, path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


HERE = Path(__file__).resolve().parent
profile = load('check_profile056', HERE/'profile.py')
scoring = load('check_scoring056', HERE/'scoring.py')
unbounded = load('check_unbounded056', HERE.parent/'d13-drift-total/total.py')
mp.dps = 70


def close(a, b, tolerance=mp.mpf('1e-55')):
    assert a == b or abs(a-b) <= tolerance*(1+abs(a)+abs(b)), (a, b)


def direct(returns, durations, drift, variance):
    # Direct normal density, not the expanded residual formula.
    return mp.fsum(-mp.log(2*mp.pi*variance*d)/2
                  -(r-(drift-variance/2)*d)**2/(2*variance*d)
                  for r, d in zip(returns, durations))


fixtures = [
    (['-.25', '.25'], [1, 1], '-.2', '.2'),  # interior
    (['-.25', '.25'], [1, 1], '.1', '.2'),   # lower endpoint
    (['-.25', '.25'], [1, 1], '-.2', '-.1'), # upper endpoint
    (['-.25', '.25'], [1, 1], '.03125', '.03125'), # singleton at free optimum
    (['.3', '.6'], [1, 2], '-.2', '.2'),    # Q=0, rate outside
    (['-.4'], [1], '-.2', '.2'),            # n=1, finite supremum
    (['.07', '-.2', '.3'], ['.1', '.3', '.6'], '-.05', '.15'),
]
dominance = optimized = 0
for raw_r, raw_d, lo, hi in fixtures:
    r, d = tuple(map(mp.mpf, raw_r)), tuple(map(mp.mpf, raw_d))
    lo, hi = mp.mpf(lo), mp.mpf(hi)
    mean, residual, value = profile.profile_returns(r, d, lo, hi)
    assert mp.isfinite(value)
    for drift in (lo, (lo+hi)/2, hi):
        for variance in map(mp.mpf, ['.0001', '.01', '.1', '1', '10']):
            assert direct(r, d, drift, variance) <= value+mp.mpf('1e-55')
            dominance += 1
    # Independent 1-D search: for each w directly clamp the normal mean's
    # implied drift, evaluate raw normal log densities, optimize over log w.
    rf, df = np.array(list(map(float, r))), np.array(list(map(float, d)))
    def objective(log_w):
        w = math.exp(log_w)
        b = np.clip(rf.sum()/df.sum()+w/2, float(lo), float(hi))
        return float(np.sum(np.log(2*np.pi*w*df)/2+(rf-(b-w/2)*df)**2/(2*w*df)))
    grid = np.linspace(-35, 15, 1001)
    center = int(np.argmin([objective(t) for t in grid]))
    assert 0 < center < len(grid)-1
    result = minimize_scalar(objective, bounds=(grid[center-1], grid[center+1]), method='bounded',
                             options={'xatol': 1e-12})
    assert result.success
    close(value, -result.fun, mp.mpf('2e-10'))
    optimized += 1

for rate in ('-.2', '0', '.2'):
    rate = mp.mpf(rate)
    assert profile.profile_returns([rate, 2*rate], [1, 2], '-.2', '.2')[2] == mp.inf
assert profile.profile_returns(['.2'], [1], '.2', '.2')[2] == mp.inf
# Single-increment finite case must not inherit claim 055's automatic zero.
assert mp.isfinite(profile.profile_returns(['.2001'], [1], '-.2', '.2')[2])

r = tuple(map(mp.mpf, ['-.25', '.25']))
free = profile.gaussian.profile_returns(r, [1, 1])[2]
close(profile.profile_returns(r, [1, 1], '-.2', '.2')[2], free)
# Boundary optimum is exactly the free optimum at b=1/32.
close(profile.profile_returns(r, [1, 1], '.03125', '.03125')[2], free)
# Price Jacobian and mixed-support conventions.
times, prices = [0, 1, 2], [mp.mpf(1), mp.exp(r[0]), mp.exp(sum(r))]
close(profile.log_null_sup(times, prices, '-.2', '.2'), free-sum(mp.log(x) for x in prices[1:]))
assert profile.log_null_sup(times, [0, 0, 0], 0, 0) == 0
for path in ([0, 0, 1], [1, 0, 0], [1, 0, 1]):
    assert profile.log_null_sup(times, path, 0, 0) == -mp.inf

catalogue = [('.5', '.7'), (1, '.7'), ('1.5', '.7')]
times = [0, '.2', '.4', '.6', '.8']
arrays = 0
for tail in product((0, 1, 2), repeat=4):
    prices = (1,)+tail
    baseline = unbounded.score_total_path(catalogue, times, prices, 2)
    previous = baseline['raw_log_e']
    for width in ('0', '.05', '.2', '1'):
        width = mp.mpf(width)
        answer = scoring.score_total_path(catalogue, times, prices, 2, -width, width)
        assert 'numerical_failure' not in answer['status']
        assert baseline['log_e'] <= answer['log_e'] <= previous
        assert answer['fit'] == baseline['fit']
        assert answer['training'] == baseline['training']
        previous = answer['log_e']
    arrays += 1

for lower, upper in ((1, -1), (mp.nan, 1), (0, mp.inf)):
    try:
        scoring.score_total_path(catalogue, times, [1]*5, 2, lower, upper)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid drift configuration accepted')
for bad in (-1, mp.nan, mp.inf):
    answer = scoring.score_total_path(catalogue, times, [1, 1, bad, 1, 1], 2, '-.2', '.2')
    assert answer['log_e'] == -mp.inf and 'outside_domain' in answer['status']
original = scoring.profile.log_null_sup
try:
    for replacement in (lambda *args: mp.nan, lambda *args: (_ for _ in ()).throw(ArithmeticError('injected'))):
        scoring.profile.log_null_sup = replacement
        answer = scoring.score_total_path(catalogue, times, [1, 1, 1, 2, 1], 2, '-.2', '.2')
        assert answer['log_e'] == -mp.inf and 'numerical_failure' in answer['status']
finally:
    scoring.profile.log_null_sup = original

print(f'PASS: {optimized} independently optimized profiles; {dominance} direct density bounds; '
      f'{arrays} arrays with four nested intervals; endpoint, singleton, zero-residual, '
      'mixed-support, Jacobian and retained-failure checks. No simulations.')
