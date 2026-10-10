"""Deterministic profile/domain checks; not simulations or certificates."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from itertools import product
import math
import numpy as np
from scipy.optimize import minimize_scalar
from mpmath import mp


def load(name, path):
    spec = spec_from_file_location(name, path)
    result = module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


HERE = Path(__file__).resolve().parent
profile = load('test_profile057', HERE/'profile.py')
scoring = load('test_scoring057', HERE/'scoring.py')
bounded = load('test_bounded057', HERE.parent/'056/scoring.py')
mp.dps = 70


def close(a, b, tol=mp.mpf('1e-55')):
    assert a == b or abs(a-b) <= tol*(1+abs(a)+abs(b)), (a, b)


def direct(r, d, b, w):
    return mp.fsum(-mp.log(2*mp.pi*w*t)/2-(x-(b-w/2)*t)**2/(2*w*t)
                  for x, t in zip(r, d))


fixtures = [
    (['-.25', '.25'], [1, 1], ['-.2', '.2', '.2', '.4']), # interior
    (['-.25', '.25'], [1, 1], ['.1', '.2', '.1', '.5']),  # lower drift
    (['-.25', '.25'], [1, 1], ['-.2', '-.1', '.1', '.5']), # upper drift
    (['-.25', '.25'], [1, 1], [-1, 1, '.3', '.5']),       # lower scale
    (['-.25', '.25'], [1, 1], [-1, 1, '.1', '.2']),       # upper scale
    (['-.25', '.25'], [1, 1], ['.5', '.7', '.01', '.05']),
    (['-.25', '.25'], [1, 1], ['-.7', '-.5', '.01', '.05']),
    (['-.25', '.25'], [1, 1], ['-.2', '0', 2, 3]),
    ([0, 0], [1, 1], ['.1', '.2', '.4', '.5']),
    ([0, 0], [1, 1], ['-.2', '.2', '.2', '.4']),          # old infinite profile
    (['.3', '.6'], [1, 2], ['-.2', '.2', '.1', '.5']),    # Q=0 outside B
    (['.2'], [1], ['.2', '.2', '.3', '.3']),             # singleton both, n=1
    (['-.25', '.25'], [1, 1], ['.03125', '.03125', '.25', '.25']),
    (['.02', '-.1', '.15'], ['.1', '.2', '.7'], ['-.2', '.3', '.3', '.3']),
    (['.02', '-.1', '.15'], ['.1', '.2', '.7'], ['.1', '.1', '.1', '1']),
]
comparisons = 0
for rr, dd, bb in fixtures:
    r, d, bounds = tuple(map(mp.mpf, rr)), tuple(map(mp.mpf, dd)), tuple(map(mp.mpf, bb))
    lo, hi, slo, shi = bounds
    _, _, exact = profile.profile_returns(r, d, *bounds)
    assert mp.isfinite(exact)
    for b in (lo, (lo+hi)/2, hi):
        for sigma in (slo, (slo+shi)/2, shi):
            assert direct(r, d, b, sigma*sigma) <= exact+mp.mpf('1e-55')
            comparisons += 1
    # Independent raw-density search, eliminating b by direct clamping at
    # each variance. Endpoints are explicitly included in this comparator.
    rf, df = np.array(list(map(float, r))), np.array(list(map(float, d)))
    def objective(log_w):
        w = math.exp(log_w)
        b = np.clip(rf.sum()/df.sum()+w/2, float(lo), float(hi))
        return float(np.sum(np.log(2*np.pi*w*df)/2+(rf-(b-w/2)*df)**2/(2*w*df)))
    left, right = math.log(float(slo*slo)), math.log(float(shi*shi))
    grid = np.linspace(left, right, 301)
    values = [objective(z) for z in grid]
    best = min(values)
    j = int(np.argmin(values))
    if left < right:
        result = minimize_scalar(objective, method='bounded',
                                 bounds=(grid[max(0,j-1)], grid[min(300,j+1)]),
                                 options={'xatol': 1e-13})
        assert result.success
        best = min(best, result.fun)
    close(exact, -best, mp.mpf('2e-10'))

# Exact stationarity cases ensure every edge and each corner is reachable.
r, d = list(map(mp.mpf, ['-.25', '.25'])), [mp.mpf(1)]*2
for bounds, expected in [
    ([-1, 1, '.2', '.4'], (mp.mpf(1)/32, mp.mpf(1)/16)),
    ([-1, 1, '.3', '.5'], (mp.mpf('.09')/2, mp.mpf('.09'))),
    ([-1, 1, '.1', '.2'], (mp.mpf('.04')/2, mp.mpf('.04'))),
    (['.5', '.7', '.01', '.05'], (mp.mpf('.5'), mp.mpf('.05')**2)),
    (['-.7', '-.5', '.01', '.05'], (mp.mpf('-.5'), mp.mpf('.05')**2)),
    (['-.2', 0, 2, 3], (mp.mpf(0), mp.mpf(4))),
]:
    close(profile.profile_returns(r, d, *bounds)[2], direct(r, d, *expected))
close(profile.profile_returns([0, 0], d, '.1', '.2', '.4', '.5')[2],
      direct([0, 0], d, mp.mpf('.1'), mp.mpf('.16')))
# Zero residual now finite even at an in-bound drift; singleton equals density.
assert mp.isfinite(profile.profile_returns([0], [1], 0, 0, '.2', '.4')[2])
close(profile.profile_returns([mp.mpf('.2')], [1], '.2', '.2', '.3', '.3')[2],
      direct([mp.mpf('.2')], [1], mp.mpf('.2'), mp.mpf('.09')))
# Price Jacobian and mixed support.
prices = [mp.mpf(1), mp.exp(r[0]), mp.exp(sum(r))]
close(profile.log_null_sup([0, 1, 2], prices, -1, 1, '.2', '.4'),
      profile.profile_returns(r, d, -1, 1, '.2', '.4')[2]-sum(mp.log(x) for x in prices[1:]))
assert profile.log_null_sup([0, 1], [0, 0], -1, 1, '.2', '.4') == 0
for prices in ([0, 1], [1, 0]):
    assert profile.log_null_sup([0, 1], prices, -1, 1, '.2', '.4') == -mp.inf

cat = [('.5', '.7'), (1, '.7'), ('1.5', '.7')]
times = [0, '.2', '.4', '.6', '.8']
count = 0
for tail in product((0, 1, 2), repeat=4):
    prices = (1,)+tail
    base = bounded.score_total_path(cat, times, prices, 2, '-.2', '.2')
    previous = base['raw_log_e']
    for slo, shi in (('.3', '.3'), ('.2', '.4'), ('.1', '1')):
        answer = scoring.score_total_path(cat, times, prices, 2, '-.2', '.2', slo, shi)
        assert 'numerical_failure' not in answer['status']
        assert base['log_e'] <= answer['log_e'] <= previous
        assert answer['training'] == base['training'] and answer['fit'] == base['fit']
        previous = answer['log_e']
    count += 1
# Invalid scale configuration is never turned into an ordinary data failure.
for slo, shi in ((0, 1), (-1, 1), (2, 1), (1, mp.inf), (mp.nan, 1)):
    try:
        scoring.score_total_path(cat, times, [1]*5, 2, '-.2', '.2', slo, shi)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid scale bounds accepted')
for bad in (-1, mp.nan, mp.inf):
    result = scoring.score_total_path(cat, times, [1, 1, bad, 1, 1], 2, '-.2', '.2', '.2', '.4')
    assert result['log_e'] == -mp.inf and 'outside_domain' in result['status']
original = scoring.profile.log_null_sup
try:
    for replacement in (lambda *args: mp.inf, lambda *args: mp.nan,
                        lambda *args: (_ for _ in ()).throw(ArithmeticError('injected'))):
        scoring.profile.log_null_sup = replacement
        result = scoring.score_total_path(cat, times, [1, 1, 1, 2, 1], 2, '-.2', '.2', '.2', '.4')
        assert result['log_e'] == -mp.inf and 'numerical_failure' in result['status']
finally:
    scoring.profile.log_null_sup = original
print(f'PASS: {len(fixtures)} independent optimizations, {comparisons} density bounds, '
      f'{count} arrays with nested scale intervals; all edges/corners, singleton, '
      'zero-residual, Jacobian, mixed-domain and retained-failure checks. No simulations.')
