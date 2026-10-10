"""Fixed confidence-set and failure-budget checks; no simulation or certificate."""
from fractions import Fraction as F
from itertools import product
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp
from declaration import declare, corrected_log_score

mp.dps = 70
ROOT = Path(__file__).resolve().parents[1]

def load(name, path):
    spec = spec_from_file_location(name, path)
    result = module_from_spec(spec)
    spec.loader.exec_module(result)
    return result

kernels = load('kernels058', ROOT/'d13-cev-input/kernels.py')
ebh = load('ebh058', ROOT/'053/procedure.py')

def normal_log(r, d, b, sigma):
    return mp.fsum(-mp.log(2*mp.pi*sigma*sigma*t)/2
                  -(x-(b-sigma*sigma/2)*t)**2/(2*sigma*sigma*t)
                  for x, t in zip(r, d))

fixtures = [(['-.15', '.2'], ['.5', '.5']),
            (['.001', '-.02', '.03'], ['.01', '.02', '.04']),
            (['-.4', '.1', '.2'], [1, 2, 3]),
            (['.01', '.010001'], [1, 1])]
containment = 0
for rr, dd in fixtures:
    r, d = tuple(map(mp.mpf, rr)), tuple(map(mp.mpf, dd))
    answers = [declare(r, d, delta) for delta in ('.01', '.1')]
    wide, narrow = (a['bounds'] for a in answers)
    assert wide[0] <= narrow[0] <= narrow[1] <= wide[1]
    assert wide[2] <= narrow[2] <= narrow[3] <= wide[3]
    for answer in answers:
        assert answer['mode'] == 'rectangle'
        lo, hi, slo, shi = answer['bounds']
        assert lo < hi and 0 < slo < shi
        # Each variance endpoint solves the unrestricted-mean profile equation.
        for variance in answer['variance']:
            free_b = answer['mean']+variance/2
            height = normal_log(r, d, free_b, mp.sqrt(variance))
            assert abs(height-answer['threshold']) < mp.mpf('1e-55')*(1+abs(height))
        # Compare the original likelihood region with its rectangular enclosure.
        for b, sigma in product(map(mp.mpf, ['-2', '-.2', '0', '.2', '2']),
                                map(mp.mpf, ['.01', '.1', '.3', '.7', '2'])):
            if normal_log(r, d, b, sigma) >= answer['threshold']:
                assert lo <= b <= hi and slo <= sigma <= shi
                containment += 1
        # Fixed q is always in its own 1/delta confidence set.
        assert lo <= 0 <= hi and slo <= mp.mpf('.3') <= shi
assert containment > 0
for r, d in (([0, 0], [1, 1]), (['.2', '.4'], [1, 2])):
    assert declare(r, d, '.01')['mode'] == 'unrestricted'
for args in (([0, 1], [1, 1], 0), ([0], [1], '.1'), ([0, 1], [0, 1], '.1')):
    try:
        declare(*args)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid declaration configuration accepted')

# Exact abstract good/bad-earlier-window fixtures: sharp cap normalization.
# These are probability arrays, not diffusion simulations.
for delta, cap in product((F(0), F(1,100), F(1,10), F(1,2)), (F(2), F(20), F(100))):
    law = [(1-delta, [(F(1,2), F(2)), (F(1,2), F(0))]),
           (delta, [(F(1), cap)])]
    mean = sum(pw*pv*min(e,cap) for pw, row in law for pv,e in row)
    assert mean == 1+(cap-1)*delta
    adjusted = mean/(1+(cap-1)*delta)
    assert adjusted == 1
    raw_flag = sum(pw*pv for pw,row in law for pv,e in row if e > 10)
    assert raw_flag <= F(1,10)+F(9,10)*delta
# Marginal validity does not become validity conditional on a bad W.
delta, cap = F(1,100), F(20)
bad_corrected = cap/(1+(cap-1)*delta)
assert bad_corrected > 10
assert len(ebh.ranked_discoveries([bad_corrected], F(1,10))) == 1
assert delta <= F(1,10)  # one-name unconditional FDR, conditional bad-W FDR=1
assert (1-delta)+delta*1000 > 1  # unbounded raw moment has no cap correction
close_score = mp.exp(corrected_log_score(mp.log(1000), 20, '.01'))
assert abs(close_score-mp.mpf(bad_corrected.numerator)/bad_corrected.denominator) < mp.mpf('1e-55')
assert corrected_log_score(-mp.inf, 20, '.01') == -mp.inf

# Concrete Gaussian/CEV counterexample: narrow declaration sigma=1/2,
# actual sigma=1, retained p=1 scale=1/2, fitted p=2 scale=1.
# A large training endpoint makes the alternative the training maximizer.
x = mp.exp(4)
assert kernels.log_transition(2,1,1,1,x) > kernels.log_transition(1,'.5',1,1,x)
weighted = []
for r in (8, 12, 16, 20):
    y = x*mp.exp(r)
    weighted.append(kernels.log_transition(2,1,1,x,y)
                    +kernels.log_transition(1,1,1,x,y)
                    -kernels.log_transition(1,'.5',1,x,y)+mp.log(y))
assert all(a < b for a,b in zip(weighted, weighted[1:]))
# The second difference converges to 2*(1/(2*.5^2)-1/2)*4^2 = 48.
assert abs(weighted[-1]-2*weighted[-2]+weighted[-3]-48) < mp.mpf('1e-8')
print(f'PASS: {containment} likelihood-set inclusions, variance roots and nested budgets; '
      'zero-residual fallback; exact cap/conditional-FDR fixtures; Gaussian/CEV tail obstruction. '
      'No simulations or performance estimates.')
