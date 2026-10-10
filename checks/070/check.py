"""Deterministic checks for claim 070; no simulation or statistical proof."""
import importlib.util
import itertools
import math
from pathlib import Path

import numpy as np
from mpmath import mp
from scipy.optimize import minimize
from profile import clock, profile_joint

mp.dps = 65
ROOT = Path(__file__).resolve().parents[2]
def module(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT/path)
    obj = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj
free = module('free069', 'checks/069/profile.py')
experiment = module('experiment037', 'experiments/037/run.py')
def near(x, y, tol=mp.mpf('1e-50')):
    assert abs(x-y) < tol, (x, y)
def flat(rows):
    return tuple(x for row in rows for x in row)

r = [('.03', '-.02', '.01'), ('-.01', '.07'), ('.02', '-.04', '.05')]
delta = [('.01', '.02', '.01'), ('.03', '.01'), ('.02', '.01', '.02')]
u = [('.02', '.01', '.03'), ('.01', '.02'), ('.03', '.04', '.01')]
fits = [profile_joint(r, delta, u, k) for k in range(3)]
near(fits[0]['log_sup'], clock.profile_returns(flat(r), flat(delta), flat(u))['log_sup'])
near(fits[-1]['log_sup'], sum(clock.profile_returns(a,b,c)['log_sup'] for a,b,c in zip(r,delta,u)))
for budget, fit in enumerate(fits):
    brute = []
    for k in range(budget+1):
        for cuts in itertools.combinations(range(1, 3), k):
            edges = (0,)+cuts+(3,)
            value = mp.mpf(0)
            for a,b in zip(edges, edges[1:]):
                rr, dd, uu = map(lambda z: flat(z[a:b]), (r, delta, u))
                p = clock.profile_returns(rr, dd, uu)
                value += p['log_sup']
                # Direct raw Gaussian log density, independent of Q,K,H formula.
                def neg(th):
                    drift, logw = th
                    w = math.exp(logw)
                    return sum((float(x)-drift*float(t)+w*float(v)/2)**2/(2*w*float(v))
                               + .5*math.log(2*math.pi*w*float(v)) for x,t,v in zip(rr,dd,uu))
                opt = minimize(neg, [0., -3.], method='Nelder-Mead',
                               options={'maxiter':10000, 'xatol':1e-11, 'fatol':1e-12})
                assert opt.success
                assert abs(-opt.fun-float(p['log_sup'])) < 1e-9
            brute.append(value)
    near(max(brute), fit['log_sup'])
    assert fit['log_sup'] <= free.profile_switches(r, delta, u, budget)['log_sup']+mp.mpf('1e-50')
    scaled = [[3*mp.mpf(x) for x in row] for row in u]
    near(profile_joint(r, delta, scaled, budget)['log_sup'], fit['log_sup'])
assert fits[0]['log_sup'] < fits[1]['log_sup'] < fits[2]['log_sup']

# Calendar drift-cost identity: concatenation includes between-day residual.
rr = list(map(clock.vector, r)); dd = list(map(clock.vector, delta))
qdays = [clock.profile_returns(a,b,b)['Q'] for a,b in zip(rr,dd)]
means = [sum(a)/sum(b) for a,b in zip(rr,dd)]
mean = sum(flat(rr))/sum(flat(dd))
qpool = sum(qdays)+sum(sum(b)*(m-mean)**2 for b,m in zip(dd,means))
near(qpool, clock.profile_returns(flat(rr),flat(dd),flat(dd))['Q'])
loss = free.profile_switches(r,delta,delta,0)['log_sup']-profile_joint(r,delta,delta,0)['log_sup']
near(loss, len(flat(r))/2*mp.log(qpool/sum(qdays)))

# A middle singular day requires two cuts, an edge day only one.
gaps = [(1,1)]*3
for rec, first_bad in [([(1,2),(3,3),(4,5)],2), ([(1,1),(2,3),(4,5)],1)]:
    for k in range(3):
        value = profile_joint(rec,gaps,gaps,k)['log_sup']
        assert (value == mp.inf) == (k >= first_bad)
# Every day singular does NOT make a pooled segment singular when slopes differ.
assert mp.isfinite(profile_joint([(1,), (2,)],[(1,), (1,)],[(1,), (1,)],0)['log_sup'])
assert profile_joint([(1,), (2,)],[(1,), (1,)],[(1,), (1,)],1)['log_sup'] == mp.inf

# Exact price Jacobian, with the same endpoint shared between adjacent segments.
returns = flat(clock.vector(row) for row in r)
prices = [mp.mpf(1)]
for x in returns:
    prices.append(prices[-1]*mp.exp(x))
near(clock.log_null_sup(flat(delta),flat(u),prices), fits[0]['log_sup']-sum(mp.log(y) for y in prices[1:]))

# Independent experiment float implementation versus arbitrary-precision formulas.
# A fixed deterministic 12-day record, not a sampled experiment.
z = np.array([[[.006*math.sin(3*d+j)+.002*math.cos(d+2*j) for j in range(3)]
               for d in range(12)]])
d = [[experiment.DT]*3 for _ in range(12)]
fast = experiment.calendar_profiles(z)[0]
for index, budget in enumerate((0,1,3,10,11)):
    accurate = profile_joint(z[0].tolist(),d,d,budget)['log_sup']
    assert abs(float(accurate)-fast[index]) < 1e-9
for index,budget in ((5,0),(6,3)):
    accurate = free.profile_switches(z[0].tolist(),d,d,budget)['log_sup']
    assert abs(float(accurate)-fast[index]) < 1e-9

# Fixed out-of-class daily drift example used in FINDINGS. Both days have
# scale epsilon; their return means are -1 and +1, so budget zero misses them.
center = [(-1,-1),(1,1)]
design = [(1,1),(1,1)]
lp = profile_joint(center,design,design,0)['log_sup']
for eps in (mp.mpf('.1'),mp.mpf('.01')):
    lq = -2*mp.log(2*mp.pi*eps)
    near(mp.exp(lq-lp), mp.exp(2)/eps**2, mp.mpf('1e-45'))

for budget in (-1,3,True,.5):
    try: profile_joint(r,delta,u,budget)
    except ValueError: pass
    else: raise AssertionError('invalid budget accepted')
for args in (([],[],[],0), ([(1,2)],[(1,)],[(1,)],0),
             ([(1,2)],[(1,1)],[(1,0)],0)):
    try: profile_joint(*args)
    except ValueError: pass
    else: raise AssertionError('invalid design accepted')
print('070 checks passed: joint optimization, partitions, nesting, drift cost, singularities, Jacobian, experiment evaluator')
