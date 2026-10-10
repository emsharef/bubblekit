"""Deterministic enclosure checks, not a simulation or proof of FLINT."""
from fractions import Fraction as F
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from unittest.mock import patch
from flint import ctx, arb
from mpmath import mp
from certify import (certify, transition, probability_endpoint, edges, endpoint,
                     Certificate)

spec = spec_from_file_location('monetary031', Path(__file__).resolve().parents[1]/'031/cells.py')
reference = module_from_spec(spec)
spec.loader.exec_module(reference)
mp.dps = 160


def m(value):
    return mp.mpf(value.numerator)/value.denominator


count = 0
with ctx.workprec(96):
    # Include exact clipping boundaries, the zero atom, very narrow cells and
    # tails far beyond ordinary double-precision CDF subtraction.
    cases = [((F(a), F(b)), (F(c), F(d))) for a,b in ((0,1),(1,4),(2,8),(1,F(10001,10000)))
             for c,d in ((0,1),(1,4),(4,16),(100,101))]
    for source, target in cases:
        for drift, scale in ((F(1,2),F(1)), (F(-2),F(1,10))):
            value = transition(source, target, F(1), drift, scale)
            lower, upper = (probability_endpoint(value, side) for side in (False,True))
            exact = reference.upper(tuple(map(m,source)),tuple(map(m,target)),mp.mpf(1),m(drift),m(scale))
            assert m(lower) <= exact <= m(upper), (source,target,drift,scale)
            count += 1
    # A plain CDF difference loses this target near 40 standard deviations;
    # the tail-aware evaluator must retain a strictly positive lower endpoint.
    value = transition((F(1),F(10001,10000)), (F(10**17),F(2*10**17)), F(1), F(1,2), F(1))
    assert probability_endpoint(value,False) > 0

paths = ((0,0,0),(0,1,0),(1,0,1),(1,2,1),(50,51,49),(500,501,499),(10000,10021,10000))
nulls = ((F(0),F(3,10)), (F(1,50),F(3,5)))
forecast = (F(0),F(1,5))
for path in paths:
    gaps = (F(1,252),F(1,19656))
    cert = certify(path,gaps,'0.01',nulls,forecast,3,96)
    fine = certify(path,gaps,'0.01',nulls,forecast,3,192)
    assert cert.status == fine.status == 'enclosed'
    exact_bounds = [reference.bounds(path,tuple(map(m,gaps)),'.01',m(b),m(k),3) for b,k in nulls]
    exact_q = reference.forecast(path,tuple(map(m,gaps)),'.01',m(forecast[0]),m(forecast[1]))
    for level,(upper,score) in enumerate(zip(cert.denominator_upper,cert.score_lower)):
        exact_d = max(bs[level] for bs in exact_bounds)
        assert exact_d <= m(upper) <= 1
        assert 0 <= m(cert.numerator_lower) <= exact_q
        assert 0 <= m(score) <= exact_q/exact_d
        assert m(fine.denominator_upper[level]) >= exact_d
    assert all(b <= a for a,b in zip(cert.denominator_upper,cert.denominator_upper[1:]))
    assert all(b >= a for a,b in zip(cert.score_lower,cert.score_lower[1:]))
    # Rational outputs survive exact serialization with no rounded-up score.
    num, den = cert.score_ratio_hex()
    assert F(int(num,16),int(den,16)) == cert.score_lower[-1]
    if path == (0,0,0):
        assert cert.denominator_upper == (F(1),)*4
        assert cert.score_lower[-1] <= 1

# Independent two-step integration for moderate transitions, including a
# positive latent endpoint whose quote is zero. Check the implemented upper
# bounds against the actual joint probability, not just the earlier prototype.
mp.dps = 60
for path, start in (((0,1,0),mp.mpf('.004')), ((1,0,1),mp.mpf('.01')), ((1,2,1),mp.mpf('.01'))):
    cert = certify(path,('0.5','0.5'),'.01',(('0.02','0.6'),),('0.02','0.6'),2)
    dt,b,k = map(mp.mpf,('.5','.02','.6'))
    mu,sd = (b-k*k/2)*dt,k*mp.sqrt(dt)
    first,second = reference.edges('.01',path[1]), reference.edges('.01',path[2])
    lo = -mp.inf if first[0]==0 else (mp.log(first[0]/start)-mu)/sd
    hi = (mp.log(first[1]/start)-mu)/sd
    cuts = [lo]+[mp.mpf(t) for t in (-8,-4,0,4,8) if lo<t<hi]+[hi]
    actual = mp.quad(lambda t: mp.exp(-t*t/2)/mp.sqrt(2*mp.pi)*
        reference.probability(start*mp.exp(mu+sd*t),second,dt,b,k),cuts)
    assert all(actual <= m(bound) for bound in cert.denominator_upper)

# Not identically zero: fixed forecast concentrated on a tiny unchanged cell
# can reject against a diffuse null. This is a deterministic score, not power.
positive = certify((10000,10000),('1',),'.01',(('0','1'),),('0','0.00001'),1,128)
assert positive.status == 'enclosed' and positive.rejects('0.05')

# Exact threshold equality and validation: no accidental >= comparison.
equality = Certificate((F(1,20),),F(1),(F(20),),'enclosed')
assert not equality.rejects('0.05')
assert equality.rejects(F(51,1000))

# A failed enclosure must return retained zero evidence, never a density
# approximation or a partial/null-family maximum with failed entries omitted.
with patch('certify.transition', return_value=arb.nan()):
    failed = certify((1,2),('1',),'.01',(('0','1'),),('0','1'),1)
assert failed.status.startswith('zero fallback') and failed.score_lower == (0,0)

base = dict(labels=(1,2),durations=('1',),tick='.01',nulls=(('0','1'),),forecast=('0','1'))
for key,value in [('labels',(1,-1)),('labels',(True,1)),('durations',('0',)),
                  ('durations',()),('tick',0.01),('nulls',()),('nulls',(('0','0'),)),
                  ('forecast',('nan','1')),('max_level',-1),('bits',31)]:
    try:
        certify(**(base | {key:value}))
    except ValueError:
        pass
    else:
        raise AssertionError(('invalid input accepted',key,value))
print(f'PASS: {count} transition enclosures, tail positivity, 7 paths at 2 precisions, '
      '3 independent joint integrals, exact threshold/serialization, zero fallback and invalid inputs.')
print('Fixed unchanged-cell score lower bound > 20:',positive.rejects('0.05'))
print('Trusts FLINT ball arithmetic; no Lean certificate, observed-feed validation or power measurement.')
