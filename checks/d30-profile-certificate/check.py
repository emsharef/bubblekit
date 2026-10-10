"""Fixed certificate checks, not a simulation, power table or Lean proof.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d30-profile-certificate/check.py
"""
from fractions import Fraction as F
from unittest.mock import patch

from flint import arb, ctx
from mpmath import mp

import certify as c

mp.dps = 220


def m(x):
    x = F(x)
    return mp.mpf(x.numerator)/x.denominator


def enclosure(value, interval):
    assert m(c.endpoint(interval, False)) <= value <= m(c.endpoint(interval, True))


def reference(prices, dt, budget, u, z):
    rr = [mp.log(m(b)/m(a)) for a, b in zip(prices, prices[1:])]
    dd = list(map(m, dt))
    aa, bb = [r*r/(2*d) for r, d in zip(rr, dd)], [d/8 for d in dd]
    constant = -len(rr)*mp.log(2*mp.pi)/2-mp.fsum(mp.log(d) for d in dd)/2-mp.fsum(rr)/2
    lower = mp.fsum(-mp.log(2*mp.pi*d*mp.exp(m(s)))/2
                   -(r+d*mp.exp(m(s))/2)**2/(2*d*mp.exp(m(s)))
                   for r, d, s in zip(rr, dd, z))
    hs = []
    for a, b, ci in zip(aa, bb, c.incidence(u)):
        d = mp.mpf('.5')+m(ci)
        if a == 0 and d >= 0:
            hs.append(mp.inf if d > 0 else mp.mpf(0))
        else:
            # Independent high-precision root; these fixtures are moderate.
            y = (mp.sqrt(d*d+4*a*b)-d)/(2*b)
            hs.append(-d*mp.log(y)-a/y-b*y)
    upper = constant + m(budget)*max(map(lambda x:abs(m(x)), u), default=0)+mp.fsum(hs)
    return lower, upper


# Closed profile against the independent common-scale normal likelihood.
for prices, dt in [((1, F(101, 100)), (F(1, 252),)),
                   ((1, 1, F(11, 10), F(9, 10)), (F(1, 10),)*3),
                   ((1, 2, 1, 3), (F(1, 100), F(1, 5), F(1, 3)))]:
    rr = [mp.log(m(b)/m(a)) for a, b in zip(prices, prices[1:])]
    aa = mp.fsum(r*r/(2*m(d)) for r, d in zip(rr, dt))
    bb = mp.fsum(m(d)/8 for d in dt)
    d = mp.mpf(len(dt))/2
    y = 2*aa/(d+mp.sqrt(d*d+4*aa*bb))
    exact = mp.fsum(-mp.log(2*mp.pi*m(h)*y)/2-(r+m(h)*y/2)**2/(2*m(h)*y)
                   for r, h in zip(rr, dt))
    for bits in (64, 192):
        out = c.certify(prices, dt, 0, bits=bits)
        assert out.status == 'enclosed closed profile'
        assert m(out.log_lower) <= exact <= m(out.log_upper)
        assert out.gap_upper == out.log_upper-out.log_lower
        assert out.within_gap('1e-10')
        safe = out.score_lower(F(3, 2), bits)
        assert 0 < m(safe) <= mp.mpf('1.5')*mp.exp(-exact)

# A tight nonconstant witness constructed independently on the active face
# z_2-z_1=V. Rationalizing z_1 then adding V exactly preserves feasibility.
prices, dt = (1, F(101, 100), F(109, 100)), (F(1, 10),)*2
rr = [mp.log(m(b)/m(a)) for a, b in zip(prices, prices[1:])]
aa = [r*r/(2*m(dt[0])) for r in rr]
bb = m(dt[0])/8
for budget in (F(1, 4), F(1), F(2)):
    A = aa[0]+aa[1]*mp.exp(-m(budget))
    B = bb*(1+mp.exp(m(budget)))
    y = 2*A/(1+mp.sqrt(1+4*A*B))
    z0 = F(mp.nstr(mp.log(y), 100))
    z = (z0, z0+budget)
    u = (F(mp.nstr(mp.mpf('.5')-aa[0]/y+bb*y, 100)),)
    lower, upper = reference(prices, dt, budget, u, z)
    out = c.certify(prices, dt, budget, u, z, bits=256)
    assert out.status == 'enclosed supplied witness'
    assert m(out.log_lower) <= lower <= upper <= m(out.log_upper)
    assert out.within_gap('1e-60'), out
    scaled = c.certify(tuple(7*p for p in prices), dt, budget, u, z, bits=256)
    assert out == scaled
    loose = c.certify(prices, dt, budget, (0,), bits=128)
    assert loose.status == 'enclosed supplied witness'
    assert not loose.within_gap('1e-6')

# Exact zero boundaries are classified by prices and rational incidence.
prices, dt = (1, 1, 2), (F(1, 10),)*2
for u in ((F(1, 2),), (F(1),)):
    out = c.certify(prices, dt, 1, u, (0, 0), bits=192)
    lo, hi = reference(prices, dt, 1, u, (0, 0))
    assert m(out.log_lower) <= lo <= hi <= m(out.log_upper)
assert c.certify(prices, dt, 1, (0,)).status == 'infinite dual certificate'
out = c.certify((1, 1, 1), dt, 1, (0,))
assert out.status == 'infinite profile: all returns zero'
assert out.score_lower(1) == 0

# Root stability at both extreme signs, where one of the algebraic forms
# loses all meaningful digits in ordinary floating-point arithmetic.
with ctx.workprec(192):
    for d in (F(10**40), F(-10**40), F(0)):
        a, b = F(1, 10**80), F(1, 8)
        value = c.scalar(c.ball(a), c.ball(b), d, False)
        root = mp.sqrt(m(d*d)+4*m(a*b))
        y = 2*m(a)/(root+m(d)) if d >= 0 else (root-m(d))/(2*m(b))
        enclosure(-m(d)*mp.log(y)-m(a)/y-m(b)*y, value)
    assert c.scalar(arb(0), arb(1), F(0), True).is_zero()
    assert c.scalar(arb(0), arb(1), F(1), True) is None

near = (1, 1+F(1, 10**100))
assert c.certify(near, (1,), 0, bits=64).status == 'unresolved arithmetic'
assert c.certify(near, (1,), 0, bits=1024).status == 'enclosed closed profile'
for prices in (None, (), (1, 0, 2), (1, 'nan', 2), (1, 1.1, 2)):
    out = c.certify(prices, dt, 1, (0,))
    assert out.status == 'invalid observations' and out.score_lower(1) == 0
for u, z in ((None, None), ((), None), ((0,), (0, 2)), ((0.1,), None)):
    out = c.certify((1, 2, 3), dt, 1, u, z)
    assert out.status == 'invalid witness' and out.score_lower(1) == 0
with patch.object(c, 'loglik', side_effect=ArithmeticError('forced failure')):
    assert c.certify((1, 2), (1,), 0).score_lower(1) == 0
for change in ({'durations': ()}, {'durations': (-1,)}, {'budget': -1}, {'bits': 31}):
    args = dict(prices=(1, 2), durations=(1,), budget=0)
    args.update(change)
    try:
        c.certify(**args)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid design accepted')
assert ctx.prec == 53
print('PASS: closed and active-face profiles, rational score bounds, exact zeros, '
      'stable roots, loose-gap detection, scaling, precision recovery and failure retention')

# CEV forecast: independently use the unscaled AX-56 density, not the
# implementation's transformed exponent or scaled Bessel expression.
import forecast


def reference_transition(x, y, dt, p, k, returns=True):
    x, y, dt, p, k = map(m, (x, y, dt, p, k))
    h = p-1
    v = k*k*h*h*dt
    value = (mp.log(x)/2+(mp.mpf('.5')-2*p)*mp.log(y)
             -mp.log(k*k*h*dt)-(x**(2-2*p)+y**(2-2*p))/(2*v)
             +mp.log(mp.besseli(1/(2*h), x**(1-p)*y**(1-p)/v)))
    return value+mp.log(y) if returns else value


fixtures = [((F(1), F(101, 100), F(99, 100), F(27, 25)), (F(1, 252),)*3),
            ((F(1), F(1), F(3, 2)), (F(1, 19656), F(1, 40))),
            ((F(1), F(1)), (F(1, 10**12),))]
for prices, dt in fixtures:
    component_logs = []
    for w, p, k in forecast.CATALOGUE:
        exact = mp.fsum(reference_transition(x, y, d, p, k)
                       for x, y, d in zip(prices, prices[1:], dt))
        component_logs.append(mp.log(m(w))+exact)
        out = forecast.enclose(prices, dt, ((1, p, k),), bits=256)
        assert out.status == 'enclosed'
        assert m(out.log_lower) <= exact <= m(out.log_upper)
        assert out.log_upper-out.log_lower < F(1, 10**40)
        price_density = mp.fsum(reference_transition(x, y, d, p, k, returns=False)
                               for x, y, d in zip(prices, prices[1:], dt))
        assert abs(exact-price_density-mp.fsum(mp.log(m(y)) for y in prices[1:])) < mp.mpf('1e-180')
    maximum = max(component_logs)
    exact = maximum+mp.log(mp.fsum(mp.exp(x-maximum) for x in component_logs))
    out = forecast.enclose(prices, dt, bits=256)
    assert out.status == 'enclosed'
    assert m(out.log_lower) <= exact <= m(out.log_upper)
    profile = c.certify(prices, dt, 0, bits=256)
    decision = forecast.decide(profile, out, bits=256)
    if all(x == prices[0] for x in prices):
        assert decision.status == 'certified noncrossing: infinite profile'
    else:
        assert decision.status in ('certified rejection', 'certified noncrossing')
        assert decision.log_score_lower <= decision.log_score_upper

# Heterogeneous deterministic component clocks and whole-path mixing order.
prices, dt = fixtures[0]
rows = ((F(1, 3), F(5, 4), F(3, 10)), (F(2, 3), F(2), F(3, 5)))
clocks = (dt, tuple((j+1)*d for j, d in enumerate(dt)))
parts = [[reference_transition(x, y, d, p, k)
          for x, y, d in zip(prices, prices[1:], grid)]
         for (_, p, k), grid in zip(rows, clocks)]
exact = mp.log(mp.fsum(m(row[0])*mp.exp(mp.fsum(part)) for row, part in zip(rows, parts)))
out = forecast.enclose(prices, dt, rows, clocks, bits=256)
assert m(out.log_lower) <= exact <= m(out.log_upper)
wrong_order = mp.fsum(mp.log(mp.fsum(m(row[0])*mp.exp(part[j])
                                    for row, part in zip(rows, parts))) for j in range(len(dt)))
assert abs(wrong_order-exact) > mp.mpf('1e-3')

# Coordinate scaling: for p=2, S -> 3S and k -> k/3 leave RETURN density
# unchanged. This would fail if the destination-price Jacobian were missing.
base = forecast.enclose(prices, dt, ((1, 2, F(3, 5)),), bits=256)
scaled = forecast.enclose(tuple(3*x for x in prices), dt, ((1, 2, F(1, 5)),), bits=256)
assert base.log_lower <= scaled.log_upper and scaled.log_lower <= base.log_upper

# Threshold logic: strict rejection, a proved upper noncrossing, uncertain
# equality and invalid arithmetic are different outcomes; no float comparison.
profile = c.ProfileCertificate('enclosed', F(0), F(0), F(0))
assert forecast.decide(profile, forecast.ForecastEnclosure('enclosed', F(4), F(5))).status == 'certified rejection'
assert forecast.decide(profile, forecast.ForecastEnclosure('enclosed', F(0), F(1))).status == 'certified noncrossing'
with ctx.workprec(192):
    threshold = c.ball(F(20)).log()
    equality = forecast.ForecastEnclosure('enclosed', c.endpoint(threshold, False), c.endpoint(threshold, True))
assert forecast.decide(profile, equality, bits=192).status == 'unresolved threshold'
assert forecast.decide(profile, forecast.ForecastEnclosure('unresolved arithmetic')).status == 'unresolved forecast'
assert forecast.decide(c.ProfileCertificate('invalid witness'), equality).status == 'unresolved profile'
assert forecast.decide(c.certify((1, 1), (1,), 0), equality).status == 'certified noncrossing: infinite profile'

for prices in (None, (), (1, 0), (1, 'nan'), (1, 1.1)):
    assert forecast.enclose(prices, (1,)).status == 'invalid observations'
with patch.object(forecast, 'log_transition', side_effect=ArithmeticError('forced failure')):
    assert forecast.enclose((1, 2), (1,)).status == 'unresolved arithmetic'
for change in ({'catalogue': ((1, 1, 1),)}, {'catalogue': ((F(1, 2), 2, 1),)},
               {'catalogue': ((1, 2, 0),)}, {'clocks': ()}, {'clocks': ((-1,),)*12},
               {'durations': (-1,)}, {'bits': 31}):
    args = dict(prices=(1, 2), durations=(1,))
    args.update(change)
    try:
        forecast.enclose(**args)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid forecast design accepted')
assert ctx.prec == 53
print('PASS: 36 component enclosures, mixtures and clocks, return Jacobian, '
      'large Bessel argument, strict decisions and forecast failure retention')
