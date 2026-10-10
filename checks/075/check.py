"""Claim 075 deterministic coefficient and energy checks, no simulation.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/075/check.py
"""
from fractions import Fraction as F
from itertools import product
from mpmath import mp

mp.dps = 50


def close(a, b):
    assert abs(a-b) < mp.mpf('1e-35')*(1+abs(a)+abs(b)), (a, b)


fixtures = 0
for x, sigma, exposure in product((F(1, 3), F(1), F(5)),
                                 (F(-2), F(1, 2), F(3)),
                                 (F(-1), F(0), F(1, 4), F(2))):
    a = sigma*sigma
    mu = exposure/x
    assert a*mu == exposure*sigma*sigma/x
    assert mu*a*mu == exposure**2*sigma**2/x**2
    fixtures += 1

geometric = 0
for x, kappa, exposure in product((F(1, 7), F(2), F(9)),
                                  (F(1, 5), F(2)),
                                  (F(-2), F(0), F(1, 2))):
    a = (kappa*x)**2
    mu = exposure/x
    assert mu*a*mu == kappa**2*exposure**2
    assert a*mu == kappa**2*exposure*x
    geometric += 1

thresholds = 0
for kappa, bound, horizon in product((F(1, 5), F(2)),
                                    (F(0), F(1, 2), F(3)),
                                    (F(0), F(1, 3), F(10))):
    ceiling = kappa**2*bound**2
    n = int(ceiling*horizon) + 1
    assert n > ceiling*horizon
    for fraction in (F(0), F(1, 4), F(1, 2), F(1)):
        # Bound on energy at every selected time, for either sign of exposure.
        time = fraction*horizon
        assert ceiling*time < n
    thresholds += 1

integrals = 0
for gamma, horizon in product((mp.mpf(0), mp.mpf('.25'), mp.mpf('.5'),
                               mp.mpf(1), mp.mpf(2)),
                              (mp.mpf(1), mp.mpf(10), mp.mpf(100))):
    direct = mp.quad(lambda t: (1+t)**(-2*gamma), [0, horizon])
    formula = (mp.log1p(horizon) if gamma == mp.mpf('.5') else
               ((1+horizon)**(1-2*gamma)-1)/(1-2*gamma))
    close(direct, formula)
    if gamma > mp.mpf('.5'):
        total = 1/(2*gamma-1)
        tail = (1+horizon)**(1-2*gamma)/(2*gamma-1)
        close(direct+tail, total)
    integrals += 1
close(mp.quad(lambda t: mp.exp(-2*t), [0, 1, mp.inf]), mp.mpf('.5'))
for c in (mp.mpf('.25'), mp.mpf(1), mp.mpf(3)):
    close(mp.quad(lambda x: x**(-3), [c, mp.inf]), 1/(2*c*c))
print(f'PASS: {fixtures} coefficient fixtures; {geometric} geometric cancellations; '
      f'{thresholds} stop thresholds; {integrals} power-schedule quadratures; '
      'exponential energy and 3 upper-endpoint integrals')
