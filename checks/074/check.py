"""Deterministic checks for claim 074; no paths or performance estimates.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/074/check.py
"""
from fractions import Fraction as F
from itertools import product
from mpmath import mp

mp.dps = 50


def close(x, y):
    assert abs(x-y) < mp.mpf('1e-35') * (1+abs(x)+abs(y)), (x, y)


def real(q):
    return mp.mpf(q.numerator)/q.denominator


count = 0
for p, x, c, exponent in product(
        (F(0), F(1, 4), F(1, 2), F(2)),
        (F(1, 3), F(1), F(5)), (F(1, 2), F(3)), (-1, 0, 1, 2)):
    sigma = x**exponent
    b = p*sigma/x
    s = x-c
    left_scale = -c
    goodness = (s-left_scale)*b*b/(sigma*sigma)
    assert goodness == p*p/x
    assert b*b/(sigma*sigma) == p*p/(x*x)
    assert (b == 0) == (p == 0)
    count += 1

integrals = 0
for p, upper in product((F(0), F(1, 4), F(1, 2), F(2)), (F(1), F(3))):
    previous = mp.mpf('-1')
    for ratio in (10, 100, 1000):
        d = real(upper)
        eps = d/ratio
        value = mp.quad(lambda x: real(p)**2/x, [eps, d])
        close(value, real(p)**2 * mp.log(ratio))
        if p > 0:
            assert value > previous
        else:
            assert value == 0
        previous = value
        integrals += 1

# Gaussian fixture: Z=exp(a sqrt(t) G - a²t/2), G standard normal.
# Direct weighted quadrature is independent of the completed-square tail formula.
tails = 0
for a, time, cutoff in product((mp.mpf('.5'), mp.mpf('1')),
                               (mp.mpf(1), mp.mpf(4)), (mp.mpf(2), mp.mpf(10))):
    scale = a*mp.sqrt(time)
    threshold = (mp.log(cutoff)+scale**2/2)/scale
    weighted = lambda z: mp.exp(scale*z-scale**2/2-z*z/2)/mp.sqrt(2*mp.pi)
    split = max(threshold, scale)
    direct = mp.quad(weighted, [threshold, split, mp.inf])
    formula = mp.erfc((mp.log(cutoff)-scale**2/2)/(scale*mp.sqrt(2)))/2
    close(direct, formula)
    close(mp.quad(weighted, [-mp.inf, 0, scale, mp.inf]), 1)
    tails += 1

# Fixed cutoff, increasing time: tail means approach one despite mean one at each time.
previous = mp.mpf(0)
for time in (1, 4, 16, 64, 256):
    scale = mp.sqrt(time)
    tail = mp.erfc((mp.log(10)-scale**2/2)/(scale*mp.sqrt(2)))/2
    assert previous < tail < 1
    previous = tail
assert previous > mp.mpf('.999999')
print(f'PASS: {count} exact endpoint fixtures; {integrals} cutoff integrals; '
      f'{tails} Gaussian tail/mean quadratures; increasing-time tail fixture')
