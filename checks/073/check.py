"""Claim 073 deterministic density checks; no simulation or estimated power.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/073/check.py
"""
from itertools import product
from mpmath import mp

mp.dps = 80


def coordinates(k, dt, z):
    prices = [mp.mpf(1)]
    for d, a in zip(dt, z):
        prices.append(prices[-1]*mp.exp(k*mp.sqrt(d)*a-k*k*d/2))
    return prices


def log_f1(k, d, x, y):
    v = k*k*d
    return -mp.log(y)-mp.log(2*mp.pi*v)/2-(mp.log(y/x)+v/2)**2/(2*v)


def log_f2(k, d, x, y):
    # Source density, with its exponential difference stabilized.
    v = k*k*d
    a = (1/y-1/x)**2/(2*v)
    b = (1/y+1/x)**2/(2*v)
    return mp.log(x)-3*mp.log(y)-mp.log(2*mp.pi*v)/2-a+mp.log(-mp.expm1(a-b))


def log_ratio(k, dt, z):
    prices = coordinates(k, dt, z)
    return mp.fsum(mp.log(x)-2*mp.log(y)+a*a/2
                   -(1/y-1/x)**2/(2*k*k*d)+mp.log(-mp.expm1(-2/(k*k*d*x*y)))
                   for x, y, d, a in zip(prices, prices[1:], dt, z))


def close(a, b, tol=mp.mpf('1e-55')):
    assert abs(a-b) < tol*(1+abs(a)+abs(b)), (a, b)


count = 0
for n in (1, 2, 3):
    dt = [mp.mpf(j+1)/10 for j in range(n)]
    for raw in product(('-2', '0', '1.5'), repeat=n):
        z = list(map(mp.mpf, raw))
        for k in map(mp.mpf, ('.8', '.1', '.01', '1e-7')):
            prices = coordinates(k, dt, z)
            p1 = mp.fsum(log_f1(k, d, x, y) for x, y, d in zip(prices, prices[1:], dt))
            p2 = mp.fsum(log_f2(k, d, x, y) for x, y, d in zip(prices, prices[1:], dt))
            jac = mp.fsum(mp.log(y*k*mp.sqrt(d)) for y, d in zip(prices[1:], dt))
            gaussian = -n*mp.log(2*mp.pi)/2-mp.fsum(a*a for a in z)/2
            close(p1+jac, gaussian)
            close(p2-p1, log_ratio(k, dt, z))
            if k == mp.mpf('1e-7'):
                assert abs(mp.expm1(log_ratio(k, dt, z))) < mp.mpf('1e-4')
                for x, y, d, a in zip(prices, prices[1:], dt, z):
                    assert abs((1/y-1/x)/(k*mp.sqrt(d))+a) < mp.mpf('1e-5')
            count += 1

# One-dimensional shortfall quadrature, used only as a check. Normalization
# in the proof is the cited kernel fact, never inferred from these integrals.
# d_grid = 2 E[(1-L)_+] when E L = 1. On |z|>12 its omitted integrand
# contribution is at most 2 P(|Z|>12), independent of the alternative tails.
# Find sign-change breakpoints before quadrature to resolve the positive part.
mp.dps = 50
phi = lambda z: mp.exp(-z*z/2)/mp.sqrt(2*mp.pi)
previous = mp.inf
for k in map(mp.mpf, ('.3', '.1', '.03')):
    lr = lambda a: log_ratio(k, [mp.mpf(1)], [a])
    grid = [mp.mpf(-12)+mp.mpf(j)/4 for j in range(97)]
    roots = []
    for a, b in zip(grid, grid[1:]):
        fa, fb = lr(a), lr(b)
        if fa*fb < 0:
            for _ in range(160):
                mid = (a+b)/2
                fm = lr(mid)
                if fa*fm <= 0:
                    b = mid
                else:
                    a, fa = mid, fm
            roots.append((a+b)/2)
    edges = [mp.mpf(-12), *roots, mp.mpf(12)]
    value = 2*mp.fsum(mp.quad(lambda a: phi(a)*max(0, -mp.expm1(lr(a))), [left, right])
                      for left, right in zip(edges, edges[1:]))
    assert 0 < value < previous
    previous = value
assert 2*mp.erfc(12/mp.sqrt(2)) < mp.mpf('1e-31')
print(f'PASS: {count} fixed chain-ratio/Jacobian checks, pointwise small-scale limits, '
      'three one-dimensional overlap checks; no simulation or rate estimate')
