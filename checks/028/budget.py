"""Proposed claim 028's supplied Gaussian rounding budgets; not certified."""
from mpmath import mp


def positive(x):
    x = mp.mpf(x)
    if not mp.isfinite(x) or x <= 0:
        raise ValueError('finite positive design values required')
    return x


def budget(h_tick, minimum_scale, first_gap):
    h, k, dt = map(positive, (h_tick, minimum_scale, first_gap))
    return mp.sqrt(-mp.expm1(-h*h/(16*k*k*dt)))


def spacing_limit(target, minimum_scale, first_gap):
    e, k, dt = map(positive, (target, minimum_scale, first_gap))
    if e >= 1:
        raise ValueError('target must be below one')
    return 4*k*mp.sqrt(dt)*mp.sqrt(-mp.log1p(-e*e))


def report():
    mp.dps = 60
    print('Supplied scale floor .3; log lattice; first evaluation gap only.')
    for frequency in (252,19656,98280):
        dt = mp.mpf(1)/frequency
        print(f'increments/year={frequency}: '
              f'epsilon(h=.0001)={float(budget(".0001",".3",dt)):.9f}, '
              f'epsilon(h=.001)={float(budget(".001",".3",dt)):.9f}, '
              f'max h for epsilon .025={float(spacing_limit(".025",".3",dt)):.9f}')
    print('Upper bounds, not actual TV or performance; future joint-cell likelihood still required.')


if __name__ == '__main__':
    report()
