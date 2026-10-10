"""CEV mixed transition kernel, AX-56 source-audited at 2ca814c.

Diagnostic high-precision formulas, not a calibrated test or certified numerics.
Reference measure: Lebesgue on (0, infinity) plus unit mass at zero.
The zero boundary is absorbing; no conditioning on survival and no price floor.
"""
from mpmath import mp


def number(value, name, strictly_positive=False):
    value = mp.mpf(value)
    if not mp.isfinite(value) or value < 0 or (strictly_positive and value == 0):
        raise ValueError(f'{name} must be finite and ' +
                         ('positive' if strictly_positive else 'nonnegative'))
    return value


def log_transition(power, kappa, delta, x, y):
    """Log mixed density, including the exact mathematical atom at y=0."""
    p, k, t = (number(v, n, True) for v, n in
               ((power, 'power'), (kappa, 'kappa'), (delta, 'delta')))
    x, y = number(x, 'x'), number(y, 'y')
    if x == 0:
        return mp.mpf(0) if y == 0 else -mp.inf
    if y == 0:
        if p >= 1:
            return -mp.inf
        h = 1 - p
        order = 1 / (2 * h)
        z = x**(2 * h) / (2 * k**2 * h**2 * t)
        return mp.log(mp.gammainc(order, z, mp.inf, regularized=True))
    if p == 1:
        v = k**2 * t
        return -mp.log(y) - mp.log(2 * mp.pi * v) / 2 - (mp.log(y / x) + v / 2)**2 / (2 * v)
    h = abs(p - 1)
    a, b = x**(1 - p), y**(1 - p)
    v = k**2 * h**2 * t
    return (mp.log(x) / 2 + (mp.mpf('0.5') - 2 * p) * mp.log(y)
            - mp.log(k**2 * h * t) - (a*a + b*b) / (2 * v)
            + mp.log(mp.besseli(1 / (2 * h), a*b / v)))


def transition(power, kappa, delta, x, y):
    return mp.exp(log_transition(power, kappa, delta, x, y))
