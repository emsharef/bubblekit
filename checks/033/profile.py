"""Claim 033 diagnostic profile: calendar drift and a declared variance clock.

Exact-price/log-return formulas at arbitrary precision, NOT outward bounds.
Near-singular floating-point residuals are not certified zero/nonzero tests.
No rounded/noisy observation likelihood or fitted-clock coverage is supplied.
"""
from mpmath import mp


def vector(values):
    result = tuple(mp.mpf(x) for x in values)
    if not result or any(not mp.isfinite(x) for x in result):
        raise ValueError("nonempty finite vector required")
    return result


def design(durations, clock):
    d, v = vector(durations), vector(clock)
    if len(d) != len(v) or any(x <= 0 for x in d + v):
        raise ValueError("matching positive calendar and variance increments required")
    return d, v


def profile_returns(returns, durations, clock):
    """Return log supremum in return coordinates, fitted b,w, and Q,K,H."""
    r = vector(returns)
    d, v = design(durations, clock)
    if len(r) != len(d):
        raise ValueError("return/design length mismatch")
    n = len(r)
    A = mp.fsum(x*x/y for x, y in zip(d, v))
    B = mp.fsum(x*z/y for x, y, z in zip(d, v, r))
    T = mp.fsum(d)
    residual = tuple(z - (B/A)*x for x, z in zip(d, r))
    Q = mp.fsum(z*z/y for z, y in zip(residual, v))
    K = mp.fsum(residual)
    H = mp.fsum((y-(T/A)*x)**2/y for x, y in zip(d, v))
    # This only handles exactly recognized singular inputs, not a tolerance band.
    if n == 1 or all(z*d[0] == r[0]*x for z, x in zip(r, d)):
        return dict(log_sup=mp.inf, b=None, w=None, Q=mp.mpf(0), K=mp.mpf(0), H=H)
    if Q == 0:
        raise ArithmeticError("unresolved residual: increase precision")
    w = 2*Q/(n + mp.sqrt(n*n + H*Q))
    b = (B+w*T/2)/A
    log_sup = (-n*mp.log(2*mp.pi*w)/2
               -mp.fsum(mp.log(y) for y in v)/2-Q/(2*w)-K/2-w*H/8)
    return dict(log_sup=log_sup, b=b, w=w, Q=Q, K=K, H=H)


def log_null_sup(durations, clock, prices):
    """Include the price Jacobian and claim 055's mixed-domain extension."""
    d, v = design(durations, clock)
    y = vector(prices)
    if len(y) != len(d)+1 or any(x < 0 for x in y):
        raise ValueError("nonnegative prices matching the design required")
    if y[0] == 0:
        return mp.mpf(0) if all(x == 0 for x in y[1:]) else -mp.inf
    if any(x == 0 for x in y[1:]):
        return -mp.inf
    r = tuple(mp.log(b/a) for a, b in zip(y, y[1:]))
    return profile_returns(r, d, v)["log_sup"]-mp.fsum(mp.log(x) for x in y[1:])
