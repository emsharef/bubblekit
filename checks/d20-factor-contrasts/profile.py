"""Diagnostic Gaussian contrast profile: mean beta*Delta + gamma*v, variance omega*v.

This is a signed reference observation, not an adjusted tradable price.
No outward certificate, fitted-loading coverage or stochastic model inference.
"""
from mpmath import mp


def profile(x, durations, clock):
    x, d, v = (tuple(mp.mpf(z) for z in a) for a in (x, durations, clock))
    if not x or len(x) != len(d) or len(x) != len(v):
        raise ValueError("matching nonempty arrays required")
    if any(not mp.isfinite(z) for z in x + d + v) or any(z <= 0 for z in d + v):
        raise ValueError("finite observations and positive increments required")
    n = len(x)
    A = mp.fsum(t * t / s for t, s in zip(d, v))
    B = mp.fsum(t * z / s for t, s, z in zip(d, v, x))
    T = mp.fsum(d)
    orth = tuple(s - T * t / A for t, s in zip(d, v))
    rank = 1 if all(v[j] * d[0] == v[0] * d[j] for j in range(n)) else 2
    if rank == 1:
        beta, gamma = B / A, mp.mpf(0)
    else:
        H = mp.fsum(z * z / s for z, s in zip(orth, v))
        if H <= 0:
            raise ArithmeticError("unresolved mean-regressor rank")
        K = mp.fsum((z - B * t / A) * h / s for z, t, h, s in zip(x, d, orth, v))
        gamma = K / H
        beta = B / A - gamma * T / A
    residual = tuple(z - beta * t - gamma * s for z, t, s in zip(x, d, v))
    Q = mp.fsum(z * z / s for z, s in zip(residual, v))
    # No residual degrees of freedom gives an exactly infinite supremum.
    # Exact residual zero is recognized without a numerical tolerance.
    if n <= rank or Q == 0:
        return dict(log_sup=mp.inf, beta=beta, gamma=gamma, omega=mp.mpf(0),
                    Q=mp.mpf(0), rank=rank)
    omega = Q / n
    return dict(log_sup=-n * (mp.log(2 * mp.pi * omega) + 1) / 2
                - mp.fsum(mp.log(s) for s in v) / 2,
                beta=beta, gamma=gamma, omega=omega, Q=Q, rank=rank)


def log_density(x, d, v, beta, gamma, omega):
    if omega <= 0:
        raise ValueError("positive variance scale required")
    return mp.fsum(-mp.log(2 * mp.pi * omega * s) / 2
                   - (z - beta * t - gamma * s) ** 2 / (2 * omega * s)
                   for z, t, s in zip(x, d, v))
