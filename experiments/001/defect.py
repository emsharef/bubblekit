"""Martingale defect of constant-proportion wealth on a CEV process (experiment 001).

Method P: backward equation under Q on a truncated domain (eps, M), in y = log x, BDF2 in time.
Method X: exit probability of the auxiliary diffusion, via the Bessel-type hitting law
[karatzas2015distribution] (6.10).  See experiments/001-d1-threshold.md for the derivations.
"""
import math

import numpy as np
from scipy.sparse import diags
from scipy.sparse.linalg import splu
from scipy.special import gammaincc


def pde_defect(beta, pi, eps, M, h, dt, times=(1.0, 5.0)):
    """Return ({T: D_P}, eps_used, M_used) with D_P = 1 - E_1[V_T ; exit of (eps, M) after T] / V_0.

    The grid is y_j = j h, so the start y = 0 (S_0 = 1) is a node; the cut points are rounded outward
    to the grid and the cut actually used is returned.
    """
    jlo = math.floor(math.log(eps) / h)
    jhi = math.ceil(math.log(M) / h)
    y = h * np.arange(jlo + 1, jhi)                     # interior nodes; boundaries carry u = 0
    i0 = -jlo - 1                                       # index of y = 0
    n = y.size
    # w = 1/a(y), a(y) = exp((2 beta - 2) y); exponent clipped: overflow means a frozen row, underflow
    # means the quasi-static row L_h u = 0, both the correct limits.
    w = np.exp(np.clip(-(2.0 * beta - 2.0) * y, -745.0, 700.0))
    c = pi - 0.5
    lo = 0.5 / h**2 - c / (2.0 * h)
    up = 0.5 / h**2 + c / (2.0 * h)
    L = diags([np.full(n - 1, lo), np.full(n, -1.0 / h**2), np.full(n - 1, up)], [-1, 0, 1], format="csc")
    euler = splu((diags(w) - dt * L).tocsc())
    bdf2 = splu((diags(3.0 * w) - 2.0 * dt * L).tocsc())

    nsteps = round(max(times) / dt)
    record = {round(T / dt): T for T in times}
    out = {}
    u_prev = np.ones(n)
    u = euler.solve(w * u_prev)
    if 1 in record:
        out[record[1]] = 1.0 - u[i0]
    for step in range(2, nsteps + 1):
        u, u_prev = bdf2.solve(w * (4.0 * u - u_prev)), u
        if step in record:
            out[record[step]] = 1.0 - u[i0]
    return out, math.exp(h * jlo), math.exp(h * jhi)


def exact_defect(beta, pi, T, s0=1.0):
    """Method X: P~(auxiliary diffusion exits (0, inf) by T)."""
    if beta == 1.0:
        return 0.0                                      # auxiliary diffusion is a GBM
    delta = (1.0 - 2.0 * beta + 2.0 * pi) / (1.0 - beta)
    if delta >= 2.0:
        return 0.0                                      # R does not reach 0 (AX-02)
    nu = 1.0 - delta / 2.0
    xi = s0 ** (1.0 - beta) / abs(1.0 - beta)
    return float(gammaincc(nu, xi**2 / (2.0 * T)))
