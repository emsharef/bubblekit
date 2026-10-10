"""Experiment 008 solvers: discretely rebalanced fixed-share fund by exact backward recursion over intervals.

In y = log x the Q generator is a(y)[1/2 u_yy - 1/2 u_y] and the share-measure generator a(y)[1/2 u_yy + 1/2 u_y],
a(y) = sigma^2(e^y) e^{-2y}.  Rows are divided by a (experiment 001's scheme) so huge or tiny a stays finite.
"""
import math

import numpy as np
from scipy.sparse import diags
from scipy.sparse.linalg import splu


def log_a_cev(beta):
    return lambda y: (2.0 * beta - 2.0) * y


def log_a_quad(y):                    # sigma = 1 + x^2
    ay = np.abs(y)
    return 2.0 * (ay + np.log1p(np.exp(-2.0 * ay)))


class Op:
    """Backward solver on interior nodes y_j = j h, jlo < j < jhi, drift coefficient c (= -1/2 for Q, +1/2 share)."""

    def __init__(self, log_a, c, h, jlo, jhi, dt):
        self.y = h * np.arange(jlo + 1, jhi)
        n = self.y.size
        self.w = np.exp(np.clip(-log_a(self.y), -745.0, 700.0))
        self.lo, self.up = 0.5 / h**2 - c / (2 * h), 0.5 / h**2 + c / (2 * h)
        L = diags([np.full(n - 1, self.lo), np.full(n, -1.0 / h**2), np.full(n - 1, self.up)], [-1, 0, 1], format="csc")
        self.dt = dt
        self.euler = splu((diags(self.w) - dt * L).tocsc())
        self.bdf2 = splu((diags(3.0 * self.w) - 2.0 * dt * L).tocsc())

    def _bc(self, b_lo, b_hi):
        v = np.zeros(self.y.size)
        v[0] += self.lo * b_lo
        v[-1] += self.up * b_hi
        return v

    def solve(self, u0, steps, b_lo=0.0, b_hi=0.0):
        """u0 at time-to-go 0; return u after `steps` steps (first implicit Euler, then BDF2), constant Dirichlet."""
        bc = self._bc(b_lo, b_hi)
        u_prev = u0
        u = self.euler.solve(self.w * u_prev + self.dt * bc)
        for _ in range(steps - 1):
            u, u_prev = self.bdf2.solve(self.w * (4.0 * u - u_prev) + 2.0 * self.dt * bc), u
        return u


def grid_bounds(eps, M, h):
    return math.floor(math.log(eps) / h), math.ceil(math.log(M) / h)


def fund_defects(log_a, pi, eps, M, h, Delta, m, n_record):
    """D_n = 1 - E[V after n intervals] at S_0 = 1 for each n in n_record (time-homogeneous backward recursion)."""
    jlo, jhi = grid_bounds(eps, M, h)
    dt = Delta / m
    A = Op(log_a, -0.5, h, jlo, jhi, dt)
    B = Op(log_a, +0.5, h, jlo, jhi, dt)
    i0 = -jlo - 1
    w = np.ones(A.y.size)
    out, delta1 = {}, None
    for n in range(1, max(n_record) + 1):
        a = A.solve(w, m, b_lo=1.0, b_hi=0.0)          # w(0) = 1: fund held as cash after absorption
        b = B.solve(w, m, b_lo=0.0, b_hi=0.0)
        if n == 1:
            delta1 = 1.0 - b[i0]                        # one-interval defect of the underlying from S_0 = 1
            a1 = a[i0]
        w = (1.0 - pi) * a + pi * b
        if n in n_record:
            out[n] = 1.0 - w[i0]
    return out, delta1, a1


def continuous_defect(log_a, pi, eps, M, h, dt, times):
    """Experiment 006's method P (both endpoints, any pi): 1 - E[V_T] for continuous rebalancing."""
    jlo, jhi = grid_bounds(eps, M, h)
    op = Op(log_a, pi - 0.5, h, jlo, jhi, dt)
    i0 = -jlo - 1
    return {T: 1.0 - float(op.solve(np.ones(op.y.size), max(1, round(T / dt)))[i0]) for T in times}


def breach_one_interval(log_a, pi, Delta, m, h_target=0.005, eps=1e-8):
    """P(max_{t<=Delta} S_t >= (1 + 1/|pi|) S_0) from S_0 = 1: Q backward eq., u = 1 at the level, 0 at eps."""
    Lg = math.log(1.0 + 1.0 / abs(pi))
    h = Lg / max(1, round(Lg / h_target))
    jlo, jhi = math.floor(math.log(eps) / h), round(Lg / h)
    op = Op(log_a, -0.5, h, jlo, jhi, Delta / m)
    u = op.solve(np.zeros(op.y.size), m, b_lo=0.0, b_hi=1.0)
    return float(u[-jlo - 1])


def breach_horizon(log_a, pi, Delta, m, n_record, h_target=0.02, ymin=-10.0, ymax=10.0):
    """P(fund value <= 0 in some interval within n intervals), S_0 = 1.  Per-node killed solves (exact level)."""
    Lg = math.log(1.0 + 1.0 / abs(pi))
    s = max(1, round(Lg / h_target))
    h = Lg / s
    jlo, jhi = math.floor(ymin / h), math.ceil(ymax / h)
    ys = h * np.arange(jlo, jhi + 1)                      # all nodes; ys[0] plays the absorbing lower cut
    nodes = range(1, len(ys) - 1)
    ops = {}
    for i in nodes:                                      # start node i: domain (ys[0], ys[i] + Lg) -> interior up to i+s-1
        top = min(i + s, len(ys) - 1)
        ops[i] = (Op(log_a, -0.5, h, jlo, jlo + top, Delta / m), top)
    P = np.ones(len(ys))                                 # no-breach probability over the remaining intervals
    out = {}
    for n in range(1, max(n_record) + 1):
        newP = np.ones(len(ys))
        for i in nodes:
            op, top = ops[i]
            init = P[1:top]                              # terminal data on interior nodes 1..top-1
            hit_level = 0.0 if top == i + s else P[top]  # killed at the breach level (prob 0 of no-breach)
            u = op.solve(init, m, b_lo=1.0, b_hi=hit_level)
            newP[i] = u[i - 1]
        newP[0] = 1.0                                    # absorbed: no further breach
        newP[-1] = newP[-2]
        P = newP
        if n in n_record:
            out[n] = 1.0 - float(P[-jlo])                # node of y = 0
    return out
