"""Experiment 009: pathwise distance between claim 005's finite-grid fund and claim 001's continuous wealth.

Fine grid of F steps on [0, 1]; S simulated exactly on it (sigma = 1: Brownian motion with bridge-crossing absorption;
sigma = x^2: S = 1/|x0 + B3|).  V from log V = pi log S + pi(1-pi)/2 int sigma^2(S)/S^2 dt (trapezoid), with the
integral accruing only while the (possibly stopped) price moves; V = 0 from tau_0.
"""
import numpy as np

F = 4032 * 8


def sim_bm(rng, reps, F=F, s0=1.0):
    dt = 1.0 / F
    S = np.empty((reps, F + 1))
    S[:, 0] = s0
    s = np.full(reps, s0)
    dead = np.zeros(reps, bool)
    for j in range(F):
        nxt = s + np.sqrt(dt) * rng.standard_normal(reps)
        u = rng.random(reps)
        cross = (nxt <= 0) | ((s > 0) & (nxt > 0) & (u < np.exp(-2.0 * s * np.maximum(nxt, 0) / dt)))
        dead |= cross
        s = np.where(dead, 0.0, nxt)
        S[:, j + 1] = s
    return S


def sim_inv_bes3(rng, reps, F=F, return_X=False):
    dt = 1.0 / F
    inc = np.sqrt(dt) * rng.standard_normal((reps, F, 3))
    X = np.concatenate([np.zeros((reps, 1, 3)), np.cumsum(inc, axis=1)], axis=1)
    X[:, :, 0] += 1.0
    S = 1.0 / np.linalg.norm(X, axis=2)
    return (S, X) if return_X else S


def refine_bes3(rng, X):
    """Halve the fine step of the 3-d Brownian path (bridge midpoints) and return the refined S."""
    reps, n, _ = X.shape
    dt = 1.0 / (n - 1)
    mid = 0.5 * (X[:, 1:] + X[:, :-1]) + np.sqrt(dt / 4) * rng.standard_normal((reps, n - 1, 3))
    out = np.empty((reps, 2 * n - 1, 3))
    out[:, ::2], out[:, 1::2] = X, mid
    return 1.0 / np.linalg.norm(out, axis=2)


def stop_at(S, m):
    """Freeze S at its first fine-grid exit from (1/m, m); return stopped S and a 'moving' mask per step."""
    if m is None:
        moving = np.ones((S.shape[0], S.shape[1] - 1), bool)
        return S, moving
    out = (S <= 1.0 / m) | (S >= m)
    first = np.where(out.any(1), out.argmax(1), S.shape[1])
    idx = np.minimum(np.arange(S.shape[1])[None, :], first[:, None])
    Ss = np.take_along_axis(S, idx, axis=1)
    moving = np.arange(S.shape[1] - 1)[None, :] < first[:, None]
    return Ss, moving


def wealth_V(S, moving, pi, sigma):
    """Continuous wealth along the fine grid; V = 0 from the first zero of S."""
    with np.errstate(divide="ignore", invalid="ignore"):
        g = (1.0 / S**2) if sigma == "one" else S**2
    g = np.where(np.isfinite(g), g, np.inf)
    seg = 0.5 * (g[:, 1:] + g[:, :-1]) / (S.shape[1] - 1)
    seg = np.where(moving, seg, 0.0)
    I = np.concatenate([np.zeros((S.shape[0], 1)), np.cumsum(seg, axis=1)], axis=1)
    with np.errstate(divide="ignore", invalid="ignore"):
        logV = pi * np.log(S) + 0.5 * pi * (1.0 - pi) * I
        V = np.exp(logV)
    V = np.where(S > 0, V, 0.0)
    if pi == 1.0:
        V = np.where(S > 0, S, 0.0)
    return np.nan_to_num(V, nan=0.0, posinf=np.inf)


def fund_W(S, pi, N):
    """Claim 005 recursion (1) on the grid t_i = i/N, evaluated on every fine point."""
    K = (S.shape[1] - 1) // N
    Si = S[:, ::K]                                            # grid prices S_0..S_N
    W = np.ones((S.shape[0], N + 1))
    for i in range(N):
        ratio = np.where(Si[:, i] > 0, Si[:, i + 1] / np.where(Si[:, i] > 0, Si[:, i], 1.0), 1.0)
        W[:, i + 1] = np.where(Si[:, i] > 0, W[:, i] * ((1 - pi) + pi * ratio), W[:, i])
    i_of = np.minimum(np.arange(S.shape[1]) // K, N - 1)
    Wi, Sii = W[:, i_of], Si[:, i_of]
    with np.errstate(divide="ignore", invalid="ignore"):
        inside = np.where(Sii > 0, Wi * ((1 - pi) + pi * S / np.where(Sii > 0, Sii, 1.0)), Wi)
    inside[:, -1] = W[:, -1]
    return inside


def refine_bm(rng, S):
    """Halve the fine step on the same path (Brownian bridge midpoints; absorption kept)."""
    reps, n = S.shape
    dt = 1.0 / (n - 1)
    mid = 0.5 * (S[:, 1:] + S[:, :-1]) + np.sqrt(dt / 4) * rng.standard_normal((reps, n - 1))
    dead = (S[:, 1:] <= 0) | (mid <= 0)
    mid = np.where(dead & (S[:, :-1] <= 0), 0.0, np.maximum(mid, 0.0))
    out = np.empty((reps, 2 * n - 1))
    out[:, ::2], out[:, 1::2] = S, mid
    first0 = np.where((out <= 0).any(1), (out <= 0).argmax(1), out.shape[1])
    out = np.where(np.arange(out.shape[1])[None, :] >= first0[:, None], 0.0, out)
    return out
