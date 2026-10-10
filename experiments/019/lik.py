"""Claim 052's split-likelihood catalogue test, vectorized over paths (float64), with a time vector.

Catalogue, split, alpha and blocks: experiments/019-d5-claim052-size-power.md, Deviation 1 (mathb's specification).
"""
import importlib.util
import os

import numpy as np

CATALOGUE = [(1, 0.20), (1, 0.30), (1, 0.45), (2, 0.20), (2, 0.30), (2, 0.45)]
NULL = [i for i, (p, _) in enumerate(CATALOGUE) if p == 1]
R, RATIO = np.exp(-0.15), np.exp(0.15)
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def log_f(p, kappa, dt, x, y):
    """Log transition density in y (claim 052 (1)); p = 2 in the stable factored form. dt may be an array."""
    v = kappa * kappa * dt
    if p == 1:
        return -np.log(y) - 0.5 * np.log(2 * np.pi * v) - (np.log(y / x) + v / 2) ** 2 / (2 * v)
    gap = 2.0 / (x * y * v)
    return (np.log(x) - 3 * np.log(y) - 0.5 * np.log(2 * np.pi * v) - (1 / y - 1 / x) ** 2 / (2 * v)
            + np.log(-np.expm1(-gap)))


def blocks(p, kappa):
    if p == 1:
        b = np.log(RATIO) / kappa ** 2
        return b, b
    b1 = (1 - RATIO ** -2) / (2 * kappa ** 2 * R ** 2)
    return b1, b1 / RATIO ** 2


B = np.array([blocks(p, k) for p, k in CATALOGUE])        # (C, 2)


def scores(S, times):
    """S: (P, N + 1) prices at `times` (years, times[0] = 0). Split k = N // 2. Returns sel, logT (P, C), margin."""
    N = S.shape[1] - 1
    k = N // 2
    dt = np.diff(times)[None, :]
    x, y = S[:, :-1], S[:, 1:]
    train = np.empty((S.shape[0], len(CATALOGUE)))
    ev = np.empty_like(train)
    for c, (p, kap) in enumerate(CATALOGUE):
        lf = log_f(p, kap, dt, x, y)
        train[:, c] = lf[:, :k].sum(1)
        ev[:, c] = lf[:, k:].sum(1)
    sel = np.argmax(train, axis=1)                              # first maximum: the catalogue's tie order
    srt = np.sort(train, axis=1)
    margin = srt[:, -1] - srt[:, -2]
    logT = ev[np.arange(S.shape[0]), sel][:, None] - ev
    return sel, logT, margin


def decide(logT, alpha, truth=None):
    """Claim 051/052 outputs at one alpha, all in log space."""
    logE = logT[:, NULL].min(1)
    thr = -np.log(alpha)
    inC = logT <= thr
    L = np.where(inC[:, :, None], B[None, :, :], np.inf).min(1)       # (P, 2)
    U = np.where(inC[:, :, None], B[None, :, :], -np.inf).max(1)
    out = {"reject": logE > thr, "band_reject": U[:, 1] < L[:, 0], "ambiguous": np.abs(logE - thr) < 1e-6}
    if truth is not None:
        out["noncover_param"] = ~inC[:, truth]
        b = B[truth]
        out["noncover_joint"] = ~((L[:, 0] <= b[0]) & (b[0] <= U[:, 0]) & (L[:, 1] <= b[1]) & (b[1] <= U[:, 1]))
    return out


def crosscheck_fast(S, times, logT):
    """Max |Delta log T| against mathb's float64 fast.py, and the selections it makes."""
    fast = _load("fast052", "checks/d3-price-likelihood/fast.py")
    sel_f, logT_f = fast.batch_split_scores(CATALOGUE, times, S, (S.shape[1] - 1) // 2)
    return np.asarray(sel_f), np.asarray(logT_f, float)


def crosscheck_mp(S_row, times):
    """High-precision (mpmath) selection and log T for one path, via mathb's kernels.split_scores."""
    kern = _load("kern052", "checks/d3-price-likelihood/kernels.py")
    sel, lt = kern.split_scores(CATALOGUE, list(times), list(S_row), (len(S_row) - 1) // 2)
    return int(sel), np.array([float(v) for v in lt])
