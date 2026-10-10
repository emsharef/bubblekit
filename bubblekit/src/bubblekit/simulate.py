"""Synthetic price paths for testing and comparing bubble detectors.

All functions take a numpy Generator and return prices (not returns). Daily units use 252 sessions per year.
Strict-local-martingale ("bubble") laws: CEV with p > 1 (:func:`cev`), the market-scale level model with beta > 0
(:func:`market_and_stock`), CEV under stochastic volatility (:func:`market_and_stock_sv` with p > 1) and the
intraday session model with beta > 0 (:func:`intraday_sessions`). Explosive-root bubbles in the time-series sense
are in :func:`bubblekit.explosive.psy.simulate_evans`.
"""
from __future__ import annotations

import math

import numpy as np

from .slm.cev import sample_cev

__all__ = [
    "gbm", "cev", "heston", "merton", "regime_switching", "market_and_stock", "market_and_stock_sv",
    "intraday_sessions", "diurnal_clock",
]

DT = 1.0 / 252


def _prices(logret, s0):
    lr = np.atleast_2d(logret)
    out = s0 * np.exp(np.concatenate([np.zeros((lr.shape[0], 1)), np.cumsum(lr, axis=1)], axis=1))
    return out[0] if np.ndim(logret) == 1 else out


def gbm(rng, n: int, sigma: float = 0.3, mu: float = 0.0, dt: float = DT, s0: float = 1.0, n_paths: int | None = None):
    """Geometric Brownian motion (a true martingale when mu = 0): n steps, shape (n + 1,) or (n_paths, n + 1)."""
    shape = (n,) if n_paths is None else (n_paths, n)
    z = rng.standard_normal(shape)
    return _prices((mu - 0.5 * sigma ** 2) * dt + sigma * math.sqrt(dt) * z, s0)


def cev(rng, n: int, p: float, kappa: float, dt: float = DT, n_paths: int | None = None):
    """Exact absorbed CEV dS = kappa S^p dW from S_0 = 1. Strict local martingale (bubble) iff p > 1."""
    out = sample_cev(rng, p, kappa, 1 if n_paths is None else n_paths, n, dt)
    return out[0] if n_paths is None else out


def heston(rng, n: int, v0: float = 0.09, kappa: float = 2.0, theta: float = 0.09, xi: float = 0.5,
           rho: float = -0.7, dt: float = DT, substeps: int = 10, s0: float = 1.0):
    """Heston stochastic volatility, zero drift (full-truncation Euler on log price). Shape (n + 1,)."""
    h = dt / substeps
    v, ls = v0, 0.0
    out = np.empty(n + 1)
    out[0] = s0
    for t in range(n):
        for _ in range(substeps):
            zv, zw = rng.standard_normal(2)
            dw = rho * zv + math.sqrt(1 - rho * rho) * zw
            vp = max(v, 0.0)
            ls += -0.5 * vp * h + math.sqrt(vp * h) * dw
            v += kappa * (theta - vp) * h + xi * math.sqrt(vp * h) * zv
        out[t + 1] = s0 * math.exp(ls)
    return out


def merton(rng, n: int, sigma: float = 0.25, lam: float = 5.0, jump_mean: float = -0.05, jump_sd: float = 0.08,
           dt: float = DT, s0: float = 1.0):
    """Merton jump-diffusion with compensated drift (a true martingale). Shape (n + 1,)."""
    k = math.exp(jump_mean + 0.5 * jump_sd ** 2) - 1
    nj = rng.poisson(lam * dt, n)
    jumps = np.array([rng.normal(jump_mean, jump_sd, j).sum() for j in nj])
    lr = (-0.5 * sigma ** 2 - lam * k) * dt + sigma * math.sqrt(dt) * rng.standard_normal(n) + jumps
    return _prices(lr, s0)


def regime_switching(rng, n: int, sigmas=(0.15, 0.45), stay: float = 0.95, dt: float = DT, s0: float = 1.0):
    """Two-state Markov-switching volatility (true martingale): returns (prices, states)."""
    sig = np.asarray(sigmas, float)
    st = np.empty(n, int)
    s = int(rng.integers(sig.size))
    for t in range(n):
        if rng.random() > stay:
            s = 1 - s if sig.size == 2 else int(rng.integers(sig.size))
        st[t] = s
    sd = sig[st]
    lr = -0.5 * sd ** 2 * dt + sd * math.sqrt(dt) * rng.standard_normal(n)
    return _prices(lr, s0), st


def _market_logret(rng, n):
    """Market with AR(1) log variance (0.95, s.d. 0.15, mean log(0.04/252)) and Gaussian returns."""
    m = math.log(0.04 / 252)
    lv = m + 0.15 / math.sqrt(1 - 0.95 ** 2) * rng.standard_normal()
    out = np.empty(n)
    for t in range(n):
        lv = m + 0.95 * (lv - m) + 0.15 * rng.standard_normal()
        v = math.exp(lv)
        out[t] = -0.5 * v + math.sqrt(v) * rng.standard_normal()
    return out


def market_and_stock(rng, beta: float, n_train: int = 252, n_score: int = 252, nu: float = 6, g: int = 1,
                     persistent: bool = False, warm: int = 20, max_abs_log: float = 5.0):
    """Aligned (stock, market) prices for :func:`bubblekit.slm.daily.daily_score` under its own model.

    Stock variance is 2.25 * (lagged market scale) * exp(beta * x) with x the log price relative to the scored
    window's first close (beta acts only in the scored window unless ``persistent``); g = 0 gives a constant
    background. beta > 0 is the bubble direction. Returns None if the path leaves exp(±max_abs_log).
    Both arrays have length warm + n_train + n_score + 1.
    """
    nm = warm + n_train + n_score
    mret = _market_logret(rng, nm)
    c = np.concatenate([[0.0], np.cumsum(mret * mret)])
    M = np.full(nm, np.nan)
    M[warm:] = (c[warm:nm] - c[:nm - warm]) / warm
    ns = n_train + n_score
    z = rng.standard_t(nu, ns) * math.sqrt((nu - 2) / nu)
    r = np.empty(ns)
    x_tr = x_sc = 0.0
    for i in range(ns):
        A = 2.25 * M[warm + i] if g == 1 else 0.09 / 252
        if i < n_train:
            b, x = (beta, x_tr) if persistent else (0.0, 0.0)
        else:
            b, x = (beta, x_tr) if persistent else (beta, x_sc)
        r[i] = math.sqrt(A * math.exp(b * x)) * z[i]
        x_tr += r[i]
        if i >= n_train:
            x_sc += r[i]
        if abs(x_tr) > max_abs_log:
            return None
    market = _prices(mret, 100.0)
    warm_r = math.sqrt(0.09 / 252) * rng.standard_normal(warm)  # warm-up dates are unused by the daily statistic
    stock = _prices(np.concatenate([warm_r, r]), 100.0)
    return stock, market


def market_and_stock_sv(rng, p: float, rho: float, market_driven: bool = True, n_train: int = 252,
                        n_score: int = 252, warm: int = 20, substeps: int = 10, max_abs_log: float = 5.0):
    """CEV-type level effect under stochastic volatility, with a market.

    dS/S = (S/S_L)^(p-1) sqrt(v) dW after the scored window starts (p = 1 before), dv = 2(0.09 - v)dt +
    0.5 sqrt(v) dZ, corr(W, Z) = rho. ``market_driven`` makes the market share the stock's variance factor;
    otherwise the market has its own. Returns aligned (stock, market) prices or None.
    """
    nm = warm + n_train + n_score
    h = DT / substeps
    vs = vm = 0.09
    ls = lm = 0.0
    lL = None
    sp, mp = np.empty(nm + 1), np.empty(nm + 1)
    sp[0] = mp[0] = 100.0
    for t in range(nm):
        launched = t >= warm + n_train
        if launched and lL is None:
            lL = ls
        for _ in range(substeps):
            zv, zw, zm, zmv = rng.standard_normal(4)
            dws = rho * zv + math.sqrt(1 - rho * rho) * zw
            v_s = max(vs, 0.0)
            lev = math.exp((p - 1) * (ls - lL)) if (launched and p != 1) else 1.0
            s2 = lev * lev * v_s
            ls += -0.5 * s2 * h + math.sqrt(s2 * h) * dws
            vs += 2.0 * (0.09 - v_s) * h + 0.5 * math.sqrt(v_s * h) * zv
            if market_driven:
                v_m, dwm = v_s, -0.7 * zv + math.sqrt(0.51) * zm
            else:
                v_m = max(vm, 0.0)
                dwm = -0.7 * zmv + math.sqrt(0.51) * zm
                vm += 2.0 * (0.09 - v_m) * h + 0.5 * math.sqrt(v_m * h) * zmv
            lm += -0.5 * v_m * h + math.sqrt(v_m * h) * dwm
            if abs(ls) > max_abs_log or not math.isfinite(ls):
                return None
        sp[t + 1], mp[t + 1] = 100.0 * math.exp(ls), 100.0 * math.exp(lm)
    return sp, mp


def diurnal_clock(n_slots: int = 77, depth: float = 1.5, floor: float = 0.25) -> np.ndarray:
    """U-shaped intraday variance clock for slots 1..n_slots, normalized to mean one (index 0 is unused = 1)."""
    u = np.linspace(-1, 1, n_slots)
    c = floor + depth * u ** 2
    out = np.ones(n_slots + 1)
    out[1:] = c / c.mean()
    return out


def intraday_sessions(rng, n_sessions: int, beta: float = 0.0, sigma: float = 0.3, nu: float = 6,
                      clock: np.ndarray | None = None, s0: float = 100.0):
    """Regular-session 5-minute closes, shape (n_sessions, 78), for :func:`bubblekit.slm.intraday.intraday_monitor`.

    Slot-j variance is sigma²/(252·77) · clock_j · (S_{j-1}/s_d)^beta with s_d the session's first close
    (beta is the variance exponent; beta > 0 is the bubble direction). Overnight moves are Gaussian with the
    daily variance of one slot.
    """
    clock = diurnal_clock() if clock is None else clock
    base = sigma ** 2 / (252 * 77)
    out = np.empty((n_sessions, 78))
    price = s0
    for d in range(n_sessions):
        price *= math.exp(math.sqrt(base) * rng.standard_normal())
        out[d, 0] = price
        open_ = price
        for j in range(1, 78):
            v = base * clock[j] * (price / open_) ** beta
            price *= math.exp(math.sqrt(v) * rng.standard_t(nu) * math.sqrt((nu - 2) / nu))
            out[d, j] = price
    return out
