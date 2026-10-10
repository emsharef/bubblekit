"""Reviewer's independent check of claim 059 (written before reading checks/059/*).
(a) Single-switch profile (5) vs direct 4-parameter Nelder-Mead at every cut of small random paths; singleton cut
    (c = 1) gives an unbounded supremum.
(b) Daily prices, two years, train year one (n_e = 252), absorbed CEV catalogue p in {1/2,1,3/2} x kappa in
    {0.2,0.3,0.45}; alpha = 0.1. Scores: claim 055 E^drift and claim 059 E^sw with cut sets K_month = {21,42,...,231}
    and K_all = {2,...,250}. Truths: GBM with a volatility switch 0.25 -> 0.40 at cut 126 (in both K), at cut 130 (in
    K_all only), and at a uniformly random cut in K_month (latent mixture); a constant GBM; CEV p = 3/2 alternatives.

Rerun:  uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/059/reproduce.py
Seed:   numpy default_rng(59). Runtime about 3 minutes. Not a CI check (not check.py)."""

"""Reviewer's independent check of claim 026 (written before reading checks/026/check.py).
(a) Exact rationals: random finite reference laws G with scores E satisfying int E dG <= 1, random contamination
    laws J and p <= rho; checks (2), the adjusted threshold, (3)'s clipped moment and (4); plus the dependent-coupling
    fixture (clipped mean 1 + c rho > 1 + (c-1) rho).
(b) Price Monte Carlo: daily prices for two years, train year one; claim 055's E^drift with the full absorbed CEV
    catalogue p in {1/2,1,3/2} x kappa in {0.2,0.3,0.45}. Truth: physical GBM (b=0.05, sigma=0.3, a pricing null under
    claim 055's link) plus compound-Poisson log jumps with intensity lam per year, independent of the diffusion, so
    (1) holds with rho = 1 - exp(-lam * tau_e) (part 3). Reports actual raw false alarms against bound (2), raw mean,
    and the mean of the clipped score (3) (c = 50).

Rerun:  uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/026/reproduce.py
Seed:   numpy default_rng(26) for (b), Python random.seed(26) for (a). Runtime about 2 minutes. Not a CI check."""
from fractions import Fraction as Fr
import random, math
import numpy as np
from scipy.special import ive, gammaincc

def logf(p, D, x, y, k):
    if p == 1:
        v = k * k * D; return -(np.log(y / x) + v / 2) ** 2 / (2 * v) - np.log(y * np.sqrt(2 * np.pi * v))
    h = abs(p - 1); nu = 1 / (2 * h); v = k * k * h * h * D
    A, B = x ** (2 - 2 * p), y ** (2 - 2 * p); z = x ** (1 - p) * y ** (1 - p) / v
    with np.errstate(divide='ignore'):
        return 0.5 * np.log(x) + (0.5 - 2 * p) * np.log(y) - np.log(k * k * h * D) - (np.sqrt(A) - np.sqrt(B)) ** 2 / (2 * v) + np.log(ive(nu, z))
def logK(p, k, D, x, y):
    out = np.full(np.broadcast(x, y).shape, -np.inf); pos = (x > 0) & (y > 0); out[pos] = logf(p, D, x[pos], y[pos], k)
    if p < 1:
        a0 = (x > 0) & (y == 0); hh = 1 - p; v = k * k * hh * hh * D
        with np.errstate(divide='ignore'): out[a0] = np.log(gammaincc(1 / (2 * hh), x[a0] ** (2 - 2 * p) / (2 * v)))
    out[(x == 0) & (y == 0)] = 0.0
    return out
CAT = [(p, k) for p in (0.5, 1.0, 1.5) for k in (0.2, 0.3, 0.45)]; NULL = [i for i, (p, k) in enumerate(CAT) if p <= 1]
N, K, D, AL = 504, 252, 1 / 252, 0.1
def Edrift(S):
    full = np.c_[np.ones(len(S)), S]; M = len(S)
    tr = np.array([logK(p, k, D, full[:, :K], full[:, 1:K + 1]).sum(1) for p, k in CAT]); sel = np.argmax(tr, axis=0)
    ev = np.array([logK(p, k, D, full[:, K:-1], full[:, K + 1:]).sum(1) for p, k in CAT]); lG = ev[sel, np.arange(M)]
    lG0 = ev[NULL].max(axis=0); R = np.log(full[:, K + 1:] / full[:, K:-1]); n_e = N - K; tau = n_e * D
    a = R.sum(1) / tau; Q = ((R - a[:, None] * D) ** 2).sum(1) / D
    lDG = np.where(Q > 0, -(n_e / 2) * (np.log(2 * np.pi * Q / n_e) + 1) - 0.5 * n_e * math.log(D) - np.log(full[:, K + 1:]).sum(1), np.inf)
    lD = np.maximum(lG0, lDG)
    return np.where(np.isfinite(lG) & np.isfinite(lD), np.exp(np.minimum(lG - lD, 700)), 0.0)


from scipy.optimize import minimize
rng = np.random.default_rng(59)
def seg_logmax(R, Dt):
    n = len(R); tau = Dt.sum(); a = R.sum() / tau; Q = ((R - a * Dt) ** 2 / Dt).sum()
    return (-(n / 2) * (math.log(2 * math.pi * Q / n) + 1) - 0.5 * np.log(Dt).sum()) if Q > 0 else math.inf
worst = 0.0
for t in range(10):
    n = int(rng.integers(4, 9)); Dt = rng.uniform(0.002, 0.05, n); R = rng.normal(0, 0.3 * np.sqrt(Dt))
    for c in range(2, n - 1):
        f = seg_logmax(R[:c], Dt[:c]) + seg_logmax(R[c:], Dt[c:])
        def nll(th):
            bL, lkL, bR, lkR = th; wL, wR = math.exp(2 * lkL), math.exp(2 * lkR)
            m = np.where(np.arange(n) < c, (bL - wL / 2) * Dt, (bR - wR / 2) * Dt); v = np.where(np.arange(n) < c, wL * Dt, wR * Dt)
            return -np.sum(-(R - m) ** 2 / (2 * v) - 0.5 * np.log(2 * math.pi * v))
        best = min(minimize(nll, x0, method='Nelder-Mead', options={'xatol': 1e-12, 'fatol': 1e-13, 'maxiter': 60000}).fun
                   for x0 in ([0, -1, 0, -1], [1, -2, -1, -0.5], [0, 0, 0, -2]))
        worst = max(worst, abs(-best - f) / max(1, abs(f)))
print(f'(a) switch profile vs 4-parameter Nelder-Mead (returns-only part): max rel diff {worst:.2e}; singleton segment: {seg_logmax(np.array([0.01]), np.array([0.01]))}')

M = 10000; n_e = N - K; Kmonth = list(range(21, 252, 21)); Kall = list(range(2, n_e - 1))
def Esw_and_drift(S, cuts_list):
    full = np.c_[np.ones(len(S)), S]
    tr = np.array([logK(p, k, D, full[:, :K], full[:, 1:K + 1]).sum(1) for p, k in CAT]); sel = np.argmax(tr, axis=0)
    ev = np.array([logK(p, k, D, full[:, K:-1], full[:, K + 1:]).sum(1) for p, k in CAT]); lG = ev[sel, np.arange(len(S))]
    lG0 = ev[NULL].max(axis=0); P = full[:, K:]; R = np.log(P[:, 1:] / P[:, :-1]); ly = np.log(P[:, 1:]).sum(1)
    cR = np.c_[np.zeros(len(S)), np.cumsum(R, 1)]; cR2 = np.c_[np.zeros(len(S)), np.cumsum(R * R, 1)]
    def lmax(lo, hi):                       # segment increments lo..hi-1, constant Delta = D
        nn = hi - lo; s = cR[:, hi] - cR[:, lo]; s2 = cR2[:, hi] - cR2[:, lo]; Q = (s2 - s * s / nn) / D
        with np.errstate(divide='ignore', invalid='ignore'):
            return np.where(Q > 0, -(nn / 2) * (np.log(2 * math.pi * Q / nn) + 1) - 0.5 * nn * math.log(D), np.inf)
    lDG = lmax(0, n_e) - ly
    out = {'drift': np.where(np.isfinite(np.maximum(lG0, lDG)), np.exp(np.minimum(lG - np.maximum(lG0, lDG), 700)), 0.0)}
    for name, cuts in cuts_list:
        lsw = np.max(np.array([lmax(0, c) + lmax(c, n_e) for c in cuts]), axis=0) - ly
        lD = np.maximum(lG0, lsw); out[name] = np.where(np.isfinite(lD), np.exp(np.minimum(lG - lD, 700)), 0.0)
    return out
def gbm_switch(c_of_path, s1=0.25, s2=0.40, b=0.05):
    j = np.arange(N)[None, :]; sig = np.where(j < K + c_of_path[:, None], s1, s2)
    return np.exp(np.cumsum((b - sig ** 2 / 2) * D + sig * math.sqrt(D) * rng.standard_normal((M, N)), axis=1))
def cev15(k):
    cc = k * 0.5; B = np.zeros((M, 4)); B[:, 0] = 1 / cc; out = np.empty((M, N))
    for j in range(N): B += math.sqrt(D) * rng.standard_normal((M, 4)); out[:, j] = (cc * np.linalg.norm(B, axis=1)) ** -2
    return out
cases = [('switch 0.25->0.40 at cut 126 (in K_month, K_all)', gbm_switch(np.full(M, 126))),
         ('switch at cut 130 (in K_all only)', gbm_switch(np.full(M, 130))),
         ('switch at a random cut in K_month (latent mixture)', gbm_switch(rng.choice(Kmonth, M))),
         ('constant GBM 0.30', gbm_switch(np.zeros(M, int), 0.30, 0.30)),
         ('CEV p=1.5 k=0.3 (alt)', cev15(0.3)), ('CEV p=1.5 k=0.45 (alt)', cev15(0.45))]
print('(b) mean / P(score > 1/alpha), alpha = 0.1:   claim 055 E^drift | 059 K_month | 059 K_all')
for label, S in cases:
    o = Esw_and_drift(S, [('Km', Kmonth), ('Ka', Kall)]); ok = bool(np.all(o['Km'] <= o['drift'] * (1 + 1e-12) + 1e-300) and np.all(o['Ka'] <= o['Km'] * (1 + 1e-12) + 1e-300))
    f = lambda x: f'{x.mean():.3g} / {np.mean(x > 1 / AL):.4f}'
    print(f'   {label:52s} {f(o["drift"]):>18s} | {f(o["Km"]):>16s} | {f(o["Ka"]):>16s}   ordering (7) ok {ok}', flush=True)
