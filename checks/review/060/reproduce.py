"""Reviewer's independent check of claim 060 (written before reading checks/060/*).
(a) Domination g_J <= U_J: for random parameters in Theta_J and random short positive paths, the exact Merton series
    density (truncated, plus the claim's tail bound (7) added to be conservative) against the envelope (4).
(b) Daily prices, two years, train year one, absorbed CEV catalogue p in {1/2,1,3/2} x kappa in {0.2,0.3,0.45};
    alpha = 0.1; sigma_min = 0.20. Scores: claim 055 E^drift and claim 060 E^J for intensity caps Lambda_J in
    {0, 1e-120, 1e-60, 0.1, 1} per year. Truths: GBM sigma 0.3 + compound-Poisson lognormal jumps (in class for
    Lambda_J >= lam), and CEV p = 3/2 alternatives. Also the typical log(M_J / D_G).

Rerun:  uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/060/reproduce.py
Seed:   numpy default_rng(60). Runtime about 2 minutes. Not a CI check (not check.py)."""
import numpy as np, math
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

from scipy.stats import norm, poisson
rng = np.random.default_rng(60)
def logGsup(R, Dt, Y):
    n = len(R); tau = Dt.sum(); a = R.sum() / tau; Q = ((R - a * Dt) ** 2 / Dt).sum()
    return (-(n / 2) * (math.log(2 * math.pi * Q / n) + 1) - 0.5 * np.log(Dt).sum() - np.log(Y).sum()) if Q > 0 else math.inf
def logU(R, Dt, Y, smin, Lam):
    lM = -np.sum(np.log(Y * smin * np.sqrt(2 * math.pi * Dt))); lDG = logGsup(R, Dt, Y); rho = -math.expm1(-Lam * Dt.sum()) if Lam < math.inf else 1.0
    lmin = min(lDG, lM)
    return np.logaddexp((-Lam * Dt.sum() if Lam < math.inf else -math.inf) + lmin if rho < 1 else -math.inf, math.log(rho) + lM if rho > 0 else -math.inf)
viol = 0; cases = 0
for t in range(300):
    n = int(rng.integers(2, 6)); Dt = rng.uniform(0.002, 0.1, n); smin = float(rng.uniform(0.05, 0.4)); Lam = float(rng.choice([0.0, 0.5, 5.0, 50.0]))
    a, sJ, lam, mu, eta = rng.normal(0, .2), smin * rng.uniform(1, 3), Lam * rng.uniform(0, 1), rng.normal(0, .1), rng.uniform(.01, .3)
    R = rng.normal(0, 0.3 * np.sqrt(Dt)) + (rng.random(n) < 0.2) * rng.normal(0, .2, n); Y = np.exp(np.cumsum(R))
    Kt = 60; dens = 1.0
    for j in range(n):
        k = np.arange(Kt + 1); w = poisson.pmf(k, lam * Dt[j])
        hK = np.sum(w * norm.pdf(R[j], a * Dt[j] + k * mu, np.sqrt(sJ ** 2 * Dt[j] + k * eta ** 2)))
        dens *= (hK + poisson.sf(Kt, lam * Dt[j]) / (smin * math.sqrt(2 * math.pi * Dt[j]))) / Y[j]
    cases += 1; viol += math.log(dens) > logU(R, Dt, Y, smin, Lam) + 1e-9
print(f'(a) {cases} random (theta, path) cases: g_J (series + tail bound) <= U_J violations: {viol}')

M = 10000; SMIN = 0.20; CAPS = [0.0, 1e-120, 1e-60, 0.1, 1.0]
def scores(S):
    full = np.c_[np.ones(len(S)), S]
    tr = np.array([logK(p, k, D, full[:, :K], full[:, 1:K + 1]).sum(1) for p, k in CAT]); sel = np.argmax(tr, axis=0)
    ev = np.array([logK(p, k, D, full[:, K:-1], full[:, K + 1:]).sum(1) for p, k in CAT]); lG = ev[sel, np.arange(len(S))]; lG0 = ev[NULL].max(axis=0)
    Dt = np.full(N - K, D); out = {c: np.zeros(len(S)) for c in ['drift'] + CAPS}; gap = []
    for i in range(len(S)):
        Y = full[i, K + 1:]; R = np.log(Y / full[i, K:-1]); lDG = logGsup(R, Dt, Y)
        lM = -np.sum(np.log(Y * SMIN * np.sqrt(2 * math.pi * Dt))); gap.append(lM - lDG)
        out['drift'][i] = math.exp(min(lG[i] - max(lG0[i], lDG), 700))
        for c in CAPS: out[c][i] = math.exp(min(lG[i] - max(lG0[i], lDG, logU(R, Dt, Y, SMIN, c)), 700))
    return out, np.array(gap)
def gbm_jumps(lam, mJ=-0.05, sJ=0.10, s=0.3, b=0.05):
    nj = rng.poisson(lam * D, (M, N)); L = mJ * nj + sJ * np.sqrt(nj) * rng.standard_normal((M, N))
    return np.exp(np.cumsum((b - s * s / 2) * D + s * math.sqrt(D) * rng.standard_normal((M, N)) + L, axis=1))
def cev15(k):
    cc = k * 0.5; B = np.zeros((M, 4)); B[:, 0] = 1 / cc; out = np.empty((M, N))
    for j in range(N): B += math.sqrt(D) * rng.standard_normal((M, 4)); out[:, j] = (cc * np.linalg.norm(B, axis=1)) ** -2
    return out
print(f'(b) sigma_min = {SMIN}; mean / P(>1/alpha) for E^drift (055) | E^J at Lambda_J = ' + ' | '.join(str(c) for c in CAPS))
for label, S in [('GBM 0.3, no jumps', gbm_jumps(0.0)), ('GBM 0.3 + jumps lam=1/yr', gbm_jumps(1.0)), ('GBM 0.3 + jumps lam=5/yr', gbm_jumps(5.0)),
                 ('CEV p=1.5 k=0.3 (alt)', cev15(0.3)), ('CEV p=1.5 k=0.45 (alt)', cev15(0.45))]:
    o, gap = scores(S); f = lambda x: f'{x.mean():.3g}/{np.mean(x > 1 / AL):.4f}'
    print(f'   {label:28s} ' + ' | '.join(f(o[c]) for c in ['drift'] + CAPS) + f'   median log(M_J/D_G) {np.median(gap):.1f}', flush=True)
