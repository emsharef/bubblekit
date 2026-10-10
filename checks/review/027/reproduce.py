"""Reviewer's independent check of claim 027 (written before reading checks/027/*).
(a) Monte Carlo TV between a variable-parameter Gaussian return vector and a constant reference (likelihood-ratio sign),
    against the affinity bound (3), and the bound (3) against the uniform envelope (7).
(b) Price Monte Carlo of claim 055's E^drift (daily, two years, train year one, absorbed CEV catalogue
    p in {1/2,1,3/2} x kappa in {0.2,0.3,0.45}), alpha = 0.1, under: a latent two-point mixture of admitted GBMs
    (zero budget); a within-window volatility switch; a smooth deterministic volatility path; and a leverage-correlated
    stochastic volatility (outside the claim's representation). Reports raw mean, false alarms and the budget (3)/(7).

Rerun:  uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/027/reproduce.py
Seed:   numpy default_rng(27). Runtime about 2 minutes. Not a CI check (not check.py)."""
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

from scipy.stats import norm
rng = np.random.default_rng(27)
def affinity(b, s, bref, k, Dt):
    return np.prod(np.sqrt(2 * s * k / (s * s + k * k))) * math.exp(-np.sum(Dt * (b - bref + (k * k - s * s) / 2) ** 2 / (4 * (s * s + k * k))))
def envelope(n, tau, h, Bp, smin, smax):
    L = n * math.log(math.cosh(h)) + tau * (Bp / (2 * smin) + smax * math.sinh(h) / 2) ** 2; return math.sqrt(1 - math.exp(-L))
worst = 0.0; worst_env = 0.0
for t in range(12):
    n = int(rng.choice([5, 20, 60])); Dt = np.full(n, 1 / 252); k = float(rng.uniform(.2, .4)); bref = float(rng.uniform(-.1, .1))
    s = k * np.exp(rng.uniform(-.15, .15, n)); b = bref + rng.uniform(-.1, .1, n)
    A = affinity(b, s, bref, k, Dt); eps = math.sqrt(1 - A * A)
    Mc = 200000; mh, sh = (b - s * s / 2) * Dt, s * np.sqrt(Dt); mg, sg = (bref - k * k / 2) * Dt, k * np.sqrt(Dt)
    llr = lambda R: (norm.logpdf(R, mh, sh) - norm.logpdf(R, mg, sg)).sum(1)
    Rh = rng.normal(mh, sh, (Mc, n)); Rg = rng.normal(mg, sg, (Mc, n)); tv = np.mean(llr(Rh) > 0) - np.mean(llr(Rg) > 0)
    worst = max(worst, tv - eps)
    h = float(np.max(np.abs(np.log(s / k)))); Bp = float(np.max(np.abs(b - bref))); env = envelope(n, Dt.sum(), h, Bp, min(s.min(), k), max(s.max(), k))
    worst_env = max(worst_env, eps - env)
print(f'(a) 12 variable-parameter vectors: max (MC TV - eps_(3)) = {worst:+.4f} (<= 0 up to MC error ~0.003); max (eps_(3) - envelope(7)) = {worst_env:+.2e} (<= 0)')

CAT = [(p, k) for p in (0.5, 1.0, 1.5) for k in (0.2, 0.3, 0.45)]; NULL = [i for i, (p, k) in enumerate(CAT) if p <= 1]
M = 10000; n_e = N - K
def paths_sigma(sig, b=0.05):        # sig: (M, N) per-step vol, independent Gaussian returns given sig
    return np.exp(np.cumsum((b - sig ** 2 / 2) * D + sig * math.sqrt(D) * rng.standard_normal((M, N)), axis=1))
cases = []
z = rng.random(M) < 0.5; sig = np.where(z[:, None], 0.25, 0.40) * np.ones((M, N)); cases.append(('latent mix of GBM 0.25 / 0.40 (zero budget)', paths_sigma(sig), 0.0))
sig = np.ones((M, N)) * 0.25; sig[:, K + (N - K) // 2:] = 0.40
e_sw = 1 - affinity(np.full(n_e, .05), sig[0, K:], .05, math.sqrt((0.25 ** 2 + 0.40 ** 2) / 2), np.full(n_e, D)) ** 2
cases.append(('switch 0.25 -> 0.40 mid-evaluation', paths_sigma(sig), math.sqrt(max(e_sw, 0))))
tgrid = np.arange(N) * D; sig = (0.3 + 0.05 * np.sin(2 * math.pi * tgrid))[None, :] * np.ones((M, 1))
best = min(math.sqrt(1 - affinity(np.full(n_e, .05), sig[0, K:], .05, kk, np.full(n_e, D)) ** 2) for kk in np.linspace(.25, .35, 101))
cases.append(('smooth vol 0.30 +- 0.05 sin', paths_sigma(sig), best))
v = np.full(M, 0.09); S = np.empty((M, N)); x = np.zeros(M)                       # Heston-type, leverage rho = -0.7
for j in range(N):
    z1 = rng.standard_normal(M); z2 = -0.7 * z1 + math.sqrt(1 - 0.49) * rng.standard_normal(M)
    x += (0.05 - v / 2) * D + np.sqrt(v * D) * z1; v = np.abs(v + 3.0 * (0.09 - v) * D + 0.4 * np.sqrt(v * D) * z2); S[:, j] = np.exp(x)
cases.append(('Heston-type SV, leverage -0.7 (outside (1)-(2))', S, float('nan')))
print(f'(b) claim 055 E^drift, alpha = {AL}: mean / false alarm; budget = best constant-reference eps (3) where defined')
for label, S, eps in cases:
    E = Edrift(S)
    print(f'   {label:48s} mean {E.mean():.3g}  P(>1/a) {np.mean(E > 1 / AL):.4f}  eps {eps:.3f}  size bound {min(1, AL + eps) if eps == eps else float("nan"):.3f}', flush=True)
