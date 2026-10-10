"""Reviewer's independent check of claim 028 (written before reading checks/028/*).
(a) Exact one-step TV between rounded labels started at the exact endpoint x_h e^a and at x_h, worst |a| = h/2, against
    the budget (2); and Monte Carlo TV for rounded 3-step blocks (empirical label histograms).
(b) Size and moment of the restarted-cell score with n = 1 evaluation step: true null GBM (b, kappa) = (0, 0.3), exact
    daily training prices rounded at h, so the last exact endpoint has its true (non-uniform) posterior in the cell;
    catalogue Gamma = {(0, 0.3), (0, 0.45)}; normalized rounded forecast q = restarted cell law of (0, 0.2). Reports
    P(E^restart > 1/alpha) against alpha + eps and the mean of the capped score (4).
(c) The budget (2) at realistic ticks.

Rerun:  uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/028/reproduce.py
Seed:   numpy default_rng(28). Runtime about 1 minute. Not a CI check (not check.py)."""
import numpy as np, math
from scipy.stats import norm
rng = np.random.default_rng(28)
def eps(h, k, D): return math.sqrt(1 - math.exp(-h * h / (16 * k * k * D)))
print('(a) one-step exact TV of rounded labels at worst displacement a = h/2 vs budget (2):')
for h, k, D in [(0.02, 0.3, 1 / 252), (0.01, 0.2, 1 / 252), (0.002, 0.3, 1 / 19656), (0.05, 0.3, 1 / 252)]:
    s = k * math.sqrt(D); mu = -k * k / 2 * D; a = h / 2
    edges = h * (np.arange(-400, 401) - 0.5)        # labels relative to the start cell: R + a in [h(v-1/2), h(v+1/2))
    p1 = np.diff(norm.cdf(edges, mu - a, s)); p0 = np.diff(norm.cdf(edges, mu, s))
    print(f'    h={h} kappa={k} Delta={D:.2e}: TV {0.5 * np.abs(p1 - p0).sum():.4f} <= eps {eps(h, k, D):.4f}')
h, k, D, n, Mc = 0.02, 0.3, 1 / 252, 3, 400000
for a in (h / 2, -h / 2, 0.3 * h):
    R = rng.normal(-k * k / 2 * D, k * math.sqrt(D), (Mc, n)); cs0 = np.cumsum(R, 1); cs1 = cs0.copy(); cs1 += a
    lab = lambda c: np.floor(c / h + 0.5).astype(np.int64)
    L0 = lab(cs0); L1 = lab(np.cumsum(rng.normal(-k * k / 2 * D, k * math.sqrt(D), (Mc, n)), 1) + a)
    key = lambda L: L[:, 0] * 10 ** 6 + L[:, 1] * 10 ** 3 + L[:, 2]
    u0, c0 = np.unique(key(L0), return_counts=True); u1, c1 = np.unique(key(L1), return_counts=True)
    allk = np.union1d(u0, u1); f0 = dict(zip(u0, c0 / Mc)); f1 = dict(zip(u1, c1 / Mc))
    tv = 0.5 * sum(abs(f0.get(x, 0) - f1.get(x, 0)) for x in allk)
    print(f'    3-step rounded block, a = {a:+.4f}: MC TV {tv:.4f} (MC bias ~ +0.01) <= eps {eps(h, k, D):.4f}')

# (b) size/moment with genuine latent uncertainty; n = 1
GAM = [(0.0, 0.30), (0.0, 0.45)]; QK = 0.20; AL = 0.1; c = 20.0
M = 200000; Ntr = 252
Xtr = np.exp(np.cumsum(rng.normal(-0.045 * D, 0.3 * math.sqrt(D), (M, Ntr)), 1))[:, -1]   # exact training endpoint
z = np.floor(np.log(Xtr) / h + 0.5); xh = np.exp(h * z)
R1 = rng.normal(-0.045 * D, 0.3 * math.sqrt(D), M); v = np.floor((np.log(Xtr) + R1) / h + 0.5)        # true future label
def g_restart(v, z, b, kk):
    lo, hi = h * (v - z - 0.5), h * (v - z + 0.5); m, s = (b - kk * kk / 2) * D, kk * math.sqrt(D)
    return norm.cdf(hi, m, s) - norm.cdf(lo, m, s)
den = np.maximum.reduce([g_restart(v, z, b, kk) for b, kk in GAM]); q = g_restart(v, z, 0.0, QK)
E = q / den; e_ = eps(h, min(kk for _, kk in GAM), D)
print(f'(b) n=1, h={h}: eps = {e_:.4f}; P(E^restart > 1/alpha) = {np.mean(E > 1 / AL):.4f} <= alpha + eps = {AL + e_:.4f}; '
      f'raw mean {E.mean():.3f}; capped (4) mean (c={c:.0f}) {np.mean(np.minimum(E, c) / (1 + c * e_)):.4f} <= 1')
offset = np.log(Xtr) - h * z
print(f'    latent displacement within the cell: mean {offset.mean():+.5f}, sd {offset.std():.5f} (uniform would be sd {h / math.sqrt(12):.5f})')
print('(c) budget (2) at realistic ticks, kappa_min = 0.2:')
for lab_, h_ in [('1 cent on $100', 1e-4), ('1 cent on $10', 1e-3), ('1 cent on $2', 5e-3)]:
    print(f'    {lab_:16s} (log tick {h_:.0e}): daily {eps(h_, 0.2, 1 / 252):.4f}, 5-minute {eps(h_, 0.2, 1 / 19656):.4f}')
