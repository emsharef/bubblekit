"""Reviewer's independent check of claim 029 (written before reading checks/029/*).
(a) Interval maximum (1) vs brute force over a fine grid of exact starts in the previous cell; the excess mass (4)
    by direct summation; the normalization counterexample's null mean S_cell.
(b) Joint-cell domination (3) by Monte Carlo for n = 2, coarse tick, with an adversarial latent start (cell edge).
(c) Validity and the envelope's cost: GBM null with exact latent prices, rounded on the log lattice; singleton
    Gamma = {true theta}; numerator q = product of normalized one-step Gaussian forecasts from previous representatives
    (true theta). Mean E^cell (<= 1) and median log E^cell per year of daily / 5-minute data at log ticks 1e-4, 1e-3.

Rerun:  uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/029/reproduce.py
Seed:   numpy default_rng(29). Runtime about 1 minute. Not a CI check (not check.py)."""
import numpy as np, math
from scipy.stats import norm
rng = np.random.default_rng(29)
def Kcell(zp, z, h, mu, s):
    m = np.clip(h * z, h * (zp - 0.5) + mu, h * (zp + 0.5) + mu)
    return norm.cdf((h * (z + 0.5) - m) / s) - norm.cdf((h * (z - 0.5) - m) / s)
worst = 0.0
for h, mu, s in [(0.02, 0.0, 0.0189), (0.01, -0.0004, 0.0126), (0.05, 0.001, 0.0189), (1e-3, 0.0, 0.0126)]:
    for z in range(-3, 4):
        x = np.linspace(-h / 2, h / 2, 20001)[:-1]
        brute = np.max(norm.cdf((h * (z + 0.5) - x - mu) / s) - norm.cdf((h * (z - 0.5) - x - mu) / s))
        worst = max(worst, brute - Kcell(0, z, h, mu, s))
print(f'(a) interval maximum (1) vs brute force (20,000 starts): max (brute - formula) = {worst:.2e} (<= 0 up to grid)')
for h, s in [(0.02, 0.0189), (1e-4, 0.2 / math.sqrt(252)), (1e-3, 0.2 / math.sqrt(252))]:
    tot = sum(Kcell(0, z, h, 0.0, s) for z in range(-20000, 20001)); S = 2 * norm.cdf(h / (2 * s))
    print(f'    excess mass h={h} s={s:.4f}: sum {tot:.8f} vs 2 Phi(h/2s) = {S:.8f}; counterexample null mean = {S:.6f} > 1')

h, mu, s, M = 0.02, 0.0, 0.0189, 2_000_000
x0 = np.full(M, h / 2 - 1e-12)                 # adversarial latent start at the upper cell edge of z0 = 0
y1 = x0 + rng.normal(mu, s, M); y2 = y1 + rng.normal(mu, s, M)
z1 = np.floor(y1 / h + 0.5).astype(int); z2 = np.floor(y2 / h + 0.5).astype(int)
viol = 0; checked = 0
for a in range(-3, 4):
    for b in range(-4, 5):
        p = np.mean((z1 == a) & (z2 == b)); env = Kcell(0, a, h, mu, s) * Kcell(a, b, h, mu, s)
        if p > 1e-4: checked += 1; viol += p > env + 4 * math.sqrt(p / M)
print(f'(b) n=2 joint-cell domination, edge start: {checked} label pairs checked, violations {viol}')

print('(c) null GBM kappa=0.3, b=kappa^2/2 (zero log drift), latent exact prices; E^cell with q = normalized Gaussian forecast:')
for lab, D, n in [('daily, 1 year', 1 / 252, 252), ('5-minute, 1 month', 1 / 19656, 1638)]:
    for h in (1e-4, 1e-3):
        k = 0.3; s = k * math.sqrt(D); Mp = 4000
        X = np.cumsum(np.r_[np.zeros((1, Mp)), rng.normal(0, s, (n, Mp))], axis=0) + rng.uniform(-h / 2, h / 2, Mp)
        Z = np.floor(X / h + 0.5).astype(int)
        lE = np.zeros(Mp)
        for j in range(1, n + 1):
            zp, z = Z[j - 1], Z[j]
            q = norm.cdf((h * (z + 0.5) - h * zp) / s) - norm.cdf((h * (z - 0.5) - h * zp) / s)   # forecast from representative
            lE += np.log(q) - np.log(Kcell(zp, z, h, 0.0, s))
        S = 2 * norm.cdf(h / (2 * s))
        print(f'    {lab:18s} h={h:.0e}: mean E {np.exp(lE).mean():.4f} (<= 1); median log E {np.median(lE):+.3f}; '
              f'n log S_cell = {n * math.log(S):.3f}')
