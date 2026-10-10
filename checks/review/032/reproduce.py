"""Reviewer's independent check of claim 032 (written before reading checks/032/*). Single process (CPU budget).
Reuses the reviewer's independent claim-031 implementation (checks/review/031/reproduce.py functions, inlined).
(a) Data processing: exact TV of rounded labels after one step, actual N(.,sigma^2) vs reference N(.,kappa^2) from the
    same exact start, never exceeds the Gaussian affinity budget sqrt(1 - A^2); also not the 2-step bound (MC).
(b) Reference moment at every exact endpoint: sum_v q(v) / D^{delta,L}(v) * P_theta(v | x) <= 1 for starts x across
    the cell (including 0 in a zero quote), n = 2, levels 0..3.
(c) Size: cent ticks, start $1, daily, n = 15; Gamma = {(0, 0.30)}; forecast prototype with kappa = 0.20; actual
    GBM sigma = 0.30 (in catalogue) and 0.40 (off-grid, budget from (1)); raw P(E > 1/alpha) vs alpha + e, and the
    mean of the clipped score (5) with c = 50; alpha = 0.1; level 2.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/032/reproduce.py
Seed:   numpy default_rng(32). Single process, about 10 minutes. Not a CI check (not check.py)."""

import numpy as np, math
from scipy.stats import norm
from scipy.integrate import quad
rng = np.random.default_rng(31)
DEL = 0.01
def cell(z): return (0.0, DEL / 2) if z == 0 else (DEL * (z - 0.5), DEL * (z + 0.5))
def W(a, b, c, d, mu, s):
    if c == 0:
        return 1.0 if a == 0 else norm.cdf((math.log(d) - math.log(a) - mu) / s)
    lo = -math.inf if a == 0 else math.log(a) + mu; m = min(max((math.log(c) + math.log(d)) / 2, lo), math.log(b) + mu)
    return norm.cdf((math.log(d) - m) / s) - norm.cdf((math.log(c) - m) / s)
def p_from(x, c, d, mu, s):          # exact one-step probability from state x into [c, d)
    if x == 0: return 1.0 if c == 0 else 0.0
    f = lambda y: norm.cdf((math.log(y) - math.log(x) - mu) / s) if y > 0 else 0.0
    return f(d) - (f(c) if c > 0 else 0.0)
def log_bound(z, mu, s, L):
    """Backward recursion over price-width subcells (claim 030 structure with kernel (2)); returns log bound per level."""
    n = len(z) - 1; out = []; prev = None
    for l in range(L + 1):
        K = 2 ** l; U = [None] * (n + 1); U[n] = np.zeros(K)
        def subs(zz):
            a, b = cell(zz); e = a + (b - a) * np.arange(K + 1) / K; return e[:-1], e[1:]
        for j in range(n - 1, -1, -1):
            sa, sb = subs(z[j]); tc, td = subs(z[j + 1])
            lw = np.array([[math.log(max(W(sa[i], sb[i], tc[k], td[k], mu, s), 1e-300)) for k in range(K)] for i in range(K)])
            T = np.logaddexp.reduce(lw + U[j + 1][None, :], axis=1); Uj = np.minimum(T, 0.0)
            if prev is not None: Uj = np.minimum(Uj, prev[j][np.arange(K) // 2])
            U[j] = Uj
        out.append(U[0].max()); prev = U
    return np.array(out)

def forecast_logq(z, mu, s):
    lq = 0.0
    for j in range(1, len(z)):
        x = DEL * z[j - 1] if z[j - 1] >= 1 else DEL / 4; c, d = cell(z[j]); lq += math.log(max(p_from(x, c, d, mu, s), 1e-300))
    return lq
rng = np.random.default_rng(32)
def labels_prob(x, z, mu, s):
    c, d = cell(z); return p_from(x, c, d, mu, s)
# (a)
worst = -1.0
for sig, kap, Dt in [(0.4, 0.3, 1 / 252), (0.25, 0.3, 1 / 252), (0.6, 0.3, 1 / 52), (0.31, 0.30, 1 / 19656)]:
    for x in (0.004, 0.012, 0.05, 1.003):
        za = np.arange(0, int(3 * x / DEL) + 60)
        pa = np.array([labels_prob(x, z, -sig * sig / 2 * Dt, sig * math.sqrt(Dt)) for z in za]); pr = np.array([labels_prob(x, z, -kap * kap / 2 * Dt, kap * math.sqrt(Dt)) for z in za])
        tv = 0.5 * np.abs(pa - pr).sum() + 0.5 * abs((1 - pa.sum()) - (1 - pr.sum()))
        A = math.sqrt(2 * sig * kap / (sig * sig + kap * kap)) * math.exp(-Dt * ((kap * kap - sig * sig) / 2) ** 2 / (4 * (sig * sig + kap * kap)))
        worst = max(worst, tv - math.sqrt(1 - A * A))
print(f'(a) rounded one-step TV minus Gaussian affinity budget: max {worst:+.4f} (<= 0: rounding never adds error)')
# (b)
mu, s = 0.0, 0.3 / math.sqrt(252); bad = 0; tot = 0
for z0, xs in [(0, [0.0, 1e-5, 0.002, 0.0049]), (2, [0.0151, 0.02, 0.0249]), (100, [0.9951, 1.0, 1.0049])]:
    for L in range(4):
        for x in xs:
            S = 0.0
            for z1 in range(max(0, z0 - 4), z0 + 5):
                for z2 in range(max(0, z1 - 4), z1 + 5):
                    path = [z0, z1, z2]; lD = log_bound(path, mu, s, L)[-1]
                    lq = forecast_logq(path, 0.0, 0.2 / math.sqrt(252))
                    if x == 0: P = 1.0 if (z1 == 0 and z2 == 0) else 0.0
                    else:
                        c1, d1 = cell(z1); c2, d2 = cell(z2)
                        g = lambda y1: (norm.pdf((math.log(y1) - math.log(x) - mu) / s) / (s * y1)) * p_from(y1, c2, d2, mu, s)
                        P = quad(g, max(c1, 1e-300), d1, limit=100)[0]
                    if P > 0: S += math.exp(lq - lD + math.log(P))
            tot += 1; bad += S > 1 + 1e-9
print(f'(b) per-endpoint reference moment (truncated label sum) <= 1: {tot - bad}/{tot} cases')
# (c)
n = 15; AL = 0.1; c = 50.0
for sig in (0.30, 0.40):
    A = (2 * sig * 0.3 / (sig * sig + 0.09)) ** (n / 2) * math.exp(-n / 252 * ((0.09 - sig * sig) / 2) ** 2 / (4 * (sig * sig + 0.09))); e = math.sqrt(max(0.0, 1 - A * A))
    lE = []
    for p in range(300):
        X = 1.0 * np.exp(np.cumsum(np.r_[0.0, rng.normal(-sig * sig / 2 / 252, sig / math.sqrt(252), n)])); z = list(np.floor(X / DEL + 0.5).astype(int))
        lE.append(forecast_logq(z, 0.0, 0.2 / math.sqrt(252)) - log_bound(z, 0.0, 0.3 / math.sqrt(252), 2)[-1])
    E = np.exp(np.array(lE)); clipped = np.minimum(E, c) / (1 + c * e)
    print(f'(c) actual sigma={sig}: budget e={e:.4f}; P(E > 1/alpha) {np.mean(E > 1 / AL):.4f} <= alpha + e = {AL + e:.4f}; '
          f'raw mean {E.mean():.3f}; clipped (5) mean {clipped.mean():.3f}', flush=True)
