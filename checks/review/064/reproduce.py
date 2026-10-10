"""Reviewer's independent check of claim 064 (written before reading checks/064/*). Single process (CPU budget).
Reuses the reviewer's claim-031 interval supremum W (inlined). Cent tick, monetary cells.
(a) Uniform emissions (3) sum to one over labels at sample latent prices (including 0); subinterval suprema (4) vs
    brute force.
(b) Domination (6): latent GBM from an exact endpoint drawn inside the expanded first interval, uniform noise
    (uniform mode) or adversarial bounded errors pushing every observation to the edge of its band (support mode);
    empirical 2-step label-path frequencies vs the level-3 bounds (coarse tick, 400,000 draws).
(c) Evidence cost: daily GBM null kappa = 0.3 from $5, 60 days, a = delta/2 uniform noise; numerator = claim 031's
    forecast prototype; median log E by level for support mode and uniform mode, beside claim 031's no-noise bound.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/064/reproduce.py
Seed:   numpy default_rng(64). Single process, a few minutes. Not a CI check (not check.py)."""

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
def forecast_logq(z, mu, s):
    lq = 0.0
    for j in range(1, len(z)):
        x = DEL * z[j - 1] if z[j - 1] >= 1 else DEL / 4; c, d = cell(z[j]); lq += math.log(max(p_from(x, c, d, mu, s), 1e-300))
    return lq

rng = np.random.default_rng(64)
def g_emit(z, x, a):
    if a == 0: l, r = cell(z); return 1.0 if l <= x < r else 0.0
    if z == 0: return min(1.0, max(0.0, (DEL / 2 - x + a) / (2 * a)))
    l, r = cell(z); return max(0.0, min(a, r - x) - max(-a, l - x)) / (2 * a)
def M_sup(z, c, d, a, mode):
    if mode == 'support' or a == 0: return 1.0
    if z == 0: return g_emit(0, c, a)
    l, r = cell(z); return g_emit(z, min(max((l + r) / 2, c), d), a)
def expanded(z, a):
    l, r = cell(z); return max(0.0, l - a), r + a
def log_bound_noise(z, mu, s, a, mode, L):
    n = len(z) - 1; out = []; prev = None
    for lv in range(L + 1):
        K = 2 ** lv; U = [None] * (n + 1); U[n] = np.zeros(K)
        def subs(zz):
            lo, hi = expanded(zz, a); e = lo + (hi - lo) * np.arange(K + 1) / K; return e[:-1], e[1:]
        for j in range(n - 1, -1, -1):
            sa, sb = subs(z[j]); tc, td = subs(z[j + 1])
            lw = np.array([[math.log(max(W(sa[i], sb[i], tc[k], td[k], mu, s) * M_sup(z[j + 1], tc[k], td[k], a, mode), 1e-300)) for k in range(K)] for i in range(K)])
            T = np.logaddexp.reduce(lw + U[j + 1][None, :], axis=1); Uj = np.minimum(T, 0.0)
            if prev is not None: Uj = np.minimum(Uj, prev[j][np.arange(K) // 2])
            U[j] = Uj
        out.append(U[0].max()); prev = U
    return np.array(out)
# (a)
a = DEL / 2; worst_n = 0.0; worst_s = 0.0
for x in (0.0, 0.001, 0.004, 0.0074, 0.013, 0.05, 1.234):
    worst_n = max(worst_n, abs(sum(g_emit(z, x, a) for z in range(0, 400)) - 1))
for z in (0, 1, 3, 50):
    lo, hi = expanded(z, a)
    for c, d in [(lo, hi), (lo, (lo + hi) / 2), ((lo + hi) / 2, hi), (lo + 0.3 * (hi - lo), lo + 0.4 * (hi - lo))]:
        brute = max(g_emit(z, x, a) for x in np.linspace(c, d, 20001)[:-1]); worst_s = max(worst_s, brute - M_sup(z, c, d, a, 'uniform'))
print(f'(a) emission sums to 1: max |sum - 1| {worst_n:.1e}; subinterval suprema (4) vs brute force: max (brute - formula) {worst_s:.1e}')
# (b) coarse tick for visible probabilities
DEL0 = DEL; DEL = 0.05; a = 0.02; mu, s = 0.0, 0.08; Mc = 400000; z0 = 4
lo, hi = expanded(z0, a)
for mode in ('uniform', 'support'):
    X0 = rng.uniform(lo, hi, Mc); X1 = X0 * np.exp(rng.normal(mu, s, Mc)); X2 = X1 * np.exp(rng.normal(mu, s, Mc))
    if mode == 'uniform':
        Y1 = np.maximum(0, X1 + rng.uniform(-a, a, Mc)); Y2 = np.maximum(0, X2 + rng.uniform(-a, a, Mc))
    else:   # adversarial bounded errors: push each observation up or down by a, depending on the latent fractional position
        f1 = (X1 / DEL) % 1; f2 = (X2 / DEL) % 1
        Y1 = np.maximum(0, X1 + np.where(f1 > 0.5, a, -a)); Y2 = np.maximum(0, X2 + np.where(f2 > 0.5, a, -a))
    L1 = np.floor(Y1 / DEL + 0.5).astype(int); L2 = np.floor(Y2 / DEL + 0.5).astype(int)
    viol = 0; cnt = 0
    for v1 in range(z0 - 2, z0 + 3):
        for v2 in range(v1 - 2, v1 + 3):
            p = np.mean((L1 == v1) & (L2 == v2))
            if p > 2e-4:
                cnt += 1; viol += math.log(p) > log_bound_noise([z0, v1, v2], mu, s, a, mode, 3)[-1] + 4 * math.sqrt(p / Mc) / p
    print(f'(b) {mode:7s} mode: {cnt} frequent 2-step label paths, domination violations {viol}')
DEL = DEL0
# (c)
sd = 0.3 / math.sqrt(252); a = DEL / 2; n = 60; rows = {'none': [], 'support': [], 'uniform': []}
for p_ in range(12):
    X = 5.0 * np.exp(np.cumsum(np.r_[0.0, rng.normal(0, sd, n)])); Y = np.maximum(0, X + rng.uniform(-a, a, n + 1)); z = list(np.floor(Y / DEL + 0.5).astype(int))
    lq = forecast_logq(z, 0.0, sd)
    rows['support'].append(lq - log_bound_noise(z, 0.0, sd, a, 'support', 3)); rows['uniform'].append(lq - log_bound_noise(z, 0.0, sd, a, 'uniform', 3))
    rows['none'].append(lq - log_bound_noise(z, 0.0, sd, 0.0, 'support', 3))
for k, v in rows.items():
    print(f'(c) $5 start, cent tick, a = delta/2, 60 days, mode {k:8s}: median log E by level 0..3: ' + ', '.join(f'{x:+.2f}' for x in np.median(np.array(v), 0)), flush=True)
