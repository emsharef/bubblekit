"""Reviewer's independent check of claim 034 (written before reading checks/034/* and checks/d17-clock-cells/*).
Single process (CPU budget). Reuses the reviewer's claim-031 interval supremum W and forecast prototype (inlined).
(a) W_clock (2)-(3) against brute force: over the independent mean/scale rectangle (must match) and over the coupled
    (x, b, w) box (must not exceed W_clock); random boxes, clocks, source/target cells including zero cells.
(b) Singleton box with v = Delta equals claim 031's W; refinement monotone in parameter level h and state level l.
(c) Domination by Monte Carlo: two steps, coarse tick, endpoint uniform in the cell, (b, w) uniform in the box, the
    clock drawn from a two-clock set; empirical label-path frequencies vs D_clock at h = 2, l = 3.
(d) Cost of a compact box: cent tick, $5 GBM null (b = 0.05, kappa = 0.30), 60 daily steps, clock {Delta}; numerator
    = claim 031's forecast at the true parameters; median log E for the singleton true box (claim 031) and for the box
    b in [-0.1, 0.2] x kappa in [0.15, 0.45] at h = 0..3, state level l = 2.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/034/reproduce.py
Seed:   numpy default_rng(34). Single process, a few minutes. Not a CI check (not check.py)."""
import numpy as np, math
from scipy.stats import norm
from scipy.integrate import quad
rng = np.random.default_rng(34)
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

def Wc(a, dS, c, dT, bL, bH, wL, wH, Dl, v):
    if a == 0 and c == 0: return 1.0
    Mm = -math.inf if a == 0 else math.log(a) + bL * Dl - wH * v / 2; Mp = math.log(dS) + bH * Dl - wL * v / 2
    sm, sp = math.sqrt(wL * v), math.sqrt(wH * v)
    if c == 0:
        t = math.log(dT) - Mm; return norm.cdf(t / sm) if t >= 0 else norm.cdf(t / sp)
    L, R = math.log(c), math.log(dT); m = min(max((L + R) / 2, Mm), Mp)
    if L <= m <= R: s = sm
    else:
        l, r = sorted((abs(L - m), abs(R - m))); s = min(max(math.sqrt((r * r - l * l) / (2 * math.log(r / l))), sm), sp)
    return max(norm.cdf((R - m) / s) - norm.cdf((L - m) / s), 1e-300)
def prob(lx, L, R, mu, s):
    return norm.cdf((R - lx - mu) / s) - (norm.cdf((L - lx - mu) / s) if L > -math.inf else 0.0)
# (a)
w_rect = 0.0; w_coup = 0.0; gap = []; ncase = 0; tight = 0.0
for t in range(60):
    DEL_ = 0.05; z0 = int(rng.integers(0, 8)); z1 = int(rng.integers(0, 10)); Dl = rng.uniform(0.01, 0.1); v = Dl * rng.uniform(0.3, 3)
    bL = rng.uniform(-1, 0.5); bH = bL + rng.uniform(0, 1); wL = rng.uniform(0.01, 0.3); wH = wL + rng.uniform(0, 0.5)
    a, dS = (0.0, DEL_ / 2) if z0 == 0 else (DEL_ * (z0 - .5), DEL_ * (z0 + .5)); c, dT = (0.0, DEL_ / 2) if z1 == 0 else (DEL_ * (z1 - .5), DEL_ * (z1 + .5))
    W_ = Wc(a, dS, c, dT, bL, bH, wL, wH, Dl, v); Lg = -math.inf if c == 0 else math.log(c); Rg = math.log(dT)
    if a == 0 and c == 0: continue
    ncase += 1
    Mm = (math.log(a) if a > 0 else math.log(dS) - 30) + bL * Dl - wH * v / 2; Mp = math.log(dS) + bH * Dl - wL * v / 2
    ms = np.linspace(Mm, Mp, 801); ss = np.linspace(math.sqrt(wL * v), math.sqrt(wH * v), 801)
    rect = max(norm.cdf((Rg - ms[:, None]) / ss[None, :]).max() if c == 0 else (norm.cdf((Rg - ms[:, None]) / ss[None, :]) - norm.cdf((Lg - ms[:, None]) / ss[None, :])).max(), 0)
    w_rect = max(w_rect, rect - W_); tight = max(tight, (W_ - rect) / W_) if W_ > 1e-12 else tight
    xs = np.linspace(a if a > 0 else dS * 1e-6, dS, 41); bs = np.linspace(bL, bH, 41); ws = np.linspace(wL, wH, 41)
    X, B, Wg = np.meshgrid(np.log(xs), bs, ws, indexing='ij'); mu = X + B * Dl - Wg * v / 2; s = np.sqrt(Wg * v)
    coup = (norm.cdf((Rg - mu) / s) - (norm.cdf((Lg - mu) / s) if c > 0 else 0)).max()
    w_coup = max(w_coup, coup - W_); gap.append(coup / W_)
print(f'(a) {ncase} cases: max (rectangle brute - W_clock) {w_rect:.1e}, max relative (W_clock - rectangle brute) {tight:.1e} where W_clock > 1e-12 (grid); '
      f'max (coupled-box brute - W_clock) {w_coup:.1e} (<= 0); median coupled/W ratio {np.median(gap):.3f}')
# recursion over parameter boxes and state subcells
def log_bound_box(z, box, Dls, vs, L):
    bL, bH, wL, wH = box; n = len(z) - 1; out = []; prev = None
    for l in range(L + 1):
        K = 2 ** l; U = [None] * (n + 1); U[n] = np.zeros(K)
        def subs(zz):
            a, b = cell(zz); e = a + (b - a) * np.arange(K + 1) / K; return e[:-1], e[1:]
        for j in range(n - 1, -1, -1):
            sa, sb = subs(z[j]); tc, td = subs(z[j + 1])
            lw = np.array([[math.log(Wc(sa[i], sb[i], tc[k], td[k], bL, bH, wL, wH, Dls[j], vs[j])) for k in range(K)] for i in range(K)])
            T = np.logaddexp.reduce(lw + U[j + 1][None, :], axis=1); Uj = np.minimum(T, 0.0)
            if prev is not None: Uj = np.minimum(Uj, prev[j][np.arange(K) // 2])
            U[j] = Uj
        out.append(U[0].max()); prev = U
    return np.array(out)
def boxes(B, h):
    bL, bH, wL, wH = B; k = 2 ** h; be = np.linspace(bL, bH, k + 1); we = np.linspace(wL, wH, k + 1)
    return [(be[i], be[i + 1], we[j], we[j + 1]) for i in range(k) for j in range(k)]
def logD(z, B, h, clocks, Dls, L):
    return np.max([log_bound_box(z, bx, Dls, v, L) for bx in boxes(B, h) for v in clocks], axis=0)
# (b)
DEL = 0.05; sing = 0.0; mono = True
for t in range(20):
    z = [int(x) for x in rng.integers(1, 9, 4)]; Dls = rng.uniform(0.01, 0.08, 3); b = rng.uniform(-0.5, 0.5); w = rng.uniform(0.02, 0.4)
    lb = log_bound_box(z, (b, b, w, w), Dls, Dls, 0)[0]
    direct = sum(math.log(max(W(*cell(z[j]), *cell(z[j + 1]), b * Dls[j] - w * Dls[j] / 2, math.sqrt(w * Dls[j])), 1e-300)) for j in range(3))
    sing = max(sing, abs(lb - direct))
    Bx = (b - 0.3, b + 0.3, w * 0.5, w * 1.5); vs = Dls * rng.uniform(0.5, 2, 3)
    grid = np.array([logD(z, Bx, h, [vs], Dls, 3) for h in range(3)])
    mono &= bool(np.all(np.diff(grid, axis=0) <= 1e-12) and np.all(np.diff(grid, axis=1) <= 1e-12))
print(f'(b) singleton box, v = Delta, level 0 vs claim 031 product: max |diff| {sing:.1e}; monotone in h and l on 20 paths: {mono}')
# (c)
Dls = np.array([0.02, 0.06]); clocks = [Dls, np.array([0.04, 0.02])]; Bx = (-0.5, 0.5, 0.09, 0.36); Mc = 400000; z0 = 4
a0, b0 = cell(z0); X0 = rng.uniform(a0, b0, Mc); bb = rng.uniform(-0.5, 0.5, Mc); ww = rng.uniform(0.09, 0.36, Mc); ci = rng.integers(0, 2, Mc)
vv = np.array(clocks)[ci]; X1 = X0 * np.exp(bb * Dls[0] - ww * vv[:, 0] / 2 + np.sqrt(ww * vv[:, 0]) * rng.standard_normal(Mc))
X2 = X1 * np.exp(bb * Dls[1] - ww * vv[:, 1] / 2 + np.sqrt(ww * vv[:, 1]) * rng.standard_normal(Mc))
L1 = np.floor(X1 / DEL + 0.5).astype(int); L2 = np.floor(X2 / DEL + 0.5).astype(int); viol = 0; cnt = 0; ratio = []
for v1 in range(1, 9):
    for v2 in range(0, 11):
        p = np.mean((L1 == v1) & (L2 == v2))
        if p > 2e-4:
            cnt += 1; lD = logD([z0, v1, v2], Bx, 2, clocks, Dls, 3)[-1]; viol += math.log(p) > lD + 4 * math.sqrt(p / Mc) / p; ratio.append(lD - math.log(p))
print(f'(c) {cnt} frequent two-step label paths: domination violations {viol}; median log(D / frequency) {np.median(ratio):.2f}')
# (d)
DEL = 0.01; sd = 0.3 / math.sqrt(252); D1 = 1 / 252; n = 60; Bx = (-0.1, 0.2, 0.15 ** 2, 0.45 ** 2); rows = []
for p_ in range(8):
    X = 5.0 * np.exp(np.cumsum(np.r_[0.0, (0.05 - 0.045) * D1 + sd * rng.standard_normal(n)])); z = list(np.floor(X / DEL + 0.5).astype(int))
    mu = 0.05 * D1 - 0.09 * D1 / 2; lq = forecast_logq(z, mu, sd); Dls = np.full(n, D1)
    r = [lq - log_bound_box(z, (0.05, 0.05, 0.09, 0.09), Dls, Dls, 2)[-1]] + [lq - logD(z, Bx, h, [Dls], Dls, 2)[-1] for h in range(4)]
    rows.append(r)
md = np.median(np.array(rows), 0)
print(f'(d) $5, cent tick, 60 days, kappa 0.3: median log E singleton true box {md[0]:+.2f}; compact box h = 0..3: ' + ', '.join(f'{x:+.2f}' for x in md[1:]))
