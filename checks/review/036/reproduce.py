"""Reviewer's independent check of claim 036 (written before reading checks/036/* and checks/d19-*). Single process.
Reuses the reviewer's claim-031 envelope and forecast and claim-034 box recursion (inlined).
(a) Relative enclosure (6): midpoint sums Q at M = 4, 16, 64 with their eps bounds against independent quadrature
    of L for J = 2 (1-D quad of a Gaussian CDF difference) and J = 3 (2-D quad); coarse tick so cells are wide.
(b) Parameter cover (8): on a box, D_cert's upper bound over a grid of subboxes is at least the brute-force
    conditional likelihood at 400 interior parameters (computed with M = 256 and its own enclosure), and the
    centre lower bound is at most it; conditional normalization over the next label (n = 1) is one.
(c) What the exact filter buys: cent tick, $5 GBM null (b = .05, kappa = .3), k = n = 30 daily steps, 6 paths;
    numerator = claim 031's forecast at the true law on the evaluation labels. log E for: claim 031's envelope at
    the true parameter (level 3); the filtered likelihood at the true parameter (bounds from M = 64); claim 034's
    box b in [-0.1, 0.2] x kappa in [0.15, 0.45] (h = 2, level 2); and the filtered maximum over the same box
    approximated on a 41 x 41 grid of centres (an upper bound on log E, not certified), with the certified
    allowance H that the same grid would carry under (7).

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/036/reproduce.py
Seed:   numpy default_rng(36). Single process, a few minutes. Not a CI check (not check.py)."""
import numpy as np, math
from scipy.stats import norm
from scipy.integrate import quad, dblquad
from scipy.special import logsumexp
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
rng = np.random.default_rng(36)
def logcells(z): return np.array([[math.log(DEL * (x - 0.5)), math.log(DEL * (x + 0.5))] for x in z])
def logQ(s, z, Dl, v, b, w, M):
    """(5) in log space, vectorized over parameter arrays b, w (same shape). Returns log Q_J for J = 1..len(z)."""
    b = np.atleast_1d(b)[:, None]; w = np.atleast_1d(w)[:, None]; lc = logcells(z); out = []
    prev_t = np.array([math.log(s)]); lA = np.zeros((b.shape[0], 1))
    for j in range(len(z)):
        h = (lc[j, 1] - lc[j, 0]) / M; t = lc[j, 0] + h * (np.arange(M) + 0.5); m = b * Dl[j] - w * v[j] / 2; var = w * v[j]
        dif = t[None, None, :] - prev_t[None, :, None]                                   # (1, Mprev, M)
        lphi = -(dif - m[:, :, None]) ** 2 / (2 * var[:, :, None]) - 0.5 * np.log(2 * math.pi * var[:, :, None])
        lA = math.log(h) + logsumexp(lA[:, :, None] + lphi, axis=1); prev_t = t; out.append(logsumexp(lA, axis=1))
    return np.array(out)                                                                  # (J, G)
def eps(s, z, Dl, v, B, M):
    bm, bp, wm, wp = B; lc = logcells(z); a = np.r_[math.log(s), lc[:, 0]]; d = np.r_[math.log(s), lc[:, 1]]; Bmax = max(abs(bm), abs(bp))
    Rmax = np.maximum(np.abs(a[1:] - d[:-1]), np.abs(d[1:] - a[:-1])); C = (Rmax + Bmax * Dl + wp * v / 2) / (wm * v)
    r = np.r_[0.0, (d[1:] - a[1:]) / (2 * M)]; e = np.cumsum(C * (r[:-1] + r[1:]))
    Lb = np.cumsum(Dl * C); Lw = np.arange(1, len(z) + 1) / (2 * wm) + np.cumsum((Rmax + Bmax * Dl) ** 2 / (2 * wm ** 2 * v)) + np.cumsum(v / 8)
    return e, Lb, Lw
def L_quad(s, z, Dl, b, w):
    lc = logcells(z); m = b * Dl - w * Dl / 2; sd = np.sqrt(w * Dl); y0 = math.log(s)
    if len(z) == 2:
        f = lambda y1: norm.pdf(y1 - y0, m[0], sd[0]) * (norm.cdf(lc[1, 1] - y1, m[1], sd[1]) - norm.cdf(lc[1, 0] - y1, m[1], sd[1]))
        return quad(f, lc[0, 0], lc[0, 1], epsabs=0, epsrel=1e-12, limit=200)[0]
    f = lambda y2, y1: norm.pdf(y1 - y0, m[0], sd[0]) * norm.pdf(y2 - y1, m[1], sd[1]) * (norm.cdf(lc[2, 1] - y2, m[2], sd[2]) - norm.cdf(lc[2, 0] - y2, m[2], sd[2]))
    return dblquad(f, lc[0, 0], lc[0, 1], lc[1, 0], lc[1, 1], epsabs=0, epsrel=1e-10)[0]
# (a)
DEL = 0.05; worst = -math.inf; cases = 0; widths = {}
for _ in range(12):
    s = rng.uniform(0.8, 1.2); J = int(rng.integers(2, 4)); Dl = rng.uniform(0.004, 0.03, J); b = rng.uniform(-0.3, 0.3); w = rng.uniform(0.02, 0.3)
    X = s * np.exp(np.cumsum(b * Dl - w * Dl / 2 + np.sqrt(w * Dl) * rng.standard_normal(J))); z = [max(1, int(math.floor(x / DEL + 0.5))) for x in X]
    Lt = math.log(L_quad(s, z, Dl, b, w))
    for M in (4, 16, 64):
        lq = logQ(s, z, Dl, Dl, b, w, M)[-1, 0]; e = eps(s, z, Dl, Dl, (b, b, w, w), M)[0][-1]
        worst = max(worst, abs(Lt - lq) - e); cases += 1; widths.setdefault(M, []).append(e)
print(f'(a) {cases} (path, M) cases: max (|log L_quad - log Q| - eps) {worst:.2e} (<= 0); median eps at M = 4, 16, 64: '
      + ', '.join(f'{np.median(widths[M]):.3f}' for M in (4, 16, 64)))
# (b)
s = 1.0; Dl = np.array([0.01, 0.02, 0.01, 0.015]); v = Dl * np.array([1.5, 0.5, 1.0, 2.0]); k = 3; Bx = (-0.05, 0.05, 0.07, 0.09)
X = s * np.exp(np.cumsum(0.0 * Dl - 0.04 * v + np.sqrt(0.08 * v) * rng.standard_normal(4))); z = [max(1, int(math.floor(x / DEL + 0.5))) for x in X]
bs = rng.uniform(Bx[0], Bx[1], 400); ws = rng.uniform(Bx[2], Bx[3], 400); lq = logQ(s, z, Dl, v, bs, ws, 256)
lg_brute = lq[-1] - lq[k - 1]; e256 = eps(s, z, Dl, v, Bx, 256)[0]; brute_hi = (lg_brute + e256[-1] + e256[k - 1]).max(); brute_lo = (lg_brute - e256[-1] - e256[k - 1]).max()
nb = nw = 24; be = np.linspace(Bx[0], Bx[1], nb + 1); we = np.linspace(Bx[2], Bx[3], nw + 1); ups = []; los = []; Hs = []
for i in range(nb):
    for j_ in range(nw):
        B = (be[i], be[i + 1], we[j_], we[j_ + 1]); bg, wg = (be[i] + be[i + 1]) / 2, (we[j_] + we[j_ + 1]) / 2
        e, Lb, Lw = eps(s, z, Dl, v, B, 64); eta = Lb * (be[1] - be[0]) / 2 + Lw * (we[1] - we[0]) / 2
        q = logQ(s, z, Dl, v, bg, wg, 64)[:, 0]; H = e[-1] + e[k - 1] + eta[-1] + eta[k - 1]; Hs.append(H)
        ups.append(min(0.0, H + q[-1] - q[k - 1])); los.append(q[-1] - q[k - 1] - e[-1] - e[k - 1])
norm_ = sum(math.exp(logQ(s, z[:k] + [zz], Dl, v, 0.0, 0.08, 256)[-1, 0] - logQ(s, z[:k], Dl, v, 0.0, 0.08, 256)[-1, 0]) for zz in range(1, 80))
print(f'(b) labels {z}, box b in [-.05, .05] x w in [.07, .09], 24 x 24 cover, M = 64 (median H {np.median(Hs):.3f}): log D_cert {max(ups):.4f} >= brute max over 400 parameters (upper side) {brute_hi:.4f}; centre lower bound {max(los):.4f} <= '
      f'{brute_lo:.4f} (lower side); conditional mass over next label at M = 256: {norm_:.6f}')
# (c)
DEL = 0.01; sd = 0.3 / math.sqrt(252); D1 = 1 / 252; k = n = 30; Bx = (-0.1, 0.2, 0.15 ** 2, 0.45 ** 2); rows = []
bg = np.linspace(Bx[0], Bx[1], 41); wg = np.linspace(Bx[2], Bx[3], 41); BG, WG = [a.ravel() for a in np.meshgrid(bg, wg)]
for _ in range(6):
    X = 5.0 * np.exp(np.cumsum((0.05 - 0.045) * D1 + sd * rng.standard_normal(k + n))); z = [int(math.floor(x / DEL + 0.5)) for x in X]
    Dl = np.full(k + n, D1); mu = (0.05 - 0.045) * D1; ze = [z[k - 1]] + z[k:]
    lq = forecast_logq(ze, mu, sd)
    l31 = log_bound(ze, mu, sd, 3)[-1]
    Q = logQ(5.0, z, Dl, Dl, 0.05, 0.09, 64)[:, 0]; e = eps(5.0, z, Dl, Dl, (0.05, 0.05, 0.09, 0.09), 64)[0]; lf = Q[-1] - Q[k - 1]; ef = e[-1] + e[k - 1]
    l34 = max(log_bound_box(ze, bx, Dl[:n], Dl[:n], 2)[-1] for bx in [(a1, a2, c1, c2) for a1, a2 in zip(np.linspace(-0.1, 0.2, 5)[:-1], np.linspace(-0.1, 0.2, 5)[1:]) for c1, c2 in zip(np.linspace(Bx[2], Bx[3], 5)[:-1], np.linspace(Bx[2], Bx[3], 5)[1:])])
    QG = logQ(5.0, z, Dl, Dl, BG, WG, 16); lgrid = (QG[-1] - QG[k - 1]).max()
    e1, Lb, Lw = eps(5.0, z, Dl, Dl, Bx, 16); Hgrid = e1[-1] + e1[k - 1] + (Lb[-1] + Lb[k - 1]) * (bg[1] - bg[0]) / 2 + (Lw[-1] + Lw[k - 1]) * (wg[1] - wg[0]) / 2
    rows.append([lq - l31, lq - lf - ef, lq - lf + ef, lq - l34, lq - lgrid, Hgrid])
r = np.median(np.array(rows), 0)
print(f'(c) $5, cent tick, k = n = 30 days, median log E: claim 031 envelope (true parameter, level 3) {r[0]:+.2f}; filtered, true parameter '
      f'[{r[1]:+.2f}, {r[2]:+.2f}]; claim 034 box (h = 2, level 2) {r[3]:+.2f}; filtered box maximum on a 41 x 41 grid <= {r[4]:+.2f} '
      f'(certified allowance (7) for that grid H = {r[5]:.0f})')
