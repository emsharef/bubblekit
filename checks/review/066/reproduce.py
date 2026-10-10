"""Reviewer's independent check of claim 066 (written before reading checks/066/*). Single process (CPU budget).
Reuses the reviewer's claim-031 W and forecast, claim-064 support and claim-065 sign recursions, claim-034 W_clock and
box recursion, and the absorbed-CEV kernel (all inlined).
(a) Domination by Monte Carlo of the full composition (2): coarse tick, a = 0.4 tick, rho = .6, beta = +-5, (b, w)
    uniform in a box, clock drawn from a two-clock set, endpoint/sign uniform on a random feasible cell; empirical
    2-step label-path frequencies vs D_clocknoise at h = 1, l = 2.
(b) Reductions: a = 0 gives claim 034's denominator (beta = 3); singleton box with v = Delta gives claim 065's
    min(state, support).
(c) Forecast (6): row sums over (z', t) equal one (standardized-log quadrature with explicit tails); the two-step
    forecast summed over a covering label range is one; the forward sign filter sums to one.
(d) Evidence cost on top of noise: cent tick, $5 GBM null kappa = .3, 40 days, a = tick/2, signs rho = .5, beta = 0;
    numerator = claim 031's forecast at the true law; median log E for claim 065 at the true parameters (singleton
    box) and for the box b in [-0.1, 0.2] x kappa in [0.15, 0.45] at h = 0, 1, 2 (state level 2, clock {Delta}).

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/066/reproduce.py
Seed:   numpy default_rng(66). Single process, several minutes. Not a CI check (not check.py)."""
from scipy.special import ive, gammaincc
CAT = [(p, k) for p in (0.5, 0.75, 1.0, 1.25, 1.5, 2.0) for k in (0.2, 0.3, 0.45)]; NULL = [i for i, (p, k) in enumerate(CAT) if p <= 1]
BAR = 1 / (252 * 78)
def logive(nu, z):
    with np.errstate(all='ignore'): v = np.log(ive(nu, z))
    big = ~np.isfinite(v) & (z > 1e4)
    v[big] = -0.5 * np.log(2 * np.pi * z[big]) + np.log1p(-(4 * nu * nu - 1) / (8 * z[big]))
    return v
def logK(p, k, D, x, y):
    out = np.full(np.broadcast(x, y).shape, -np.inf); pos = (x > 0) & (y > 0); xp, yp = x[pos], y[pos]
    Dp = np.broadcast_to(D, out.shape)[pos]
    if p == 1:
        v = k * k * Dp; out[pos] = -(np.log(yp / xp) + v / 2) ** 2 / (2 * v) - np.log(yp * np.sqrt(2 * np.pi * v))
    else:
        h = abs(p - 1); nu = 1 / (2 * h); v = k * k * h * h * Dp; A, B = xp ** (2 - 2 * p), yp ** (2 - 2 * p); z = xp ** (1 - p) * yp ** (1 - p) / v
        out[pos] = 0.5 * np.log(xp) + (0.5 - 2 * p) * np.log(yp) - np.log(k * k * h * Dp) - (np.sqrt(A) - np.sqrt(B)) ** 2 / (2 * v) + logive(nu, z)
        if p < 1:
            a0 = (x > 0) & (y == 0); Da = np.broadcast_to(D, out.shape)[a0]; v0 = k * k * h * h * Da
            with np.errstate(divide='ignore'): out[a0] = np.log(gammaincc(nu, x[a0] ** (2 - 2 * p) / (2 * v0)))
    out[(x == 0) & (y == 0)] = 0.0
    return out


import numpy as np, math
from scipy.stats import norm
from scipy.integrate import quad
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

rng = np.random.default_rng(65)
def logistic(v): return 0.5 * (1 + math.tanh(v / 2)) if math.isfinite(v) else (1.0 if v > 0 else 0.0)
def A(h, t, x, y, rho, beta):
    L = 0.5 if (x == 0 or y == 0) else logistic(beta * math.log(y / x)); ap = rho * (h == 1) + (1 - rho) * L
    return ap if t == 1 else 1 - ap
def Abar(h, t, a, b, c, d, rho, beta):
    if beta == 0: Lm = Lp = 0.5
    else:
        rm = math.log(c / b) if c > 0 else -math.inf; rp = math.log(d / a) if a > 0 else math.inf
        vals = [logistic(beta * rm), logistic(beta * rp)] + ([0.5] if (a == 0 or c == 0) else []); Lm, Lp = min(vals), max(vals)
    if t == 1: return rho * (h == 1) + (1 - rho) * Lp
    return 1 - (rho * (h == 1) + (1 - rho) * Lm)
def Iint(z, t, a):
    lo, hi = (0.0, DEL / 2 - t * a) if z == 0 else (max(0.0, DEL * (z - 0.5) - t * a), DEL * (z + 0.5) - t * a)
    return (lo, hi) if hi > lo else None
def log_bound_state(z, mu, s, a, rho, beta, L):
    n = len(z) - 1; out = []; prev = None
    for lv in range(L + 1):
        K = 2 ** lv; U = [dict() for _ in range(n + 1)]
        def subs(zz, t):
            I = Iint(zz, t, a)
            if I is None: return None
            e = I[0] + (I[1] - I[0]) * np.arange(K + 1) / K; return e[:-1], e[1:]
        for t in (1, -1):
            if Iint(z[n], t, a): U[n][t] = np.zeros(K)
        for j in range(n - 1, -1, -1):
            for h in (1, -1):
                sh = subs(z[j], h)
                if sh is None: continue
                terms = []
                for t, Ut in U[j + 1].items():
                    tc, td = subs(z[j + 1], t)
                    terms.append(np.array([[math.log(max(W(sh[0][i], sh[1][i], tc[k], td[k], mu, s), 1e-300)) + math.log(Abar(h, t, sh[0][i], sh[1][i], tc[k], td[k], rho, beta)) for k in range(K)] for i in range(K)]) + Ut[None, :])
                T = np.logaddexp.reduce(np.concatenate(terms, axis=1), axis=1); Uj = np.minimum(T, 0.0)
                if prev is not None: Uj = np.minimum(Uj, prev[j][h][np.arange(K) // 2])
                U[j][h] = Uj
        out.append(max(u.max() for u in U[0].values())); prev = U
    return np.array(out)
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

rng = np.random.default_rng(66)
def rec(z, box, Dls, vs, a, mode, rho, beta, L):
    """Claim 066 (4) for one box and clock: mode 'state' (065 sign cells, Abar) or 'support' (064 expanded cells)."""
    bL, bH, wL, wH = box; n = len(z) - 1; signs = (1, -1) if mode == 'state' else (0,); out = []; prev = None
    def cellint(zz, t): return Iint(zz, t, a) if mode == 'state' else expanded(zz, a)
    for lv in range(L + 1):
        K = 2 ** lv; U = [dict() for _ in range(n + 1)]
        def subs(zz, t):
            I = cellint(zz, t)
            if I is None: return None
            e = I[0] + (I[1] - I[0]) * np.arange(K + 1) / K; return e[:-1], e[1:]
        for t in signs:
            if cellint(z[n], t): U[n][t] = np.zeros(K)
        for j in range(n - 1, -1, -1):
            for h in signs:
                sh = subs(z[j], h)
                if sh is None: continue
                terms = []
                for t, Ut in U[j + 1].items():
                    tc, td = subs(z[j + 1], t)
                    terms.append(np.array([[math.log(Wc(sh[0][i], sh[1][i], tc[k], td[k], bL, bH, wL, wH, Dls[j], vs[j]))
                                            + (math.log(Abar(h, t, sh[0][i], sh[1][i], tc[k], td[k], rho, beta)) if mode == 'state' else 0.0)
                                            for k in range(K)] for i in range(K)]) + Ut[None, :])
                T = np.logaddexp.reduce(np.concatenate(terms, axis=1), axis=1); Uj = np.minimum(T, 0.0)
                if prev is not None: Uj = np.minimum(Uj, prev[j][h][np.arange(K) // 2])
                U[j][h] = Uj
        out.append(max(u.max() for u in U[0].values())); prev = U
    return np.array(out)
def boxes(B, h):
    bL, bH, wL, wH = B; k = 2 ** h; be = np.linspace(bL, bH, k + 1); we = np.linspace(wL, wH, k + 1)
    return [(be[i], be[i + 1], we[j], we[j + 1]) for i in range(k) for j in range(k)]
def logD66(z, B, h, clocks, Dls, a, rho, beta, L):
    st = np.max([rec(z, bx, Dls, v, a, 'state', rho, beta, L) for bx in boxes(B, h) for v in clocks], axis=0)
    su = np.max([rec(z, bx, Dls, v, a, 'support', rho, beta, L) for bx in boxes(B, h) for v in clocks], axis=0)
    return np.minimum(st, su)
# (a)
DEL = 0.05; a = 0.02; rho = 0.6; Dls = np.array([0.02, 0.06]); clocks = [Dls, np.array([0.04, 0.02])]; Bx = (-0.5, 0.5, 0.09, 0.36); Mc = 400000; z0 = 4
for beta in (5.0, -5.0):
    H0 = np.where(rng.random(Mc) < 0.5, 1, -1); lo = np.array([Iint(z0, h, a)[0] for h in (1, -1)]); hi = np.array([Iint(z0, h, a)[1] for h in (1, -1)])
    idx = (H0 == -1).astype(int); X0 = lo[idx] + (hi[idx] - lo[idx]) * rng.random(Mc)
    bb = rng.uniform(-0.5, 0.5, Mc); ww = rng.uniform(0.09, 0.36, Mc); vv = np.array(clocks)[rng.integers(0, 2, Mc)]
    X1 = X0 * np.exp(bb * Dls[0] - ww * vv[:, 0] / 2 + np.sqrt(ww * vv[:, 0]) * rng.standard_normal(Mc))
    X2 = X1 * np.exp(bb * Dls[1] - ww * vv[:, 1] / 2 + np.sqrt(ww * vv[:, 1]) * rng.standard_normal(Mc))
    def step(h, x, y):
        Lg = 0.5 * (1 + np.tanh(beta * np.log(y / x) / 2)); ap = rho * (h == 1) + (1 - rho) * Lg; return np.where(rng.random(Mc) < ap, 1, -1)
    H1 = step(H0, X0, X1); H2 = step(H1, X1, X2)
    L1 = np.floor(np.maximum(0, X1 + a * H1) / DEL + 0.5).astype(int); L2 = np.floor(np.maximum(0, X2 + a * H2) / DEL + 0.5).astype(int)
    viol = 0; cnt = 0; marg = []
    for v1 in range(z0 - 3, z0 + 4):
        for v2 in range(v1 - 3, v1 + 4):
            p = np.mean((L1 == v1) & (L2 == v2))
            if p > 2e-4:
                cnt += 1; lD = logD66([z0, v1, v2], Bx, 1, clocks, Dls, a, rho, beta, 2)[-1]
                viol += math.log(p) > lD + 4 * math.sqrt(p / Mc) / p; marg.append(lD - math.log(p))
    print(f'(a) beta = {beta:+.0f}: {cnt} frequent 2-step label paths, domination violations {viol}; median log(D / frequency) {np.median(marg):.2f}', flush=True)
# (b)
w0 = 0.0; w1 = 0.0
for _ in range(10):
    z = [int(x) for x in rng.integers(1, 7, 4)]; Dls = rng.uniform(0.01, 0.08, 3); vs = Dls * rng.uniform(0.5, 2, 3); B = (-0.3, 0.3, 0.05, 0.2)
    d66 = logD66(z, B, 1, [vs], Dls, 0.0, 0.5, 3.0, 2); d34 = np.max([log_bound_box(z, bx, Dls, vs, 2) for bx in boxes(B, 1)], axis=0)
    w0 = max(w0, np.max(np.abs(d66 - d34)))
    b, w = rng.uniform(-0.3, 0.3), rng.uniform(0.05, 0.2); mu = (b - w / 2) * Dls[0]; Dc = np.full(3, Dls[0])
    d66s = logD66(z, (b, b, w, w), 0, [Dc], Dc, 0.02, 0.5, 3.0, 2)
    d65 = np.minimum(log_bound_state(z, mu, math.sqrt(w * Dls[0]), 0.02, 0.5, 3.0, 2), log_bound_noise(z, mu, math.sqrt(w * Dls[0]), 0.02, 'support', 2))
    w1 = max(w1, np.max(np.abs(d66s - d65)))
print(f'(b) zero radius vs claim 034: max |log diff| {w0:.1e}; singleton box, v = Delta vs claim 065: max |log diff| {w1:.1e}', flush=True)
# (c)
def cevmass(p, k, v, r, lo, hi):
    s = k * r ** (p - 1) * math.sqrt(v)
    g = lambda u: math.exp(logK(p, k, np.array([v]), np.array([r]), np.array([r * math.exp(s * u)]))[0]) * r * math.exp(s * u) * s
    ul = max(-60.0, (math.log(lo) - math.log(r)) / s) if lo > 0 else -60.0; uh = min(60.0, (math.log(hi) - math.log(r)) / s)
    return quad(g, ul, uh, limit=400, points=[0.0] if ul < 0 < uh else None)[0] if uh > ul else 0.0
def rowF(xi, z, h, a, v, Zmax):
    p, k, rf = xi; lo, hi = Iint(z, h, a); r = (lo + hi) / 2; out = {}
    for t in (1, -1):
        At = rf * (h == t) + (1 - rf) / 2
        for zp in range(Zmax + 1):
            I = Iint(zp, t, a)
            if I: out[(zp, t)] = At * cevmass(p, k, v, r, I[0], I[1])
        I = Iint(Zmax, t, a); out[('tail', t)] = At * cevmass(p, k, v, r, I[1], math.inf)
    return out
DEL = 0.05; a = 0.02; worst = 0.0
for xi in ((1.5, 0.45, 0.7), (2.0, 0.3, 0.0), (1.25, 0.2, 0.4)):
    for z in (0, 1, 4):
        for h in (1, -1):
            if Iint(z, h, a) is None: continue
            for v in (0.02, 0.25):
                worst = max(worst, abs(sum(rowF(xi, z, h, a, v, 40).values()) - 1))
xi = (1.5, 0.45, 0.7); v = 0.05; z0 = 4; pi0 = {h: 1.0 / len([t for t in (1, -1) if Iint(z0, t, a)]) for h in (1, -1) if Iint(z0, h, a)}
tot = 0.0
r1 = {h: rowF(xi, z0, h, a, v, 30) for h in pi0}
for (z1, t1), p1 in {k_: sum(pi0[h] * r1[h].get(k_, 0) for h in pi0) for k_ in set().union(*r1.values())}.items():
    if z1 == 'tail' or p1 < 1e-14: tot += p1; continue
    tot += p1 * sum(rowF(xi, z1, t1, a, v, 30).values())
print(f'(c) forecast rows over (z\', t) with tails: max |sum - 1| {worst:.1e} (36 rows); two-step forecast total mass {tot:.10f}', flush=True)
# (d)
DEL = 0.01; sd = 0.3 / math.sqrt(252); D1 = 1 / 252; n = 40; a = DEL / 2; Bx = (-0.1, 0.2, 0.15 ** 2, 0.45 ** 2); rows = []
for _ in range(6):
    X = 5.0 * np.exp(np.cumsum(np.r_[0.0, rng.normal(-0.045 * D1, sd, n)])); Hs = [1 if rng.random() < 0.5 else -1]
    for j in range(n): Hs.append(1 if rng.random() < 0.5 * (Hs[-1] == 1) + 0.25 else -1)
    z = list(np.floor(np.maximum(0, X + a * np.array(Hs)) / DEL + 0.5).astype(int)); lq = forecast_logq(z, -0.045 * D1, sd); Dls = np.full(n, D1)
    r = [lq - logD66(z, (0.0, 0.0, 0.09, 0.09), 0, [Dls], Dls, a, 0.5, 0.0, 2)[-1]] + [lq - logD66(z, Bx, h, [Dls], Dls, a, 0.5, 0.0, 2)[-1] for h in range(3)]
    rows.append(r)
md = np.median(np.array(rows), 0)
print(f'(d) $5, cent tick, a = tick/2, rho = .5, 40 days: median log E singleton true box (claim 065) {md[0]:+.2f}; box at h = 0, 1, 2: ' + ', '.join(f'{x:+.2f}' for x in md[1:]))
