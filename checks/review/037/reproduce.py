"""Reviewer's independent check of claim 037 (written before reading checks/037/* and checks/d19-conditional-*).
Single process. Reuses the reviewer's claim-036 midpoint recursion and allowances (inlined).
(a) Bound (6): for random positive-label records (coarse tick, nonproportional clocks) and random subboxes, the exact
    conditional log ratio log g_theta - log g_centre at 200 parameters in the box (computed with M = 256, widened by
    its own eps enclosure) never exceeds eta_cond; also Taylor's T_E(B) bounds the evaluation log density ratio at y*.
(b) The old and new parameter allowances on the claim-036 review's cent-tick design ($5 GBM null kappa = .3,
    box b in [-0.1, 0.2] x kappa in [0.15, 0.45], 41 x 41 cover, per-subbox constants): median over boxes of
    eta_N + eta_k and of eta_cond, for k = n = 30 and k = n = 125 days; and the certified median log E using claim 036's
    allowance alone and using min(old, new), with M = 16, against the
    uncertified grid value and claim 034's box bound at h = 2, level 2 on the same paths (k = n = 30 only); numerator =
    claim 031's forecast at the true law. Float evaluation, not outward arithmetic.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/037/reproduce.py
Seed:   numpy default_rng(37). Single process, a few minutes. Not a CI check (not check.py)."""

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

rng = np.random.default_rng(37)
def eta_cond(s, z, Dl, v, k, B):
    bm, bp, wm, wp = B; bg, wg = (bm + bp) / 2, (wm + wp) / 2; rb, rw = (bp - bm) / 2, (wp - wm) / 2
    lc = logcells(z); ys = np.r_[math.log(s), lc.mean(1)]; hs = np.r_[0.0, (lc[:, 1] - lc[:, 0]) / 2]; R = np.diff(ys); t = hs[:-1] + hs[1:]; av = Dl / v; N = len(z)
    T = slice(0, k); E = slice(k, N)
    OBT = np.sum(np.abs(av[:k - 1] - av[1:k]) * 2 * hs[1:k]) + abs(av[k - 1]) * 2 * hs[k]
    OCT = np.sum(((np.abs(R[T]) + t[T]) ** 2 - np.maximum(0, np.abs(R[T]) - t[T]) ** 2) / v[T])
    dBE = abs(av[k]) * hs[k] + np.sum(np.abs(av[k:N - 1] - av[k + 1:N]) * hs[k + 1:N]) + abs(av[N - 1]) * hs[N]
    dCE = np.sum((2 * np.abs(R[E]) * t[E] + t[E] ** 2) / v[E])
    c1 = max(abs(b / w - bg / wg) for b in (bm, bp) for w in (wm, wp)); c2 = max(abs(1 / w - 1 / wg) for w in (wm, wp)) / 2
    AE = np.sum(Dl[E] ** 2 / v[E]); BE = np.sum(Dl[E] * R[E] / v[E]); VE = v[E].sum(); n = N - k
    QE = lambda b: np.sum((R[E] - b * Dl[E]) ** 2 / v[E])
    Sb = (BE - bg * AE) / wg + Dl[E].sum() / 2; Sw = -n / (2 * wg) + QE(bg) / (2 * wg ** 2) - VE / 8
    Hbb = AE / wm; Hbw = max(abs(BE - bm * AE), abs(BE - bp * AE)) / wm ** 2; Hww = n / (2 * wm ** 2) + max(QE(bm), QE(bp)) / wm ** 3
    TE = abs(Sb) * rb + abs(Sw) * rw + (Hbb * rb ** 2 + 2 * Hbw * rb * rw + Hww * rw ** 2) / 2
    return c1 * (OBT + dBE) + c2 * (OCT + dCE) + TE, TE, (R, Dl, v, E)
# (a)
DEL = 0.05; worst = -math.inf; wtay = -math.inf; cases = 0
for _ in range(20):
    s = 1.0; k = int(rng.integers(2, 5)); n = int(rng.integers(1, 4)); N = k + n; Dl = rng.uniform(0.005, 0.03, N); v = Dl * rng.uniform(0.4, 2.5, N)
    X = s * np.exp(np.cumsum(-0.04 * v + np.sqrt(0.08 * v) * rng.standard_normal(N))); z = [max(1, int(math.floor(x / DEL + 0.5))) for x in X]
    bc, wc = rng.uniform(-0.3, 0.3), rng.uniform(0.04, 0.2); rb, rw = rng.uniform(0.01, 0.3), rng.uniform(0.002, 0.03); rw = min(rw, wc / 2)
    B = (bc - rb, bc + rb, wc - rw, wc + rw); ec, TE, (R, _, _, E) = eta_cond(s, z, Dl, v, k, B)
    bs = np.r_[bc, rng.uniform(B[0], B[1], 200)]; ws = np.r_[wc, rng.uniform(B[2], B[3], 200)]; lq = logQ(s, z, Dl, v, bs, ws, 256); e = eps(s, z, Dl, v, B, 256)[0]
    lg = lq[-1] - lq[k - 1]; slack = 2 * (e[-1] + e[k - 1]); worst = max(worst, (lg[1:] - lg[0] - slack - ec).max()); cases += 200
    f = lambda b, w: np.sum(-(R[E] - b * Dl[E] + w * v[E] / 2) ** 2 / (2 * w * v[E]) - 0.5 * np.log(2 * math.pi * w * v[E]))
    wtay = max(wtay, max(f(b, w) - f(bc, wc) for b, w in zip(bs[1:], ws[1:])) - TE)
print(f'(a) {cases} (record, box, parameter) cases: max (log g_theta - log g_centre - 2*eps - eta_cond) {worst:.2e} (<= 0); '
      f'max (evaluation log ratio at y* - T_E) {wtay:.2e} (<= 0)')
# (b)
DEL = 0.01; sd = 0.3 / math.sqrt(252); D1 = 1 / 252; Bx = (-0.1, 0.2, 0.15 ** 2, 0.45 ** 2)
bgr = np.linspace(Bx[0], Bx[1], 42); wgr = np.linspace(Bx[2], Bx[3], 42)
for kk in (30, 125):
    rows = []
    for _ in range(4):
        N = 2 * kk; X = 5.0 * np.exp(np.cumsum((0.05 - 0.045) * D1 + sd * rng.standard_normal(N))); z = [int(math.floor(x / DEL + 0.5)) for x in X]
        Dl = np.full(N, D1); ze = [z[kk - 1]] + z[kk:]; lq = forecast_logq(ze, (0.05 - 0.045) * D1, sd)
        olds, news, ups, lows, upo, hmax = [], [], [], [], [], []
        cent_b = (bgr[:-1] + bgr[1:]) / 2; cent_w = (wgr[:-1] + wgr[1:]) / 2; BG, WG = [a.ravel() for a in np.meshgrid(cent_b, cent_w, indexing='ij')]
        QG = logQ(5.0, z, Dl, Dl, BG, WG, 16); idx = 0
        for i in range(41):
            for j in range(41):
                B = (bgr[i], bgr[i + 1], wgr[j], wgr[j + 1]); e, Lb, Lw = eps(5.0, z, Dl, Dl, B, 16)
                old = (Lb[-1] + Lb[kk - 1]) * (B[1] - B[0]) / 2 + (Lw[-1] + Lw[kk - 1]) * (B[3] - B[2]) / 2; new = eta_cond(5.0, z, Dl, Dl, kk, B)[0]
                lr = QG[-1, idx] - QG[kk - 1, idx]; ups.append(min(0.0, e[-1] + e[kk - 1] + min(old, new) + lr)); upo.append(min(0.0, e[-1] + e[kk - 1] + old + lr)); lows.append(lr); olds.append(old); news.append(new); idx += 1
        l34 = max(log_bound_box(ze, bx, Dl[:kk], Dl[:kk], 2)[-1] for bx in [(a1, a2, c1, c2) for a1, a2 in zip(np.linspace(Bx[0], Bx[1], 5)[:-1], np.linspace(Bx[0], Bx[1], 5)[1:])
                                                                        for c1, c2 in zip(np.linspace(Bx[2], Bx[3], 5)[:-1], np.linspace(Bx[2], Bx[3], 5)[1:])]) if kk == 30 else math.nan
        rows.append([np.median(olds), np.median(news), lq - max(ups), lq - max(lows), lq - max(upo), lq - l34])
    r = np.median(np.array(rows), 0)
    print(f'(b) k = n = {kk} days, 41 x 41 cover, M = 16: median allowance per box old eta_N + eta_k {r[0]:.2f}, new eta_cond {r[1]:.3f}; '
          f'median log E certified: claim 036 alone {r[4]:+.2f}, with min(old, new) {r[2]:+.2f}; uncertified grid {r[3]:+.2f}; claim 034 box (h = 2, level 2) {r[5]:+.2f}', flush=True)
