"""Reviewer's independent check of claim 038 (written before reading checks/038/*). Single process.
Reuses the reviewer's claim-036 midpoint recursion and allowances and claim-037 eta_cond (inlined).
(a) Two-sided enclosure (2): exp(-eps-) Q <= L <= exp(eps+) Q against independent quadrature of L (J = 2, 3; coarse
    tick, nonproportional clocks, random parameters inside random boxes, M = 2, 4, 8, 16), with the box's own C_j;
    also the M^-2 scaling of eps+- and the comparison with claim 036's eps.
(b) The cent-tick design of the claim-036/037 reviews ($5 GBM null kappa = .3, box b in [-0.1, 0.2] x kappa in
    [0.15, 0.45], 41 x 41 cover, M = 16, k = n = 30 and 125 days): median integration allowances (claim 036 vs
    centered, training + joint, at the box nearest the truth) and the certified median log E with claim 037's
    parameter allowance and (i) claim 036's integration allowance, (ii) the directional centered allowances (4); and the
    upper bound on the ideal filtered log E from the centre lower bound D_center^low under each allowance.
    Float evaluation, not outward arithmetic.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/038/reproduce.py
Seed:   numpy default_rng(38). Single process, a few minutes. Not a CI check (not check.py)."""


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

rng = np.random.default_rng(38)
def eps_centered(s, z, Dl, v, B, M):
    """(1): prefix-J lower and upper centered allowances for every J (arrays indexed J-1)."""
    bm, bp, wm, wp = B; lc = logcells(z); a = np.r_[math.log(s), lc[:, 0]]; d = np.r_[math.log(s), lc[:, 1]]; Bmax = max(abs(bm), abs(bp))
    Rmax = np.maximum(np.abs(a[1:] - d[:-1]), np.abs(d[1:] - a[:-1])); C = (Rmax + Bmax * Dl + wp * v / 2) / (wm * v)
    r = np.r_[0.0, (d[1:] - a[1:]) / (2 * M)]; J = len(z)
    em = np.cumsum((r[1:] + r[:-1]) ** 2 / (2 * wm * v))
    ep = np.array([np.sum(r[1:Jp + 1] ** 2 * (C[:Jp] + np.r_[C[1:Jp], 0.0]) ** 2 / 2) for Jp in range(1, J + 1)])
    return em, ep
# (a)
DEL = 0.05; worst_lo = -math.inf; worst_hi = -math.inf; cases = 0; ratio = []; scal = 0.0
for _ in range(15):
    s = rng.uniform(0.8, 1.2); J = int(rng.integers(2, 4)); Dl = rng.uniform(0.004, 0.03, J); v = Dl * rng.uniform(0.5, 2.0, J)
    bc, wc = rng.uniform(-0.3, 0.3), rng.uniform(0.04, 0.25); B = (bc - 0.1, bc + 0.1, wc * 0.8, wc * 1.2)
    X = s * np.exp(np.cumsum(-wc * v / 2 + np.sqrt(wc * v) * rng.standard_normal(J))); z = [max(1, int(math.floor(x / DEL + 0.5))) for x in X]
    for _p in range(3):
        b, w = rng.uniform(B[0], B[1]), rng.uniform(B[2], B[3])
        lc = logcells(z); m = b * Dl - w * v / 2; sd = np.sqrt(w * v); y0 = math.log(s)
        if J == 2:
            f = lambda y1: norm.pdf(y1 - y0, m[0], sd[0]) * (norm.cdf(lc[1, 1] - y1, m[1], sd[1]) - norm.cdf(lc[1, 0] - y1, m[1], sd[1]))
            Lt = quad(f, lc[0, 0], lc[0, 1], epsabs=0, epsrel=1e-12, limit=200)[0]
        else:
            f = lambda y2, y1: norm.pdf(y1 - y0, m[0], sd[0]) * norm.pdf(y2 - y1, m[1], sd[1]) * (norm.cdf(lc[2, 1] - y2, m[2], sd[2]) - norm.cdf(lc[2, 0] - y2, m[2], sd[2]))
            Lt = dblquad(f, lc[0, 0], lc[0, 1], lc[1, 0], lc[1, 1], epsabs=0, epsrel=1e-10)[0]
        for M in (2, 4, 8, 16):
            lq = logQ(s, z, Dl, v, b, w, M)[-1, 0]; em, ep = eps_centered(s, z, Dl, v, B, M); e = eps(s, z, Dl, v, B, M)[0]
            worst_lo = max(worst_lo, (lq - em[-1]) - math.log(Lt)); worst_hi = max(worst_hi, math.log(Lt) - (lq + ep[-1])); cases += 1
            ratio.append(max(em[-1], ep[-1]) / e[-1])
        em1, ep1 = eps_centered(s, z, Dl, v, B, 1); em8, ep8 = eps_centered(s, z, Dl, v, B, 8); scal = max(scal, abs(em8[-1] * 64 / em1[-1] - 1), abs(ep8[-1] * 64 / ep1[-1] - 1))
print(f'(a) {cases} (record, parameter, M) cases: max violation lower {worst_lo:.2e}, upper {worst_hi:.2e} (both <= 0); '
      f'M^-2 scaling max rel error {scal:.1e}; median max(eps-, eps+) / eps_036 {np.median(ratio):.3f}')
# (b)
DEL = 0.01; sd = 0.3 / math.sqrt(252); D1 = 1 / 252; Bx = (-0.1, 0.2, 0.15 ** 2, 0.45 ** 2)
bgr = np.linspace(Bx[0], Bx[1], 42); wgr = np.linspace(Bx[2], Bx[3], 42)
for kk in (30, 125):
    rows = []
    for _ in range(4):
        N = 2 * kk; X = 5.0 * np.exp(np.cumsum((0.05 - 0.045) * D1 + sd * rng.standard_normal(N))); z = [int(math.floor(x / DEL + 0.5)) for x in X]
        Dl = np.full(N, D1); ze = [z[kk - 1]] + z[kk:]; lq = forecast_logq(ze, (0.05 - 0.045) * D1, sd)
        cent_b = (bgr[:-1] + bgr[1:]) / 2; cent_w = (wgr[:-1] + wgr[1:]) / 2; BG, WG = [a.ravel() for a in np.meshgrid(cent_b, cent_w, indexing='ij')]
        QG = logQ(5.0, z, Dl, Dl, BG, WG, 16); idx = 0; up_old, up_new, lo_old, lo_new = [], [], [], []; near = None
        for i in range(41):
            for j in range(41):
                B = (bgr[i], bgr[i + 1], wgr[j], wgr[j + 1]); e, Lb, Lw = eps(5.0, z, Dl, Dl, B, 16); em, ep = eps_centered(5.0, z, Dl, Dl, B, 16)
                eta = min((Lb[-1] + Lb[kk - 1]) * (B[1] - B[0]) / 2 + (Lw[-1] + Lw[kk - 1]) * (B[3] - B[2]) / 2, eta_cond(5.0, z, Dl, Dl, kk, B)[0])
                lr = QG[-1, idx] - QG[kk - 1, idx]
                up_old.append(min(0.0, e[-1] + e[kk - 1] + eta + lr)); lo_old.append(lr - e[-1] - e[kk - 1])
                hp = lambda J: min(e[J - 1], ep[J - 1]); hm = lambda J: min(e[J - 1], em[J - 1])
                up_new.append(min(0.0, eta + hp(N) + hm(kk) + lr)); lo_new.append(lr - hm(N) - hp(kk))
                if B[0] <= 0.05 <= B[1] and B[2] <= 0.09 <= B[3]: near = (e[-1] + e[kk - 1], hp(N) + hm(kk))
                idx += 1
        rows.append([near[0], near[1], lq - max(up_old), lq - max(up_new), lq - max(lo_old), lq - max(lo_new)])
    r = np.median(np.array(rows), 0)
    print(f'(b) k = n = {kk}: integration allowance at the true box, claim 036 {r[0]:.3f} vs centered upper {r[1]:.4f}; median certified log E '
          f'with claim 036 integration {r[2]:+.2f}, with centered {r[3]:+.2f}; upper bounds on the ideal log E from the centre lower bounds '
          f'(claim 036 / centered) {r[4]:+.2f} / {r[5]:+.2f}', flush=True)
