"""Reviewer's independent check of claim 058 (written before reading checks/058/*).
(a) Earlier-window likelihood rectangle (7)-(9): Monte Carlo coverage P(true (b,kappa) retained) >= 1 - delta for GBM
    earlier windows (daily, 1 year), several truths and references; containment of the confidence set H_dec in the
    rectangle at random parameter points.
(b) The raw-moment counterexample: truncated expected score over evaluation log-return r in [-R, R] grows without
    bound in R for a large training endpoint (integrand ~ exp(1.5 r^2 - 3 r)).
(c) Full honest pipeline: earlier 1-year daily window -> rectangle at delta = 0.05 (reference (0, 0.3)); test = next
    two years daily (train year 1, evaluate year 2) with claim 057's score on that rectangle (raw E^dec) and the safe
    score (6) with c = 50; alpha = 0.1; CEV catalogue p in {1/2,1,3/2} x kappa in {0.2,0.3,0.45}. Null false alarms
    and power at CEV p = 3/2, and the declared rectangle widths.

Rerun:  uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/058/reproduce.py
Seed:   numpy default_rng(58). Runtime about 4 minutes. Not a CI check (not check.py)."""
import numpy as np, math
from scipy.special import ive, gammaincc
from scipy.optimize import minimize

def logf(p, D, x, y, k):
    if p == 1:
        v = k * k * D; return -(np.log(y / x) + v / 2) ** 2 / (2 * v) - np.log(y * np.sqrt(2 * np.pi * v))
    h = abs(p - 1); nu = 1 / (2 * h); v = k * k * h * h * D
    A, B = x ** (2 - 2 * p), y ** (2 - 2 * p); z = x ** (1 - p) * y ** (1 - p) / v
    with np.errstate(divide='ignore'):
        return 0.5 * np.log(x) + (0.5 - 2 * p) * np.log(y) - np.log(k * k * h * D) - (np.sqrt(A) - np.sqrt(B)) ** 2 / (2 * v) + np.log(ive(nu, z))
def logK(p, k, D, x, y):
    out = np.full(np.broadcast(x, y).shape, -np.inf); pos = (x > 0) & (y > 0)
    out[pos] = logf(p, D, x[pos], y[pos], k)
    if p < 1:
        a0 = (x > 0) & (y == 0); h = 1 - p; v = k * k * h * h * D
        with np.errstate(divide='ignore'): out[a0] = np.log(gammaincc(1 / (2 * h), x[a0] ** (2 - 2 * p) / (2 * v)))
    out[(x == 0) & (y == 0)] = 0.0
    return out

def ell(b, w, R, Dt, Y):
    return np.sum(-(R - (b - w / 2) * Dt) ** 2 / (2 * w * Dt) - 0.5 * np.log(2 * np.pi * w * Dt) - np.log(Y), axis=-1)
def logDGB(y0, Y, Dt, blo, bhi, unconstrained=False):
    """Rows of Y: positive evaluation prices; Dt: step lengths (n,). Returns log sup over b in [blo,bhi], w > 0."""
    P = np.c_[y0, Y]; R = np.log(P[:, 1:] / P[:, :-1]); n = Y.shape[1]; tau = Dt.sum()
    a = R.sum(1) / tau; Q = ((R - a[:, None] * Dt) ** 2 / Dt).sum(1)
    if unconstrained:
        with np.errstate(divide='ignore'):
            return np.where(Q > 0, -(n / 2) * (np.log(2 * np.pi * Q / n) + 1) - 0.5 * np.log(Dt).sum() - np.log(Y).sum(1), np.inf)
    best = np.full(len(Y), -np.inf)
    for c in (blo, bhi):
        A = Q + tau * (a - c) ** 2; w = 2 * A / (n + np.sqrt(n * n + tau * A))
        with np.errstate(divide='ignore', invalid='ignore'):
            v = np.where(w > 0, ell(c, w[:, None], R, Dt, Y) if False else np.array([ell(c, wi, Ri, Dt, Yi) if wi > 0 else -np.inf for wi, Ri, Yi in zip(w, R, Y)]), -np.inf)
        best = np.maximum(best, v)
    bi = a + Q / (2 * n); ok = (Q > 0) & (bi >= blo) & (bi <= bhi)
    vi = np.array([ell(b_, Q_ / n, Ri, Dt, Yi) if o else -np.inf for b_, Q_, Ri, Yi, o in zip(bi, Q, R, Y, ok)])
    best = np.maximum(best, vi)
    inf = (Q == 0) & (a >= blo) & (a <= bhi)
    return np.where(inf, np.inf, best)


def logDGBC(y0, Y, Dt, blo, bhi, slo, shi):
    """log max over b in [blo,bhi], kappa in [slo,shi] of the Gaussian price likelihood (claim 057 (3)-(5))."""
    P = np.c_[y0, Y]; R = np.log(P[:, 1:] / P[:, :-1]); n = Y.shape[1]; tau = Dt.sum(); wlo, whi = slo * slo, shi * shi
    a = R.sum(1) / tau; Q = ((R - a[:, None] * Dt) ** 2 / Dt).sum(1)
    def L(b, w): return np.sum(-(R - (b[:, None] - w[:, None] / 2) * Dt) ** 2 / (2 * w[:, None] * Dt) - 0.5 * np.log(2 * np.pi * w[:, None] * Dt) - np.log(Y), axis=1)
    cands = []
    for c in (blo, bhi):
        A = Q + tau * (a - c) ** 2; v = 2 * A / (n + np.sqrt(n * n + tau * A)); cands.append(L(np.full_like(a, c), np.clip(v, wlo, whi)))
    for d in (wlo, whi):
        cands.append(L(np.clip(a + d / 2, blo, bhi), np.full_like(a, d)))
    bi, wi = a + Q / (2 * n), Q / n; ok = (bi >= blo) & (bi <= bhi) & (wi >= wlo) & (wi <= whi)
    cands.append(np.where(ok, L(np.where(ok, bi, blo), np.where(ok, wi, wlo)), -np.inf))
    return np.max(np.array(cands), axis=0)


from scipy.optimize import brentq
def rect(z, d, delta, b0, k0):
    """Claim 058 (7)-(9). z: earlier log returns, d: step lengths. Returns (blo, bhi, slo, shi) or None (fallback)."""
    n = len(z); tau = d.sum(); a = z.sum() / tau; Q = ((z - a * d) ** 2 / d).sum()
    if Q <= 0: return None
    C = -(n / 2) * math.log(2 * math.pi) - 0.5 * np.log(d).sum()
    Hv = lambda w: C - (n / 2) * math.log(w) - Q / (2 * w)
    w0 = k0 * k0; logq = np.sum(-(z - (b0 - w0 / 2) * d) ** 2 / (2 * w0 * d) - 0.5 * np.log(2 * math.pi * w0 * d))
    L = math.log(delta) + logq; wm = Q / n; Hmax = Hv(wm)
    lo = wm
    while Hv(lo) > L: lo /= 2
    hi = wm
    while Hv(hi) > L: hi *= 2
    w_m = brentq(lambda w: Hv(w) - L, lo, wm); w_p = brentq(lambda w: Hv(w) - L, wm, hi)
    M = math.sqrt(2 * w_p * (Hmax - L) / tau)
    return a + w_m / 2 - M, a + w_p / 2 + M, math.sqrt(w_m), math.sqrt(w_p), (C, Q, a, tau, L)
rng = np.random.default_rng(58)
nd = 252; d = np.full(nd, 1 / 252); worst_cov = 1.0; viol = 0
for (b, k) in [(0.0, 0.3), (0.1, 0.3), (0.05, 0.4), (-0.1, 0.2), (0.0, 0.6)]:
    for (b0, k0) in [(0.0, 0.3), (0.05, 0.25)]:
        miss = 0; R = 4000
        for r in range(R):
            z = (b - k * k / 2) * d + k * np.sqrt(d) * rng.standard_normal(nd); out = rect(z, d, 0.05, b0, k0)
            if out is None: continue
            blo, bhi, slo, shi, (C, Q, a, tau, L) = out
            miss += not (blo <= b <= bhi and slo <= k <= shi)
            if r < 50:                                   # containment of H_dec in the rectangle at random points
                for _ in range(40):
                    bb = rng.uniform(blo - 1, bhi + 1); kk = rng.uniform(max(1e-3, slo / 2), shi * 2); w = kk * kk
                    logh = np.sum(-(z - (bb - w / 2) * d) ** 2 / (2 * w * d) - 0.5 * np.log(2 * math.pi * w * d))
                    if logh >= L and not (blo <= bb <= bhi and slo <= kk <= shi): viol += 1
        worst_cov = min(worst_cov, 1 - miss / R)
print(f'(a) earlier-window rectangle, delta = 0.05, 10 (truth, reference) designs x 4000: worst coverage {worst_cov:.4f} (>= 0.95); '
      f'containment violations {viol}')

# (b) counterexample divergence: start 1, unit times, catalogue {(1,1/2),(2,1)}, true GBM scale 1, on event A
x = 6.0      # a training endpoint large enough that p=2 is selected
l1 = lambda x, y, k: -(np.log(y / x) + k * k / 2) ** 2 / (2 * k * k) - np.log(y * k * np.sqrt(2 * np.pi))
def l2(x, y, k):
    v = k * k; return np.log(x) - 3 * np.log(y) - 0.5 * np.log(2 * np.pi * v) - (1 / y - 1 / x) ** 2 / (2 * v) + np.log(-np.expm1(-2 / (x * y * v)))
sel_p2 = l2(1.0, x, 1.0) > l1(1.0, x, 0.5)
from scipy.integrate import quad
part = []
for Rr in (2, 4, 6, 8, 10):
    f = lambda r: math.exp(l2(x, x * math.exp(r), 1.0) - l1(x, x * math.exp(r), 0.5) + l1(x, x * math.exp(r), 1.0) + r + math.log(x))
    part.append(quad(f, -Rr, Rr, limit=400)[0])
print(f'(b) training endpoint {x}: p=2 selected {bool(sel_p2)}; truncated E[score | x] over |r| <= 2,4,6,8,10: ' + ', '.join(f'{v:.3g}' for v in part))

CAT = [(p, k) for p in (0.5, 1.0, 1.5) for k in (0.2, 0.3, 0.45)]; NULL = [i for i, (p, k) in enumerate(CAT) if p <= 1]
D, AL, DEL, CAP = 1 / 252, 0.1, 0.05, 50.0
def pipeline(S3):     # S3: (M, 756) prices from 1; earlier = first 252 increments; test = next 504
    M = len(S3); full = np.c_[np.ones(M), S3]; Ed = np.zeros(M); widths = []
    E_pre = full[:, :253]; T_ = full[:, 252:]
    for i in range(M):
        z = np.diff(np.log(E_pre[i])); out = rect(z, np.full(252, D), DEL, 0.0, 0.3)
        P = T_[i]; K = 252
        tr = np.array([logK(p, k, D, P[None, :K], P[None, 1:K + 1]).sum() for p, k in CAT]); sel = int(np.argmax(tr))
        ev = np.array([logK(p, k, D, P[None, K:-1], P[None, K + 1:]).sum() for p, k in CAT]); lG = ev[sel]; lG0 = ev[NULL].max()
        Dt = np.full(252, D)
        if (P[K:] > 0).all():
            lDG = (logDGB(np.array([P[K]]), P[None, K + 1:], Dt, 0, 0, unconstrained=True)[0] if out is None
                   else logDGBC(np.array([P[K]]), P[None, K + 1:], Dt, out[0], out[1], out[2], out[3])[0])
        else: lDG = -np.inf
        lD = max(lG0, lDG); Ed[i] = math.exp(min(lG - lD, 700)) if np.isfinite(lG) and np.isfinite(lD) else 0.0
        if out is not None: widths.append((out[2], out[3], out[1] - out[0]))
    Es = np.minimum(Ed, CAP) / (1 + (CAP - 1) * DEL)
    return Ed, Es, np.array(widths)
def gbm(b, s, M, n): return np.exp(np.cumsum((b - s * s / 2) * D + s * math.sqrt(D) * rng.standard_normal((M, n)), axis=1))
def cev15(k, M, n):
    c = k * 0.5; B = np.zeros((M, 4)); B[:, 0] = 1 / c; out = np.empty((M, n))
    for j in range(n): B += math.sqrt(D) * rng.standard_normal((M, 4)); out[:, j] = (c * np.linalg.norm(B, axis=1)) ** -2
    return out
print(f'(c) honest pipeline, delta={DEL}, alpha={AL}, cap {CAP}: raw E^dec and safe score (6); safe rejection needs E^dec > {(1 + (CAP - 1) * DEL) / AL:.1f}')
M = 2000
for label, S in [('GBM b=0.05 s=0.33 (null)', gbm(.05, .33, M, 756)), ('GBM b=0 s=0.30 (null, on grid)', gbm(0, .30, M, 756)),
                 ('CEV p=1.5 k=0.3 (alt)', cev15(.3, M, 756)), ('CEV p=1.5 k=0.45 (alt)', cev15(.45, M, 756))]:
    Ed, Es, W = pipeline(S)
    print(f'   {label:32s} raw: mean {Ed.mean():.3g}, P(>1/a) {np.mean(Ed > 1 / AL):.4f} | safe: mean {Es.mean():.3f}, P(>1/a) {np.mean(Es > 1 / AL):.4f} | '
          f'median rectangle scale [{np.median(W[:, 0]):.3f}, {np.median(W[:, 1]):.3f}], drift width {np.median(W[:, 2]):.2f}', flush=True)
