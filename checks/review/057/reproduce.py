"""Reviewer's independent check of claim 057 (written before reading checks/057/*).
(a) Rectangle profile (3)-(5) vs direct bounded numerical maximization over b in B, kappa in C (random paths, singleton
    intervals, Q_G = 0, n_e = 1).
(b) Monte Carlo, daily prices for two years, train year one, absorbed CEV catalogue p in {1/2,1,3/2} x kappa in
    {0.2,0.3,0.45}; B = [-0.10, 0.20]; scale intervals C in {[0.25,0.35], [0.28,0.32]}. Scores: claim 054 E,
    claim 055 E^drift, claim 056 E^B, claim 057 E^(B,C). Null means / false alarms at alpha = 0.1 for GBM inside and
    outside the rectangle, and power at CEV p = 3/2.

Rerun:  uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/057/reproduce.py
Seed:   numpy default_rng(57). Runtime about 3 minutes. Not a CI check (not check.py)."""
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

rng = np.random.default_rng(57); worst = 0.0; cases = 0
for t in range(60):
    n = int(rng.choice([1, 2, 3, 5, 20])); Dt = rng.uniform(0.002, 0.3, n); y0 = float(rng.uniform(.5, 2))
    Y = np.full((1, n), y0) if t % 10 == 0 else y0 * np.exp(np.cumsum(rng.normal(0.05 * Dt, 0.3 * np.sqrt(Dt))))[None, :]
    blo = float(rng.uniform(-1, .5)); bhi = blo if t % 7 == 0 else blo + float(rng.uniform(0, 1))
    slo = float(rng.uniform(.05, .5)); shi = slo if t % 5 == 0 else slo + float(rng.uniform(0, .6))
    lD = logDGBC(np.array([y0]), Y, Dt, blo, bhi, slo, shi)[0]; R = np.log(np.r_[y0, Y[0]][1:] / np.r_[y0, Y[0]][:-1])
    sg = lambda x: 1 / (1 + math.exp(-min(max(x, -700), 700)))
    def nll(th):
        b = blo + (bhi - blo) * sg(th[0]); s = slo + (shi - slo) * sg(th[1]); return -ell(b, s * s, R, Dt, Y[0])
    best = min(minimize(nll, [s0, l0], method='Nelder-Mead', options={'xatol': 1e-12, 'fatol': 1e-14, 'maxiter': 40000}).fun
               for s0 in (-30, -3, 0, 3, 30) for l0 in (-30, -3, 0, 3, 30))
    worst = max(worst, abs(-best - lD) / max(1, abs(lD))); cases += 1
    assert np.isfinite(lD)
print(f'(a) {cases} rectangle profiles (incl. singletons, Q_G=0, n_e=1) vs Nelder-Mead: max rel diff {worst:.2e}; all finite')

CAT = [(p, k) for p in (0.5, 1.0, 1.5) for k in (0.2, 0.3, 0.45)]; NULL = [i for i, (p, k) in enumerate(CAT) if p <= 1]
N, K, D, AL, BLO, BHI = 504, 252, 1 / 252, 0.1, -0.10, 0.20
RECTS = [(0.25, 0.35), (0.28, 0.32)]
def scores(S):
    full = np.c_[np.ones(len(S)), S]; M = len(S)
    tr = np.array([logK(p, k, D, full[:, :K], full[:, 1:K + 1]).sum(1) for p, k in CAT]); sel = np.argmax(tr, axis=0)
    ev = np.array([logK(p, k, D, full[:, K:-1], full[:, K + 1:]).sum(1) for p, k in CAT]); lG = ev[sel, np.arange(M)]
    lG0 = ev[NULL].max(axis=0); pos = (full[:, K:] > 0).all(axis=1); Dt = np.full(N - K, D)
    def g(f):
        out = np.full(M, -np.inf); out[pos] = f(full[pos, K], full[pos, K + 1:]); return out
    lU = g(lambda y0, Y: logDGB(y0, Y, Dt, 0, 0, unconstrained=True)); lB = g(lambda y0, Y: logDGB(y0, Y, Dt, BLO, BHI))
    lR = [g(lambda y0, Y, r=r: logDGBC(y0, Y, Dt, BLO, BHI, *r)) for r in RECTS]
    sc = lambda lden: np.where(np.isfinite(lG) & np.isfinite(lden), np.exp(np.minimum(lG - lden, 700)), 0.0)
    return [sc(lG0), sc(np.maximum(lG0, lU)), sc(np.maximum(lG0, lB))] + [sc(np.maximum(lG0, l)) for l in lR]
def gbm(b, s, M): return np.exp(np.cumsum((b - s * s / 2) * D + s * math.sqrt(D) * rng.standard_normal((M, N)), axis=1))
def cev15(k, M):
    c = k * 0.5; B = np.zeros((M, 4)); B[:, 0] = 1 / c; out = np.empty((M, N))
    for j in range(N): B += math.sqrt(D) * rng.standard_normal((M, 4)); out[:, j] = (c * np.linalg.norm(B, axis=1)) ** -2
    return out
print(f'(b) B=[{BLO},{BHI}]; mean / P(>1/alpha) for E(054) | E^drift(055) | E^B(056) | E^(B,C) C=[.25,.35] | C=[.28,.32]')
M = 10000
for label, S in [('GBM b=0.05 s=0.33 (in both rects)', gbm(.05, .33, M)), ('GBM b=0.05 s=0.30 (in both; on grid)', gbm(.05, .30, M)),
                 ('GBM b=0.05 s=0.40 (outside both rects)', gbm(.05, .40, M)), ('GBM b=0.05 s=0.25 (edge of wide; outside narrow)', gbm(.05, .25, M)),
                 ('CEV p=1.5 k=0.3 (alternative)', cev15(.3, M)), ('CEV p=1.5 k=0.45 (alternative)', cev15(.45, M))]:
    Es = scores(S); ok = all(bool(np.all(Es[j] <= Es[j + 1] * (1 + 1e-12) + 1e-300)) for j in (1,)) and bool(np.all(Es[2] <= Es[3] * (1 + 1e-12) + 1e-300)) and bool(np.all(Es[3] <= Es[4] * (1 + 1e-12) + 1e-300)) and bool(np.all(Es[4] <= Es[0] * (1 + 1e-12) + 1e-300))
    f = lambda x: f'{x.mean():.3g}/{np.mean(x > 1 / AL):.4f}'
    print(f'   {label:46s} ' + ' | '.join(f(e) for e in Es) + f'   ordering ok: {ok}', flush=True)
