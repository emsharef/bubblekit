"""Reviewer's independent reproduction of experiment 022's S1 (claim 054) and S3 (claim 055) rows
(written without reading experiments/022/*.py). Catalogue p in {0.5,0.75,1,1.25,1.5,2} x kappa in {0.2,0.3,0.45},
ordered p then kappa (tie order), null p <= 1; split k = floor(N/2); strides 78 (daily) and 1 (5-minute) on a
5-minute grid (78/day, 252 days/yr) keeping 0 and T; reject at log E > log 20. Kernels: AX-55 lognormal (p = 1),
AX-56 absorbed CEV (p != 1) with log ive; where scipy's ive is NaN/0 at huge argument, the large-z expansion
log ive ~ -0.5 log(2 pi z) + log(1 - (4nu^2-1)/(8z)) is used (reviewer's own handling). S3 adds claim 055's closed-form
Gaussian supremum. Own exact paths: GBM; CEV p in {1.25, 1.5, 2} as Bessel transforms of integer dimension 6, 4, 3;
CEV p = 1/2 by BESQ(0) Poisson-gamma steps (exact absorption).

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp022/reproduce.py
Seed:   SeedSequence(2222), spawned per (model, T, frequency-set) cell in loop order. Runtime about 30 minutes on 2 workers (lab CPU budget; results do not depend on the worker count).
Not a CI check (not check.py)."""
import numpy as np, math
from multiprocessing import Pool
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
def sim(model, T, M, rng):
    n = 252 * 78 * T; dt = BAR; kind, k = model[0], model[1]
    if kind == 'gbm':
        mu = model[2]; return np.exp(np.cumsum((mu - k * k / 2) * dt + k * math.sqrt(dt) * rng.standard_normal((M, n)), axis=1))
    p = model[2]
    if p == 0.5:
        Z = np.full(M, 4 / k ** 2); out = np.empty((M, n))
        for j in range(n):
            nn = rng.poisson(Z / (2 * dt)); Z = np.where(nn > 0, 2 * dt * rng.gamma(np.maximum(nn, 1)), 0.0); out[:, j] = k * k * Z / 4
        return out
    d = round((2 * p - 1) / (p - 1)); c = k * (p - 1); out = np.empty((M, n)); B = np.zeros((M, d)); B[:, 0] = 1 / c
    for j0 in range(0, n, 2000):
        j1 = min(n, j0 + 2000); inc = np.cumsum(math.sqrt(dt) * rng.standard_normal((M, j1 - j0, d)), axis=1) + B[:, None, :]
        out[:, j0:j1] = (c * np.linalg.norm(inc, axis=2)) ** (-1 / (p - 1)); B = inc[:, -1, :]
    return out
def scores(P, Dt):
    M, N1 = P.shape; N = N1 - 1; K = N // 2
    L = np.array([logK(p, k, Dt[None, :], P[:, :-1], P[:, 1:]) for p, k in CAT])
    tr = L[:, :, :K].sum(2); ev = L[:, :, K:].sum(2); sel = np.argmax(tr, axis=0); lG = ev[sel, np.arange(M)]; lG0 = ev[NULL].max(0)
    lE1 = np.where(np.isfinite(lG), lG - lG0, -np.inf)
    pos = (P[:, K:] > 0).all(1); lDG = np.full(M, -np.inf)
    if pos.any():
        Pe = P[pos, K:]; R = np.log(Pe[:, 1:] / Pe[:, :-1]); De = Dt[K:]; n_e = len(De); tau = De.sum()
        a = R.sum(1) / tau; Q = ((R - a[:, None] * De) ** 2 / De).sum(1)
        with np.errstate(divide='ignore'):
            lDG[pos] = np.where(Q > 0, -(n_e / 2) * (np.log(2 * np.pi * Q / n_e) + 1) - 0.5 * np.log(De).sum() - np.log(Pe[:, 1:]).sum(1), np.inf)
    lD = np.maximum(lG0, lDG); lE3 = np.where(np.isfinite(lG) & np.isfinite(lD), lG - lD, -np.inf)
    fail = ~np.isfinite(L[:, :, :]).any(axis=2).all(axis=0) if False else np.isnan(L).any(axis=(0, 2))
    return lE1, lE3, fail
def work(args):
    model, T, freqs, seed, M = args; rng = np.random.default_rng(seed); S = np.c_[np.ones(M), sim(model, T, M, rng)]
    n = S.shape[1] - 1; out = {}
    for f in freqs:
        st = {'daily': 78, '5min': 1}[f]; idx = np.arange(0, n + 1, st)
        if idx[-1] != n: idx = np.r_[idx, n]
        lE1, lE3, fail = scores(S[:, idx], np.diff(idx) * BAR)
        out[f] = ((lE1 > math.log(20)).sum(), (lE3 > math.log(20)).sum(), fail.sum(), (S[:, -1] == 0).sum())
    return out
MODELS = [('gbm', .30, 0.0), ('cev', .30, 0.5), ('cev', .30, 1.25), ('cev', .30, 1.5), ('cev', .30, 2.0), ('gbm', .35, 0.0), ('gbm', .30, 0.05)]
if __name__ == '__main__':
    ss = np.random.SeedSequence(2222)
    plan = [(1, ('daily', '5min'), 500), (5, ('daily',), 1000)]
    with Pool(2) as pool:
        for model in MODELS:
            for T, freqs, M in plan:
                B = 50 if '5min' in freqs else 100
                res = pool.map(work, [(model, T, freqs, s, B) for s in ss.spawn(M // B)])
                line = ' | '.join(f'{f}: S1 {sum(r[f][0] for r in res) / M:.3f} S3 {sum(r[f][1] for r in res) / M:.3f} (NaN-free {"yes" if sum(r[f][2] for r in res) == 0 else sum(r[f][2] for r in res)})' for f in freqs)
                print(f'{str(model):20s} T={T} n={M} absorbed {sum(r[freqs[0]][3] for r in res)}: {line}', flush=True)
