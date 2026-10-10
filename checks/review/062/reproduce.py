"""Reviewer's independent check of claim 062 (written before reading checks/062/*). At most 2 workers (CPU budget).
(a) Profile (2) vs direct multivariate-normal log density at (a_hat, S_pool) and at random perturbations (never higher);
    identity (4): log D_pool - sum_i log D_G,i = -(n/2) log det C_pool; rank barrier m >= n gives singular S_pool.
(b) Monte Carlo: m = 5 names, daily, train one year, evaluate one year (n = 252). Forecast catalogue: shared power
    p in {1.25, 1.5, 2}, per-name scale in {0.2, 0.3, 0.45} (claim 054 kernels), training-only first maximizer.
    Global test E_pool >= 1/alpha (alpha = 0.1) vs a per-name comparator: any_i q_i/D_G,i > m/alpha (Bonferroni,
    valid under Gaussian nulls). Truths: independent GBM (sigma 0.3); one-factor GBM (pairwise rho 0.5);
    independent CEV p = 1.5, kappa = 0.45; one-factor CEV p = 1.5 (driving 4-d BMs correlated rho 0.5).
    Reports the median correlation penalty K = -(n/2) log det C_pool.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/062/reproduce.py
Seed:   numpy default_rng(62) for (a); SeedSequence(6262) per truth for (b). About 5 minutes on 2 workers. Not a CI check."""
import numpy as np, math
from scipy.special import ive, gammaincc
def logf(p, D, x, y, k):
    if p == 1:
        v = k * k * D; return -(np.log(y / x) + v / 2) ** 2 / (2 * v) - np.log(y * np.sqrt(2 * np.pi * v))
    h = abs(p - 1); nu = 1 / (2 * h); v = k * k * h * h * D
    A, B = x ** (2 - 2 * p), y ** (2 - 2 * p); z = x ** (1 - p) * y ** (1 - p) / v
    with np.errstate(divide='ignore'):
        return 0.5 * np.log(x) + (0.5 - 2 * p) * np.log(y) - np.log(k * k * h * D) - (np.sqrt(A) - np.sqrt(B)) ** 2 / (2 * v) + np.log(ive(nu, z))
def logK(p, k, D, x, y):
    out = np.full(np.broadcast(x, y).shape, -np.inf); pos = (x > 0) & (y > 0); out[pos] = logf(p, D, x[pos], y[pos], k)
    if p < 1:
        a0 = (x > 0) & (y == 0); hh = 1 - p; v = k * k * hh * hh * D
        with np.errstate(divide='ignore'): out[a0] = np.log(gammaincc(1 / (2 * hh), x[a0] ** (2 - 2 * p) / (2 * v)))
    out[(x == 0) & (y == 0)] = 0.0
    return out

from multiprocessing import Pool
from scipy.stats import multivariate_normal
def pool_logD(R, d):
    n, m = R.shape; tau = d.sum(); ahat = R.sum(0) / tau; Z = (R - np.outer(d, ahat)) / np.sqrt(d)[:, None]; S = Z.T @ Z / n
    sign, ld = np.linalg.slogdet(S)
    if sign <= 0: return math.inf, S, ahat
    return -(n * m / 2) * math.log(2 * math.pi * math.e) - (n / 2) * ld - (m / 2) * np.log(d).sum(), S, ahat   # returns part (no Jacobian)
def scalar_logD(r, d):
    n = len(r); a = r.sum() / d.sum(); Q = ((r - a * d) ** 2 / d).sum(); return -(n / 2) * (math.log(2 * math.pi * Q / n) + 1) - 0.5 * np.log(d).sum()
def structural():
    rng = np.random.default_rng(62); worst = 0.0; above = 0; idw = 0.0
    for t in range(20):
        n, m = int(rng.integers(6, 15)), int(rng.integers(1, 5)); d = rng.uniform(0.002, 0.05, n)
        A = rng.normal(0, 0.3, (m, m)); Sig = A @ A.T + 0.01 * np.eye(m); R = np.array([rng.multivariate_normal(np.zeros(m), Sig * dj) for dj in d])
        lD, S, ah = pool_logD(R, d)
        direct = sum(multivariate_normal.logpdf(R[j], ah * d[j], S * d[j]) for j in range(n)); worst = max(worst, abs(direct - lD))
        for _ in range(30):
            a2 = ah + rng.normal(0, 0.5, m); B = rng.normal(0, 0.2, (m, m)); S2 = S + B @ B.T * rng.uniform(0, 1) - 0.5 * np.diag(np.diag(S)) * rng.uniform(0, 0.9)
            if np.all(np.linalg.eigvalsh(S2) > 0): above += sum(multivariate_normal.logpdf(R[j], a2 * d[j], S2 * d[j]) for j in range(n)) > lD + 1e-9
        C = S / np.sqrt(np.outer(np.diag(S), np.diag(S)))
        idw = max(idw, abs(lD - sum(scalar_logD(R[:, i], d) for i in range(m)) + (n / 2) * np.linalg.slogdet(C)[1]))
    Rs = rng.normal(0, 0.02, (4, 6)); sing = np.linalg.matrix_rank(pool_logD(Rs, np.full(4, 0.01))[1])
    print(f'(a) profile (2) vs direct MVN logpdf: max |diff| {worst:.1e}; perturbed (a, Sigma) above the profile: {above}/600; '
          f'identity (4) max |diff| {idw:.1e}; m=6, n=4 residual rank {sing} (<= n-1 = 3)')
N, K, D = 504, 252, 1 / 252
POW = (1.25, 1.5, 2.0); SC = (0.2, 0.3, 0.45); M_ = 5; ALPHA = 0.1
def work(args):
    truth, seed, B = args; rg = np.random.default_rng(seed); kind, rho = truth[0], truth[1]
    out = []
    for b in range(B):
        if kind == 'gbm':
            Z0 = rg.standard_normal(N); Zi = rg.standard_normal((M_, N)); Zc = math.sqrt(rho) * Z0[None, :] + math.sqrt(1 - rho) * Zi
            S = np.exp(np.cumsum((0.05 - 0.045) * D + 0.3 * math.sqrt(D) * Zc, axis=1))
        else:
            k = truth[2]; cc = k * 0.5; W0 = rg.standard_normal((N, 4)); Wi = rg.standard_normal((M_, N, 4))
            inc = (math.sqrt(rho) * W0[None] + math.sqrt(1 - rho) * Wi) * math.sqrt(D); Bm = np.cumsum(inc, axis=1); Bm[:, :, 0] += 1 / cc
            S = (cc * np.linalg.norm(Bm, axis=2)) ** -2
        full = np.c_[np.ones(M_), S]
        tr = {(p, k): logK(p, k, D, full[:, :K], full[:, 1:K + 1]).sum(1) for p in POW for k in SC}   # per name
        ev = {(p, k): logK(p, k, D, full[:, K:-1], full[:, K + 1:]).sum(1) for p in POW for k in SC}
        best_p, best_val, best_idx = None, -math.inf, None
        for p in POW:
            mat = np.array([tr[(p, k)] for k in SC]); idx = np.argmax(mat, axis=0); val = mat[idx, np.arange(M_)].sum()
            if val > best_val: best_p, best_val, best_idx = p, val, idx
        lq = np.array([ev[(best_p, SC[best_idx[i]])][i] for i in range(M_)])
        R = np.log(full[:, K + 1:] / full[:, K:-1]).T; dvec = np.full(N - K, D); lJ = -np.log(full[:, K + 1:]).sum()
        lDp, Sp, _ = pool_logD(R, dvec)
        lEpool = lq.sum() - (lDp + lJ) if np.isfinite(lDp) else -math.inf
        lDG = np.array([scalar_logD(R[:, i], dvec) - np.log(full[i, K + 1:]).sum() for i in range(M_)])
        C = Sp / np.sqrt(np.outer(np.diag(Sp), np.diag(Sp))); Kp = -(N - K) / 2 * np.linalg.slogdet(C)[1]
        out.append((lEpool, np.max(lq - lDG), Kp))
    return out
if __name__ == '__main__':
    structural()
    ss = np.random.SeedSequence(6262); Mtot = 1000
    print(f'(b) m={M_}, n={N - K}, alpha={ALPHA}: P(global E_pool >= 1/alpha) | P(per-name Bonferroni any q_i/D_G,i > m/alpha) | mean E_pool | median K')
    with Pool(2) as pool:
        for truth in [('gbm', 0.0), ('gbm', 0.5), ('cev', 0.0, 0.45), ('cev', 0.5, 0.45)]:
            res = [r for chunk in pool.map(work, [(truth, s, 25) for s in ss.spawn(Mtot // 25)]) for r in chunk]
            lE = np.array([r[0] for r in res]); lB = np.array([r[1] for r in res]); Kp = np.array([r[2] for r in res])
            print(f'   {str(truth):18s} global {np.mean(lE >= math.log(1 / ALPHA)):.4f} | per-name {np.mean(lB > math.log(M_ / ALPHA)):.4f} | '
                  f'mean E {np.exp(np.minimum(lE, 700)).mean():.3g} | median K {np.median(Kp):.1f}', flush=True)
