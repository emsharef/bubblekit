"""Reviewer's independent check of claim 063 (written before reading checks/063/*). At most 2 workers (CPU budget).
Builds on the reviewer's claim-062 script (inlined). CEV CDF for p > 1 from the Bessel transform:
Y = S^(1-p)/(kappa(p-1)) is BES(delta), delta = (2p-1)/(p-1), so F(y | x) = P(Y_D^2/D >= y_b^2/D) with
Y_D^2/D ~ noncentral chi-square(delta, Y_0^2/D).
(a) The CDF agrees with numerical integration of the claim-054 CEV density; a bivariate Gaussian-copula CEV
    transition integrates to one with CEV marginals (2-d quadrature); gain identity (5) holds exactly.
(b) Monte Carlo (m = 5, daily, train one year, evaluate one year, alpha = 0.1, gamma_cop = 0.1, w0 = 1/2):
    rejection rates of E_pool (claim 062), E_cop and E_mix under independent / one-factor (rho 0.5) GBM nulls and
    independent / one-factor CEV p = 3/2 alternatives, with the per-name Bonferroni comparator.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/063/reproduce.py
Seed:   SeedSequence(6363) per truth for (b). About 5 minutes on 2 workers. Not a CI check (not check.py)."""

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
        out.append((lEpool, np.max(lq - lDG), Kp, extra(full, best_p, best_idx, lq, lDp + lJ)))
    return out

from scipy.stats import ncx2, norm as _norm
from scipy.integrate import quad, dblquad
GAMMA, W0 = 0.1, 0.5
def zscore(p, k, Dt, x, y):
    delta = (2 * p - 1) / (p - 1); c = k * (p - 1)
    y0 = x ** (1 - p) / c; yb = y ** (1 - p) / c; nc = y0 ** 2 / Dt; t = yb ** 2 / Dt
    cdf = ncx2.sf(t, delta, nc); sf = ncx2.cdf(t, delta, nc)            # F(y) = P(Y^2 >= yb^2) since S decreasing in Y
    return np.where(cdf < 0.5, _norm.ppf(cdf), _norm.isf(sf))
def extra(full, p, idx, lq, lDtot):
    ks = [SC[idx[i]] for i in range(M_)]
    Ztr = np.array([zscore(p, ks[i], D, full[i, :K], full[i, 1:K + 1]) for i in range(M_)]).T
    Zev = np.array([zscore(p, ks[i], D, full[i, K:-1], full[i, K + 1:]) for i in range(M_)]).T
    if not (np.all(np.isfinite(Ztr)) and np.all(np.isfinite(Zev))): return (-math.inf, -math.inf)
    A = np.cov(Ztr.T, bias=True); dg = np.diag(A)
    R = np.eye(M_) if np.any(dg <= 0) else (1 - GAMMA) * A / np.sqrt(np.outer(dg, dg)) + GAMMA * np.eye(M_)
    Ri = np.linalg.inv(R); G = -(Zev.shape[0] / 2) * np.linalg.slogdet(R)[1] - 0.5 * np.trace((Ri - np.eye(M_)) @ (Zev.T @ Zev))
    lEpool = lq.sum() - lDtot if np.isfinite(lDtot) else -math.inf
    lEcop = lEpool + G; lEmix = lEpool + np.logaddexp(math.log(W0), math.log(1 - W0) + G)
    return (lEcop, lEmix)
def structural():
    p, k, Dt, x = 1.5, 0.3, 1 / 52, 1.0
    dens = lambda y: math.exp(logK(p, k, Dt, np.array([x]), np.array([y]))[0])
    worst = 0.0
    for y in (0.7, 0.95, 1.0, 1.08, 1.5):
        num = quad(dens, 1e-8, y, limit=400)[0]; z = float(zscore(p, k, Dt, np.array([x]), np.array([y]))[0])
        worst = max(worst, abs(num - _norm.cdf(z)))
    R2 = np.array([[1, 0.6], [0.6, 1]]); Ri = np.linalg.inv(R2)
    def joint(y1, y2):
        z = np.array([float(zscore(p, k, Dt, np.array([x]), np.array([y1]))[0]), float(zscore(p, 0.45, Dt, np.array([x]), np.array([y2]))[0])])
        return np.linalg.det(R2) ** -0.5 * math.exp(-0.5 * z @ (Ri - np.eye(2)) @ z) * dens(y1) * math.exp(logK(p, 0.45, Dt, np.array([x]), np.array([y2]))[0])
    tot = dblquad(lambda y2, y1: joint(y1, y2), 0.5, 2.0, 0.4, 2.5, epsabs=1e-6)[0]
    marg = quad(lambda y2: joint(1.02, y2), 0.4, 2.5, limit=200)[0] / dens(1.02)
    print(f'(a) CEV CDF vs density integral: max |diff| {worst:.1e}; copula transition mass over [0.5,2]x[0.4,2.5] {tot:.5f} (~1); '
          f'conditional marginal at y1=1.02 integrates to {marg:.5f} (~1)')
if __name__ == '__main__':
    structural()
    ss = np.random.SeedSequence(6363); Mtot = 1000
    print(f'(b) m={M_}, n={N - K}, alpha={ALPHA}, gamma_cop={GAMMA}, w0={W0}: P(reject) for E_pool | E_cop | E_mix | per-name Bonferroni')
    with Pool(2) as pool:
        for truth in [('gbm', 0.0), ('gbm', 0.5), ('cev', 0.0, 0.45), ('cev', 0.5, 0.45)]:
            res = [r for chunk in pool.map(work, [(truth, s, 25) for s in ss.spawn(Mtot // 25)]) for r in chunk]
            th = math.log(1 / ALPHA); f = lambda a: np.mean(np.array(a) >= th)
            print(f'   {str(truth):18s} {f([r[0] for r in res]):.4f} | {f([r[3][0] for r in res]):.4f} | {f([r[3][1] for r in res]):.4f} | '
                  f'{np.mean(np.array([r[1] for r in res]) > math.log(M_ / ALPHA)):.4f}', flush=True)
