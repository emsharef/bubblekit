"""Reviewer's independent check of claim 039 (written before reading checks/039/*). At most 2 workers (CPU budget).
Monte Carlo of the actual rounded Gaussian model: start s = 1, tick 0.05, weekly steps (Delta = 1/52), calendar clock,
k = 10 training and n = 10 scored labels; null = uniform mixture over the box b in [-.2, .2] x w in [.04, .36]
(drawn once per record, so the suffix law given U is a mixture of component conditionals). Filtered prefix masses
L_(theta, j) by the reviewer's claim-036 midpoint recursion (M = 64), on a 15 x 15 grid of theta (the grid maximum is
<= the true maximum, so computed scores are if anything too large: the conservative direction for this check).
Predictable forecast: the cell probabilities of a lognormal step from the last label's representative with zero drift
and variance w_hat * Delta, w_hat = mean squared log label return on the history (floor 1e-4); normalized over all
labels including the zero cell. Processes: E_seq (1), E_step (3), and the warned-against E_sep = Q / (max L_(k+t) /
max L_k). Reported: P(sup_t E >= 2, 5, 20), E[E_tau] for tau = first t with E >= 4 (else n), and the pointwise
ordering E_step <= E_seq. 4,000 records.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/039/reproduce.py
Seed:   SeedSequence(3939). 2 workers. Not a CI check (not check.py)."""
import numpy as np, math
from multiprocessing import Pool
from scipy.stats import norm
from scipy.special import logsumexp
DEL = 0.05
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

K_, N_ = 10, 10; DT = 1 / 52; Dl = np.full(K_ + N_, DT)
BG, WG = [g.ravel() for g in np.meshgrid(np.linspace(-0.2, 0.2, 15), np.linspace(0.04, 0.36, 15))]
def forecast_logp(hist, z):
    R = np.diff(np.log(DEL * np.maximum(np.array(hist, float), 0.25))); w = max(np.mean(R ** 2) / DT, 1e-4); sd = math.sqrt(w * DT)
    x = DEL * hist[-1] if hist[-1] >= 1 else DEL / 4; lo = 0.0 if z == 0 else DEL * (z - 0.5); hi = DEL * (z + 0.5)
    f = lambda y: norm.cdf((math.log(y) - math.log(x) + w * DT / 2) / sd) if y > 0 else 0.0
    return math.log(max(f(hi) - f(lo), 1e-300))
def logQz(z):
    """logQ supporting zero labels: cell [0, DEL/2) handled by a tiny positive lower edge in log space."""
    return logQ(1.0, z, Dl, Dl, BG, WG, 64)
def work(args):
    seed, B = args; rng = np.random.default_rng(seed); out = []
    for _ in range(B):
        b = rng.uniform(-0.2, 0.2); w = rng.uniform(0.04, 0.36)
        X = np.exp(np.cumsum((b - w / 2) * DT + math.sqrt(w * DT) * rng.standard_normal(K_ + N_))); z = [int(math.floor(x / DEL + 0.5)) for x in X]
        if min(z) < 1: out.append(None); continue
        L = logQz(z)                                     # (J, G): L[j-1] = log L_(theta, j)
        lQ = np.cumsum([forecast_logp(z[:K_ + t - 1] if K_ + t - 1 > 0 else [20], z[K_ + t - 1]) for t in range(1, N_ + 1)])
        G = L[K_:] - L[K_ - 1][None, :]                  # log G_(theta, t), t = 1..n
        Eseq = lQ - G.max(1)
        p = L[K_:] - np.vstack([L[K_ - 1][None, :], L[K_:-1]]); Estep = lQ - np.cumsum(p.max(1))
        Esep = lQ - (L[K_:].max(1) - L[K_ - 1].max())
        out.append((Eseq, Estep, Esep))
    return out
def summarize(name, E):
    sup = E.max(1); tau = np.array([next((t for t in range(N_) if e[t] >= math.log(4)), N_ - 1) for e in E]); Et = np.exp(E[np.arange(len(E)), tau])
    return f'{name}: P(sup >= 2, 5, 20) = {np.mean(sup >= math.log(2)):.4f}, {np.mean(sup >= math.log(5)):.4f}, {np.mean(sup >= math.log(20)):.4f}; E[E_tau] = {Et.mean():.3f}; E[E_n] = {np.exp(E[:, -1]).mean():.3f}'
if __name__ == '__main__':
    with Pool(2) as pool: R = [r for ch in pool.map(work, [(s, 50) for s in np.random.SeedSequence(3939).spawn(80)]) for r in ch]
    kept = [r for r in R if r is not None]; print(f'{len(kept)} of {len(R)} records with all labels >= 1 (zero-label records skipped: this recursion handles positive cells only)')
    Eseq, Estep, Esep = [np.array([r[i] for r in kept]) for i in range(3)]
    print(f'pointwise E_step <= E_seq on every prefix: {bool(np.all(Estep <= Eseq + 1e-9))}')
    for nm, E in (('E_seq (claim 039)', Eseq), ('E_step (comparator)', Estep), ('E_sep (ratio of separate maxima, not licensed)', Esep)): print('   ' + summarize(nm, E))
