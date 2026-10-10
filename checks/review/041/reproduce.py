"""Reviewer's independent check of claim 041 (written before reading checks/041/*). At most 2 workers (CPU budget).
Reuses the reviewer's claim-039/040 review code (inlined): rounded Gaussian model, start 1, tick 0.05, weekly steps, 24
labels, whole-record null = uniform mixture over b in [-.2, .2] x w in [.04, .36]; filtered prefix masses by the
claim-036 recursion (M = 64) on a 15 x 15 grid (grid maximum <= true maximum: scores too large, the conservative
direction); predictable plug-in forecast on all earlier labels. k_0 = 10.
Funded policy (claim 041): slot 1 launched at t = 10 with lambda = 1/2; slot 2 launched at the first t >= 12 at which
slot 1's score is below 1/2, with lambda = 1/2 if the triggering label moved and 1/4 otherwise (a trigger-dependent
allocation); unused capital kept. Free-refill policy (not licensed): an attempt with unit capital, restarted with
fresh unit capital whenever its score falls below 1/2, scoring only the current attempt. Reported over 4,000 records:
P(sup >= 2, 5, 20), E[C_tau] for tau = first t with C >= 4 (else 24), C_10 = 1, and the slot-domination check.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/041/reproduce.py
Seed:   SeedSequence(4141). 2 workers. Not a CI check (not check.py)."""
import numpy as np, math
from multiprocessing import Pool
from scipy.stats import norm
from scipy.special import logsumexp
DEL = 0.05

import numpy as np, math
from multiprocessing import Pool
from scipy.stats import norm
from scipy.special import logsumexp
DEL = 0.05

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

K0, NTOT = 10, 24; DT = 1 / 52; Dl = np.full(NTOT, DT); ANCH = (10, 16); LAM = (0.5, 0.5)
BG, WG = [g.ravel() for g in np.meshgrid(np.linspace(-0.2, 0.2, 15), np.linspace(0.04, 0.36, 15))]
def forecast_logp(hist, z):
    R = np.diff(np.log(DEL * np.maximum(np.array(hist, float), 0.25))); w = max(np.mean(R ** 2) / DT, 1e-4); sd = math.sqrt(w * DT)
    x = DEL * hist[-1] if hist[-1] >= 1 else DEL / 4; lo = 0.0 if z == 0 else DEL * (z - 0.5); hi = DEL * (z + 0.5)
    f = lambda y: norm.cdf((math.log(y) - math.log(x) + w * DT / 2) / sd) if y > 0 else 0.0
    return math.log(max(f(hi) - f(lo), 1e-300))
def logQz(z):
    """logQ supporting zero labels: cell [0, DEL/2) handled by a tiny positive lower edge in log space."""
    return logQ(1.0, z, Dl[:len(z)], Dl[:len(z)], BG, WG, 64)


def work(args):
    seed, B = args; rng = np.random.default_rng(seed); out = []
    for _ in range(B):
        b = rng.uniform(-0.2, 0.2); w = rng.uniform(0.04, 0.36)
        X = np.exp(np.cumsum((b - w / 2) * DT + math.sqrt(w * DT) * rng.standard_normal(NTOT))); z = [int(math.floor(x / DEL + 0.5)) for x in X]
        if min(z) < 1: out.append(None); continue
        L = logQz(z); lq = np.array([forecast_logp(z[:i - 1] if i > 1 else [20], z[i - 1]) for i in range(1, NTOT + 1)])
        def score(sig, t): return 0.0 if t <= sig else lq[sig:t].sum() - (L[t - 1] - L[sig - 1]).max()      # log E at t of a slot launched at sig
        ts = range(K0, NTOT + 1); C = []; dom = True; s2 = None; lam2 = 0.0
        for t in ts:
            e1 = score(K0, t)
            if s2 is None and t >= 12 and e1 < math.log(0.5): s2 = t; lam2 = 0.5 if z[t - 1] != z[t - 2] else 0.25
            c = (1 - 0.5 - (lam2 if s2 is not None else 0.0)) + 0.5 * math.exp(e1) + (lam2 * math.exp(score(s2, t)) if s2 is not None else 0.0)
            dom &= c >= 0.5 * math.exp(e1) - 1e-12 and (s2 is None or c >= lam2 * math.exp(score(s2, t)) - 1e-12); C.append(c)
        R = []; start = K0
        for t in ts:
            e = score(start, t); R.append(math.exp(e))
            if e < math.log(0.5): start = t                                       # discard the failed attempt, refill with fresh unit capital
        out.append((np.log(C), np.log(R), dom, C[0]))
    return out
def summ(name, E):
    sup = E.max(1); tau = np.array([next((t for t in range(E.shape[1]) if e[t] >= math.log(4)), E.shape[1] - 1) for e in E])
    return f'{name}: P(sup >= 2, 5, 20) = {np.mean(sup >= math.log(2)):.4f}, {np.mean(sup >= math.log(5)):.4f}, {np.mean(sup >= math.log(20)):.4f}; E[C_tau] = {np.exp(E[np.arange(len(E)), tau]).mean():.3f}'
if __name__ == '__main__':
    with Pool(2) as pool: R = [r for ch in pool.map(work, [(s, 50) for s in np.random.SeedSequence(4141).spawn(80)]) for r in ch]
    kept = [r for r in R if r is not None]; print(f'{len(kept)} of {len(R)} records with all labels >= 1')
    C, F = np.array([r[0] for r in kept]), np.array([r[1] for r in kept])
    print(f'C_10 = 1 on every record: {all(abs(r[3] - 1) < 1e-12 for r in kept)}; slot domination C_t >= lambda_r E_r on every record and time: {all(r[2] for r in kept)}')
    print('   ' + summ('funded adaptive restarts (claim 041)', C)); print('   ' + summ('free refills with fresh unit capital (not licensed)', F))
