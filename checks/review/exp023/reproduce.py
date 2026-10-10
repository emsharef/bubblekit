"""Reviewer's independent reproduction of experiment 023's daily headline cells (written without reading
experiments/023/*.py). 18-candidate absorbed-CEV catalogue (p in {0.5,0.75,1,1.25,1.5,2} x kappa in {0.2,0.3,0.45},
null p <= 1), split floor(N/2), daily grid (252/yr), reject at log E > log 20. Scores on identical paths: claim 054 raw;
claim 056 bounded-drift scores for B = [-h, h], h in {0, 0.05, 0.2}, by the exact candidate formula (endpoints with
w_c = 2A/(n + sqrt(n^2 + tau A)), interior (a + Q/(2n), Q/n) if feasible, +inf iff Q = 0 and a in B); claim 055.
Own exact paths: GBM; CEV p in {1.25, 1.5, 2} as Bessel transforms of integer dimension 6, 4, 3.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp023/reproduce.py
Seed:   SeedSequence(2323), spawned per (truth, T) in loop order (main table, 1,000 paths per cell).
        With argument `big`: SeedSequence(232300), 5,000 paths for the two T = 2 cells CEV (1.5, 0.30) and (1.25, 0.45).
        Runtime a few minutes each on 2 workers (lab CPU budget). Not a CI check (not check.py)."""
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

from multiprocessing import Pool
DD = 1 / 252; HS = (0.0, 0.05, 0.2)
def simd(truth, T, M, rng):
    n = 252 * T
    if truth[0] == 'gauss':
        b, k = truth[1], truth[2]; return np.exp(np.cumsum((b - k * k / 2) * DD + k * math.sqrt(DD) * rng.standard_normal((M, n)), axis=1))
    p, k = truth[1], truth[2]; d = round((2 * p - 1) / (p - 1)); c = k * (p - 1)
    B = np.cumsum(math.sqrt(DD) * rng.standard_normal((M, n, d)), axis=1); B[:, :, 0] += 1 / c
    return (c * np.linalg.norm(B, axis=2)) ** (-1 / (p - 1))
def ell(b, w, R, Y): return np.sum(-(R - (b - w / 2) * DD) ** 2 / (2 * w * DD) - 0.5 * np.log(2 * np.pi * w * DD) - np.log(Y))
def logDG_B(y0, Y, h):
    P = np.r_[y0, Y]; R = np.log(P[1:] / P[:-1]); n = len(Y); tau = n * DD; a = R.sum() / tau; Q = ((R - a * DD) ** 2).sum() / DD
    if h is None: return -(n / 2) * (math.log(2 * math.pi * Q / n) + 1) - 0.5 * n * math.log(DD) - np.log(Y).sum() if Q > 0 else math.inf
    if Q == 0 and -h <= a <= h: return math.inf
    best = -math.inf
    for c in (-h, h):
        A = Q + tau * (a - c) ** 2; w = 2 * A / (n + math.sqrt(n * n + tau * A)); best = max(best, ell(c, w, R, Y))
    bi = a + Q / (2 * n)
    if Q > 0 and -h <= bi <= h: best = max(best, ell(bi, Q / n, R, Y))
    return best
def work(args):
    truth, T, seed, M = args; rng = np.random.default_rng(seed); S = np.c_[np.ones(M), simd(truth, T, M, rng)]
    N = S.shape[1] - 1; K = N // 2; Dt = np.full(N, DD)
    L = np.array([logK(p, k, Dt[None, :], S[:, :-1], S[:, 1:]) for p, k in CAT])
    tr = L[:, :, :K].sum(2); ev = L[:, :, K:].sum(2); sel = np.argmax(tr, axis=0); lG = ev[sel, np.arange(M)]; lG0 = ev[NULL].max(0)
    out = {'raw': (lG - lG0 > math.log(20)).sum()}; ordok = True
    cols = {}
    for h in HS + (None,):
        lD = np.array([max(lG0[i], logDG_B(S[i, K], S[i, K + 1:], h)) if (S[i, K:] > 0).all() else lG0[i] for i in range(M)])
        lE = np.where(np.isfinite(lD), lG - lD, -np.inf); cols[h] = lE; out[h] = (lE > math.log(20)).sum()
    seq = [lG - lG0] + [cols[h] for h in HS] + [cols[None]]
    out['order'] = all(np.all(seq[j] >= seq[j + 1] - 1e-9) for j in range(len(seq) - 1))
    return out
TRUTHS = [('gauss', 0.0, 0.35), ('gauss', 0.2, 0.35), ('gauss', 0.4, 0.35), ('gauss', 0.0, 0.60), ('gauss', 0.4, 0.60),
          ('cev', 1.25, 0.45), ('cev', 1.5, 0.30), ('cev', 1.5, 0.45), ('cev', 2.0, 0.20), ('cev', 2.0, 0.30)]
if __name__ == '__main__' and 'big' in __import__('sys').argv[1:]:
    ss = np.random.SeedSequence(232300); M = 5000
    with Pool(2) as pool:
        for truth in [('cev', 1.5, 0.30), ('cev', 1.25, 0.45)]:
            res = pool.map(work, [(truth, 2, s, 50) for s in ss.spawn(M // 50)])
            f = lambda k: sum(r[k] for r in res) / M
            print(f'{truth} T=2 n={M}: raw {f("raw"):.4f} | h0 {f(0.0):.4f} | h.05 {f(0.05):.4f} | h.2 {f(0.2):.4f} | 055 {f(None):.4f}', flush=True)
elif __name__ == '__main__':
    ss = np.random.SeedSequence(2323); M = 1000
    print('daily, alpha = 0.05: rejection rate for 054 raw | h=0 | h=0.05 | h=0.2 | 055 ; pointwise ordering raw >= h0 >= h.05 >= h.2 >= 055')
    with Pool(2) as pool:
        for truth in TRUTHS:
            for T in (2, 5):
                res = pool.map(work, [(truth, T, s, 50) for s in ss.spawn(M // 50)])
                f = lambda k: sum(r[k] for r in res) / M
                print(f'   {str(truth):24s} T={T}: {f("raw"):.3f} | {f(0.0):.3f} | {f(0.05):.3f} | {f(0.2):.3f} | {f(None):.3f}   order ok {all(r["order"] for r in res)}', flush=True)
