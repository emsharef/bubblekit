"""Reviewer's independent reproduction of experiment 026's headline cells (written without reading experiments/026/*.py).
18-candidate absorbed-CEV catalogue (p in {0.5,...,2} x kappa in {0.2,0.3,0.45}, null p <= 1), first-maximizer training
numerator on the first floor(N/2) increments, reject at log E > log 20 (alpha = 0.05). Scores on identical paths:
claim 054 raw; claim 055 E^drift; claim 059 E^sw = G / max(G0, max_c D_L * D_R) with segment Gaussian profiles (4)
by prefix sums, for nested cut sets K1 = {floor(n_e/2)}, Kx = [ceil(x n_e), n_e - ceil(x n_e)], x = .40, .25, .10.
Daily 252/yr; monthly = every 21st daily price. Own exact paths: Gaussian (constant or one switch from kappa_L to
kappa_R at evaluation month c_m = round(s * 6T), i.e. daily increment K + 21 c_m), CEV as Bessel transforms (dims 6,4,3).

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp026/reproduce.py
Seed:   SeedSequence(2626), spawned per truth in list order; replicate SeedSequence(2627) with 4,000 paths for the kappa = 0.45 cells. 2 workers (CPU budget); about 10 minutes. Not a CI check."""
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
DD = 1 / 252; LT = math.log(20); COLS = ('raw', '055', 'K1', 'K40', 'K25', 'K10')
def sim(truth, T, M, rng):
    n = 252 * T; kind = truth[0]
    if kind == 'const':
        b, k = truth[1], truth[2]; return np.exp(np.cumsum((b - k * k / 2) * DD + k * math.sqrt(DD) * rng.standard_normal((M, n)), axis=1))
    if kind == 'switch':
        kL, kR, s = truth[1:]; cm = round(s * 6 * T); sw = 126 * T + 21 * cm; k = np.where(np.arange(n) < sw, kL, kR)
        return np.exp(np.cumsum(-k * k / 2 * DD + k * math.sqrt(DD) * rng.standard_normal((M, n)), axis=1))
    p, k = truth[1], truth[2]; d = round((2 * p - 1) / (p - 1)); c = k * (p - 1)
    B = np.cumsum(math.sqrt(DD) * rng.standard_normal((M, n, d)), axis=1); B[:, :, 0] += 1 / c
    return (c * np.linalg.norm(B, axis=2)) ** (-1 / (p - 1))
def cutsets(ne):
    out = {'K1': [ne // 2]}
    for nm, x in (('K40', .40), ('K25', .25), ('K10', .10)):
        lo = math.ceil(x * ne); out[nm] = list(range(max(lo, 2), min(ne - lo, ne - 2) + 1))
    return out
def seglog(n, tau, Q, D):   # (4) without the -sum log y and with -(n/2) log D per segment (constant D)
    with np.errstate(divide='ignore', invalid='ignore'):
        return np.where(Q > 0, -n / 2 * (np.log(2 * math.pi * Q / n) + 1) - 0.5 * n * math.log(D), np.inf)
def scores(S, D):
    M, N1 = S.shape; N = N1 - 1; K = N // 2; Dt = np.full(N, D)
    L = np.array([logK(p, k, Dt[None, :], S[:, :-1], S[:, 1:]) for p, k in CAT])
    tr = L[:, :, :K].sum(2); ev = L[:, :, K:].sum(2); sel = np.argmax(tr, axis=0); lG = ev[sel, np.arange(M)]; lG0 = ev[NULL].max(0)
    Pe = S[:, K:]; pos = (Pe > 0).all(1); Pe = np.where(pos[:, None], Pe, 1.0)
    R = np.log(Pe[:, 1:] / Pe[:, :-1]); ne = R.shape[1]; sly = np.log(Pe[:, 1:]).sum(1)
    c1 = np.cumsum(R, 1); c2 = np.cumsum(R * R, 1); tot1, tot2 = c1[:, -1], c2[:, -1]
    Qall = tot2 / D - tot1 ** 2 / (ne * D); lDdrift = seglog(ne, ne * D, Qall, D) - sly
    cs = np.arange(1, ne); SL1, SL2 = c1[:, :-1], c2[:, :-1]
    QL = SL2 / D - SL1 ** 2 / (cs * D); QR = (tot2[:, None] - SL2) / D - (tot1[:, None] - SL1) ** 2 / ((ne - cs) * D)
    lprod = seglog(cs, cs * D, QL, D) + seglog(ne - cs, (ne - cs) * D, QR, D) - sly[:, None]      # index c-1
    E = {'raw': lG - lG0}
    def fin(lD):
        lD = np.where(pos, np.maximum(lG0, lD), lG0); return np.where(np.isfinite(lD) & np.isfinite(lG), lG - lD, -np.inf)
    E['055'] = fin(lDdrift)
    for nm, cset in cutsets(ne).items(): E[nm] = fin(lprod[:, np.array(cset) - 1].max(1))
    order = all(np.all(E[COLS[j]] >= E[COLS[j + 1]] - 1e-9) for j in range(len(COLS) - 1))
    return E, order
def work(args):
    truth, T, seed, M = args; rng = np.random.default_rng(seed); S = np.c_[np.ones(M), sim(truth, T, M, rng)]
    out = {}
    for fr, Sx, D in (('m', S[:, ::21], 1 / 12), ('d', S, DD)):
        E, order = scores(Sx, D); out[fr] = {c: int((E[c] > LT).sum()) for c in COLS}; out[fr]['order'] = order
    return out
TRUTHS = [(('const', 0.10, 0.35), 5), (('switch', 0.45, 0.20, 0.50), 2), (('switch', 0.45, 0.20, 0.30), 5), (('switch', 0.20, 0.45, 0.15), 5),
          (('cev', 1.25, 0.45), 5), (('cev', 1.5, 0.30), 5), (('cev', 1.5, 0.45), 5), (('cev', 2.0, 0.20), 5), (('cev', 2.0, 0.45), 5), (('cev', 2.0, 0.30), 2)]
if __name__ == '__main__':
    ss = np.random.SeedSequence(2626); M = 1000
    ne = {T: (6 * T, 126 * T) for T in (2, 5)}
    for T in (2, 5): print(f'cut sets T={T}: ' + '; '.join(f'{fr} {nm} [{min(cs)},{max(cs)}]' for fr, n in zip('md', ne[T]) for nm, cs in cutsets(n).items()))
    print('alpha = 0.05 rejection rate, monthly / daily:  ' + ' | '.join(COLS))
    with Pool(2) as pool:
        for (truth, T), sd in zip(TRUTHS, ss.spawn(len(TRUTHS))):
            res = pool.map(work, [(truth, T, s, 50) for s in sd.spawn(M // 50)])
            f = lambda fr, c: sum(r[fr][c] for r in res) / M
            print(f'   {str(truth):28s} T={T}: ' + ' | '.join(f'{f("m", c):.3f}/{f("d", c):.3f}' for c in COLS)
                  + f'   order ok {all(r[fr]["order"] for r in res for fr in "md")}', flush=True)
    print('replicate, SeedSequence(2627), 4,000 paths:')
    with Pool(2) as pool:
        for (truth, T), sd in zip([(('cev', 1.25, 0.45), 5), (('cev', 1.5, 0.45), 5), (('cev', 2.0, 0.45), 5)], np.random.SeedSequence(2627).spawn(3)):
            res = pool.map(work, [(truth, T, s, 50) for s in sd.spawn(80)])
            f = lambda fr, c: sum(r[fr][c] for r in res) / 4000
            print(f'   {str(truth):28s} T={T}: ' + ' | '.join(f'{f("m", c):.3f}/{f("d", c):.3f}' for c in COLS), flush=True)
