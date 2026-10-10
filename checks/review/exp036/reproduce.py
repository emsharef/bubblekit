"""Reviewer's independent reproduction of experiment 036 (written without reading experiments/036/*.py; the numerator follows the
definition in checks/d22-predictable-forecast/forecast.py, re-implemented in float with stable log-space normal
differences). Experiment-027 hourly design, 30 sessions (239 labels), $50 start, cent labels round(50 S / 0.01);
training 79 labels; checkpoints = each later session's last label (20).
Numerator: candidates p in {1, 1.5, 2} x kappa in {.1, .2, .3, .45, .7, 1, 1.5, 2, 3} x clocks {F, U}; row j = lognormal
cell probability from the previous label's representative (start for j = 0; tick * z, or tick / 4 at z = 0), variance
kappa^2 (source / start)^(2p - 2) * clock_j, log-mean -variance / 2; ranking by cumulative log row probabilities on
prior labels; expanding (refit before each scored label) or frozen (fit once at the training length).
Denominator (NOT the certified evaluator): the claim-036 conditional filtered likelihood max over the box
b in [-.5, .5] x w in [.01, .64] and full-record clocks {F, U}, approximated by its maximum over a 21 x 21 grid at M = 8
(a lower value for D, so these scores are upper values of the ideal and hence of the certified scores); the final
checkpoint is refined by Nelder-Mead for the reported median final score.
Truths: N-in GBM b = 0, kappa .3 on U; N-switch kappa in {.15, .45} switching with probability .1 per session at
session boundaries; L-15 / L-20: N-in until the first 5-minute bar of session 15 (0-based), then exact clock-time CEV
(p = 1.5 / 2, kappa .45) from the price reached. 100 paths per cell.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp036/reproduce.py
Seed:   SeedSequence(3636), one child per cell. 2 workers. Not a CI check (not check.py)."""

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

def logD(R, Dl, v, Y):
    A = np.sum(Dl ** 2 / v); B = np.sum(Dl * R / v); C = np.sum(R ** 2 / v); T = Dl.sum(); V = v.sum(); S = R.sum(); n = len(R)
    Q = C - B * B / A; K_ = S - B * T / A; H = V - T * T / A
    if Q <= 0: return math.inf
    w = 2 * Q / (n + math.sqrt(n * n + H * Q))
    return -(n / 2) * math.log(2 * math.pi * w) - 0.5 * np.log(v).sum() - np.log(Y).sum() - Q / (2 * w) - K_ / 2 - w * H / 8

from multiprocessing import Pool
YH = 24 * 252
def grids(S, s_hi, phi):
    """5-minute increments: (Delta, v_U for given shape, group id for hourly aggregation)."""
    k = np.arange(78); sp2 = np.where((k < 12) | (k >= 66), s_hi ** 2, 0.75 ** 2); vs = (1 - phi) / 252 * sp2 / sp2.sum()
    D, V, G = [], [], []; g = 0
    for d in range(S):
        D += [5 / 60 / YH] * 78; V += list(vs); G += list(g + k // 12); g += 7
        if d < S - 1: D.append(17.5 / YH); V.append(phi / 252); G.append(g); g += 1
    return np.array(D), np.array(V), np.array(G)
def hourly(D, V, G, P):
    ends = np.r_[np.nonzero(np.diff(G))[0], len(G) - 1]
    return np.add.reduceat(D, np.r_[0, ends[:-1] + 1]), np.add.reduceat(V, np.r_[0, ends[:-1] + 1]), np.r_[P[0], P[ends + 1]]
def logdiff_ndtr(x1, x2):
    """log(Phi(x2) - Phi(x1)) for x1 < x2, stable in both tails."""
    upper = x1 > 0
    a = np.where(upper, log_ndtr(-x1), log_ndtr(x2)); b = np.where(upper, log_ndtr(-x2), log_ndtr(x1))
    with np.errstate(divide='ignore', invalid='ignore'): return a + np.log1p(-np.exp(np.minimum(b - a, 0.0)))
from multiprocessing import Pool
from scipy.special import log_ndtr, logsumexp
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

from scipy.optimize import minimize
S_ = 30; START = 50.0; TICK = 0.01; DEL = TICK / START
FC = [(p, k, c) for c in (0, 1) for p in (1.0, 1.5, 2.0) for k in (0.1, 0.2, 0.3, 0.45, 0.7, 1.0, 1.5, 2.0, 3.0)]
def sim(truth, rng):
    D5, VU5, G5 = grids(S_, 1.5, 0.25); n5 = len(D5); sid = np.cumsum(D5 > 1 / (24 * 252))     # session index of each 5-minute piece (overnight opens the next session)
    if truth == 'switch':
        k = np.empty(n5); st = rng.random() < 0.5
        for s in range(S_):
            if s > 0 and rng.random() < 0.1: st = not st
            k[sid == s] = 0.45 if st else 0.15
    else: k = np.full(n5, 0.3)
    lr = -k * k * VU5 / 2 + k * np.sqrt(VU5) * rng.standard_normal(n5); X = np.r_[1.0, np.exp(np.cumsum(lr))]
    if truth in ('L15', 'L20'):
        p = 1.5 if truth == 'L15' else 2.0; d = round((2 * p - 1) / (p - 1)); c = 0.45 * (p - 1)
        on = int(np.nonzero((sid == 15) & (D5 < 1 / (24 * 252)))[0][0])                    # first 5-minute bar of session 15
        v = VU5[on:]; Bm = np.cumsum(np.sqrt(v)[:, None] * rng.standard_normal((len(v), d)), axis=0); Bm[:, 0] += 1 / c
        X[on + 1:] = X[on] * (c * np.linalg.norm(Bm, axis=1)) ** (-1 / (p - 1))
    return X, D5, VU5, G5
def forecast_scores(z, clocks, K, frozen):
    J = len(z); src = np.r_[START, np.where(np.array(z[:-1]) > 0, TICK * np.array(z[:-1], float), TICK / 4)]
    lo = np.where(np.array(z) > 0, TICK * (np.array(z) - 0.5), 0.0); hi = TICK * (np.array(z) + 0.5)
    rows = []
    for p, k, c in FC:
        var = k * k * (src / START) ** (2 * p - 2) * clocks[c]; sd = np.sqrt(var); mu = -var / 2
        with np.errstate(divide='ignore'): zl = np.where(lo > 0, (np.log(np.maximum(lo, 1e-300) / src) - mu) / sd, -np.inf)
        rows.append(logdiff_ndtr(zl, (np.log(hi / src) - mu) / sd))
    rows = np.array(rows); cum = np.cumsum(np.c_[np.zeros(len(FC)), rows], axis=1)        # cum[:, j] = rank before label j
    out = np.zeros(J); ch = None
    for j in range(K, J):
        if ch is None or not frozen: ch = int(np.argmax(cum[:, j]))
        out[j] = rows[ch, j]
    return np.cumsum(out)                                                                  # log Q through label j (scored labels only)
def path(args):
    truth, seed = args; rng = np.random.default_rng(seed); X, D5, VU5, G5 = sim(truth, rng)
    Dh, Vh, Ph = hourly(D5, VU5, G5, X); z = [int(round(START * x / TICK)) for x in Ph[1:]]; J = len(z); K = 79
    ends = [K - 1] + [i for i in range(K, J - 1) if Dh[i + 1] > 2 / (24 * 252)] + [J - 1]; cps = ends[1:]            # checkpoint label indices (0-based)
    bs = np.linspace(-0.5, 0.5, 21); ws = np.linspace(0.01, 0.64, 21); BG, WG = [g.ravel() for g in np.meshgrid(bs, ws)]
    best = None; Dgrid = np.full(len(cps), -np.inf)
    for v in (Dh, Vh):
        Q = logQ(1.0, z, Dh, v, BG, WG, 8); g = np.array([Q[t] - Q[K - 1] for t in cps]); Dgrid = np.maximum(Dgrid, g.max(1))
        i = int(np.argmax(g[-1]))
        def neg(th):
            b, w = th[0], math.exp(th[1])
            if not (-0.5 <= b <= 0.5 and 0.01 <= w <= 0.64): return 1e18
            q = logQ(1.0, z, Dh, v, b, w, 8)[:, 0]; return -(q[-1] - q[K - 1])
        r = minimize(neg, [BG[i], math.log(WG[i])], method='Nelder-Mead', options={'xatol': 1e-6, 'fatol': 1e-5, 'maxiter': 300}); best = max(best or -np.inf, -r.fun)
    out = {}
    for mode in ('expanding', 'frozen'):
        lQ = forecast_scores(z, (Dh, Vh), K, mode == 'frozen'); sc = np.array([lQ[t] for t in cps]) - Dgrid
        out[mode] = (sc, lQ[cps[-1]] - best)
    return out
if __name__ == '__main__':
    print('cell | mode | anytime crossing alpha .05 / .10 (grid denominators: upper values of the ideal score) | median final log score (refined denominator) | crossings before onset')
    with Pool(2) as pool:
        for truth, sd in zip(('N-in', 'switch', 'L15', 'L20'), np.random.SeedSequence(3636).spawn(4)):
            R = pool.map(path, [(truth, s) for s in sd.spawn(100)], chunksize=5)
            for mode in ('expanding', 'frozen'):
                S = np.array([r[mode][0] for r in R]); fin = np.array([r[mode][1] for r in R])
                pre = np.mean((S[:, :5] > math.log(20)).any(1)) if truth in ('L15', 'L20') else float('nan')
                print(f'{truth:7s} | {mode:9s} | {np.mean((S > math.log(20)).any(1)):.2f} / {np.mean((S > math.log(10)).any(1)):.2f} | {np.median(fin):.1f} | {pre:.2f}', flush=True)
