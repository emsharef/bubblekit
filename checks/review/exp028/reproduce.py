"""Reviewer's independent reproduction of experiment 028's headline cells (written without reading experiments/028/*.py;
experiment 027's design and the reviewer's own experiment-027 code are reused). Cent tick: dollar price = S0 * X with
X in model units starting at 1; labels z = floor(S0 X / 0.01 + 1/2); tick in model units 0.01 / S0.
Columns: E033-exact (experiment 027's claim-033 column); E033-round (the same formula on label * tick / S0 as if
exact); E034(box, h, l): claim 034's denominator with clocks {F, U(1.5, .25)} computed by best-first branch and bound
over the dyadic cover at depth h (vectorized W_clock in log space, state level l), over the narrow box
[-.2, .2] x [.04, .2025] or the wide box [-.5, .5] x [.01, .64]; numerator = the claim-034 CEV cell forecast:
candidates p in {1, 1.25, 1.5, 2} x kappa in {.2, .3, .45} on clocks F and U (24), chosen on training by the kernel
log-likelihood at cent-label representatives, evaluation cell probabilities exact (lognormal for p = 1; noncentral
chi-square of the Bessel representation for p > 1), representatives tick * z, floored at 1e-300.
Truths (clock U(1.5, .25)): GBM b = 0, kappa .3 (N-in) and .6 (N-k60), $50 and $5; CEV p in {1.5, 2} x kappa .45 at $50,
p = 2, kappa .45 at $5.
(a) hourly, 250 sessions: 200 paths per cell; columns E033-exact, E033-round, E034 narrow (h, l) in {(2, 2), (4, 2)},
    wide (4, 2); narrow (4, 4) on the first 100 paths.
(b) 5-minute, 250 sessions, E033-exact and E033-round: 500 paths for N-in-$5, A-20-45 and A-20-45-$5.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp028/reproduce.py
Seed:   SeedSequence(2828), one child per cell in list order (a), then (b). 2 workers. Not a CI check.
Floor check (same seeds, forecast only): append the argument `floorcheck` to count, per hourly cell, the paths whose
selected claim-034 forecast had a p > 1 cell probability floored at 1e-300 (p = 1 cells are exact in log space)."""

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
def scores(P, D, VU):
    N = len(D); K = N // 2; x, y = P[:-1], P[1:]
    L = np.array([logK(p, k, clk, x, y) for clk in (D, VU) for p, k in CAT])           # 36 kernels: flat block, then U block
    tr = L[:, :K].sum(1); ev = L[:, K:].sum(1); nulls = NULL + [18 + i for i in NULL]
    lG = ev[int(np.argmax(tr))]; lG0 = ev[nulls].max(); lGf = ev[int(np.argmax(tr[:18]))]; lG0f = ev[NULL].max()
    Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1]); Y = Pe[1:]; De = D[K:]
    dF = logD(R, De, De, Y); dU = logD(R, De, VU[K:], Y)
    return {'v1flat': lGf - max(lG0f, dF), 'raw': lG - lG0, '055': lG - max(lG0, dF), '033': lG - max(lG0, dF, dU)}

import heapq
from multiprocessing import Pool
from scipy.special import log_ndtr, logsumexp
from scipy.stats import ncx2, norm
def sim(truth, S, rng):
    D, VU, G = grids(S, 1.5, 0.25)
    if truth[0] == 'gbm':
        b, k = truth[1], truth[2]; return np.r_[1.0, np.exp(np.cumsum(b * D - k * k * VU / 2 + k * np.sqrt(VU) * rng.standard_normal(len(D))))]
    p, k = truth[1], truth[2]; d = round((2 * p - 1) / (p - 1)); c = k * (p - 1)
    Bm = np.cumsum(np.sqrt(VU)[:, None] * rng.standard_normal((len(D), d)), axis=0); Bm[:, 0] += 1 / c
    return np.r_[1.0, (c * np.linalg.norm(Bm, axis=1)) ** (-1 / (p - 1))]
def logdiff_ndtr(x1, x2):
    """log(Phi(x2) - Phi(x1)) for x1 < x2, stable in both tails."""
    upper = x1 > 0
    a = np.where(upper, log_ndtr(-x1), log_ndtr(x2)); b = np.where(upper, log_ndtr(-x2), log_ndtr(x1))
    with np.errstate(divide='ignore', invalid='ignore'): return a + np.log1p(-np.exp(np.minimum(b - a, 0.0)))
def logWc(a, dS, c, dT, bL, bH, wL, wH, Dl, v):
    """Claim 034 (2)-(3) vectorized, positive source and target cells only."""
    Mm = np.log(a) + bL * Dl - wH * v / 2; Mp = np.log(dS) + bH * Dl - wL * v / 2; sm = np.sqrt(wL * v); sp = np.sqrt(wH * v)
    L = np.log(c); R = np.log(dT); m = np.clip((L + R) / 2, Mm, Mp); strad = (L <= m) & (m <= R)
    l = np.minimum(np.abs(L - m), np.abs(R - m)); r = np.maximum(np.abs(L - m), np.abs(R - m))
    with np.errstate(divide='ignore', invalid='ignore'): s0 = np.sqrt((r * r - l * l) / (2 * np.log(r / l)))
    s = np.where(strad, sm, np.clip(np.nan_to_num(s0, nan=0.0), sm, sp))
    return logdiff_ndtr((L - m) / s, (R - m) / s)
def subcells(z, tick, K):
    lo = np.where(z == 0, 0.0, tick * (z - 0.5)); hi = tick * (z + 0.5); e = lo[:, None] + (hi - lo)[:, None] * np.arange(K + 1)[None, :] / K
    return e[:, :-1], e[:, 1:]
def lse(x, axis):
    m = np.max(x, axis=axis, keepdims=True); m = np.where(np.isfinite(m), m, 0.0)
    return np.squeeze(m, axis) + np.log(np.sum(np.exp(x - m), axis=axis))
def logD034_boxes(z, tick, Dl, v, boxes, L):
    """Claim 034 (4) for a batch of boxes and one clock: levels 0..L with inherited same-box parent bounds; max_a U_0."""
    bx = np.array(boxes); bL, bH, wL, wH = [bx[:, i][:, None, None, None] for i in range(4)]; n = len(z) - 1; prev = None
    for lv in range(L + 1):
        K = 2 ** lv; sa, sb = subcells(z, tick, K)
        lW = logWc(sa[None, :-1, :, None], sb[None, :-1, :, None], sa[None, 1:, None, :], sb[None, 1:, None, :], bL, bH, wL, wH,
                   Dl[None, :, None, None], v[None, :, None, None])                                   # (nb, n, K, K)
        U = np.zeros((len(boxes), n + 1, K)); par = np.arange(K) // 2
        for j in range(n - 1, -1, -1):
            Uj = np.minimum(lse(lW[:, j] + U[:, j + 1][:, None, :], axis=2), 0.0)
            if prev is not None: Uj = np.minimum(Uj, prev[:, j][:, par])
            U[:, j] = Uj
        prev = U
    return U[:, 0].max(1)
def children(bx, depth):
    bL, bH, wL, wH = bx; k = 2 ** depth; be = np.linspace(bL, bH, k + 1); we = np.linspace(wL, wH, k + 1)
    return [(be[i], be[i + 1], we[j], we[j + 1]) for i in range(k) for j in range(k)]
def logD034_all_l2(z, tick, Dl, clocks, B): return logD034_all(z, tick, Dl, clocks, B, False)[:2]
def logD034_all(z, tick, Dl, clocks, B, do4=True):
    """Returns (h2 l2, h4 l2, h4 l4) maxima: exact dyadic-cover maxima, pruned by parent bounds (child <= parent) and by
    state monotonicity (l = 4 bound <= l = 2 bound of the same box)."""
    par = [(ci, bx) for ci in range(len(clocks)) for bx in children(B, 2)]
    pv = np.concatenate([logD034_boxes(z, tick, Dl, clocks[ci], children(B, 2), 2) for ci in range(len(clocks))])
    h22 = pv.max(); best = -np.inf; leaves = []
    for idx in np.argsort(-pv):
        if pv[idx] <= best: break
        ci, bx = par[idx]; ch = children(bx, 2); vals = logD034_boxes(z, tick, Dl, clocks[ci], ch, 2)
        best = max(best, vals.max()); leaves += [(vals[t], ci, ch[t]) for t in range(len(ch))]
    h42 = best; best4 = -np.inf
    if not do4: return h22, h42, np.nan
    leaves.sort(key=lambda x: -x[0])
    for t in range(0, len(leaves), 8):
        chunk = [x for x in leaves[t:t + 8] if x[0] > best4]
        if not chunk: break
        for ci in set(x[1] for x in chunk):
            sub = [x[2] for x in chunk if x[1] == ci]; best4 = max(best4, logD034_boxes(z, tick, Dl, clocks[ci], sub, 4).max())
    return h22, h42, best4
FCAT = [(p, k) for p in (1.0, 1.25, 1.5, 2.0) for k in (0.2, 0.3, 0.45)]
def cell_logprob(p, k, v, x, lo, hi):
    if p == 1.0:
        s = k * np.sqrt(v); m = np.log(x) - k * k * v / 2
        with np.errstate(divide='ignore'): llo = np.where(lo > 0, (np.log(np.maximum(lo, 1e-300)) - m) / s, -np.inf)
        return logdiff_ndtr(llo, (np.log(hi) - m) / s)
    c = k * (p - 1); d = (2 * p - 1) / (p - 1); nc = (x ** (-(p - 1)) / c) ** 2 / v
    q_hi = (hi ** (-(p - 1)) / c) ** 2 / v; q_lo = np.where(lo > 0, (np.maximum(lo, 1e-300) ** (-(p - 1)) / c) ** 2 / v, np.inf)
    F_lo = ncx2.cdf(q_hi, d, nc); F_hi = np.where(np.isfinite(q_lo), ncx2.cdf(np.minimum(q_lo, 1e300), d, nc), 1.0)
    S_lo = ncx2.sf(q_hi, d, nc); S_hi = np.where(np.isfinite(q_lo), ncx2.sf(np.minimum(q_lo, 1e300), d, nc), 0.0)
    pr = np.where(F_hi < 0.5, F_hi - F_lo, S_lo - S_hi)
    return np.log(np.maximum(pr, 1e-300))
def forecast034(z, tick, D, VU):
    N = len(z) - 1; K = N // 2; rep = tick * np.maximum(z, 0.25)
    best, sel = -np.inf, None
    for clk in (D, VU):
        for p, k in FCAT:
            ll = logK(p, k, clk[:K], rep[:K], rep[1:K + 1]).sum()
            if ll > best: best, sel = ll, (p, k, clk)
    p, k, clk = sel; lo = np.where(z[K + 1:] == 0, 0.0, tick * (z[K + 1:] - 0.5)); hi = tick * (z[K + 1:] + 0.5)
    return cell_logprob(p, k, clk[K:], rep[K:-1], lo, hi).sum()
def floorwork(args):
    truth, S0, S, seed, B = args; rng = np.random.default_rng(seed); D, VU, G = grids(S, 1.5, 0.25); tick = 0.01 / S0; n = 0
    for _ in range(B):
        P = sim(truth, S, rng); Dh, Vh, Ph = hourly(D, VU, G, P); z = np.floor(Ph * S0 / 0.01 + 0.5).astype(int)
        n += int(np.isclose(forecast034_steps(z, tick, Dh, Vh), math.log(1e-300)).any())
    return n
def forecast034_steps(z, tick, D, VU):
    N = len(z) - 1; K = N // 2; rep = tick * np.maximum(z, 0.25); best, sel = -np.inf, None
    for clk in (D, VU):
        for p, k in FCAT:
            ll = logK(p, k, clk[:K], rep[:K], rep[1:K + 1]).sum()
            if ll > best: best, sel = ll, (p, k, clk)
    p, k, clk = sel; lo = np.where(z[K + 1:] == 0, 0.0, tick * (z[K + 1:] - 0.5)); hi = tick * (z[K + 1:] + 0.5)
    return cell_logprob(p, k, clk[K:], rep[K:-1], lo, hi)
def work(args):
    truth, S0, S, seed, B, part, bi = args; rng = np.random.default_rng(seed); out = []
    D, VU, G = grids(S, 1.5, 0.25); tick = 0.01 / S0; NB = (-0.2, 0.2, 0.04, 0.2025); WB = (-0.5, 0.5, 0.01, 0.64)
    for i in range(B):
        P = sim(truth, S, rng)
        if part == 'h':
            Dh, Vh, Ph = hourly(D, VU, G, P); z = np.floor(Ph * S0 / 0.01 + 0.5).astype(int); Pr = z * tick
            ex = scores(Ph, Dh, Vh)['033']; ro = scores(Pr, Dh, Vh)['033']
            K = (len(z) - 1) // 2; ze = z[K:]; lq = forecast034(z, tick, Dh, Vh); cl = [Dh[K:], Vh[K:]]
            n22, n42, n44 = logD034_all(ze, tick, Dh[K:], cl, NB) if bi < 10 else (*logD034_all_l2(ze, tick, Dh[K:], cl, NB), np.nan)
            w42 = logD034_all_l2(ze, tick, Dh[K:], cl, WB)[1]
            r = [ex, ro, lq - n22, lq - n42, lq - w42, lq - n44, int((z == 0).any())]
        else:
            z = np.floor(P * S0 / 0.01 + 0.5).astype(int); r = [scores(P, D, VU)['033'], scores(z * tick, D, VU)['033']]
        out.append(r)
    return out
CELLS_H = [(('gbm', 0.0, 0.3), 50.0), (('gbm', 0.0, 0.6), 50.0), (('gbm', 0.0, 0.3), 5.0), (('cev', 1.5, 0.45), 50.0), (('cev', 2.0, 0.45), 50.0), (('cev', 2.0, 0.45), 5.0)]
CELLS_5 = [(('gbm', 0.0, 0.3), 5.0), (('cev', 2.0, 0.45), 50.0), (('cev', 2.0, 0.45), 5.0)]
if __name__ == '__main__':
    ss = np.random.SeedSequence(2828); sd = ss.spawn(len(CELLS_H) + len(CELLS_5)); lt = math.log(20)
    import sys
    if sys.argv[1:] == ['floorcheck']:
        with Pool(2) as pool:
            for (truth, S0), s_ in zip(CELLS_H, sd[:len(CELLS_H)]):
                print(f'floor check, hourly {str(truth):20s} ${S0:4.0f}: {sum(pool.map(floorwork, [(truth, S0, 250, s, 10) for s in s_.spawn(20)]))} of 200 paths floored', flush=True)
        raise SystemExit
    with Pool(2) as pool:
        print('(a) hourly, 250 sessions, alpha = 0.05: E033-exact | E033-round | E034 N h2 l2 | E034 N h4 l2 | E034 W h4 l2 | E034 N h4 l4 (first 100); zero-label paths')
        for (truth, S0), s_ in zip(CELLS_H, sd[:len(CELLS_H)]):
            a = np.array([x for ch in pool.map(work, [(truth, S0, 250, s, 10, 'h', bi) for bi, s in enumerate(s_.spawn(20))]) for x in ch])
            rates = [np.mean(a[:, c] > lt) for c in range(5)] + [np.mean(a[~np.isnan(a[:, 5]), 5] > lt)]
            print(f'   {str(truth):20s} ${S0:4.0f}: ' + ' | '.join(f'{x:.3f}' for x in rates) + f'; {int(a[:, 6].sum())}', flush=True)
        print('(b) 5-minute, 250 sessions, alpha = 0.05: E033-exact | E033-round')
        for (truth, S0), s_ in zip(CELLS_5, sd[len(CELLS_H):]):
            a = np.array([x for ch in pool.map(work, [(truth, S0, 250, s, 25, '5', 0) for s in s_.spawn(20)]) for x in ch])
            print(f'   {str(truth):20s} ${S0:4.0f}: {np.mean(a[:, 0] > lt):.3f} | {np.mean(a[:, 1] > lt):.3f}', flush=True)
