"""Reviewer's independent reproduction of experiment 037 (written without reading experiments/037/*.py), with the reviewer's
own claim-068/069/070 review code (inlined): days of 7 equal increments (dt = 1/(252*7)), 60 training and 60 evaluation
days, start 1; numerator = exact CEV forecast with (p, kappa) in {1.25, 1.5, 2} x {.2, .3, .45}, first training
maximizer, evaluated from the training endpoint; calendar shape. Columns: common (= joint K = 0), joint K = 1, 3, 10,
joint K = 59 (= the product of daily profiles), free (claim 069) K = 0, 3. Truths: N1 constant GBM (drift .05,
volatility .3); N-common3 (training as N1; 3 distinct uniform evaluation day boundaries, scales alternating .15/.45
from a fair start, drift .05); N-joint3 (the same scales, drift U[-.5, .5] drawn once per segment); N-daily3 (drift
redrawn every evaluation day); A (exact CEV p = 2, kappa = .45). 2,000 records each: P(E > 20), A's rejection counts,
paired loss against common and the median log profile gap relative to common.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp037/reproduce.py
Seed:   SeedSequence(3737), one child per truth. 2 workers. Not a CI check (not check.py)."""



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
from scipy.optimize import minimize
def pday(P, blocks, Dl):
    """Sum over blocks of claim-033 calendar-shape profiles (block start = previous block's last price)."""
    tot = 0.0; i = 0
    for n in blocks:
        Pe = P[i:i + n + 1]; R = np.log(Pe[1:] / Pe[:-1]); tot += logD(R, Dl[i:i + n], Dl[i:i + n], Pe[1:]); i += n
    return tot

import itertools
def day_stats(P, blocks, Dl, U):
    out = []; i = 0
    for n in blocks:
        R = np.log(P[i + 1:i + n + 1] / P[i:i + n]); dl = Dl[i:i + n]; u = U[i:i + n]
        A = np.sum(dl ** 2 / u); B = np.sum(dl * R / u); C = np.sum(R ** 2 / u); T = dl.sum(); V = u.sum(); S = R.sum()
        out.append(dict(n=n, Q=C - B * B / A, K=S - B * T / A, H=V - T * T / A, c=-0.5 * n * math.log(2 * math.pi) - 0.5 * np.log(u).sum() - np.log(P[i + 1:i + n + 1]).sum())); i += n
    return out
def seg(st, a, b):
    N = sum(s['n'] for s in st[a:b]); Q = sum(s['Q'] for s in st[a:b]); K = sum(s['K'] for s in st[a:b]); H = sum(s['H'] for s in st[a:b]); c = sum(s['c'] for s in st[a:b])
    if Q <= 0: return math.inf
    w = 2 * Q / (N + math.sqrt(N * N + H * Q)); return c - (N / 2) * math.log(w) - Q / (2 * w) - K / 2 - w * H / 8
def psw_dp(st, Kmax):
    D = len(st); Pi = [[seg(st, a, b) if b > a else None for b in range(D + 1)] for a in range(D + 1)]
    Bk = {(1, b): Pi[0][b] for b in range(1, D + 1)}; best = Bk[(1, D)]
    for k in range(2, Kmax + 2):
        for b in range(k, D + 1): Bk[(k, b)] = max(Bk[(k - 1, a)] + Pi[a][b] for a in range(k - 1, b))
        best = max(best, Bk[(k, D)])
    return best
def psw_brute(st, Kmax):
    D = len(st); best = -math.inf
    for k in range(0, Kmax + 1):
        for cuts in itertools.combinations(range(1, D), k):
            e = (0,) + cuts + (D,); best = max(best, sum(seg(st, e[i], e[i + 1]) for i in range(len(e) - 1)))
    return best

import itertools
from scipy.optimize import minimize
def raw_stats(P, blocks, Dl, U):
    out = []; i = 0
    for n in blocks:
        R = np.log(P[i + 1:i + n + 1] / P[i:i + n]); dl = Dl[i:i + n]; u = U[i:i + n]
        out.append(dict(n=n, A=np.sum(dl ** 2 / u), B=np.sum(dl * R / u), C=np.sum(R ** 2 / u), T=dl.sum(), V=u.sum(), S=R.sum(),
                        c=-0.5 * n * math.log(2 * math.pi) - 0.5 * np.log(u).sum() - np.log(P[i + 1:i + n + 1]).sum())); i += n
    return out
def seg_joint(rs, a, b):
    g = {k: sum(r[k] for r in rs[a:b]) for k in ('n', 'A', 'B', 'C', 'T', 'V', 'S', 'c')}
    Q = g['C'] - g['B'] ** 2 / g['A']; K_ = g['S'] - g['B'] * g['T'] / g['A']; H = g['V'] - g['T'] ** 2 / g['A']; N = g['n']
    if Q <= 0: return math.inf
    w = 2 * Q / (N + math.sqrt(N * N + H * Q)); return g['c'] - (N / 2) * math.log(w) - Q / (2 * w) - K_ / 2 - w * H / 8
def pj_dp(rs, Kmax):
    D = len(rs); Pi = [[seg_joint(rs, a, b) if b > a else None for b in range(D + 1)] for a in range(D + 1)]
    Bk = {(1, b): Pi[0][b] for b in range(1, D + 1)}; best = Bk[(1, D)]
    for k in range(2, Kmax + 2):
        for b in range(k, D + 1): Bk[(k, b)] = max(Bk[(k - 1, a)] + Pi[a][b] for a in range(k - 1, b))
        best = max(best, Bk[(k, D)])
    return best
def pj_brute(rs, Kmax):
    D = len(rs); best = -math.inf
    for k in range(0, Kmax + 1):
        for cuts in itertools.combinations(range(1, D), k):
            e = (0,) + cuts + (D,); best = max(best, sum(seg_joint(rs, e[i], e[i + 1]) for i in range(len(e) - 1)))
    return best

NB = 7; DAYS = 60; dt = 1 / (NB * 252); K = NB * DAYS; N = 2 * K; Dl = np.full(N, dt); FC = [(p, k) for p in (1.25, 1.5, 2.0) for k in (0.2, 0.3, 0.45)]
COLS = ('common', 'joint1', 'joint3', 'joint10', 'joint59', 'free0', 'free3')
def work(args):
    truth, seed, B = args; rng = np.random.default_rng(seed); out = []
    for _ in range(B):
        if truth == 'N1': P = np.r_[1.0, np.exp(np.cumsum((0.05 - 0.045) * dt + 0.3 * math.sqrt(dt) * rng.standard_normal(N)))]
        elif truth == 'A':
            c = 0.45; Bm = np.cumsum(math.sqrt(dt) * rng.standard_normal((N, 3)), axis=0); Bm[:, 0] += 1 / c; P = np.r_[1.0, 1 / (c * np.linalg.norm(Bm, axis=1))]
        else:
            R = list((0.05 - 0.045) * dt + 0.3 * math.sqrt(dt) * rng.standard_normal(K))
            sw = set(rng.choice(np.arange(1, DAYS), 3, replace=False)); k = 0.15 if rng.random() < 0.5 else 0.45
            b = 0.05 if truth == 'N-common3' else rng.uniform(-0.5, 0.5)
            for d in range(DAYS):
                if d in sw:
                    k = 0.6 - k
                    if truth == 'N-joint3': b = rng.uniform(-0.5, 0.5)
                if truth == 'N-daily3': b = rng.uniform(-0.5, 0.5)
                R += list((b - k * k / 2) * dt + k * math.sqrt(dt) * rng.standard_normal(NB))
            P = np.r_[1.0, np.exp(np.cumsum(R))]
        L = np.array([logK(p, k, Dl, P[:-1], P[1:]) for p, k in FC]); lq = L[int(np.argmax(L[:, :K].sum(1))), K:].sum()
        Pe = P[K:]; rs = raw_stats(Pe, [NB] * DAYS, Dl[K:], Dl[K:]); st = day_stats(Pe, [NB] * DAYS, Dl[K:], Dl[K:])
        den = [pj_dp(rs, 0), pj_dp(rs, 1), pj_dp(rs, 3), pj_dp(rs, 10), pday(Pe, [NB] * DAYS, Dl[K:]), psw_dp(st, 0), psw_dp(st, 3)]
        out.append([lq - d for d in den])
    return out
if __name__ == '__main__':
    lt = math.log(20)
    print('2,000 records per truth: P(E > 20) for ' + ' | '.join(COLS))
    with Pool(2) as pool:
        for truth, sd in zip(('N1', 'N-common3', 'N-joint3', 'N-daily3', 'A'), np.random.SeedSequence(3737).spawn(5)):
            a = np.array([x for ch in pool.map(work, [(truth, s, 50) for s in sd.spawn(40)]) for x in ch])
            print(f'   {truth:10s}: ' + ' | '.join(f'{np.mean(a[:, i] > lt):.4f}' for i in range(len(COLS))), flush=True)
            if truth == 'A':
                rej = (a > lt); base = rej[:, 0]
                for i, c in enumerate(COLS):
                    loss = base.astype(float) - rej[:, i]; gap = np.median(a[:, 0] - a[:, i])
                    print(f'      {c:8s}: rejections {rej[:, i].sum()} / 2000; paired loss {loss.mean():.4f} ({loss.std(ddof=1) / math.sqrt(len(loss)):.4f}); median log profile gap {gap:.2f}', flush=True)
