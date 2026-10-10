"""Reviewer's independent check of claim 070 (written before reading checks/070/* and experiments/037/*). At most 2 workers.
Reuses the reviewer's kernels, claim-033 profile and claim-069 segment code (inlined).
(a) Pooled segment profiles (5) via concatenation and via additive raw statistics with identity (4); recurrence (7)
    against exhaustive partitions; budget 1 against direct Nelder-Mead over pair paths; ordering (9) against the
    claim-069 denominator; calendar drift-cost identity (11).
(b) Monte Carlo on the claim-068/069 review design (days of 7 equal increments, 60 + 60 days, training-selected exact
    CEV forecast): E_common, E_joint(K) for K in {1, 3, 10}, E_sw(3) (claim 069). Truths: N1 constant GBM; N4 common
    drift .05 with exactly 3 day-boundary scale switches {.15, .45} (covered for K >= 3); N3 daily drift U[-.5, .5]
    plus 3 scale switches (outside the joint family for K < 59); A CEV p = 2, kappa = .45. 2,000 records each.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/070/reproduce.py
Seed:   numpy default_rng(70) for (a); SeedSequence(7070) per truth for (b). 2 workers. Not a CI check (not check.py)."""


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
def structural():
    rng = np.random.default_rng(70); w_b = w_c = w_4 = w_nm = w_11 = 0.0; order_ok = True
    for t in range(10):
        D = int(rng.integers(3, 6)); blocks = list(rng.integers(2, 5, D)); N = sum(blocks); Dl = rng.uniform(0.002, 0.02, N); U = Dl * rng.uniform(0.5, 2, N)
        P = np.r_[1.0, np.exp(np.cumsum(rng.normal(0, 0.05, N)))]; rs = raw_stats(P, blocks, Dl, U); st = day_stats(P, blocks, Dl, U)
        R = np.log(P[1:] / P[:-1]); w_c = max(w_c, abs(seg_joint(rs, 0, D) - logD(R, Dl, U, P[1:])))
        g = {k: sum(r[k] for r in rs) for k in ('A', 'B', 'C')}; Qi = g['C'] - g['B'] ** 2 / g['A']
        Qd = sum(r['C'] - r['B'] ** 2 / r['A'] + r['A'] * (r['B'] / r['A'] - g['B'] / g['A']) ** 2 for r in rs); w_4 = max(w_4, abs(Qi - Qd) / Qi)
        for Km in range(D):
            pj = pj_dp(rs, Km); w_b = max(w_b, abs(pj - pj_brute(rs, Km)))
            order_ok &= pj <= psw_dp(st, Km) + 1e-9 and (Km == 0 or pj >= pj_dp(rs, Km - 1) - 1e-9)
        order_ok &= abs(pj_dp(rs, D - 1) - psw_dp(st, D - 1)) < 1e-9
        best = -math.inf
        for cuts in [()] + [(c,) for c in range(1, D)]:
            e = (0,) + cuts + (D,); seg_of = [next(s for s in range(len(e) - 1) if e[s] <= d < e[s + 1]) for d in range(D)]
            def neg(th):
                tot = 0.0; i = 0
                for d, n in enumerate(blocks):
                    b, w = th[2 * seg_of[d]], math.exp(th[2 * seg_of[d] + 1]); Rr = np.log(P[i + 1:i + n + 1] / P[i:i + n]); v = U[i:i + n]; dl = Dl[i:i + n]
                    tot += np.sum(-(Rr - b * dl + w * v / 2) ** 2 / (2 * w * v) - 0.5 * np.log(2 * math.pi * w * v) - np.log(P[i + 1:i + n + 1])); i += n
                return -tot
            r = minimize(neg, np.tile([0.0, math.log(0.2)], len(e) - 1), method='Nelder-Mead', options={'xatol': 1e-11, 'fatol': 1e-13, 'maxiter': 100000, 'maxfev': 100000})
            r = minimize(neg, r.x, method='Nelder-Mead', options={'xatol': 1e-12, 'fatol': 1e-13, 'maxiter': 100000, 'maxfev': 100000}); best = max(best, -r.fun)
        w_nm = max(w_nm, abs(best - pj_dp(rs, 1)) / abs(best))
        rc = raw_stats(P, blocks, Dl, Dl); stc = day_stats(P, blocks, Dl, Dl); Ni = sum(blocks)
        gc = {k: sum(r[k] for r in rc) for k in ('A', 'B', 'C')}; Qj = gc['C'] - gc['B'] ** 2 / gc['A']; Qw = sum(s_['Q'] for s_ in stc)
        w_11 = max(w_11, abs((seg(stc, 0, D) - seg_joint(rc, 0, D)) - (Ni / 2) * math.log(Qj / Qw)))
    print(f'(a) concatenated vs additive segment profile max |diff| {w_c:.1e}; identity (4) max rel diff {w_4:.1e}; recurrence vs exhaustive '
          f'{w_b:.1e}; budget 1 vs Nelder-Mead rel {w_nm:.1e}; ordering (9) holds {bool(order_ok)}; identity (11) max |diff| {w_11:.1e}')
NB = 7; DAYS = 60; dt = 1 / (NB * 252); K = NB * DAYS; N = 2 * K; Dl = np.full(N, dt); FC = [(p, k) for p in (1.25, 1.5, 2.0) for k in (0.2, 0.3, 0.45)]
KS = (1, 3, 10)
def work(args):
    truth, seed, B = args; rng = np.random.default_rng(seed); out = []
    for _ in range(B):
        if truth == 'N1': P = np.r_[1.0, np.exp(np.cumsum((0.05 - 0.045) * dt + 0.3 * math.sqrt(dt) * rng.standard_normal(N)))]
        elif truth in ('N3', 'N4'):
            R = list((0.05 - 0.045) * dt + 0.3 * math.sqrt(dt) * rng.standard_normal(K))
            sw = set(rng.choice(np.arange(1, DAYS), 3, replace=False)); k = 0.15 if rng.random() < 0.5 else 0.45
            for d in range(DAYS):
                if d in sw: k = 0.6 - k
                b = rng.uniform(-0.5, 0.5) if truth == 'N3' else 0.05; R += list((b - k * k / 2) * dt + k * math.sqrt(dt) * rng.standard_normal(NB))
            P = np.r_[1.0, np.exp(np.cumsum(R))]
        else:
            c = 0.45; Bm = np.cumsum(math.sqrt(dt) * rng.standard_normal((N, 3)), axis=0); Bm[:, 0] += 1 / c; P = np.r_[1.0, 1 / (c * np.linalg.norm(Bm, axis=1))]
        L = np.array([logK(p, k, Dl, P[:-1], P[1:]) for p, k in FC]); lq = L[int(np.argmax(L[:, :K].sum(1))), K:].sum()
        Pe = P[K:]; rs = raw_stats(Pe, [NB] * DAYS, Dl[K:], Dl[K:]); st = day_stats(Pe, [NB] * DAYS, Dl[K:], Dl[K:])
        out.append([lq - pj_dp(rs, 0)] + [lq - pj_dp(rs, k) for k in KS] + [lq - psw_dp(st, 3)])
    return out
if __name__ == '__main__':
    structural()
    print('(b) 2,000 records per truth; mean E / P(E > 20): E_common = E_joint(0) | E_joint(1) | E_joint(3) | E_joint(10) | E_sw(3) (069)')
    with Pool(2) as pool:
        for truth, sd in zip(('N1', 'N4', 'N3', 'A'), np.random.SeedSequence(7070).spawn(4)):
            a = np.array([x for ch in pool.map(work, [(truth, s, 50) for s in sd.spawn(40)]) for x in ch])
            f = lambda x: f'{np.exp(np.minimum(x, 700)).mean():.3g} / {np.mean(x > math.log(20)):.4f}'
            print(f'   {truth}: ' + ' | '.join(f(a[:, i]) for i in range(a.shape[1])) + f';  median J_joint(3) {np.median(a[:, 0] - a[:, 2]):.1f}', flush=True)
