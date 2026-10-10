"""Reviewer's independent reproduction of experiment 030 (written without reading experiments/030/*.py), using the reviewer's
own code from earlier reviews: claim 055 / 054 scores (experiment-021 review), JKP's smooth-kernel estimator, GC-J
power fit and Method 1 / Method 2 (experiment-003 review, with N = number of increments), and SADF / GSADF
(experiment-002 review, r0 = 0.01 + 1.8 / sqrt(N)); critical values from 1,000 driftless random walks at each length.
Data (read in place, never copied): DATA_DIR = data/delisted.
  InfoSpace WIKI: wiki/wiki_subset.csv ticker BCOR close, 1998-12-15..2002-09-19, split-adjusted as registered:
    divide by 2 before each of 1999-05-05, 2000-01-05, 2000-04-07; multiply by 10 before 2002-09-13. Sensitivity:
    the same factors applied one trading day early / late.
  InfoSpace sye: sye/BCOR.csv close over the same dates (already continuous in this file; no further adjustment).
  GeoCities: sye/GCTY.csv open, 1998-08-11..1999-05-28.
Every series is divided by its first price.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp030/reproduce.py DATA_DIR
Seed:   SeedSequence(3030) for the critical values. 2 workers. Not a CI check (not check.py)."""
import numpy as np, math, csv, sys
from multiprocessing import Pool
from scipy import optimize, special
from scipy.special import ive, gammaincc
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
def stats(y, r0s):
    T = len(y); dyall = np.diff(y)
    out = {}
    L0s = {r0: int(np.floor(r0 * T)) for r0 in r0s}
    L0min = min(L0s.values())
    best = {r0: [-np.inf, -np.inf] for r0 in r0s}   # [sadf, gsadf]
    for a in range(0, T - L0min + 1):
        x = y[a:T - 1] - y[a]; dy = dyall[a:]
        n = np.arange(1, len(x) + 1, dtype=float)
        Sx = np.cumsum(x); Sy = np.cumsum(dy); Sxx = np.cumsum(x * x); Sxy = np.cumsum(x * dy); Syy = np.cumsum(dy * dy)
        with np.errstate(divide='ignore', invalid='ignore'):
            cxx = Sxx - Sx * Sx / n; cxy = Sxy - Sx * Sy / n; cyy = Syy - Sy * Sy / n
            b = cxy / cxx; ssr = np.maximum(cyy - b * cxy, 0.0)
            t = b / np.sqrt(ssr / (n - 2) / cxx)
        L = n + 1                                       # window length in y's
        for r0, L0 in L0s.items():
            if a > T - L0:
                continue
            m = np.nanmax(t[L >= L0])
            if a == 0:
                best[r0][0] = m
            best[r0][1] = max(best[r0][1], m)
    return best


import json, sys, os, hashlib, datetime as dt
from multiprocessing import Pool
EXP = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'experiments', '021')
def score(P):
    P = P / P[0]; N = len(P) - 1; Dt = np.full(N, 1 / 252); K = N // 2
    L = np.array([logK(p, k, Dt, P[:-1], P[1:]) for p, k in CAT])
    tr = L[:, :K].sum(1); ev = L[:, K:].sum(1); sel = int(np.argmax(tr)); lG = ev[sel]; lG0 = ev[NULL].max()
    Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1]); n_e = len(R); tau = n_e / 252; a = R.sum() / tau; Q = ((R - a / 252) ** 2 * 252).sum()
    lDG = -(n_e / 2) * (math.log(2 * math.pi * Q / n_e) + 1) - 0.5 * n_e * math.log(1 / 252) - np.log(Pe[1:]).sum() if Q > 0 else np.inf
    return float(lG - max(lG0, lDG)), float(lG - lG0), sel
_xs = np.linspace(-0.5, 0.5, 20001)[1:-1]
_PHI_C = np.trapezoid(np.exp(1 / (4 * _xs ** 2 - 1)), _xs)
def phi(u):
    out = np.zeros_like(u); m = np.abs(u) < 0.5
    out[m] = np.exp(1 / (4 * u[m] ** 2 - 1)) / _PHI_C
    return out

def estimators(S):
    lo, hi = S.min(), S.max(); h = N ** -0.25 * (hi - lo); M = int(np.floor(N ** 0.25 / 2))
    xk = lo + h * (2 * np.arange(1, M + 1) - 1)
    Si = S[:-1]; q = N * np.diff(S) ** 2
    keep, fz, nx, jkp = [], [], [], []
    for x in xk:
        w = np.abs(Si - x) < h; n_ = w.sum()
        if n_ < 10:
            continue
        p = phi((Si - x) / h)
        keep.append(x); nx.append(n_); fz.append(q[w].mean()); jkp.append((p * q).sum() / p.sum())
    return np.array(keep), np.array(fz), np.array(nx), np.array(jkp), lo, hi

def gcj_alpha(S):
    X2 = N * np.diff(S) ** 2; ls = np.log(S[:-1])
    prof = lambda a: np.log(np.mean(X2 * np.exp(-2 * a * ls))) + 2 * a * ls.mean()
    grid = np.linspace(-1, 8, 181); i = int(np.argmin([prof(a) for a in grid]))
    r = optimize.minimize_scalar(prof, bounds=(grid[max(i - 1, 0)], grid[min(i + 1, 180)]), method='bounded')
    a = r.x; s02 = np.mean(X2 * np.exp(-2 * a * ls))
    return a, np.sqrt(s02)

def K1(x, y, a, b, tau=6.0):
    X, Y = np.meshgrid(x, y, indexing='ij'); xg = np.maximum(X, Y); xl = np.minimum(X, Y)
    return tau / np.sinh(tau * (b - a)) * np.cosh(tau * (b - xg)) * np.cosh(tau * (xl - a))

def q2m(x, y, m):
    X, Y = np.meshgrid(x, y, indexing='ij'); xg = np.maximum(X, Y); xl = np.minimum(X, Y)
    return 4 * xg ** (-(m + 1)) * special.beta(m + 1, 2) * (1 - (m + 1) / (m + 3) * xl / xg)  # 2F1(-1,b;c;z)=1-bz/c

def solve(Q, f):
    if np.linalg.cond(Q) > 1e12:
        return np.linalg.solve(Q + 1e-12 * np.trace(Q) / len(f) * np.eye(len(f)), f), True
    return np.linalg.solve(Q, f), False

def method2(xk, sig, lo, hi):
    """xk, lo, hi in price units; returns verdict, m_hat, stopped_at_iii, tikhonov_used."""
    s = hi; x = xk / s; a_, b_ = lo / s, hi / s
    f = 1 / sig ** 2
    cb = np.linalg.solve(K1(x, x, a_, b_), f)
    thr = (hi - (hi - lo) / 3) / s
    z = np.linspace(thr, b_, 400)
    fb = K1(x, z, a_, b_).T @ cb
    if np.any(fb <= 0):
        return 'fail_ii', np.nan, False, False
    sb = fb ** -0.5
    slope = np.polyfit(np.log(z), np.log(sb), 1)[0]
    if slope <= 0:
        return 'no bubble', np.nan, True, False
    tik = [False]
    def obj(m):
        c, t = solve(q2m(x, x, m), f)
        fm = q2m(x, z, m).T @ c
        if np.any(fm <= 0):
            return np.inf
        tik[0] = t
        return np.sqrt(np.trapezoid((fm ** -0.5 - sb) ** 2, z))
    grid = np.round(np.arange(0, 20.0001, 0.01), 2)
    vals = np.array([obj(m) for m in grid]); i = int(np.argmin(vals))
    if not np.isfinite(vals[i]):
        return 'fail_iv', np.nan, False, False
    r = optimize.minimize_scalar(obj, bounds=(grid[max(i - 1, 0)], grid[min(i + 1, len(grid) - 1)]), method='bounded')
    m = r.x if r.fun <= vals[i] else grid[i]
    obj(m)
    v = 'inconclusive' if 0.8 <= m <= 1.2 else ('bubble' if m > 1 else 'no bubble')
    return v, m, False, tik[0]


def rows(path, tick, col, a, b):
    out = []
    with open(path) as f:
        for r in csv.DictReader(f):
            if r['ticker'] == tick and a <= r['date'] <= b: out.append((r['date'], float(r[col])))
    out.sort(); return [d for d, _ in out], np.array([x for _, x in out])
SPLITS = [('1999-05-05', 0.5), ('2000-01-05', 0.5), ('2000-04-07', 0.5), ('2002-09-13', 10.0)]
def adjust(dates, x, shift):
    x = x.copy(); idx = {d: i for i, d in enumerate(dates)}
    for d, f in SPLITS:
        i = idx[d] + shift; x[:i] *= f
    return x
def jkp(S):
    global N
    N = len(S) - 1; xk, fz, nx, jk, lo, hi = estimators(S)
    v2, m, stop3, tik = method2(xk, np.sqrt(jk), lo, hi) if len(xk) else ('ind', np.nan, False, False)
    ag, s0 = gcj_alpha(S); par = (s0 * xk ** ag) ** 2
    m1 = 'bubble' if ag > 1 and np.all(jk >= par) else ('no bubble' if ag <= 1 and np.all(jk <= par) else 'inconclusive')
    return m1, ag, v2, m, len(xk)
def null_stats(args):
    n, seed = args; rng = np.random.default_rng(seed); r0 = 0.01 + 1.8 / math.sqrt(n)
    st = stats(np.cumsum(np.r_[1.0, rng.standard_normal(n - 1) / math.sqrt(n)]), [r0])[r0]; return st[0], st[1]
if __name__ == '__main__':
    D = sys.argv[1]
    dw, xw = rows(f'{D}/wiki/wiki_subset.csv', 'BCOR', 'close', '1998-12-15', '2002-09-19')
    ds, xs = rows(f'{D}/sye/BCOR.csv', 'BCOR', 'close', '1998-12-15', '2002-09-19')
    dg, xg = rows(f'{D}/sye/GCTY.csv', 'GCTY', 'open', '1998-08-11', '1999-05-28')
    adj = adjust(dw, xw, 0); assert dw == ds
    agree = np.abs(adj / adj[0] / (xs / xs[0]) - 1)
    print(f'InfoSpace: {len(adj)} days; WIKI-adjusted vs sye (first-price normalized): within 1% on {np.mean(agree < 0.01):.3f}, '
          f'within 0.1% on {np.mean(agree < 0.001):.3f}; max |daily log move| WIKI-adjusted {np.abs(np.diff(np.log(adj))).max():.3f}; GeoCities {len(xg)} days')
    series = [('InfoSpace WIKI adjusted', adj), ('InfoSpace sye close', xs), ('InfoSpace WIKI, splits -1 day', adjust(dw, xw, -1)),
              ('InfoSpace WIKI, splits +1 day', adjust(dw, xw, 1)), ('GeoCities sye open', xg)]
    cv = {}
    with Pool(2) as pool:
        for n in sorted({len(x) for _, x in series}):
            a = np.array(pool.map(null_stats, [(n, s) for s in np.random.SeedSequence([3030, n]).spawn(1000)], chunksize=20)); cv[n] = np.quantile(a, 0.95, axis=0)
    print('series | n | v1 log E (055) | 054 raw log E | JKP M1 (GC-J a) | JKP M2 (m, grid points) | SADF / GSADF (5% cv)')
    for name, x in series:
        P = x / x[0]; e55, eraw, _ = score(P); m1, ag, v2, m, M = jkp(P); r0 = 0.01 + 1.8 / math.sqrt(len(P)); st = stats(P, [r0])[r0]; c = cv[len(P)]
        print(f'{name:32s} | {len(P)} | {e55:,.0f} | {eraw:,.0f} | {m1} ({ag:.2f}) | {v2} ({m:.2f}, {M}) | {st[0]:.2f} / {st[1]:.2f} ({c[0]:.2f} / {c[1]:.2f})', flush=True)
