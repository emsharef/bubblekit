"""Reviewer's independent reproduction of experiment 033 (written without reading experiments/033/*.py), with the reviewer's
own code: the experiment-032 review's hourly session parser and scorers (v1 / 054, claim-033 36-kernel score on
rounded closes with clocks {F, U_US}, SADF / GSADF on P / P0), the experiment-003 review's JKP estimator and Methods
1-2 (N = number of increments), and realized / bipower variation for the GME and AMC diagnostics.
Design inputs taken from experiments/033/results.json: each record's name, group and tested window (the mechanical
windows, and the 98 time-matched controls chosen by experiment 021's membership code), the declared US clock shares,
and each record's published 5% critical values. Column (iii) is spot-checked on PLTR, NVDA and MSTR with the
reviewer's float cross-check of the filtered denominator (experiment-032 review) and own claim-034 forecast.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp033/reproduce.py \
        BARS_DIR RESULTS_JSON
        (BARS_DIR = the analyst's data/d6-intraday/bars/60m; RESULTS_JSON = experiments/033/results.json)
Seed:   none (deterministic). 2 workers. Not a CI check (not check.py)."""



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

def logdiff_ndtr(x1, x2):
    """log(Phi(x2) - Phi(x1)) for x1 < x2, stable in both tails."""
    upper = x1 > 0
    a = np.where(upper, log_ndtr(-x1), log_ndtr(x2)); b = np.where(upper, log_ndtr(-x2), log_ndtr(x1))
    with np.errstate(divide='ignore', invalid='ignore'): return a + np.log1p(-np.exp(np.minimum(b - a, 0.0)))
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
def eps_centered(s, z, Dl, v, B, M):
    """(1): prefix-J lower and upper centered allowances for every J (arrays indexed J-1)."""
    bm, bp, wm, wp = B; lc = logcells(z); a = np.r_[math.log(s), lc[:, 0]]; d = np.r_[math.log(s), lc[:, 1]]; Bmax = max(abs(bm), abs(bp))
    Rmax = np.maximum(np.abs(a[1:] - d[:-1]), np.abs(d[1:] - a[:-1])); C = (Rmax + Bmax * Dl + wp * v / 2) / (wm * v)
    r = np.r_[0.0, (d[1:] - a[1:]) / (2 * M)]; J = len(z)
    em = np.cumsum((r[1:] + r[:-1]) ** 2 / (2 * wm * v))
    ep = np.array([np.sum(r[1:Jp + 1] ** 2 * (C[:Jp] + np.r_[C[1:Jp], 0.0]) ** 2 / 2) for Jp in range(1, J + 1)])
    return em, ep

import csv, sys, json, datetime
from scipy.special import log_ndtr
from scipy.stats import ncx2
from zoneinfo import ZoneInfo
from scipy.stats import norm
from scipy.special import logsumexp
YH = 24 * 252
MKT = {'US': (ZoneInfo('America/New_York'), (9, 30), (16, 0), [60] * 6 + [30]), 'KR': (ZoneInfo('Asia/Seoul'), (9, 0), (15, 30), [60] * 5 + [90])}
def load_sessions(path, mkt):
    tz, op, cl, _ = MKT[mkt]; byday = {}; seen = set()
    with open(path) as f:
        for r in csv.DictReader(f):
            t = int(r['timestamp_utc'])
            if t in seen: continue
            seen.add(t)
            if r['close'] in ('', 'nan', 'None'): continue
            x = float(r['close'])
            if not (x > 0): continue
            lt = datetime.datetime.fromtimestamp(t, tz); byday.setdefault(lt.date(), []).append((lt, x))
    out = []
    for d in sorted(byday):
        bars = sorted(byday[d]); hm = {(b[0].hour, b[0].minute) for b in bars}
        close = (13, 0) if (mkt == 'US' and (13, 0) in hm and (13, 30) not in hm) else cl
        cdt = datetime.datetime(d.year, d.month, d.day, close[0], close[1], tzinfo=tz)
        bars = [b for b in bars if b[0] < cdt and (b[0].hour, b[0].minute) >= op]
        if not bars: continue
        mins = [((bars[i + 1][0] if i + 1 < len(bars) else cdt) - bars[i][0]).total_seconds() / 60 for i in range(len(bars))]
        out.append((d, [b[1] for b in bars], mins))
    return out
def build(sessions, a, b, mkt, shares):
    """Prices and increments for sessions with a <= date <= b: P (N+1), Delta (years), v_U, slot ids."""
    reg = MKT[mkt][3]; P, D, V, S = [], [], [], []
    for si, (d, closes, mins) in enumerate([s for s in sessions if a <= s[0] <= b]):
        for j, (x, mn) in enumerate(zip(closes, mins)):
            slot = min(j, len(reg) - 1)
            if not P: P.append(x); continue
            dur = (mn + (17.5 * 60 if j == 0 else 0)) / 60 / YH
            vu = (shares[slot] * mn / reg[slot]) / 252 if shares is not None else 0.0
            P.append(x); D.append(dur); V.append(vu); S.append(slot)
    return np.array(P), np.array(D), np.array(V), np.array(S)
def declare(paths, a, b, mkt):
    per = []
    for p in paths:
        P, D, V, S = build(load_sessions(p, mkt), a, b, mkt, None); R = np.diff(np.log(P)); ms = np.array([np.mean(R[S == j] ** 2) for j in range(len(MKT[mkt][3]))])
        per.append(ms / ms.sum())
    return np.mean(per, 0)
def v1(P, D):
    P = P / P[0]; N = len(D); K = N // 2
    L = np.array([logK(p, k, D, P[:-1], P[1:]) for p, k in CAT]); tr = L[:, :K].sum(1); ev = L[:, K:].sum(1)
    lG = ev[int(np.argmax(tr))]; lG0 = ev[NULL].max(); Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1])
    return lG - max(lG0, logD(R, D[K:], D[K:], Pe[1:])), lG - lG0
def cert_check(P, D, VU):
    """Float cross-check of D_filter = max over the wide box and clocks {F, U} of the claim-036 conditional likelihood:
    a 21 x 21 grid of (b, w) at M = 8, then Nelder-Mead in (b, log w) from the best grid point of each clock (kept inside
    the box); returns the best value and its claim-038 centred enclosure at that single parameter (eta = 0), i.e. a
    two-sided float enclosure of one point value g_theta <= D_filter."""
    global DEL
    from scipy.optimize import minimize
    DEL = 0.01; z = [int(round(x / 0.01)) for x in P[1:]]; s = float(P[0]); N = len(z); K = N // 2
    bs = np.linspace(-0.5, 0.5, 21); ws = np.linspace(0.01, 0.64, 21); BG, WG = [g.ravel() for g in np.meshgrid(bs, ws)]
    best = (-np.inf, None, None)
    for v in (D, VU):
        Q = logQ(s, z, D, v, BG, WG, 8); g = Q[-1] - Q[K - 1]; i = int(np.argmax(g))
        def neg(th):
            b, w = th[0], math.exp(th[1])
            if not (-0.5 <= b <= 0.5 and 0.01 <= w <= 0.64): return 1e18
            q = logQ(s, z, D, v, b, w, 8)[:, 0]; return -(q[-1] - q[K - 1])
        r = minimize(neg, [BG[i], math.log(WG[i])], method='Nelder-Mead', options={'xatol': 1e-6, 'fatol': 1e-4, 'maxiter': 400})
        if -r.fun > best[0]: best = (-r.fun, (r.x[0], math.exp(r.x[1])), v)
    (b, w), v = best[1], best[2]; em, ep = eps_centered(s, z, D, v, (b, b, w, w), 8)
    return best[0], (em[-1] + ep[K - 1], ep[-1] + em[K - 1])
def record(args):
    row, var, name, path, mkt, shares, a, b = args
    sess = load_sessions(path, mkt); P, D, VU, S = build(sess, a, b, mkt, shares)
    le, raw = v1(P, D); tick = 0.01 if mkt == 'US' else 1.0; Pr = np.round(P / tick) * tick
    e33 = scores(Pr / Pr[0], D, VU)['033']; Pn = P / P[0]; r0 = 0.01 + 1.8 / math.sqrt(len(Pn)); sd, gs = stats(Pn, [r0])[r0]
    out = dict(row=row, var=var, name=name, n=len(D), v1=le, raw=raw, c033=e33, sadf=sd, gsadf=gs)
    if mkt == 'US':
        g, (alo, ahi) = cert_check(P, D, VU); zz = np.array([int(round(x / 0.01)) for x in P]); tk = 0.01 / P[0]
        out.update(cert_grid=g, cert_lo=g - alo, cert_hi=g + ahi, logq=forecast034(zz, tk, D, VU))
    return out

from scipy import optimize, special
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


def jkp(S):
    global N
    N = len(S) - 1; xk, fz, nx, jk, lo, hi = estimators(S)
    v2, m, stop3, tik = method2(xk, np.sqrt(jk), lo, hi) if len(xk) else ('ind', np.nan, False, False)
    ag, s0 = gcj_alpha(S); par = (s0 * xk ** ag) ** 2
    m1 = 'bubble' if ag > 1 and np.all(jk >= par) else ('no bubble' if ag <= 1 and np.all(jk <= par) else 'inconclusive')
    return m1, ag, v2, m, len(xk)

def rec(args):
    name, group, w0, w1, shares, path, cv, spot = args
    d = datetime.date; a = d.fromisoformat(w0); b = d.fromisoformat(w1)
    P, D, VU, S = build(load_sessions(path, 'US'), a, b, 'US', shares)
    le, raw = v1(P, D); Pr = np.round(P / 0.01) * 0.01; e33 = scores(Pr / Pr[0], D, VU)['033']
    Pn = P / P[0]; r0 = 0.01 + 1.8 / math.sqrt(len(Pn)); sd, gs = stats(Pn, [r0])[r0]; m1, ag, v2, m, M = jkp(Pn)
    out = dict(name=name, group=group, n=len(D), v1=le, c033=e33, sadf=sd, gsadf=gs, fs=sd > cv['sadf']['5%'], fg=gs > cv['gsadf']['5%'], m2=v2, m1=m1,
               tick=float(np.median(0.01 / P)))
    if name in ('GME', 'AMC') and group == 'positive':
        r = np.diff(np.log(P)); RV = np.sum(r * r); BV = math.pi / 2 * np.sum(np.abs(r[1:]) * np.abs(r[:-1]))
        out['jump'] = (RV, BV, max(0, 1 - BV / RV), np.max(r * r) / RV, np.sort(r * r)[-5:].sum() / RV)
    if spot:
        g, (alo, ahi) = cert_check(P, D, VU); zz = np.array([int(round(x / 0.01)) for x in P]); lq = forecast034(zz, 0.01 / P[0], D, VU)
        out['cert'] = (lq, g, lq - g)
    return out
if __name__ == '__main__':
    BARS, RES = sys.argv[1:3]; res = json.load(open(RES)); sh = res['clock_shares']; sh = sh['US'] if isinstance(sh, dict) and 'US' in sh else sh
    shares = np.array(sh if not isinstance(sh, dict) else list(sh.values())[0], float)
    jobs = []
    for r in res['records']:
        if not r.get('n_increments'): continue
        jobs.append((r['name'], r['group'], r['window'][0], r['window'][1], shares, f'{BARS}/{r["name"].replace("^", "_")}.csv', r['cv'],
                     r['group'] == 'positive' and r['name'] in ('PLTR', 'NVDA', 'MSTR')))
    print('declared US shares', np.round(shares, 4), f'; {len(jobs)} testable records')
    from multiprocessing import Pool
    with Pool(2) as pool: out = pool.map(rec, jobs, chunksize=1)
    pub = {(r['name'], r['group'], tuple(r['window'])): r for r in res['records']}
    grp = lambda g: 'B' if g == 'positive' else ('C+W' if g in ('C', 'W') else 'controls')
    cnt = {}; worst = {'v1': 0, 'c033': 0, 'sadf': 0, 'gsadf': 0}; nmis = 0
    for o, j in zip(out, jobs):
        p = pub[(o['name'], o['group'], (j[2], j[3]))]
        nmis += o['n'] != p['n_increments']
        for k, pk in (('v1', 'v1'), ('c033', 'c033')):
            pv = p[pk]['log_e'] if isinstance(p[pk], dict) else p[pk]; worst[k] = max(worst[k], abs(o[k] - pv))
        ps = p['sadf']; worst['sadf'] = max(worst['sadf'], abs(o['sadf'] - (ps['sadf'] if isinstance(ps, dict) else ps[0]))); worst['gsadf'] = max(worst['gsadf'], abs(o['gsadf'] - (ps['gsadf'] if isinstance(ps, dict) else ps[1])))
        c = cnt.setdefault(grp(o['group']), [0] * 7)
        for i, f in enumerate((o['v1'] > math.log(20), o['c033'] > math.log(20), o['fs'], o['fg'], o['m2'] == 'bubble', o['m1'] == 'bubble')): c[i] += bool(f)
        c[6] += 1
    print(f'increment-count mismatches {nmis}; max |diff| vs published: v1 {worst["v1"]:.3g}, claim 033 {worst["c033"]:.3g}, SADF {worst["sadf"]:.3g}, GSADF {worst["gsadf"]:.3g}')
    diffs = []
    for o, j in zip(out, jobs):
        p = pub[(o['name'], o['group'], (j[2], j[3]))]
        diffs.append((abs(o['v1'] - p['v1']['log_e']), o['name'], o['group'][:3], o['v1'], p['v1']['log_e'], o['c033'], p['c033']['log_e']))
    diffs.sort(reverse=True)
    print('largest v1 differences (name, group, own v1, published v1, own 033, published 033):')
    for x in diffs[:6]: print(f'   {x[1]} {x[2]}: {x[3]:.1f} vs {x[4]:.1f}; {x[5]:.1f} vs {x[6]:.1f}')
    print('records with |v1 diff| > 1:', sum(x[0] > 1 for x in diffs), '; median |v1 diff|', f'{np.median([x[0] for x in diffs]):.2e}')
    print('counts per group (v1, claim 033, SADF 5%, GSADF 5%, JKP M2 bubble, JKP M1 bubble; records):', cnt)
    print('largest v1 / claim-033 log e on controls:', round(max(o['v1'] for o in out if grp(o['group']) == 'controls'), 2), round(max(o['c033'] for o in out if grp(o['group']) == 'controls'), 2))
    for o in out:
        if 'jump' in o: print(f"{o['name']}: RV {o['jump'][0]:.3f}, BV {o['jump'][1]:.3f}, jump share {o['jump'][2]:.2f}, largest share {o['jump'][3]:.2f}, top-5 share {o['jump'][4]:.2f}")
        if 'cert' in o:
            pc_ = pub[(o['name'], 'positive', tuple(next(j for j in jobs if j[0] == o['name'] and j[1] == 'positive')[2:4]))]['cert']
            print(f"{o['name']}: own log q {o['cert'][0]:.1f}, own float log D (optimized point) {o['cert'][1]:.1f}, own bound {o['cert'][2]:.1f}; published log q {pc_.get('log_q')}, log D in [{pc_.get('log_D_lower')}, {pc_.get('log_D_upper')}], bound {pc_.get('log_e_bound')}")
