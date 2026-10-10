"""Reviewer's independent reproduction of experiment 034 (written without reading experiments/034/*.py), with the reviewer's
own code: experiment-027 grids, simulator and 36-kernel CEV numerator (clocks F and U(1.5, .25)), claim-033 profile,
and the experiment-032 review's hourly session parser.
Score: blocks = sessions (simulation: the overnight increment plus the session's 7 hourly bars; real bars: the
session's increments, the first spanning the overnight); evaluation blocks = complete blocks after the split
floor(N/2), the split session's remainder its own block; P_d = max over {F, U} of the claim-033 profile on the block
(with its price Jacobian); log E_day = log q - sum log P_d with log q the selected numerator's evaluation kernels;
E_033G = log q - max over {F, U} of the whole-evaluation profile (no CEV nulls). A one-increment block is singular
(log E_day = -inf).
(B) Simulation, hourly: N-const (GBM b = 0, kappa = .3 on U); N-between (kappa in {.15, .45}, Markov with switch
probability 1/10 per session at session boundaries, new state from the session's overnight piece); N-within (each
switch at a uniform 5-minute bar of the session); CEV p in {1.5, 2} x kappa .45 and p = 2, kappa .3 at 250 sessions.
(A) Real data: experiment 033's records (names, windows, controls from its results.json), declared US shares, on the
stored closes and on the closes rounded to the cent (both reported); band
counts, mean daily contribution c_d and positive-day counts per range band (max / min of the day's closes including
its starting close); GME and AMC log E_day and log E_033G.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp034/reproduce.py \
        BARS_DIR RESULTS_033_JSON
Seed:   SeedSequence(3434), one child per simulation cell. 2 workers. Not a CI check (not check.py)."""



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

import csv, sys, json, datetime
from multiprocessing import Pool
def numer_inc(P, D, VU):
    N = len(D); K = N // 2; L = np.array([logK(p, k, clk, P[:-1], P[1:]) for clk in (D, VU) for p, k in CAT])
    return L[int(np.argmax(L[:, :K].sum(1)))], K
def scores_blocks(P, D, VU, start):
    """start: boolean per increment, True at the first increment of a block (session)."""
    li, K = numer_inc(P, D, VU); N = len(D); lq = li[K:].sum()
    Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1]); Y = Pe[1:]; De = D[K:]; Ve = VU[K:]
    l033 = max(logD(R, De, De, Y), logD(R, De, Ve, Y))
    idx = [0] + [i for i in range(1, N - K) if start[K + i]] + [N - K]; cd = []; lpd = 0.0
    for a, b in zip(idx[:-1], idx[1:]):
        lp = max(logD(R[a:b], De[a:b], De[a:b], Y[a:b]), logD(R[a:b], De[a:b], Ve[a:b], Y[a:b])) if b - a >= 2 else np.inf
        lpd += lp; c = li[K + a:K + b].sum() - lp
        rng_ = Pe[a:b + 1].max() / Pe[a:b + 1].min(); cd.append((c, rng_))
    return lq - lpd, lq - l033, lpd - l033, cd
BANDS = [1.0, 1.01, 1.02, 1.05, 1.10, 1.20, np.inf]
def sim_switch(S, rng, within):
    D5, VU5, G5 = grids(S, 1.5, 0.25); n5 = len(D5)
    # session id per 5-minute increment: increments after an overnight belong to the next session; overnight belongs to next session too
    sid = np.zeros(n5, int); s = 0
    for i in range(n5):
        if D5[i] > 1 / (24 * 252): s += 1                                            # overnight increment opens session s
        sid[i] = s
    k = np.empty(n5); st = rng.random() < 0.5
    for s in range(S):
        idx = np.nonzero(sid == s)[0]
        flip = s > 0 and rng.random() < 0.1
        if flip and within:
            bars = idx[D5[idx] < 1 / (24 * 252)]; cut = rng.choice(bars); k[idx[idx < cut]] = 0.45 if st else 0.15; st = not st; k[idx[idx >= cut]] = 0.45 if st else 0.15
        else:
            if flip: st = not st
            k[idx] = 0.45 if st else 0.15
    P = np.r_[1.0, np.exp(np.cumsum(-k * k * VU5 / 2 + k * np.sqrt(VU5) * rng.standard_normal(n5)))]
    return P, D5, VU5, G5
def simwork(args):
    truth, S, seed, B = args; rng = np.random.default_rng(seed); out = []
    for _ in range(B):
        if truth in ('between', 'within'): P5, D5, VU5, G5 = sim_switch(S, rng, truth == 'within')
        else:
            D5, VU5, G5 = grids(S, 1.5, 0.25)
            P5 = np.r_[1.0, np.exp(np.cumsum(-0.09 * VU5 / 2 + 0.3 * np.sqrt(VU5) * rng.standard_normal(len(D5))))] if truth == 'const' else None
            if P5 is None:
                p, kk = truth; d = round((2 * p - 1) / (p - 1)); c = kk * (p - 1); Bm = np.cumsum(np.sqrt(VU5)[:, None] * rng.standard_normal((len(D5), d)), axis=0); Bm[:, 0] += 1 / c
                P5 = np.r_[1.0, (c * np.linalg.norm(Bm, axis=1)) ** (-1 / (p - 1))]
        Dh, Vh, Ph = hourly(D5, VU5, G5, P5); start = np.r_[True, Dh[1:] > 2 / (24 * 252)]        # overnight increments open blocks
        e_day, e033, cost, _ = scores_blocks(Ph, Dh, Vh, start); out.append((e_day, e033, cost))
    return out
def realwork(args):
    name, group, w0, w1, shares, path = args
    P, D, VU, S = build(load_sessions(path, 'US'), datetime.date.fromisoformat(w0), datetime.date.fromisoformat(w1), 'US', shares)
    res_ = {}
    for kind, X in (('stored', P), ('rounded', np.round(P / 0.01) * 0.01)):
        e_day, e033, cost, cd = scores_blocks(X / X[0], D, VU, S == 0)                     # model units: P / P0
        zero = np.mean(np.diff(np.log(X)) == 0); res_[kind] = (e_day, e033, cd, zero)
    return name, group, res_
if __name__ == '__main__':
    BARS, RES = sys.argv[1:3]; res = json.load(open(RES)); shares = np.array(res['clock_shares'], float); lt = math.log(20)
    cells = [('const', 60, 1000), ('const', 250, 1000), ('between', 250, 1000), ('within', 250, 1000), ((1.5, 0.45), 250, 500), ((2.0, 0.3), 250, 500), ((2.0, 0.45), 250, 500)]
    with Pool(2) as pool:
        print('(B) alpha = 0.05 rejection: E_day | E_033G ; mean E_day / mean E_033G ; mean reset cost log P_day - log P_033G')
        for (truth, S, M), sd in zip(cells, np.random.SeedSequence(3434).spawn(len(cells))):
            a = np.array([x for ch in pool.map(simwork, [(truth, S, s, 50) for s in sd.spawn(M // 50)]) for x in ch])
            f = lambda x: np.exp(np.minimum(x, 700)).mean()
            print(f'   {str(truth):12s} S={S}: {np.mean(a[:, 0] > lt):.3f} | {np.mean(a[:, 1] > lt):.3f} ; {f(a[:, 0]):.2g} / {f(a[:, 1]):.2g} ; {np.mean(a[:, 2]):.1f}', flush=True)
        jobs = [(r['name'], r['group'], r['window'][0], r['window'][1], shares, f'{BARS}/{r["name"].replace("^", "_")}.csv') for r in res['records'] if r.get('n_increments')]
        out = pool.map(realwork, jobs, chunksize=1)
    grp = lambda g: 'B' if g == 'positive' else ('C+W' if g in ('C', 'W') else 'controls')
    for kind in ('stored', 'rounded'):
        agg = {}; sing = {}; zs = {}
        for name, group, rr in out:
            e_day, e033, cd, zero = rr[kind]; g = grp(group); sing[g] = sing.get(g, 0) + (e_day == -np.inf); zs.setdefault(g, []).append(zero)
            for c, r in cd:
                bi = int(np.searchsorted(BANDS, r, side='right') - 1); z = agg.setdefault((g, bi), [0, 0.0, 0, 0])
                z[0] += 1; z[2] += (c > 0)
                if np.isfinite(c): z[1] += c; z[3] += 1
            if name in ('GME', 'AMC') and group == 'positive': print(f'(A, {kind} closes) {name}: log E_day {e_day:.1f}, log E_033G {e033:.1f}')
        print(f'(A, {kind} closes) singular-block records per group: {sing}; median share of exactly-zero hourly returns per group: ' + ', '.join(f'{g} {np.median(v):.3f}' for g, v in zs.items()))
        for g in ('B', 'C+W', 'controls'):
            print(f'(A, {kind} closes) {g}: ' + ' | '.join(f"{agg[(g, b)][0]} / {agg[(g, b)][1] / max(agg[(g, b)][3], 1):.1f} / {agg[(g, b)][2]}" if (g, b) in agg else '0' for b in range(6)))
