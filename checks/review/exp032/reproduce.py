"""Reviewer's independent reproduction of experiment 032 (written without reading experiments/032/*.py), with the reviewer's
own code from earlier reviews (claim-055/054 scores, claim-033 profile and experiment-027 36-kernel score, SADF/GSADF,
claim-034 CEV cell forecast, claim-036 midpoint recursion with claim-038 centred allowances).
Own parser of the archive's regular-session hourly bars (bars/60m/<symbol>.csv, first-seen closes, null closes dropped):
local times (America/New_York, Asia/Seoul); US session 09:30-16:00 (bars at 09:30..15:30), half days (a 13:00 bar and
no 13:30 bar) close at 13:00; KRX 09:00-15:30 (bars 09:00..14:00); bars starting at or after the close are dropped;
bar length = next start - start, last to the close; each session break = one 17.5 h overnight added to the first
increment; durations in years = hours / (24 * 252). Slots by position (slot 0 = overnight + first bar); declared
shares = mean over names of each name's share of mean squared log return per slot in the declaration period
(N24m-3 2023-11-07..2024-06-28; E6 2023-10-06..2023-12-28); U clock v = share / 252, scaled for irregular bars by
(bar minutes / regular slot minutes). Split floor(N/2).
Columns: (i) v1 (claim 055 with calendar durations) and 054 raw; (ii) claim 033 / experiment-027 36-kernel score on
closes rounded to the cent (US) or won (KRX), clocks {F, U}; (iv) SADF / GSADF on P / P0 with the experiment's
published 5% critical values (design input); (iii) a float cross-check of the certified denominator: the claim-036
conditional likelihood at M = 8 maximized over the wide box and both clocks (21 x 21 grid, then Nelder-Mead), with its
claim-038 centred enclosure at the maximizing parameter (a float lower value for D_filter), against the published interval;
and the reviewer's own claim-034 forecast log q (p >= 1 x 3 kappa x 2 clocks, training-selected at representatives).

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp032/reproduce.py \
        BARS_DIR RESULTS_JSON
        (BARS_DIR = the analyst's data/d6-intraday/bars/60m; RESULTS_JSON = experiments/032/results.json for the
        published critical values and certified intervals)
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
if __name__ == '__main__':
    BARS, RES = sys.argv[1:3]; res = json.load(open(RES)); f = lambda s: f'{BARS}/{s.replace("^", "_")}.csv'
    d = datetime.date; N24 = ['^GSPC', '^DJI', 'V', 'PG', 'WMT', 'KO', 'TRV']
    shE6 = declare([f('000660.KS')], d(2023, 10, 6), d(2023, 12, 28), 'KR'); shN = declare([f(s) for s in N24], d(2023, 11, 7), d(2024, 6, 28), 'US')
    print('declared shares E6', np.round(shE6, 3), ' N24m-3', np.round(shN, 3))
    jobs = [('E6', v, '000660.KS', f('000660.KS'), 'KR', shE6, d(2024, 1, 2), e) for v, e in (('full', d(2026, 10, 5)), ('to_peak', d(2026, 6, 22)))]
    jobs += [('N24m-3', v, s, f(s), 'US', shN, d(2024, 7, 1), e) for v, e in (('full', d(2026, 6, 30)), ('to_peak', d(2026, 6, 2))) for s in N24]
    from multiprocessing import Pool
    with Pool(2) as pool: out = pool.map(record, jobs)
    pub = {(r['row'], r['variant'], r['name']): r for r in res['records']}
    print('row | variant | name | n | v1 log E | 054 raw | 033 log E (rounded) | SADF / GSADF (5% flags) | grid log D (centred enclosure) vs published [lo, hi] | log q mine vs published')
    for o in out:
        cv = res['critical_values'][str(o['n'] + 1)]; fl = (o['sadf'] > cv['sadf']['5%'], o['gsadf'] > cv['gsadf']['5%'])
        line = f"{o['row']} | {o['var']:7s} | {o['name']:9s} | {o['n']} | {o['v1']:.1f} | {o['raw']:.1f} | {o['c033']:.1f} | {o['sadf']:.2f} / {o['gsadf']:.2f} ({fl[0]} / {fl[1]})"
        if 'cert_grid' in o:
            p = pub[(o['row'], o['var'], o['name'])]['cert']
            line += f" | {o['cert_grid']:.1f} [{o['cert_lo']:.1f}, {o['cert_hi']:.1f}] vs [{p['log_D_lower']:.1f}, {p['log_D_upper']:.1f}] | {o['logq']:.1f} vs {p['log_q']:.1f}"
        print(line, flush=True)
