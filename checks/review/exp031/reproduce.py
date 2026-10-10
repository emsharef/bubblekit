"""Reviewer's independent reproduction of experiment 031 (written without reading experiments/031/*.py), with the reviewer's
own code from earlier reviews: claim 055 / 054 scores (experiment-021 review), JKP estimator, GC-J fit and Methods 1-2
(experiment-003 review), SADF / GSADF (experiment-002 review, r0 = 0.01 + 1.8 / sqrt(N), on P / P0).
Own loaders for the registered sources (read in place): Wayback merged_*.csv "adjclose"; qstk "Adj Close";
sye "close"; Yahoo JSON adjclose (dates in the exchange time zone); InfoSpace WIKI closes split-adjusted at
1999-05-05, 2000-01-05, 2000-04-07 (experiment 030). Rows with empty, NaN or non-positive values are dropped. Joined
names are chain-linked: earlier source through the join day, later source after it rescaled to agree on that day
(join days 2006-05-22 Wachovia, 2006-01-04 Countrywide, 2007-04-12 Merrill Lynch, as in Deviation 2).
Windows: E2 1995-01-03..2001-12-28 (to peak 2000-03-27); E4 2003-01-02..2008-12-30 (to peak 2006-12-27).
Critical values: experiment 031's published 5% values per length (results.json), a design input as in the
reviewer's experiment-021 review. Untested names (Exodus, Commerce One, Global Crossing): own adjusted-close inventory. Rounding diagnostic: minimum price
and share of zero daily returns per name (Wayback adjclose is rounded to the cent).

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp031/reproduce.py \
        DATA_DIR VIAV_JSON CRIT_JSON
        (DATA_DIR = data/delisted; VIAV_JSON = the analyst's data/d6/yahoo_VIAV.json, SHA-256 checked against
        experiments/031/data_manifest.json; CRIT_JSON = experiments/031/results.json for its critical values)
Seed:   none (deterministic). 2 workers. Not a CI check (not check.py)."""
import numpy as np, math, csv, sys, json, hashlib, datetime
from multiprocessing import Pool
from scipy import optimize, special
from scipy.special import ive, gammaincc

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


def jkp(S):
    global N
    N = len(S) - 1; xk, fz, nx, jk, lo, hi = estimators(S)
    v2, m, stop3, tik = method2(xk, np.sqrt(jk), lo, hi) if len(xk) else ('ind', np.nan, False, False)
    ag, s0 = gcj_alpha(S); par = (s0 * xk ** ag) ** 2
    m1 = 'bubble' if ag > 1 and np.all(jk >= par) else ('no bubble' if ag <= 1 and np.all(jk <= par) else 'inconclusive')
    return m1, ag, v2, m, len(xk)

def ld_csv(path, datecol, valcol):
    out = {}
    with open(path) as f:
        rd = csv.reader(f); hdr = [h.strip().lower() for h in next(rd)]; i, j = hdr.index(datecol), hdr.index(valcol)
        for r in rd:
            try: x = float(r[j])
            except (ValueError, IndexError): continue
            if x > 0 and math.isfinite(x) and r[i] not in out: out[r[i]] = x
    return out
def ld_yahoo(path):
    r = json.load(open(path))['chart']['result'][0]; off = r['meta']['gmtoffset']; out = {}
    for t, x in zip(r['timestamp'], r['indicators']['adjclose'][0]['adjclose']):
        if x is not None and x > 0: out[datetime.datetime.utcfromtimestamp(t + off).strftime('%Y-%m-%d')] = x
    return out
def ld_wiki(path):
    out = {}
    with open(path) as f:
        for r in csv.DictReader(f):
            if r['ticker'] == 'BCOR' and r['close']: out[r['date']] = float(r['close'])
    ds = sorted(out)
    for d0 in ('1999-05-05', '2000-01-05', '2000-04-07'):
        for d in ds:
            if d < d0: out[d] *= 0.5
    return out
def chain(a, b, J):
    s = a[J] / b[J]; out = {d: x for d, x in a.items() if d <= J}; out.update({d: x * s for d, x in b.items() if d > J}); return out
def series_of(name, D, viav):
    W = lambda t: ld_csv(f'{D}/wayback_yahoo/merged_{t}.csv', 'date', 'adjclose')
    if name == 'InfoSpace': return ld_wiki(f'{D}/wiki/wiki_subset.csv')
    if name == 'CMGI': return W('CMGI')
    if name == 'JDS Uniphase': return ld_yahoo(viav)
    if name == 'VA Linux': return W('LNUX')
    if name == 'theglobe.com': return ld_yahoo(f'{D}/yahoo/yahoo_TGLO.json')
    if name == 'Lehman': return ld_csv(f'{D}/qstk/LEHMQ.csv', 'date', 'adj close')
    if name == 'Wachovia': return chain(W('WB'), ld_csv(f'{D}/qstk/WB.csv', 'date', 'adj close'), '2006-05-22')
    if name == 'Countrywide': return chain(W('CFC'), ld_csv(f'{D}/sye/CFC.csv', 'date', 'close'), '2006-01-04')
    if name == 'Merrill Lynch': return chain(W('MER'), ld_csv(f'{D}/sye/MER.csv', 'date', 'close'), '2007-04-12')
    if name == 'Freddie Mac': return ld_yahoo(f'{D}/yahoo/yahoo_FMCC.json')
NAMES = [('E2', 'InfoSpace'), ('E2', 'CMGI'), ('E2', 'JDS Uniphase'), ('E2', 'VA Linux'), ('E2', 'theglobe.com'),
         ('E4', 'Lehman'), ('E4', 'Wachovia'), ('E4', 'Countrywide'), ('E4', 'Merrill Lynch'), ('E4', 'Freddie Mac')]
WIN = {'E2': ('1995-01-03', '2001-12-28', '2000-03-27'), 'E4': ('2003-01-02', '2008-12-30', '2006-12-27')}
def job(args):
    row, name, var, D, viav = args; s = series_of(name, D, viav); a, b, pk = WIN[row]; end = b if var == 'full' else pk
    ds = sorted(d for d in s if a <= d <= end); P = np.array([s[d] for d in ds]); P = P / P[0]
    le, raw, _ = score(P); r0 = 0.01 + 1.8 / math.sqrt(len(P)); sd, gs = stats(P, [r0])[r0]; m1, ag, v2, m, M = jkp(P)
    return row, name, var, len(P), ds[0], ds[-1], le, raw, sd, gs, v2, m1
if __name__ == '__main__':
    D, viav, critp = sys.argv[1:4]
    print('VIAV sha256', hashlib.sha256(open(viav, 'rb').read()).hexdigest()[:16])
    cv = json.load(open(critp))['critical_values']
    for t in ('EXDS', 'CMRC', 'GBLX', 'GX'):
        x = ld_csv(f'{D}/wayback_yahoo/merged_{t}.csv', 'date', 'adjclose'); ds = sorted(x)
        print(f'inventory {t}: {len(x)} adjusted closes' + (f', {ds[0]} .. {ds[-1]}' if ds else ''))
    jobs = [(row, name, var, D, viav) for row, name in NAMES for var in ('full', 'to_peak')]
    with Pool(2) as pool: res = pool.map(job, jobs)
    print('row | name | variant | n | first..last | v1 log E (flag) | 054 raw (flag) | SADF / GSADF (5% flags) | JKP M2 | JKP M1')
    cnt = {}
    for row, name, var, n, f, l, le, raw, sd, gs, v2, m1 in res:
        c = cv[str(n)] if str(n) in cv else None
        fs = (sd > c['sadf']['5%'], gs > c['gsadf']['5%']) if c else (None, None)
        print(f'{row} | {name:14s} | {var:7s} | {n} | {f}..{l} | {le:,.1f} ({le > math.log(20)}) | {raw:,.1f} ({raw > math.log(20)}) | {sd:.3f} / {gs:.3f} ({fs[0]} / {fs[1]}) | {v2} | {m1}', flush=True)
        k = (row, var); z = cnt.setdefault(k, [0] * 6)
        for i, flag in enumerate((le > math.log(20), raw > math.log(20), fs[0], fs[1], v2 == 'bubble', m1 == 'bubble')): z[i] += bool(flag)
    for row, name in NAMES:
        x = series_of(name, D, viav); a, b, _ = WIN[row]; ds = sorted(d for d in x if a <= d <= b); P = np.array([x[d] for d in ds]); R = np.diff(np.log(P))
        print(f'rounding diagnostic {name:14s}: min price in window {P.min():.4f}; share of zero daily returns {np.mean(R == 0):.3f}; '
              f'in the first year {np.mean(R[:252] == 0):.3f}; median |nonzero return| first year {np.median(np.abs(R[:252][R[:252] != 0])):.4f}')
    print('counts (v1, 054 raw, SADF, GSADF, JKP M2 bubble, JKP M1 bubble):', {f'{k[0]} {k[1]}': v for k, v in cnt.items()})
