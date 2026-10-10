"""Reviewer's independent reproduction of experiment 041 (written without reading experiments/041/*.py), on the two largest
record blocks: experiment 021's daily records (adjusted closes, full and to-peak) and experiment 033's hourly records.
Own code: the jump statistics (jump share 1 - BV/RV with BV = (pi/2) sum |r_j||r_(j-1)|; top-5 squared-return share of
RV; second/first-half volatility ratio in calendar time), the registered jump filter (|r_j| > 4 sigma_j sqrt(tau_j),
sigma_j^2 = (pi/2) sum |r_i||r_(i-1)| / sum tau_i over 42 bipower terms around j that use none of r_(j-1), r_j,
r_(j+1): i = j-22..j-2 and j+3..j+23, missing terms taken from the other side at the edges; tau = days / 365.25 daily,
the declared clock hourly), the continuous-component record (jump returns set to zero, prices rebuilt), and the scores
on raw and filtered records with the reviewer's experiment-021 / 033 code (v1 and E daily; SADF / GSADF with the
sources' stored critical values). Also the no-jump reference table (2,000 Gaussian paths, volatility .3, durations
1 / 252) at n in {252, 881, 1737, 3482}.
Inputs: experiment 021's results.json (series names and dates), its Yahoo cache (data/d6), experiment 033's
results.json (names, windows, critical values, declared shares) and the hourly archive bars; experiment 041's
results.json for comparison only.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp041/reproduce.py D6_DIR BARS_DIR
Seed:   SeedSequence(4141) for the reference table. 2 workers. Not a CI check (not check.py)."""
import numpy as np, math, json, sys, os, datetime, csv
import datetime as dt
from zoneinfo import ZoneInfo
from multiprocessing import Pool
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
def load(D, sym):
    j = json.load(open(os.path.join(D, f'yahoo_{sym}.json')))['chart']['result'][0]; off = j['meta'].get('gmtoffset', 0)
    d = np.array([(dt.datetime.utcfromtimestamp(t + off)).date().isoformat() for t in j['timestamp']])
    c = np.array(j['indicators']['quote'][0]['close'], dtype=float); a = np.array(j['indicators']['adjclose'][0]['adjclose'], dtype=float)
    ok = np.isfinite(c) & np.isfinite(a); return d[ok], c[ok], a[ok]
def score(P):
    P = P / P[0]; N = len(P) - 1; Dt = np.full(N, 1 / 252); K = N // 2
    L = np.array([logK(p, k, Dt, P[:-1], P[1:]) for p, k in CAT])
    tr = L[:, :K].sum(1); ev = L[:, K:].sum(1); sel = int(np.argmax(tr)); lG = ev[sel]; lG0 = ev[NULL].max()
    Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1]); n_e = len(R); tau = n_e / 252; a = R.sum() / tau; Q = ((R - a / 252) ** 2 * 252).sum()
    lDG = -(n_e / 2) * (math.log(2 * math.pi * Q / n_e) + 1) - 0.5 * n_e * math.log(1 / 252) - np.log(Pe[1:]).sum() if Q > 0 else np.inf
    return float(lG - max(lG0, lDG)), float(lG - lG0), sel

def jump_stats(r, tau_cal):
    RV = np.sum(r * r); BV = math.pi / 2 * np.sum(np.abs(r[1:]) * np.abs(r[:-1])); top5 = np.sort(r * r)[-5:].sum() / RV
    h = len(r) // 2; v1 = np.sum(r[:h] ** 2) / tau_cal[:h].sum(); v2 = np.sum(r[h:] ** 2) / tau_cal[h:].sum()
    return 1 - BV / RV, top5, math.sqrt(v2 / v1)
def jump_filter(r, tau):
    n = len(r); bp = np.r_[np.nan, np.abs(r[1:]) * np.abs(r[:-1])]; valid = np.arange(1, n); out = np.zeros(n, bool)
    for j in range(n):
        left = [i for i in range(j - 22, j - 1) if 1 <= i]; right = [i for i in range(j + 3, j + 24) if i < n]
        need = 42 - len(left) - len(right); extra = []
        if need > 0:
            if len(left) < 21: extra = [i for i in range(j + 24, n)][:need]
            else: extra = [i for i in range(j - 23, 0, -1)][:need]
        W = np.array(left + right + extra); s2 = math.pi / 2 * bp[W].sum() / tau[W].sum()
        out[j] = abs(r[j]) > 4 * math.sqrt(s2 * tau[j])
    return out
def rebuild(P, jumps):
    r = np.diff(np.log(P)); r[jumps] = 0.0; return P[0] * np.exp(np.r_[0.0, np.cumsum(r)])
def daily_job(args):
    D, name, first, last, key, cv = args; d, c, a = load(D, name); m = (d >= first) & (d <= last); P = a[m]; dd = d[m]
    tau = np.array([(dt.date.fromisoformat(y) - dt.date.fromisoformat(x)).days for x, y in zip(dd[:-1], dd[1:])]) / 365.25
    r = np.diff(np.log(P)); js, t5, vr = jump_stats(r, tau); J = jump_filter(r, tau); Pf = rebuild(P, J)
    res = {'key': key, 'jumps': int(J.sum()), 'jump_share': js, 'top5': t5, 'vol_ratio': vr}
    for lab, X in (('raw', P), ('filt', Pf)):
        le, lr, _ = score(X); r0 = 0.01 + 1.8 / math.sqrt(len(X)); s, g = stats(X / X[0], [r0])[r0]
        c5 = cv.get(str(len(X))); res[lab] = {'v1': le > math.log(20), 'E': lr > math.log(20), 'sadf': s > c5['sadf']['5%'] if c5 else None, 'gsadf': g > c5['gsadf']['5%'] if c5 else None}
    return res
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

def hourly_job(args):
    BARS, name, w0, w1, shares, key, cv = args
    P, D, VU, S = build(load_sessions(f'{BARS}/{name.replace("^", "_")}.csv', 'US'), datetime.date.fromisoformat(w0), datetime.date.fromisoformat(w1), 'US', shares)
    r = np.diff(np.log(P)); js, t5, vr = jump_stats(r, D); J = jump_filter(r, VU); Pf = rebuild(P, J)
    res = {'key': key, 'jumps': int(J.sum()), 'jump_share': js, 'top5': t5, 'vol_ratio': vr}
    for lab, X in (('raw', P), ('filt', Pf)):
        Xn = X / X[0]; r0 = 0.01 + 1.8 / math.sqrt(len(Xn)); s, g = stats(Xn, [r0])[r0]; res[lab] = {'sadf': s > cv['sadf']['5%'], 'gsadf': g > cv['gsadf']['5%']}
    return res
def ref_job(args):
    n, seed = args; rng = np.random.default_rng(seed); r = 0.3 * math.sqrt(1 / 252) * rng.standard_normal(n) - 0.045 / 252; tau = np.full(n, 1 / 252)
    js, t5, vr = jump_stats(r, tau); return js, t5, vr, int(jump_filter(r, tau).sum())
if __name__ == '__main__':
    D6, BARS = sys.argv[1:3]; pub = {(r['src'], r['key']): r for r in json.load(open('experiments/041/results.json'))['records']}   # keys repeat across sources (E6)
    r21 = json.load(open('experiments/021/results.json')); cv21 = r21['critical_values']
    cv21n = {k: ({'sadf': v['sadf'], 'gsadf': v['gsadf']} if isinstance(v, dict) else None) for k, v in cv21.items()}
    jobs = []
    for row in r21['rows']:
        for s in row['series']:
            if s['kind'] != 'adj': continue
            key = f"{row['row']}|{row['variant']}|{s['name']}"
            if ('021', key) in pub: jobs.append((D6, s['name'], s['first'], s['last'], ('021', key), cv21n))
    r33 = json.load(open('experiments/033/results.json')); sh = np.array(r33['clock_shares'], float); hj = []
    for r in r33['records']:
        if not r.get('n_increments'): continue
        key = f"{r['group'] if r['group'] in ('positive', 'C', 'W') else r['group']}|{r['name']}|{r['window'][0]}|{r['window'][1]}"
        hj.append((BARS, r['name'], r['window'][0], r['window'][1], sh, ('033', key), r['cv']))
    with Pool(2) as pool:
        D = pool.map(daily_job, jobs, chunksize=2); H = pool.map(hourly_job, hj, chunksize=2)
        refs = {n: np.array(pool.map(ref_job, [(n, s) for s in np.random.SeedSequence([4141, n]).spawn(2000)], chunksize=50)) for n in (252, 881, 1737, 3482)}
    for n, a in refs.items():
        q = lambda c: '/'.join(f'{x:.3f}' for x in np.quantile(a[:, c], [.05, .5, .95]))
        print(f'reference n = {n}: jump share {q(0)} | top-5 {q(1)} | vol ratio {q(2)} | detections ' + '/'.join(f'{x:.0f}' for x in np.quantile(a[:, 3], [.05, .5, .95])))
    def compare(R, label):
        st = {'jump_share': [], 'top5': [], 'vol_ratio': []}; jd = []; agree = {}
        for r in R:
            p = pub.get(r['key'])
            if p is None: continue
            for k in st: st[k].append(abs(r[k] - p[{'top5': 'top5_share'}.get(k, k)]))
            jd.append(r['jumps'] - p['jumps'])
            for c in r['raw']:
                if r['raw'][c] is None or c not in p['flags_raw']: continue
                a_ = agree.setdefault(c, [0, 0, 0, 0]); a_[0] += r['raw'][c] == p['flags_raw'][c]; a_[1] += r['filt'][c] == p['flags_filtered'][c]; a_[2] += 1
        print(f'{label}: {len(R)} records; max |diff| jump share {max(st["jump_share"]):.1e}, top-5 {max(st["top5"]):.1e}, vol ratio {max(st["vol_ratio"]):.1e}; '
              f'jump-count difference (mine - theirs): mean {np.mean(jd):+.2f}, exact on {np.mean(np.array(jd) == 0) * 100:.0f}%; flag agreement raw / filtered: '
              + ', '.join(f'{c} {v[0]}/{v[2]} / {v[1]}/{v[2]}' for c, v in agree.items()))
    compare(D, '021 daily'); compare(H, '033 hourly')
    def rates(R, grp_of, cols):
        out = {}
        for r in R:
            g = grp_of(r)
            for c in cols:
                if r['raw'].get(c) is None: continue
                z = out.setdefault((g, c), [0, 0, 0]); z[0] += r['raw'][c]; z[1] += r['filt'][c]; z[2] += 1
        for (g, c), z in sorted(out.items()): print(f'   {g} {c}: raw {z[0] / z[2] * 100:.1f}% -> filtered {z[1] / z[2] * 100:.1f}% (n = {z[2]})')
    print('021 full-window rates:'); rates([r for r in D if '|full|' in r['key'][1]], lambda r: pub[r['key']]['group'], ('gsadf', 'sadf', 'E', 'v1'))
    print('033 rates:'); rates([r for r in H if r['key'] in pub], lambda r: pub[r['key']]['group'], ('gsadf', 'sadf'))
    surv = {}
    for r in D + H:
        p = pub.get(r['key'])
        if p is None or p['group'] == 'control': continue                      # Sections 6.2-6.3 flags: positives and the C / W groups
        for c, f in r['raw'].items():
            if f: z = surv.setdefault((p['src'], p['variant'], c), [0, 0]); z[0] += 1; z[1] += bool(r['filt'][c])
    print('flags / survive on non-control records (mine): ' + '; '.join(f'{k[0]} {k[1]} {k[2]} {v[0]}/{v[1]}' for k, v in sorted(surv.items())))
