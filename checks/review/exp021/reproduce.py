"""Reviewer's independent reproduction of experiment 021's headline flags (written without reading experiments/021/*.py).
Inputs (design data only): Yahoo JSON files from the analyst's data/d6 cache, verified against experiments/021/
data_manifest.json SHA-256; the row compositions, windows and per-series date ranges from experiments/021/results.json;
the selected negative windows from selection.json (also recomputed here from ^GSPC by the preregistered calm rule).
Scores: claim 055 E^drift (primary) and claim 054 raw, own code: 18-candidate absorbed-CEV catalogue (experiment 022's),
split floor(N/2) increments, S/S0 normalization, time = index/252; flag at log E > log 20. GSADF/SADF statistics with the
reviewer's own experiment-002 implementation (r0 = 0.01 + 1.8/sqrt(N)), flagged against the experiment's published
5% critical values for each length.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp021/reproduce.py DATA_DIR
        (DATA_DIR = a copy of the analyst's data/d6 cache; hashes are checked against the manifest)
Seed:   none (deterministic). Runtime about 30 minutes on 2 workers (lab CPU budget; results do not depend on the worker count). Not a CI check (not check.py)."""
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
    d = np.array([(dt.datetime.fromtimestamp(t + off, dt.timezone.utc)).date().isoformat() for t in j['timestamp']])
    c = np.array(j['indicators']['quote'][0]['close'], dtype=float); a = np.array(j['indicators']['adjclose'][0]['adjclose'], dtype=float)
    ok = np.isfinite(c) & np.isfinite(a); return d[ok], c[ok], a[ok]
def score(P):
    P = P / P[0]; N = len(P) - 1; Dt = np.full(N, 1 / 252); K = N // 2
    L = np.array([logK(p, k, Dt, P[:-1], P[1:]) for p, k in CAT])
    tr = L[:, :K].sum(1); ev = L[:, K:].sum(1); sel = int(np.argmax(tr)); lG = ev[sel]; lG0 = ev[NULL].max()
    Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1]); n_e = len(R); tau = n_e / 252; a = R.sum() / tau; Q = ((R - a / 252) ** 2 * 252).sum()
    lDG = -(n_e / 2) * (math.log(2 * math.pi * Q / n_e) + 1) - 0.5 * n_e * math.log(1 / 252) - np.log(Pe[1:]).sum() if Q > 0 else np.inf
    return float(lG - max(lG0, lDG)), float(lG - lG0), sel
def job(args):
    D, name, kind, first, last, rowkey = args; d, c, a = load(D, name); m = (d >= first) & (d <= last); P = (a if kind == 'adj' else c)[m]
    le, raw, sel = score(P); N = len(P); r0 = 0.01 + 1.8 / math.sqrt(N); s, gsd = stats(P / P[0], [r0])[r0]
    return rowkey, name, kind, N, le, raw, sel, s, gsd

if __name__ == '__main__':
    D = sys.argv[1]; man = json.load(open(os.path.join(EXP, 'data_manifest.json')))
    for k, v in man.items():
        if k.startswith('yahoo_') and 'sha256' in v and os.path.exists(os.path.join(D, k)):
            assert hashlib.sha256(open(os.path.join(D, k), 'rb').read()).hexdigest() == v['sha256'], k
    # (1) recompute the calm-score selection from ^GSPC
    sel = json.load(open(os.path.join(EXP, 'selection.json'))); d, c, a = load(D, '^GSPC')
    US = [('1995-01-03', '2001-12-28'), ('2003-01-02', '2008-12-30'), ('2020-06-01', '2021-06-29'), ('2019-01-02', '2022-06-29')]
    def addm(day, L):                       # trading start day + L calendar months (day of month kept; Deviation 2)
        y, mth = divmod(day.month - 1 + L, 12); import calendar
        return dt.date(day.year + y, mth + 1, min(day.day, calendar.monthrange(day.year + y, mth + 1)[1]))
    agree = 0; total = 0
    for Ls, info in sel['lengths'].items():
        L = int(Ls); cands = []
        for y in range(1990, 2027):
            for q in (1, 4, 7, 10):
                first = dt.date(y, q, 1).isoformat(); idx = np.searchsorted(d, first)
                if idx >= len(d) or idx < 252: continue
                st = d[idx]; endlim = addm(dt.date.fromisoformat(str(st)), L).isoformat(); j = np.searchsorted(d, endlim) - 1
                en = d[j]
                if en > '2026-09-30' or j <= idx: continue
                if any(not (en < s0 or st > e0) for s0, e0 in US): continue
                tr = a[idx - 252:idx]; lr = np.diff(np.log(tr)); sig = lr.std(ddof=1) * math.sqrt(252); dd = float(np.max(1 - tr / np.maximum.accumulate(tr)))
                cands.append([st, en, sig, dd])
        sg = np.array([x[2] for x in cands]); dg = np.array([x[3] for x in cands])
        rk = lambda v: np.array([1 + np.sum(v < x) for x in v])
        scs = rk(sg) + rk(dg); order = sorted(range(len(cands)), key=lambda i: (scs[i], cands[i][0])); kept = []
        for i in order:
            if all(cands[i][1] < cands[k][0] or cands[i][0] > cands[k][1] for k in kept): kept.append(i)
            if len(kept) == 3: break
        mine = [str(cands[i][0]) for i in kept]; theirs = [w['start'] for w in info['windows']]
        total += 1; agree += mine == theirs
        print(f'(1) L={L:3d}: candidates {len(cands)} (theirs {info["n_candidates"]}); selected starts mine {mine} | theirs {theirs}')
    print(f'    selection agrees on {agree}/{total} lengths')
    # (2) scores on every series
    res = json.load(open(os.path.join(EXP, 'results.json'))); jobs = []; ref = {}
    for r in res['rows']:
        key = (r['row'], r['variant'])
        for s in r['series']:
            if 'first' not in s: continue                # e.g. XHB's empty to-peak series
            jobs.append((D, s['name'], s['kind'], s['first'], s['last'], key)); ref[(key, s['name'], s['kind'])] = s
    with Pool(2) as pool: out = pool.map(job, jobs, chunksize=2)
    cv = res['critical_values']; dmax = 0; fl_mis = 0; nmis = 0; gmax = 0; gfl_mis = 0; summ = {}
    for rowkey, name, kind, N, le, raw, sl, s, gsd in out:
        t = ref[(rowkey, name, kind)]; nmis += N != t['n']
        dmax = max(dmax, abs(le - t['log_e']) / max(1, abs(t['log_e'])), abs(raw - t['raw_log_e']) / max(1, abs(t['raw_log_e'])))
        f1, f2 = le > math.log(20), raw > math.log(20); fl_mis += (f1 != t['flags']['lab_0.05']) + (f2 != t['flags']['lab054_0.05'])
        gmax = max(gmax, abs(gsd - t['gsadf']), abs(s - t['sadf']))
        c5 = cv[str(N)] if str(N) in cv else None
        g5 = bool(gsd > c5['gsadf']['5%']) if c5 else None; s5 = bool(s > c5['sadf']['5%']) if c5 else None
        gfl_mis += (g5 != t['flags']['gsadf_5%']) + (s5 != t['flags']['sadf_5%'])
        sign = 'positive' if rowkey[0].startswith('E') else 'negative'
        if kind == 'adj':
            k = (sign, rowkey[1]); summ.setdefault(k, []).append((f1, f2, s5, g5))
    print(f'(2) {len(out)} series: N mismatches {nmis}; max rel |log E diff| (E^drift and 054 raw) {dmax:.2e}; flag mismatches {fl_mis}; '
          f'max |SADF/GSADF stat diff| {gmax:.2e}; SADF/GSADF 5% flag mismatches {gfl_mis}')
    print('    per-name flag rates, adj closes (E^drift 5% / 054 raw 5% / SADF 5% / GSADF 5%):')
    for k in sorted(summ):
        v = summ[k]; print(f'     {k[0]:8s} {k[1]:8s} names {len(v):3d}: {np.mean([x[0] for x in v]):.2f} / {np.mean([x[1] for x in v]):.2f} / {np.mean([x[2] for x in v]):.2f} / {np.mean([x[3] for x in v]):.2f}')
