"""Reviewer's independent reproduction of experiment 054 (written without reading experiments/054/*.py or
checks/d36-monitor-calibration/monitor.py), in three stages. Own code throughout.
(1) Calendar and manifest from the SIP cache (data/d29): SPY session dates; early closes detected as SPY trade share after
    13:00 ET < 10%; daily close = last present regular-session bar (split-adjusted); reference eligibility (>= 200 of 252
    prior sessions with >= 70 bars; calm predicate on the prior 127 daily closes, stock RMS vol <= .30 and drawdown <= .15,
    SPY <= .20 and <= .10), SHA-256 order of "d36ref|sym|launch", one per symbol per quarter, 499.
(2) From the experiment's per-launch archive (data/d36/exp054: per-checkpoint log Q, log D, status; session-end GSADF
    statistics): path scores (2/pi) arctan(max(0, log Q - log D)), -1 when unsupported; the reference cutoffs (rank 475,
    max(0, q) for the monitor); first strict crossings (1-based checkpoint t = 77 d + j); every alarm share; per-record
    onset / peak (SIP daily closes within the record) and lead times; forward regressions on Yahoo adjusted closes
    (data/d24; 039's outcomes and coverage rule; launch-date percentile ranks with average ties; Driscoll-Kraay, launch-month
    groups, 9 lags; out-of-sample R^2, train outcome interval ending before 2023-01-01, test launches from 2023-01-01).
(3) Spot check of the scoring on 24 launches (8 references, 8 positives, 8 unselected; default_rng(5454)): own prior fit
    (prior 252 sessions, clock with SPY fallback, (mu, h_init, nu) at beta = 0, lambda = 2^(-1/20), L-BFGS-B per nu in
    normalized coordinates), own session-anchor 8-point beta mixture log Q at every checkpoint, own beta <= 0 profile log D
    (doubling grid to -2^30 then bounded refinement) at 26 checkpoints, and own monitoring-form GSADF, against the archive.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp054/reproduce.py D29_DIR D24_DIR ARCHIVE_DIR
        (Deviation 3 / 4 figures: ... reproduce.py --dev34 ARCHIVE_DIR)
Seed:   default_rng(5454) for the spot-check sample. 2 workers. Not a CI check (not check.py)."""
import numpy as np, math, json, gzip, sys, datetime, csv, hashlib, glob, os
from zoneinfo import ZoneInfo
from multiprocessing import Pool
from scipy.optimize import minimize, minimize_scalar
from scipy.special import ive, gammaincc, gammaln
from scipy.stats import rankdata
NY = ZoneInfo('America/New_York')
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
def sip_t(D, sym, splits):
    out = {}; trades = {}
    with gzip.open(f'{D}/sip/{sym}.csv.gz', 'rt') as fh:
        for r in csv.DictReader(fh):
            t = datetime.datetime.fromisoformat(r['t'].replace('Z', '+00:00')).astimezone(NY); slot = (t.hour * 60 + t.minute - 570) // 5
            if 0 <= slot < 78 and t.minute % 5 == 0:
                d = t.date().isoformat(); out.setdefault(d, {})[slot] = float(r['c']); trades.setdefault(d, [0, 0]); trades[d][0] += int(r['n']); trades[d][1] += int(r['n']) * (slot >= 42)
    adj = {}
    for d, s in out.items():
        f = 1.0
        for ev in splits.get(sym, []):
            if d < ev['date']: f *= ev['numerator'] / ev['denominator']
        adj[d] = {k: v / f for k, v in s.items()}
    return adj, trades
def feats(P):
    r = np.diff(np.log(P)); return math.sqrt(np.mean(r * r) * 252), float(np.max(1 - P / np.maximum.accumulate(P)))
def yload(sym, D24=None):
    r = json.load(open(f'{D24}/yahoo_{sym}.json'))['chart']['result'][0]; off = r['meta'].get('gmtoffset', 0)
    d = [datetime.datetime.utcfromtimestamp(t + off).date().isoformat() for t in r['timestamp']]; a = r['indicators']['adjclose'][0]['adjclose']
    return {x: y for x, y in zip(d, a) if y is not None and y > 0}
def dk(X, y, t, L):
    XtX = X.T @ X; b = np.linalg.solve(XtX, X.T @ y); u = y - X @ b; h = np.zeros((t.max() + 1, X.shape[1])); np.add.at(h, t, X * u[:, None]); S = h.T @ h
    for l in range(1, L + 1): G = h[l:].T @ h[:-l]; S += (1 - l / (L + 1)) * (G + G.T)
    Ai = np.linalg.inv(XtX); return b, np.sqrt(np.diag(Ai @ S @ Ai))

def stage2(A, D24, D29):
    arc = json.load(gzip.open(f'{A}/launches.json.gz', 'rt'))['launches']; T = json.load(gzip.open('experiments/054/targets.json.gz', 'rt')); man = json.load(open('experiments/054/manifest.json'))
    pub = json.load(open('experiments/054/results.json'))
    def path(rec):
        if not rec.get('archive'): return None, None
        z = np.load(f'{A}/{rec["archive"]}'); ok = z['status'] == 0; sc = np.where(ok, 2 / math.pi * np.arctan(np.maximum(0, z['logq'] - z['logd'])), -1.0); return sc, float(sc.max())
    ref = [r for r in arc if r['tag'] == 'ref']; refmax = []
    for r in ref:
        sc, m = path(r); refmax.append(-1.0 if m is None else m)
    rs = sorted(refmax); qc = rs[474]; cut = max(0.0, qc); gref = sorted(max(r['gsadf']) if r.get('gsadf') else -1e300 for r in ref); gcut = gref[474]
    print(f'(A) references {len(ref)}; monitor cutoff max(0, q) = {cut:.6f} (published {pub["calibration"]["monitor_cutoff"]:.6f}); exceed {sum(m > cut for m in refmax)} (24); '
          f'quantiles 50/90/95/99% ' + '/'.join(f'{x:.4f}' for x in np.quantile(refmax, [.5, .9, .95, .99])) + f'; GSADF cutoff {gcut:.6f} (published {pub["calibration"]["gsadf_cutoff"]:.6f})')
    amap = {(r['tag'], r['sym'], r['launch']): r for r in arc}
    dmax = 0; dal = 0; galm = 0; n = 0
    for t in T:
        r = amap.get((t['kind'] if t['kind'] != 'control' else 'control', t['sym'], t['launch'])) or amap.get(('ctrl', t['sym'], t['launch']))
        if r is None: continue
        sc, m = path(r); n += 1
        if m is not None:
            dmax = max(dmax, abs(m - t['monitor'])); first = next((i + 1 for i, v in enumerate(sc) if v > cut), None); dal += first != t['monitor_alarm']   # 1-based checkpoint t = 77 d + j
        g = r.get('gsadf'); fg = next((i for i, v in enumerate(g) if v > gcut), None) if g else None; galm += fg != t['gsadf_alarm_session']
    print(f'(A) {n} target launches matched to archive: path-score max |diff| {dmax:.1e}; monitor first-alarm checkpoint (1-based) disagreements {dal}; GSADF alarm-session disagreements {galm}')
    # SIP daily closes for onset / peak, reviewer's split handling
    splits = json.load(open(f'{D29}/splits.json')); from zoneinfo import ZoneInfo; NY = ZoneInfo('America/New_York')
    def sipclose(sym):
        out = {}
        with gzip.open(f'{D29}/sip/{sym}.csv.gz', 'rt') as fh:
            for row in csv.DictReader(fh):
                tt = datetime.datetime.fromisoformat(row['t'].replace('Z', '+00:00')).astimezone(NY); slot = (tt.hour * 60 + tt.minute - 570) // 5
                if 0 <= slot < 78: d = tt.date().isoformat(); out.setdefault(d, {})[slot] = float(row['c'])
        res = {}
        for d, s in out.items():
            f = 1.0
            for ev in splits.get(sym, []):
                if d < ev['date']: f *= ev['numerator'] / ev['denominator']
            res[d] = s[max(s)] / f
        return res
    spy = sipclose('SPY'); cal = sorted(spy); idx = {d: i for i, d in enumerate(cal)}
    recs = {}
    for t in T:
        if t['kind'] == 'positive': recs.setdefault((t['sym'], t['group'], tuple(t['record'])), []).append(t)
    before = after = never = 0; leads_m = []; leads_g = []; gb = ga = gn = 0
    for (sym, grp, (a, b)), ls in recs.items():
        try: c = sipclose(sym)
        except FileNotFoundError: c = {}
        ds = [d for d in cal if a <= d <= b and d in c]
        if not ds: never += 1; gn += 1; continue
        v = np.array([c[d] for d in ds]); pk = int(np.argmax(v)); on = int(np.argmin(v[:pk + 1])); pki = idx[ds[pk]]
        am = [t['k'] + (t['monitor_alarm'] - 1) // 77 for t in ls if t['monitor_alarm'] is not None]; ag = [t['k'] + t['gsadf_alarm_session'] for t in ls if t['gsadf_alarm_session'] is not None]
        P = next(p for p in pub['positives'] if p['sym'] == sym and p['group'] == grp and tuple(p['record']) == (a, b))
        if (ds[pk], ds[on]) != (P['peak'], P['onset']) or (ag and cal[min(ag)] != P['gsadf']['first_alarm']) or (am and cal[min(am)] != P['monitor']['first_alarm']):
            print(f'    record {sym} {grp}: peak/onset mine {ds[pk]}/{ds[on]} published {P["peak"]}/{P["onset"]}; first alarm monitor {cal[min(am)] if am else None} vs {P["monitor"]["first_alarm"]}, GSADF {cal[min(ag)] if ag else None} vs {P["gsadf"]["first_alarm"]}')
        if am:
            f = min(am)
            if f < pki: before += 1; leads_m.append(pki - f)
            else: after += 1
        else: never += 1
        if ag:
            f = min(ag)
            if f < pki: gb += 1; leads_g.append(pki - f)
            else: ga += 1
        else: gn += 1
    print(f'(A) positive records {len(recs)}: monitor before peak {before}, only after {after}, never {never}; median lead {np.median(leads_m):.0f} | GSADF before {gb}, after {ga}, never {gn}; median lead {np.median(leads_g):.0f}')
    for kind, grp in (('positive', None), ('positive', 'E5'), ('positive', '033-B'), ('positive', 'E9'), ('control', None), ('unselected', None)):
        ls = [t for t in T if t['kind'] == kind and (grp is None or t['group'] == grp)]
        print(f'(A) {kind} {grp or "all"} ({len(ls)}): monitor alarm share {np.mean([t["monitor_alarm"] is not None for t in ls]) * 100:.1f}%, GSADF {np.mean([t["gsadf_alarm_session"] is not None for t in ls]) * 100:.1f}%, fit failures {sum(not t["fit_ok"] for t in ls)}')
    ctl = [t for t in T if t['kind'] == 'control']; sd = [t for t in ctl if t['sym'] in ('SPY', 'DIA')]; mem = [t for t in ctl if t['sym'] not in ('SPY', 'DIA')]
    print(f'(A) controls SPY/DIA {len(sd)}: {np.mean([t["monitor_alarm"] is not None for t in sd]) * 100:.1f}%; members {len(mem)}: {np.mean([t["monitor_alarm"] is not None for t in mem]) * 100:.1f}%')
    U = [t for t in T if t['kind'] == 'unselected']; ux = [t for t in U if not t.get('overlap_052')]
    print(f'(A) unexposed (no overlap launches) {len(ux)}: monitor {np.mean([t["monitor_alarm"] is not None for t in ux]) * 100:.1f}%, GSADF {np.mean([t["gsadf_alarm_session"] is not None for t in ux]) * 100:.1f}%')
    yrs = sorted({t['launch'][:4] for t in U}); print('(A) unselected by year (monitor / GSADF): ' + ', '.join(f'{y} {np.mean([t["monitor_alarm"] is not None for t in U if t["launch"][:4] == y]) * 100:.1f}/{np.mean([t["gsadf_alarm_session"] is not None for t in U if t["launch"][:4] == y]) * 100:.1f}' for y in yrs))
    # forward regressions, 039's outcomes on Yahoo adjusted closes, ^GSPC calendar
    g = yload('^GSPC', D24); gcal = sorted(g); gidx = {d: i for i, d in enumerate(gcal)}; rows = []; cache = {}
    for t in U:
        if t['sym'] not in cache:
            try: cache[t['sym']] = yload(t['sym'], D24)
            except FileNotFoundError: cache[t['sym']] = None
        px = cache[t['sym']]; last = cal[t['k'] + 20]
        if px is None or last not in px or last not in gidx: continue
        fd = gcal[gidx[last] + 1:gidx[last] + 127]
        if len(fd) < 126 or sum(d in px for d in fd) < 0.99 * 126: continue
        F = np.array([px[d] for d in sorted(px) if d > last][:126]); P0 = px[last]; out = []   # the name's own next 126 closes (039's rule)
        for h in (63, 126):
            pth = np.r_[P0, F[:h]]; out += [float(np.max(1 - pth / np.maximum.accumulate(pth))), math.log(F[h - 1] / P0)]
        rows.append((t, out, fd[-1]))
    print(f'(A) forward rows {len(rows)} (published {pub["forward"]["n"]})')
    L_ = np.array([r[0]['launch'] for r in rows]); ud, tid = np.unique(L_, return_inverse=True); mon = np.array([int(x[:4]) * 12 + int(x[5:7]) for x in L_]); mon -= mon.min()
    def rk(x):
        out = np.empty(len(x))
        for i in range(len(ud)):
            j = np.nonzero(tid == i)[0]; out[j] = (rankdata(x[j], method='average') - 1) / max(len(j) - 1, 1)
        return out
    xm = np.array([r[0]['monitor'] for r in rows]); print(f'(A) monitor path scores tied with another at the same launch date: {np.mean([np.sum(xm[tid == tid[i]] == xm[i]) > 1 for i in range(len(xm))]) * 100:.1f}%; at <= 0: {np.mean(xm <= 0) * 100:.1f}%')
    Rm = rk(np.array([r[0]['monitor'] for r in rows])); Rg = rk(np.array([r[0]['gsadf'] for r in rows])); train = np.array([r[2] < '2023-01-01' for r in rows]); test = L_ >= '2023-01-01'
    def rk_ord(x):
        out = np.empty(len(x))
        for i in range(len(ud)):
            j = np.nonzero(tid == i)[0]; out[j] = (rankdata(x[j], method='ordinal') - 1) / max(len(j) - 1, 1)
        return out
    Ro = rk_ord(xm)
    for j, name in ((0, 'mdd63'), (2, 'mdd126')):
        y = np.array([r[1][j] for r in rows]); b, se = dk(np.c_[np.ones(len(y)), Ro], y, mon, 9); print(f'(A) {name} monitor with ordinal ranks: {b[1]:+.4f} ({b[1] / se[1]:.2f})')
    for j, name in enumerate(('mdd63', 'ret63', 'mdd126', 'ret126')):
        y = np.array([r[1][j] for r in rows]); line = []
        for lab, X in (('monitor', np.c_[np.ones(len(y)), Rm]), ('gsadf', np.c_[np.ones(len(y)), Rg]), ('both', np.c_[np.ones(len(y)), Rm, Rg])):
            b, se = dk(X, y, mon, 9); bt = np.linalg.lstsq(X[train], y[train], rcond=None)[0]; r2 = 1 - np.sum((y[test] - X[test] @ bt) ** 2) / np.sum((y[test] - y[train].mean()) ** 2)
            line.append(f'{lab} ' + ','.join(f'{bb:+.3f}({bb / s:.2f})' for bb, s in zip(b[1:], se[1:])) + f' OOS {r2 * 100:+.2f}%')
        print(f'(A) {name}: ' + '; '.join(line))
LAM = 2 ** (-1 / 20); BETAS = np.array([1 / 16, 1 / 8, 1 / 4, 1 / 2, 1, 2, 4, 8])
OPT = dict(ftol=1e-10, gtol=1e-5, maxiter=400, maxfun=20000, maxls=40, eps=1e-6)
def logf(z, nu): return gammaln((nu + 1) / 2) - gammaln(nu / 2) - 0.5 * math.log(math.pi * (nu - 2)) - (nu + 1) / 2 * np.log1p(z * z / (nu - 2))
def sip(D, sym, splits):
    out = {}
    with gzip.open(f'{D}/sip/{sym}.csv.gz', 'rt') as fh:
        for r in csv.DictReader(fh):
            t = datetime.datetime.fromisoformat(r['t'].replace('Z', '+00:00')).astimezone(NY); slot = (t.hour * 60 + t.minute - 570) // 5
            if 0 <= slot < 78 and t.minute % 5 == 0: out.setdefault(t.date().isoformat(), {})[slot] = float(r['c'])
    adj = {}
    for d, s in out.items():
        f = 1.0
        for ev in splits.get(sym, []):
            if d < ev['date']: f *= ev['numerator'] / ev['denominator']
        adj[d] = {k: v / f for k, v in s.items()}
    return adj
def day_returns(b, last):
    j = np.array([k for k in range(1, last + 1) if k in b and (k - 1) in b]); return (np.array([math.log(b[k] / b[k - 1]) for k in j]), j) if len(j) else (np.array([]), j)
def launch(args):
    D, sym, k, cal, early, splits = args; px = sip(D, sym, splits); spy = sip(D, 'SPY', splits); last = {d: (41 if d in early else 77) for d in cal}
    prior = cal[k - 252:k]; good = [d for d in prior if len(px.get(d, {})) >= 70]
    out = {}
    if len(good) < 200: return {'fit_ok': False}
    def clock(src, days):
        acc = np.zeros(78); cnt = np.zeros(78)
        for d in days:
            r, j = day_returns(src.get(d, {}), last[d]); np.add.at(acc, j, r * r); np.add.at(cnt, j, 1)
        ok = bool(np.all(cnt[1:] >= 150) and np.all(acc[1:] > 0)); s = acc[1:] / np.maximum(cnt[1:], 1); return np.r_[0.0, s / s.mean()], ok
    c, ok = clock(px, good); kind = 'name'
    if not ok: c, ok2 = clock(spy, good); kind = 'spy'
    out['clock'] = kind
    TR = [day_returns(px.get(d, {}), last[d]) for d in prior]; allr = np.concatenate([r for r, j in TR if len(r)]); allc = np.concatenate([c[j] for r, j in TR if len(r)])
    def obj(mu, h, nu):
        tot = 0.0
        for r, j in TR:
            if not len(r): continue
            w = c[j] * h; z = (r - mu) / np.sqrt(w); tot += float(np.sum(logf(z, nu) - 0.5 * np.log(w))); h = LAM * h + (1 - LAM) * float(np.mean((r - mu) ** 2 / c[j]))
            if not (math.isfinite(h) and h > 0): return -math.inf, h
        return tot, h
    mu0 = min(max(allr.mean(), -.01), .01); h0 = min(max(np.mean((allr - mu0) ** 2 / allc), 1e-12), .04); LL = (math.log(1e-12), math.log(.04)); best = None
    for nu in (6, 10):
        f = lambda u: (-v if math.isfinite(v := obj(-.01 + .02 * u[0], math.exp(LL[0] + u[1] * (LL[1] - LL[0])), nu)[0]) else 1e100)
        o = minimize(f, [(mu0 + .01) / .02, (math.log(h0) - LL[0]) / (LL[1] - LL[0])], method='L-BFGS-B', bounds=[(0, 1)] * 2, options=OPT)
        mu, hi = -.01 + .02 * o.x[0], math.exp(LL[0] + o.x[1] * (LL[1] - LL[0])); v, hc = obj(mu, hi, nu)
        if o.success and math.isfinite(v) and (best is None or v > best[0]): best = (v, mu, hi, nu, hc)
    if best is None: return {'fit_ok': False, 'clock': kind}
    v, mu, hi, nu, h = best; out.update(fit_ok=True, objective=v, mu=mu, h_init=hi, nu=nu, h_carried=h)
    # monitoring
    Lk = np.zeros(8); logq = np.full(1617, np.nan); logd_at = {}; Rs, Ws, Xs = [], [], []; supported = True; check = set(range(76, 1617, 77)) | {0, 1, 2, 500, 1000}
    for d in range(21):
        day = cal[k + d]; b = px.get(day, {}); dr = []
        for j in range(1, 78):
            t = 77 * d + j - 1
            if j > last[day] or not supported: continue
            if 0 not in b or j not in b or (j - 1) not in b: supported = False; continue
            R = math.log(b[j] / b[j - 1]); x = math.log(b[j - 1] / b[0]); w = c[j] * h; dr.append((R, c[j]))
            Lk += logf((R - mu) / np.sqrt(w * np.exp(2 * BETAS * x)), nu) - 0.5 * np.log(w * np.exp(2 * BETAS * x)); Rs.append(R); Ws.append(w); Xs.append(x)
            logq[t] = math.log(np.mean(np.exp(Lk - Lk.max()))) + Lk.max()
            if t in check:
                Ra, Wa, Xa = np.array(Rs), np.array(Ws), np.array(Xs)
                def ll(bt):
                    with np.errstate(all='ignore'):
                        lv = np.log(Wa) + 2 * bt * Xa; z = (Ra - mu) * np.exp(-lv / 2); v_ = float(np.sum(logf(z, nu) - 0.5 * lv))
                    return v_ if math.isfinite(v_) else -math.inf
                grid = [0.0] + [-(2.0 ** e) for e in range(-6, 31)]; vals = [ll(g) for g in grid]; i = int(np.argmax(vals))
                lo, hi_ = grid[min(i + 1, len(grid) - 1)], grid[max(i - 1, 0)]
                o = minimize_scalar(lambda bt: -ll(bt), bounds=(lo, hi_), method='bounded', options={'xatol': 1e-10}) if lo < hi_ else None
                logd_at[t] = max(vals[i], -o.fun if o is not None else -math.inf)
        if dr and supported:
            h = LAM * h + (1 - LAM) * float(np.mean([(R - mu) ** 2 / cj for R, cj in dr]))
    out['logq'] = logq; out['logd_at'] = logd_at
    # GSADF in monitoring form
    def dclose(dd):
        bb = px.get(dd, {}); ks = [q for q in bb if q <= last[dd]]; return bb[max(ks)] if ks else None
    g = []
    for d in range(21):
        P = np.array([v for v in (dclose(dd) for dd in cal[k - 252:k + d + 1]) if v is not None]); r0 = 0.01 + 1.8 / math.sqrt(len(P)); g.append(stats(P / P[0], [r0])[r0][1])
    out['gsadf'] = g; return out

def stage3(D29, A, cal, early):
    splits = json.load(open(f'{D29}/splits.json')); arc = json.load(gzip.open(f'{A}/launches.json.gz', 'rt'))['launches']; rng = np.random.default_rng(5454); pick = []
    for tag in ('ref', 'positive', 'unselected'):
        pool_ = [r for r in arc if r['tag'] == tag and r.get('fit')]; pick += [pool_[i] for i in rng.choice(len(pool_), 8, replace=False)]
    with Pool(2) as pool: res = pool.map(launch, [(D29, r['sym'], r['k'], cal, set(early), splits) for r in pick], chunksize=1)
    fit_d = []; q_d = []; d_d = []; g_d = []; nu_ok = 0
    for r, m in zip(pick, res):
        if not m.get('fit_ok'): print(f'    {r["sym"]} {r["launch"]}: my fit failed'); continue
        F = r['fit']; nu_ok += m['nu'] == F['nu']; fit_d.append(max(abs(m['objective'] - F['objective']) / abs(F['objective']), abs(m['mu'] - F['mu']) / 1e-4, abs(math.log(m['h_carried'] / F['h_carried']))))
        z = np.load(f'{A}/{r["archive"]}'); ok = (z['status'] == 0) & np.isfinite(m['logq']); q_d.append(np.max(np.abs(m['logq'][ok] - z['logq'][ok])) if ok.any() else 0)
        d_d += [abs(v - z['logd'][t]) for t, v in m['logd_at'].items() if z['status'][t] == 0]; g_d.append(max(abs(a - b) for a, b in zip(m['gsadf'], r['gsadf'])))
    print(f'(3) {len(pick)} launches: nu agrees {nu_ok}/{len(fit_d)}; fit max(rel objective, |mu| / 1e-4, |log h_carried|) median {np.median(fit_d):.1e}, max {max(fit_d):.1e}; '
          f'log Q max |diff| per launch median {np.median(q_d):.1e}, max {max(q_d):.1e}; log D |diff| at {np.isfinite(d_d).sum()} finite checkpoints median {np.nanmedian(d_d):.1e}, 99% {np.nanquantile(d_d, .99):.1e}, max {np.nanmax(d_d):.1e} ({np.isnan(d_d).sum()} nonfinite in mine); '
          f'GSADF session-end max |diff| median {np.median(g_d):.1e}, max {max(g_d):.1e}')

if __name__ == '__main__' and sys.argv[1] != '--dev34':
    D29, D24, A = sys.argv[1:4]
    D = D29; splits = json.load(open(f'{D}/splits.json')); man = json.load(open('experiments/054/manifest.json'))
    spy, tr = sip_t(D, 'SPY', splits); cal = sorted(spy); idx = {d: i for i, d in enumerate(cal)}
    early = sorted(d for d in cal if tr[d][1] / max(tr[d][0], 1) < .10)
    print(f'calendar {len(cal)} sessions {cal[0]}..{cal[-1]} (manifest {man["calendar"]["sessions"]}); early closes by SPY trade share after 13:00 < 10%: {len(early)}, identical to manifest list: {early == man["calendar"]["early_closes"]}')
    last_slot = {d: (41 if d in set(early) else 77) for d in cal}
    def dclose(px, d):
        b = px.get(d, {}); ks = [k for k in b if k <= last_slot[d]]; return b[max(ks)] if ks else None
    syms = sorted(os.path.basename(p)[:-7] for p in glob.glob(f'{D}/sip/*.csv.gz'))
    launches = [cal[i] for i in range(1, len(cal)) if cal[i][:7] != cal[i - 1][:7] and '2017-01' <= cal[i][:7] <= '2018-12']
    spyc = {d: dclose(spy, d) for d in cal}
    feat_of = {}; cands = []; excl = {'training': 0, 'calm': 0, 'daily_closes': 0}; data = {}
    for s in syms:
        px, _ = sip_t(D, s, splits); data[s] = px
        for L in launches:
            k = idx[L]; prior = cal[k - 252:k] if k >= 252 else cal[:k]
            if len(prior) < 252 or sum(len(px.get(d, {})) >= 70 for d in prior) < 200: excl['training'] += 1; continue
            p127 = cal[k - 127:k]; c = [dclose(px, d) for d in p127]; m = [spyc[d] for d in p127]
            if any(v is None for v in c) or any(v is None for v in m): excl['daily_closes'] += 1; continue
            sv, sd = feats(np.array(c)); mv, md = feats(np.array(m))
            if not (sv <= .30 and sd <= .15 and mv <= .20 and md <= .10): excl['calm'] += 1; continue
            cands.append((s, L, k)); feat_of[(s, L)] = (sv, sd, mv, md)
    print(f'reference candidates {len(cands)} (manifest {man["reference_candidates"]}); exclusions {excl} (manifest {man["reference_exclusions"]})')
    cands.sort(key=lambda c: hashlib.sha256(f'd36ref|{c[0]}|{c[1]}'.encode()).hexdigest()); kept = []; used = set()
    for s, L, k in cands:
        q = (s, L[:4], (int(L[5:7]) - 1) // 3)
        if q in used: continue
        used.add(q); kept.append((s, L, k))
        if len(kept) == 499: break
    mref = [(r['sym'], r['launch'], r['k']) for r in man['reference']]
    diff = next((i for i, (a, b) in enumerate(zip(kept, mref)) if a != b), None)
    if diff is not None:
        a = kept[diff]; inman = a in set(mref); print(f'first order difference at position {diff}: mine {a[:2]} (in manifest: {inman}), features (stock vol, dd, SPY vol, dd) {feat_of[a[:2]]}; manifest {mref[diff][:2]}')
    print(f'reference: {len(kept)} kept; identical to the manifest in order: {sum(a == b for a, b in zip(kept, mref))}/499; latest end {max(cal[k + 20] for _, _, k in kept)}')
    stage2(A, D24, D29)
    stage3(D29, A, cal, early)
# ---- Deviation 3 / 4 figures (run: python checks/review/exp054/reproduce.py --dev34 ARCHIVE_DIR)
def dev34(A):
    T = json.load(gzip.open('experiments/054/targets.json.gz', 'rt')); arc = json.load(gzip.open(f'{A}/launches.json.gz', 'rt'))['launches']; pub = json.load(open('experiments/054/results.json'))
    ctl = {}
    for t in [t for t in T if t['kind'] == 'control']: ctl[(t['sym'], t['launch'])] = t['monitor_alarm'] is not None
    mem = {k: v for k, v in ctl.items() if k[0] not in ('SPY', 'DIA')}; sd = {k: v for k, v in ctl.items() if k[0] in ('SPY', 'DIA')}
    print(f'(D3) distinct control name-launches {len(ctl)}, alarms {sum(ctl.values())} ({sum(ctl.values()) / len(ctl) * 100:.2f}%); members {sum(mem.values())}/{len(mem)}; SPY/DIA {sum(sd.values())}/{len(sd)}')
    for kind in ('positive', 'unselected'):
        al = [t for t in T if t['kind'] == kind and t['gsadf_alarm_session'] is not None]; print(f'(D3) GSADF {kind} alarms at session 0: {sum(t["gsadf_alarm_session"] == 0 for t in al)} of {len(al)}')
    fails = [r for r in arc if r['tag'] != 'ref' and not r.get('fit')]; import collections
    print(f'(D3) failed target launches {len(fails)}; clock reasons: {collections.Counter(r.get("clock_reason") for r in fails).most_common(4)}')
    on_before = sum(1 for p in pub['positives'] if p['monitor']['first_alarm'] and p['monitor']['sessions_from_onset'] is not None and p['monitor']['sessions_from_onset'] >= 0 and p['monitor']['sessions_from_peak'] < 0)
    pre_on = sum(1 for p in pub['positives'] if p['monitor']['first_alarm'] and p['monitor']['sessions_from_onset'] is not None and p['monitor']['sessions_from_onset'] < 0)
    print(f'(D3) monitor first alarms before onset {pre_on}; on/after onset and strictly before peak {on_before}')
    F = pub['forward']['full']; print('(D4) combined OOS gains over GSADF (pp): ' + ', '.join(f'{o} {(F[o + "|monitor+gsadf"]["oos_r2"] - F[o + "|gsadf"]["oos_r2"]) * 100:+.2f}' for o in ('mdd63', 'mdd126')))
if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == '--dev34': dev34(sys.argv[2])
