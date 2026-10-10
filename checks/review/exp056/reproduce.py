"""Reviewer's independent reproduction of experiment 056 (written without reading experiments/056/*.py or
experiments/055/d37stat.py), in two parts.
(A) From the experiment's per-launch archive (data/d37/exp056: launches.json.gz, episode_prefixes.npz), own code: the
    earlier-only per-month calm references (eligible universe launches with a complete prior, the stored calm flag and a
    scored suffix ending strictly before the target month; global SHA-256 order of "d37ref|symbol|launch"; at most one
    per symbol per calendar quarter; 499) and their strict-rank cutoffs (zero floor for batch and monitor, raw for GSADF);
    every universe flag rate overall, calm / other, finite-cutoff months and by period; own forward outcomes (039's rule,
    Yahoo adjusted closes, data/d24) and regressions (launch-date percentile ranks, average ties, and ordinal ties as
    published; Driscoll-Kraay, launch-month groups, 18 lags; out-of-sample R^2, train outcome interval ending before
    2011-01-01, test prior period starting on or after it); episode first alarms from the prefixes and the month
    cutoffs; the 051 common-window Spearman correlation.
(B) Rescoring spot check on 40 random scored universe launches (default_rng(5656)): own window rebuild (SPY calendar from
    data/d37/yahoo_SPY.json, stock adjusted closes from data/d24), own calm predicate, own D37 statistic (prior fit at
    beta = 0, batch half-line contrast, all-real maximizer; the reviewer's experiment-055 implementation) and own
    GSADF path maximum (the running maximum of the backward-SADF series, prior period included, r0 by 021's rule at n = 505), against the archive.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp056/reproduce.py ARCHIVE_DIR D24_DIR D37_DIR
Seed:   default_rng(5656) for the spot-check sample. 2 workers for part B. Not a CI check (not check.py)."""
import numpy as np, math, json, gzip, sys, hashlib, datetime
from multiprocessing import Pool
from scipy.stats import rankdata, spearmanr
from scipy.optimize import minimize, minimize_scalar
from scipy.special import gammaln
OPT = dict(ftol=1e-10, gtol=1e-5, maxiter=400, maxfun=20000, maxls=40, eps=1e-6)
def logf(z, nu): return gammaln((nu + 1) / 2) - gammaln(nu / 2) - 0.5 * math.log(math.pi * (nu - 2)) - (nu + 1) / 2 * np.log1p(z * z / (nu - 2))
def statistic(R, M):
    tr, sr = R[:252], R[252:]; Mref = math.exp(np.mean(np.log(M[:252]))); m = M / Mref; lm_tr, lm_sc = np.log(m[:252]), np.log(m[252:]); best = None
    for nu in (6, 10):
        for g0 in (0., 1., 2.):
            mu0 = min(max(tr.mean(), -.1), .1); w0 = min(max(np.mean((tr - mu0) ** 2 / np.exp(g0 * lm_tr)), 1e-8), .25)
            def obj(u):
                mu, w, g = -.1 + .2 * u[0], math.exp(math.log(1e-8) + u[1] * (math.log(.25) - math.log(1e-8))), 2 * u[2]; lv = math.log(w) + g * lm_tr
                v = float(np.sum(logf((tr - mu) * np.exp(-lv / 2), nu) - lv / 2)); return -v if math.isfinite(v) else 1e100
            u0 = [(mu0 + .1) / .2, (math.log(w0) - math.log(1e-8)) / (math.log(.25) - math.log(1e-8)), g0 / 2]; o = minimize(obj, u0, method='L-BFGS-B', bounds=[(0, 1)] * 3, options=OPT)
            if o.success and o.fun < 1e99 and (best is None or -o.fun > best[0]): best = (-o.fun, -.1 + .2 * o.x[0], math.exp(math.log(1e-8) + o.x[1] * (math.log(.25) - math.log(1e-8))), 2 * o.x[2], nu)
    if best is None: return None
    _, mu, w, g, nu = best; x = np.concatenate([[0.0], np.cumsum(sr)[:-1]]); base = math.log(w) + g * lm_sc
    def ll(b):
        lv = base + b * x; v = float(np.sum(logf((sr - mu) * np.exp(-lv / 2), nu) - lv / 2)); return v if math.isfinite(v) else -math.inf
    def halfmax(sign):
        grid = [0.0] + [sign * 2.0 ** e for e in range(-6, 8)]; vals = [ll(b) for b in grid]; i = int(np.argmax(vals))
        lo, hi = sorted((grid[max(i - 1, 0)], grid[min(i + 1, len(grid) - 1)]))
        o = minimize_scalar(lambda b: -ll(b), bounds=(lo, hi), method='bounded', options={'xatol': 1e-10}) if lo < hi else None
        cands = [(vals[i], grid[i])] + ([(-o.fun, o.x)] if o is not None else []); return max(cands)
    pos, neg = halfmax(1.0), halfmax(-1.0); A = pos[0] - neg[0]; bh = pos[1] if pos[0] >= neg[0] else neg[1]
    return 2 / math.pi * math.atan(max(0.0, A)), bh, g
A, D24, D37 = sys.argv[1], sys.argv[2], sys.argv[3]
def yload(path):
    r = json.load(open(path))['chart']['result'][0]; off = r['meta'].get('gmtoffset', 0)
    d = [datetime.datetime.utcfromtimestamp(t + off).date().isoformat() for t in r['timestamp']]; a = r['indicators']['adjclose'][0]['adjclose']
    return {x: y for x, y in zip(d, a) if y is not None and y > 0}
def dk(X, y, t, L):
    XtX = X.T @ X; b = np.linalg.solve(XtX, X.T @ y); u = y - X @ b; h = np.zeros((t.max() + 1, X.shape[1])); np.add.at(h, t, X * u[:, None]); S = h.T @ h
    for l in range(1, L + 1): G = h[l:].T @ h[:-l]; S += (1 - l / (L + 1)) * (G + G.T)
    Ai = np.linalg.inv(XtX); return b, np.sqrt(np.diag(Ai @ S @ Ai))
def cutoff(vals, floor0):
    n = len(vals)
    if n == 0: return math.inf
    k = math.ceil((n + 1) * .95)
    if k > n: return math.inf
    q = sorted(vals)[k - 1]; return max(0.0, q) if floor0 else q

def bsadf_max(y, r0, e_min):
    T = len(y); dyall = np.diff(y); L0 = int(np.floor(r0 * T)); best = -np.inf
    for a in range(0, T - L0 + 1):
        x = y[a:T - 1] - y[a]; dy = dyall[a:]; n = np.arange(1, len(x) + 1, dtype=float)
        Sx = np.cumsum(x); Sy = np.cumsum(dy); Sxx = np.cumsum(x * x); Sxy = np.cumsum(x * dy); Syy = np.cumsum(dy * dy)
        with np.errstate(divide='ignore', invalid='ignore'):
            cxx = Sxx - Sx * Sx / n; cxy = Sxy - Sx * Sy / n; cyy = Syy - Sy * Sy / n; b = cxy / cxx; ssr = np.maximum(cyy - b * cxy, 0.0); t = b / np.sqrt(ssr / (n - 2) / cxx)
        end = a + n; ok = (n + 1 >= L0) & (end >= e_min)
        if ok.any(): best = max(best, float(np.nanmax(t[ok])))
    return best
def feats(P):
    r = np.diff(np.log(P)); return math.sqrt(np.mean(r * r) * 252), float(np.max(1 - P / np.maximum.accumulate(P)))
def rescore(args):
    Pst, Pspy = (np.asarray(a) for a in args)     # stock closes cal[k-253..k+251]; SPY closes cal[k-274..k+251]
    R = np.diff(np.log(Pst)); rs = np.diff(np.log(Pspy)); M = np.array([np.mean(rs[t:t + 20] ** 2) for t in range(len(rs) - 20)])[-504:]
    out = statistic(R, M); sv, sd = feats(Pst[126:253]); mv, md = feats(Pspy[147:274]); calm = sv <= .30 and sd <= .15 and mv <= .20 and md <= .10
    g = bsadf_max(Pst / Pst[0], 0.01 + 1.8 / math.sqrt(len(Pst)), 0)   # running maximum of the backward-SADF series over all 505 closes
    return out, calm, g
def partB(A, D24, D37):
    X = json.load(gzip.open(f'{A}/launches.json.gz', 'rt'))['launches']; spy = yload(f'{D37}/yahoo_SPY.json'); cal = sorted(spy)
    U = [x for x in X if x['tag'] == 'universe' and x['status'] == 'ok']; rng = np.random.default_rng(5656); pick = [U[i] for i in rng.choice(len(U), 40, replace=False)]
    jobs = []
    for x in pick:
        px = yload(f'{D24}/yahoo_{x["key"]}.json'); k = x['k']; jobs.append(([px[cal[i]] for i in range(k - 253, k + 252)], [spy[cal[i]] for i in range(k - 274, k + 252)]))
    with Pool(2) as pool: res = pool.map(rescore, jobs, chunksize=2)
    db = [abs(r[0][0] - x['batch']) for r, x in zip(res, pick) if r[0]]; dbh = [abs(r[0][1] - x['beta_hat']) for r, x in zip(res, pick) if r[0]]
    bad = [(x['key'], x['launch'], round(r[2], 3), round(x['gsadf'], 3)) for r, x in zip(res, pick) if abs(r[2] - x['gsadf']) > 1e-6]
    print(f'(B) GSADF differences > 1e-6: {bad}')
    print(f'(B) {len(pick)} launches rescored: suffix end check {sum(cal[x["k"] + 251] == x["suffix_end"] for x in pick)}/40; calm flag agrees {sum(r[1] == x["calm"] for r, x in zip(res, pick))}/40; '
          f'batch |diff| median {np.median(db):.1e}, max {max(db):.1e}; beta-hat |diff| median {np.median(dbh):.1e}, max {max(dbh):.1e}; GSADF path max |diff| median {np.median([abs(r[2] - x["gsadf"]) for r, x in zip(res, pick)]):.1e}, max {max(abs(r[2] - x["gsadf"]) for r, x in zip(res, pick)):.1e}')

if __name__ == '__main__':
    Lall = json.load(gzip.open(f'{A}/launches.json.gz', 'rt')); X = Lall['launches']; pubc = json.load(open('experiments/056/cutoffs.json')); pub = json.load(open('experiments/056/results.json'))
    U = [x for x in X if x['tag'] == 'universe']; val = lambda x, s: x.get(s) if x.get(s) is not None and x['status'] != 'incomplete_prior' else (-1e300 if s == 'gsadf' else -1.0)
    elig = [x for x in U if x['status'] != 'incomplete_prior' and x['calm']]
    elig.sort(key=lambda x: (hashlib.sha256(f'd37ref|{x["key"]}|{x["launch"]}'.encode()).hexdigest(), x['key'], x['launch']))
    months = sorted({x['launch'] for x in U}); cuts = {}; agree = {'batch': 0, 'monitor': 0, 'gsadf': 0}; nag = 0
    for m in months:
        refs = []; used = set()
        for x in elig:
            if x['suffix_end'] >= m: continue
            q = (x['key'], x['launch'][:4], (int(x['launch'][5:7]) - 1) // 3)
            if q in used: continue
            used.add(q); refs.append(x)
            if len(refs) == 499: break
        c = {s: cutoff([val(r, s) for r in refs], s != 'gsadf') for s in ('batch', 'monitor', 'gsadf')}; c['n'] = len(refs); cuts[m] = c
        pc = pubc.get(m)
        if pc:
            nag += pc['n'] == len(refs)
            for s in agree: agree[s] += (pc[s] is None or pc[s] == math.inf) and c[s] == math.inf or (pc[s] is not None and pc[s] != math.inf and abs(pc[s] - c[s]) < 1e-12)
    print(f'(A) months {len(months)}; reference count agrees {nag}/{len(pubc)}; cutoffs agree batch {agree["batch"]}, monitor {agree["monitor"]}, GSADF {agree["gsadf"]}; '
          f'months with 499 {sum(c["n"] == 499 for c in cuts.values())}, with none {sum(c["n"] == 0 for c in cuts.values())}, first full {min(m for m, c in cuts.items() if c["n"] == 499)}')
    T = [x for x in U if x['status'] != 'incomplete_prior']
    fl = lambda x, s: val(x, s) > cuts[x['launch']][s]
    def rates(sel): return {s: np.mean([fl(x, s) for x in sel]) for s in ('batch', 'monitor', 'gsadf')}
    for name, sel in (('all', T), ('calm', [x for x in T if x['calm']]), ('other', [x for x in T if not x['calm']])):
        r = rates(sel); fin = [x for x in sel if cuts[x['launch']]['batch'] < math.inf]; rf = rates(fin)
        print(f'(A) universe {name} ({len(sel)}): ' + ' / '.join(f'{r[s] * 100:.2f}%' for s in r) + f'  finite-cutoff months ({len(fin)}): ' + ' / '.join(f'{rf[s] * 100:.2f}%' for s in rf))
    for lo, hi in ((1994, 1999), (2000, 2002), (2003, 2007), (2008, 2009), (2010, 2019), (2020, 2021), (2022, 2026)):
        sel = [x for x in T if lo <= int(x['launch'][:4]) <= hi]; a = rates(sel); c_ = rates([x for x in sel if x['calm']]); o = rates([x for x in sel if not x['calm']])
        print(f'(A) {lo}-{hi}: all ' + '/'.join(f'{a[s] * 100:.1f}' for s in a) + ' | calm ' + '/'.join(f'{c_[s] * 100:.1f}' for s in c_) + ' | other ' + '/'.join(f'{o[s] * 100:.1f}' for s in o))
    # own outcomes (039's rule on Yahoo adjusted closes) and regressions
    spy = yload(f'{D37}/yahoo_SPY.json'); cal = sorted(spy); gs = yload(f'{D24}/yahoo_^GSPC.json'); gcal = sorted(gs); gidx = {d: i for i, d in enumerate(gcal)}
    cache = {}; rows = []; od = []
    for x in T:
        s = x['key']
        if s not in cache:
            try: cache[s] = yload(f'{D24}/yahoo_{s}.json')
            except FileNotFoundError: cache[s] = None
        px = cache[s]; last = x['suffix_end']
        if px is None or last not in px or last not in gidx: continue
        fd = gcal[gidx[last] + 1:gidx[last] + 127]
        if len(fd) < 126 or sum(d in px for d in fd) < .99 * 126: continue
        after = sorted(d for d in px if d > last)[:126]; F = np.array([px[d] for d in after]); P0 = px[last]; out = []
        for h in (63, 126):
            p_ = np.r_[P0, F[:h]]; out += [float(np.max(1 - p_ / np.maximum.accumulate(p_))), math.log(F[h - 1] / P0)]
        rows.append((x, out, fd[-1])); od.append(max(abs(a - x[k]) for a, k in zip(out, ('mdd63', 'ret63', 'mdd126', 'ret126')) if x.get(k) is not None) if x.get('mdd63') is not None else np.nan)
    print(f'(A) forward rows {len(rows)} (published {pub["forward"]["n"]}); own outcomes vs stored: median |diff| {np.nanmedian(od):.1e}, max {np.nanmax(od):.1e}')
    L_ = np.array([r[0]['launch'] for r in rows]); ud, tid = np.unique(L_, return_inverse=True); mon = np.array([int(a[:4]) * 12 + int(a[5:7]) for a in L_]); mon -= mon.min()
    def rk(v, method='average'):
        out = np.empty(len(v))
        for i in range(len(ud)):
            j = np.nonzero(tid == i)[0]; out[j] = (rankdata(v[j], method=method) - 1) / max(len(j) - 1, 1)
        return out
    Rk = {s: rk(np.array([val(r[0], s) for r in rows])) for s in ('batch', 'monitor', 'gsadf')}
    train = np.array([r[2] < '2011-01-01' for r in rows]); test = np.array([cal[r[0]['k'] - 253] >= '2011-01-01' if r[0]['k'] >= 253 else False for r in rows])   # first close of the 252-return prior period
    print(f'(A) train {train.sum()}, test {test.sum()} (published 63,702 / 74,503)')
    tie = {s: np.mean([sum(1 for _ in ()) for _ in ()]) for s in ()}
    for s in ('batch', 'monitor'):
        v = np.array([val(r[0], s) for r in rows]); print(f'(A) {s} scores exactly 0 (or failure): {np.mean(v <= 0) * 100:.1f}%')
    Ro = {s: rk(np.array([val(r[0], s) for r in rows]), 'ordinal') for s in ('batch', 'monitor', 'gsadf')}
    for j, o in ((0, 'mdd63'), (2, 'mdd126')):
        y = np.array([r[1][j] for r in rows]); b, se = dk(np.c_[np.ones(len(y)), Ro['batch']], y, mon, 18); b3, se3 = dk(np.column_stack([np.ones(len(y)), Ro['batch'], Ro['monitor'], Ro['gsadf']]), y, mon, 18)
        print(f'(A) {o} with ordinal ranks: batch {b[1]:+.4f} (t {b[1] / se[1]:.2f}); race t ' + '/'.join(f'{bb / ss:.2f}' for bb, ss in zip(b3[1:], se3[1:])))
    for j, o in enumerate(('mdd63', 'ret63', 'mdd126', 'ret126')):
        y = np.array([r[1][j] for r in rows]); line = []
        for lab, cols in (('batch', ['batch']), ('monitor', ['monitor']), ('gsadf', ['gsadf']), ('race', ['batch', 'monitor', 'gsadf'])):
            Xm = np.c_[np.ones(len(y))] if False else np.column_stack([np.ones(len(y))] + [Rk[c] for c in cols]); b, se = dk(Xm, y, mon, 18); bt = np.linalg.lstsq(Xm[train], y[train], rcond=None)[0]
            r2 = 1 - np.sum((y[test] - Xm[test] @ bt) ** 2) / np.sum((y[test] - y[train].mean()) ** 2); line.append(f'{lab} ' + ','.join(f'{bb:+.4f}(t {bb / s_:.2f})' for bb, s_ in zip(b[1:], se[1:])) + f' OOS {r2 * 100:+.2f}%')
        print(f'(A) {o}: ' + '; '.join(line))
    # episodes: first alarm from prefixes and month cutoffs
    Z = np.load(f'{A}/episode_prefixes.npz', allow_pickle=True); E = Lall['episodes']; byk = {}
    for x in X:
        if x['tag'].startswith('episode'): byk[(x['tag'], x['k'])] = x
    agree = 0; tot = 0; first_idx = {'monitor': [], 'gsadf': []}
    for i, e in enumerate(pub['episodes']):
        if e.get('exclusion'): continue
        meta = E[i]; tag = f'episode{i}'; firsts = {'monitor': None, 'gsadf': None}
        for k in meta['launches']:
            key = f'{tag}|{meta["name"]}|{k}'
            if key not in Z.files: continue
            pref = Z[key].item(); x = byk.get((tag, k)); m = x['launch'] if x else None
            if m is None or m not in cuts: continue
            for s in firsts:
                v = np.asarray(pref[s], float); hit = np.nonzero(v > cuts[m][s])[0]
                if len(hit): first_idx[s].append(int(hit[0])); d_ = cal[k + int(hit[0])]; firsts[s] = d_ if firsts[s] is None or d_ < firsts[s] else firsts[s]
        tot += 1; agree += firsts['monitor'] == e['monitor_first_alarm'] and firsts['gsadf'] == e['gsadf_first_alarm']
    print('(A) alarmed episode launches whose first alarm is on scored day 0 (evidence from the prior period for GSADF): ' + ', '.join(f'{s} {sum(v == 0 for v in first_idx[s])} of {len(first_idx[s])}' for s in first_idx))
    print(f'(A) episode records with first alarms identical to results.json (monitor and GSADF): {agree}/{tot}')
    pos = [e for e in pub['episodes'] if e['set'] == '021' and e['sign'] == 'positive' and not e.get('exclusion')]
    mb = [e['monitor_sessions_from_peak'] for e in pos if e['monitor_sessions_from_peak'] is not None]; gb = [e['gsadf_sessions_from_peak'] for e in pos if e['gsadf_sessions_from_peak'] is not None]
    print(f'(A) 021 positives supported {len(pos)}: monitor alarms {len(mb)}, before peak {sum(v < 0 for v in mb)} (median lead {np.median([-v for v in mb if v < 0]):.0f}); GSADF {len(gb)}, before {sum(v < 0 for v in gb)} (median {np.median([-v for v in gb if v < 0]):.0f})')
    # 051 comparison
    W = [x for x in X if x['tag'] == 'w051']; w51 = json.load(gzip.open('experiments/051/windows.json.gz', 'rt')); s51 = {w['i']: w for w in w51 if w['kind'] == 'sample'}
    m51 = json.load(open('experiments/051/manifest.json'))['sample']; idmap = {(a, c): i for i, (a, b, c) in enumerate(m51)}
    pairs = [(x['batch'], s51[idmap[(x['key'], x['suffix_end'])]]['new']) for x in W if x['status'] == 'ok' and (x['key'], x['suffix_end']) in idmap and x.get('batch') is not None]
    print(f'(A) 051 common windows matched {len(pairs)}; Spearman {spearmanr([p[0] for p in pairs], [p[1] for p in pairs]).correlation:.3f} (published {pub["compare_051"]["spearman_batch_vs_051"]:.3f})')
    partB(A, D24, D37)
