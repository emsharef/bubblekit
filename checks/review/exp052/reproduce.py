"""Reviewer's independent reproduction of experiment 052 (written without reading experiments/052/run.py or
experiments/042/run.py), on the experiment's own record list (names, windows, kinds and groups taken from its results.json,
since the positives and controls are experiment 042's reused selections).
Own code from the Design: SIP 5-minute bars (data/d29/sip), raw closes divided by each later split ratio (data/d29/splits.json,
042's Deviation 3); ET regular sessions (78 slots 09:30..15:55), days with >= 70 bars; intraday returns between consecutive
present slots (open and overnight excluded), a multi-slot return carrying the summed clock of its slots; diurnal clock =
per-slot mean squared return over complete prior-12-month sessions (all 78 bars), normalized to mean 1 over slots 1..77, or
the record's own sessions when fewer than 100 (labelled in-record); EWMA state (half-life 20) of past days' deseasonalized
variance, first 20 sessions burn-in; (a1) day-fixed-effect Gaussian quasi-likelihood in beta (bounded search [-20, 20],
curvature SE); (a2) OLS of log q_d on the log open, log q_d of SPY (same days) and log h_d, Newey-West 10 lags; (b) oracle
quasi-likelihood with sigma^2 s_j h_d exp(beta x), beta in [-20, 20] against [-20, 0]; run-up segment (record peak = max daily
close, onset = min daily close before it), (a1) on segments of >= 20 used sessions; sub-cent close shares on raw and on split-adjusted closes, and zero-return shares.

Rerun:  OMP_NUM_THREADS=1 uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp052/reproduce.py D29_DIR
Seed:   none (deterministic). 2 workers. Not a CI check (not check.py)."""
import numpy as np, math, json, gzip, sys, datetime, csv
from zoneinfo import ZoneInfo
from multiprocessing import Pool
from scipy.optimize import minimize_scalar
NY = ZoneInfo('America/New_York'); LAM = 0.5 ** (1 / 20)
def bars(D, sym, splits):
    out = {}
    with gzip.open(f'{D}/sip/{sym}.csv.gz', 'rt') as fh:
        for r in csv.DictReader(fh):
            t = datetime.datetime.fromisoformat(r['t'].replace('Z', '+00:00')).astimezone(NY); slot = (t.hour * 60 + t.minute - 570) // 5
            if 0 <= slot < 78 and (t.minute % 5 == 0): out.setdefault(t.date().isoformat(), {})[slot] = float(r['c'])
    adj = {}
    for d, s in out.items():
        f = 1.0
        for ev in splits.get(sym, []):
            if d < ev['date']: f *= ev['numerator'] / ev['denominator']
        adj[d] = {k: v / f for k, v in s.items()}
    return out, adj
def day_returns(s):
    ks = sorted(s); r, j0, j1 = [], [], []
    for a, b in zip(ks[:-1], ks[1:]): r.append(math.log(s[b] / s[a])); j0.append(a); j1.append(b)
    return np.array(r), np.array(j0), np.array(j1)
def record(args):
    D, sym, start, end, splits, spy_q = args
    raw, adj = bars(D, sym, splits); days = sorted(adj)
    prior0 = (datetime.date.fromisoformat(start) - datetime.timedelta(days=365)).isoformat()
    comp = [d for d in days if prior0 <= d < start and len(adj[d]) == 78]
    rec = [d for d in days if start <= d <= end and len(adj[d]) >= 70]
    if len(rec) <= 40: return {'sym': sym, 'start': start, 'status': 'too few sessions', 'sessions': len(rec)}
    def clock_from(ds):
        acc = np.zeros(78); cnt = np.zeros(78)
        for d in ds:
            r, j0, j1 = day_returns(adj[d]); m = j1 == j0 + 1; np.add.at(acc, j1[m], r[m] ** 2); np.add.at(cnt, j1[m], 1)
        s = acc[1:] / np.maximum(cnt[1:], 1); s = s / s.mean(); return np.r_[0.0, s]
    kind = 'prior year' if len(comp) >= 100 else 'in-record'; s = clock_from(comp if kind == 'prior year' else rec); cs = np.cumsum(s)
    cref = adj[rec[0]][min(adj[rec[0]])]; D_ = []
    for d in rec:
        r, j0, j1 = day_returns(adj[d]); sj = cs[j1] - cs[j0]; c = adj[d]; x0 = math.log(c[min(c)] / cref)
        xprev = np.array([math.log(c[k] / cref) for k in j0]); D_.append((d, r, sj, xprev, x0, float(np.mean(r * r / sj)), c[max(c)]))
    h = np.full(len(D_), np.nan)
    for i in range(1, len(D_)): h[i] = D_[0][5] if i == 1 else LAM * h[i - 1] + (1 - LAM) * D_[i - 1][5]
    U = list(range(20, len(D_)))
    def a1(idx):
        R = [D_[i][1] for i in idx]; S = [D_[i][2] for i in idx]; Z = [D_[i][3] - D_[i][4] for i in idx]; n = sum(len(r) for r in R)
        def ll(b):
            tot = 0.
            for r, sj, z in zip(R, S, Z):
                w = sj * np.exp(b * z); sig = np.mean(r * r / w); tot += -0.5 * (len(r) * math.log(sig) + np.sum(np.log(w)) + len(r))
            return tot
        o = minimize_scalar(lambda b: -ll(b), bounds=(-20, 20), method='bounded', options={'xatol': 1e-8}); b = o.x; e = 1e-3
        curv = (ll(b + e) - 2 * ll(b) + ll(b - e)) / e ** 2; return b, (1 / math.sqrt(-curv) if curv < 0 else float('nan')), n
    def b_or(idx):
        r = np.concatenate([D_[i][1] for i in idx]); w0 = np.concatenate([D_[i][2] * h[i] for i in idx]); x = np.concatenate([D_[i][3] for i in idx])
        def ll(b):
            w = w0 * np.exp(b * x); sig = np.mean(r * r / w); return -0.5 * (len(r) * math.log(sig) + np.sum(np.log(w)) + len(r))
        alt = minimize_scalar(lambda b: -ll(b), bounds=(-20, 20), method='bounded', options={'xatol': 1e-9}); nul = minimize_scalar(lambda b: -ll(b), bounds=(-20, 0), method='bounded', options={'xatol': 1e-9})
        return alt.x, max(-alt.fun, ll(0.0) if False else -alt.fun) - max(-nul.fun, ll(0.0)), -alt.fun - (-nul.fun)
    b1, se1, n1 = a1(U); ba, lr_raw, lr = b_or(U)
    # (a2)
    y = np.log([D_[i][5] for i in U]); X = [np.ones(len(U)), np.array([D_[i][4] for i in U]), np.log(h[U])]
    if spy_q is not None:
        sq = [spy_q.get(D_[i][0]) for i in U]; keep = np.array([q is not None and q > 0 for q in sq]); X.insert(2, np.log([q if q else 1 for q in sq]))
    else: keep = np.ones(len(U), bool)
    X = np.array(X).T[keep]; y = y[keep]; bb = np.linalg.lstsq(X, y, rcond=None)[0]; u = y - X @ bb; XtXi = np.linalg.inv(X.T @ X); S_ = (X * u[:, None]).T @ (X * u[:, None])
    for l in range(1, 11):
        G = (X[l:] * u[l:, None]).T @ (X[:-l] * u[:-l, None]); S_ += (1 - l / 11) * (G + G.T)
    se2 = math.sqrt((XtXi @ S_ @ XtXi)[1, 1])
    # run-up
    closes = np.array([D_[i][6] for i in range(len(D_))]); pk = int(np.argmax(closes)); on = int(np.argmin(closes[:pk + 1])); seg = [i for i in range(on, pk + 1) if i >= 20]
    ru = a1(seg)[0] if len(seg) >= 20 else None
    allc = [v for d in rec for v in raw[d].values()]; sub = np.mean([abs(v * 100 - round(v * 100)) > 1e-6 for v in allc]); alla = [v for d in rec for v in adj[d].values()]; sub_adj = np.mean([abs(v * 100 - round(v * 100)) > 1e-6 for v in alla]); zr = np.mean(np.concatenate([D_[i][1] for i in range(len(D_))]) == 0)
    return {'sym': sym, 'start': start, 'status': 'ok', 'clock': kind, 'prior': len(comp), 'sessions': len(rec), 'used': len(U), 'a1': b1, 'a1_se': se1, 'n': n1,
            'a2': bb[1], 'a2_t': bb[1] / se2, 'b_beta': ba, 'b_lr': lr, 'runup_a1': ru, 'runup_sessions': pk - on, 'sub': sub, 'sub_adj': sub_adj, 'zero': zr,
            'q': {D_[i][0]: D_[i][5] for i in range(len(D_))}}
if __name__ == '__main__':
    D = sys.argv[1]; pub = json.load(open('experiments/052/results.json')); splits = json.load(open(f'{D}/splits.json')); recs = pub['records']
    wins = sorted({(r['start'], r['end']) for r in recs})
    with Pool(2) as pool:
        spy = dict(zip(wins, pool.map(record, [(D, 'SPY', a, b, splits, None) for a, b in wins])))
        jobs = [(D, r['sym'], r['start'], r['end'], splits, None if r['sym'] == 'SPY' else spy[(r['start'], r['end'])].get('q')) for r in recs]
        out = pool.map(record, jobs, chunksize=2)
    cmp = {k: [] for k in ('a1', 'a1_se', 'a2', 'b_beta', 'b_lr', 'runup', 'sub', 'sub_adj', 'zero')}; meta = 0; okn = 0
    for r, m in zip(recs, out):
        if r.get('status') != 'ok' or m['status'] != 'ok':
            print(f'    status: {r["sym"]} {r["start"]}: published {r.get("status")}, mine {m["status"]} ({m.get("sessions")} sessions)'); continue
        okn += 1; meta += (m['clock'] == r['clock'] and m['prior'] == r['prior_sessions'] and m['sessions'] == r['sessions'] and m['used'] == r['used_sessions'])
        cmp['a1'].append(m['a1'] - r['a1']['beta']); cmp['a1_se'].append(m['a1_se'] / r['a1']['se'] - 1 if r['a1']['se'] else 0); cmp['a2'].append(m['a2'] - r['a2']['beta'])
        cmp['b_beta'].append(m['b_beta'] - r['b']['beta_alt']); cmp['b_lr'].append(m['b_lr'] - r['b']['loglr']); cmp['sub'].append(m['sub'] - r['subcent_share']); cmp['sub_adj'].append(m['sub_adj'] - r['subcent_share']); cmp['zero'].append(m['zero'] - r['zero_return_share'])
        if r.get('runup') and r['runup'].get('a1') and m['runup_a1'] is not None: cmp['runup'].append(m['runup_a1'] - r['runup']['a1']['beta'])
    print(f'{okn} records ok in both; clock kind, prior sessions, sessions and used sessions identical on {meta}/{okn}')
    for k, v in cmp.items():
        v = np.abs(np.array(v)); print(f'    |mine - published| {k}: median {np.median(v):.2e}, 90% {np.quantile(v, .9):.2e}, max {v.max():.2e} (n = {len(v)})')
    G = {}
    for r, m in zip(recs, out):
        if m['status'] != 'ok': continue
        g = r['group'] if r['kind'] == 'positive' else ('SPY/DIA' if r['sym'] in ('SPY', 'DIA') else 'calm members'); G.setdefault(g, []).append(m)
        if r['kind'] == 'positive': G.setdefault('all positives', []).append(m)
        else: G.setdefault('controls, all', []).append(m)
    for g, ms in G.items():
        a1 = np.array([m['a1'] for m in ms]); t1 = a1 / np.array([m['a1_se'] for m in ms]); a2 = np.array([m['a2'] for m in ms]); bb = np.array([m['b_beta'] for m in ms]); lr = np.array([m['b_lr'] for m in ms])
        ru = [m['runup_a1'] for m in ms if m['runup_a1'] is not None]
        print(f'{g} ({len(ms)}): a1 median {np.median(a1):+.2f} (> 0 {np.mean(a1 > 0) * 100:.0f}%), t>2 / t<-2 {np.sum(t1 > 2)}/{np.sum(t1 < -2)}, at -20 {np.sum(a1 < -19.999)}; a2 median {np.median(a2):+.2f}, t>2 {np.sum(np.array([m["a2_t"] for m in ms]) > 2)}; '
              f'b beta median {np.median(bb):+.2f} (> 0 {np.mean(bb > 0) * 100:.0f}%), LR > 1e-6 {np.sum(lr > 1e-6)}, > log 20 {np.sum(lr > math.log(20))}' + (f'; run-up a1 median {np.median(ru):+.2f} ({len(ru)}, > 0 {np.mean(np.array(ru) > 0) * 100:.0f}%)' if ru and 'positive' in g or g in ('E5', 'E9', '033-B') else ''))
    pairs = []
    for r, m in zip(recs, out):
        if r['kind'] != 'positive' or m['status'] != 'ok': continue
        cs = [mm['a1'] for rr, mm in zip(recs, out) if rr['kind'] != 'positive' and (rr['start'], rr['end']) == (r['start'], r['end']) and mm['status'] == 'ok']
        pairs.append(m['a1'] - np.mean(cs))
    for r, m in zip(recs, out):
        if r['kind'] == 'positive' and m['status'] == 'ok' and (abs(m['b_lr'] - r['b']['loglr']) > 0.1 or (m['b_lr'] > math.log(20)) != (r['b']['loglr'] > math.log(20))):
            print(f'    oracle differs: {r["sym"]} {r["start"]}: mine {m["b_lr"]:.4f}, published {r["b"]["loglr"]:.4f}')
    pr = [(m['sub'], m['sub_adj']) for r, m in zip(recs, out) if m['status'] == 'ok' and r['kind'] == 'positive']; ct = [(m['sub'], m['sub_adj']) for r, m in zip(recs, out) if m['status'] == 'ok' and r['kind'] != 'positive']
    print(f'sub-cent close share, median raw / split-adjusted: positives {np.median([a for a, b in pr]):.2f} / {np.median([b for a, b in pr]):.2f}, controls {np.median([a for a, b in ct]):.2f} / {np.median([b for a, b in ct]):.2f}')
    print(f'paired a1 (positive minus own-window control mean): > 0 in {np.sum(np.array(pairs) > 0)}/{len(pairs)}, median {np.median(pairs):+.1f}')
