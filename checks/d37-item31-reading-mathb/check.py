"""Independent recount of 056 summaries and optional external launch archive.

No experiment implementation is imported. No score, fit, DK error or bootstrap
is rerun. --data-root points to the existing analyst cache, never downloads data.
"""
import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import gzip
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
R = json.loads((ROOT/'experiments/056/results.json').read_text())
C = json.loads((ROOT/'experiments/056/cutoffs.json').read_text())
E = R['episodes']
SCORES = ('batch', 'monitor', 'gsadf')
COMPLETE = ('ok', 'unsupported_suffix', 'fit_failure')


def near(a, b):
    assert math.isclose(a, b, rel_tol=1e-8, abs_tol=1e-10), (a, b)


def flags(row):
    return {s: row.get(s, -1 if s != 'gsadf' else -1e300)>C[row['launch']][s] for s in SCORES}


out = {'scope': 'saved-output recount, not experiment reproduction'}
assert len(C) == R['calibration']['months'] == 380
assert sum(c['n'] == 499 for c in C.values()) == R['calibration']['months_with_full_499']
assert sum(math.isinf(c['batch']) for c in C.values()) == 12
out['episode_counts'] = {}
for group in ('021', '031', '033-B'):
    rows = [e for e in E if e['set'] == group and (group != '021' or e['sign'] == 'positive')]
    support = [e for e in rows if e['launches_scored']]
    block = {'requested': len(rows), 'supported': len(support)}
    for s in ('monitor', 'gsadf'):
        block[s] = dict(Counter('none' if e[f'{s}_sessions_from_peak'] is None else
                               'before' if e[f'{s}_sessions_from_peak'] < 0 else
                               'on' if e[f'{s}_sessions_from_peak'] == 0 else 'after' for e in support))
    out['episode_counts'][group] = block
neg = [e for e in E if e['set'] == '021' and e['sign'] != 'positive']
out['negative_records'] = {'requested': len(neg), 'supported': sum(e['launches_scored']>0 for e in neg)}
for s in SCORES:
    k, n = sum(e['flags'][s] for e in neg), sum(e['launches_scored'] for e in neg)
    near(k/n, R['consensus_negatives'][s])
    out['negative_records'][s] = {'launch_flags': k, 'launches': n,
                                 'records_flagged': sum(e['flags'][s]>0 for e in neg)}

# Calendar dates, not offsets from potentially different peaks, determine which
# monitor alarm is earlier. Neither establishes an equal-information comparison.
previous = json.loads((ROOT/'experiments/054/results.json').read_text())['positives']
comparison = Counter()
mismatched_peaks = []
for p in previous:
    matches = [e for e in E if e['name'] == p['sym'] and
               (e['set'] == '033-B' and p['group'] == '033-B' or e['row'] == p['group'])]
    assert len(matches) == 1
    e = matches[0]
    a, b = e['monitor_first_alarm'], p['monitor']['first_alarm']
    label = 'neither' if a is None and b is None else 'daily_only' if b is None else 'intraday_only' if a is None else 'daily_earlier' if a < b else 'intraday_earlier' if b < a else 'same_date'
    comparison[label] += 1
    if e['peak'] != p['peak']:
        mismatched_peaks.append({'name':p['sym'], 'group':p['group'], 'daily_peak':e['peak'],
                                 'intraday_peak':p['peak'], 'daily_alarm':a, 'intraday_alarm':b})
out['054_calendar_date_comparison'] = dict(comparison)
out['054_different_peaks'] = mismatched_peaks
out['oos_increments_percentage_points'] = {
    oc: 100*(R['forward']['regressions'][oc+'|batch+monitor+gsadf']['oos_r2']-
             R['forward']['regressions'][oc+'|gsadf']['oos_r2']) for oc in ('mdd63','mdd126')}

parser = argparse.ArgumentParser()
parser.add_argument('--data-root', type=Path)
args = parser.parse_args()
if args.data_root:
    import numpy as np
    archive = args.data_root/'d37/exp056/launches.json.gz'
    with gzip.open(archive, 'rt') as f:
        A = json.load(f)
    L = A['launches']
    out['archive_sha256'] = hashlib.sha256(archive.read_bytes()).hexdigest()
    for tag, expected in R['launch_counts'].items():
        assert sum(x['tag'].startswith(tag) for x in L) == expected
    spy = json.loads((args.data_root/'d37/yahoo_SPY.json').read_text())['chart']['result'][0]
    dates = sorted(datetime.fromtimestamp(t, timezone.utc).date().isoformat()
                   for t,p in zip(spy['timestamp'], spy['indicators']['adjclose'][0]['adjclose']) if p is not None and p>0)
    index = {d:i for i,d in enumerate(dates)}
    U = [u for u in L if u['tag'] == 'universe']
    assert dict(Counter(u['status'] for u in U)) == R['universe_status']
    T = [u for u in U if u['status'] in COMPLETE]
    eligible = sorted((u for u in T if u.get('calm')), key=lambda u:
                      (hashlib.sha256(f"d37ref|{u['key']}|{u['launch']}".encode()).hexdigest(), u['key'], u['launch']))
    for month, expected in C.items():
        refs, used = [], set()
        for u in eligible:
            quarter = (u['key'], u['launch'][:4], (int(u['launch'][5:7])-1)//3)
            if u['suffix_end'] < month and quarter not in used:
                refs.append(u); used.add(quarter)
            if len(refs) == 499: break
        n = len(refs)
        assert n == expected['n']
        rank = (19*(n+1)+19)//20
        for s in SCORES:
            ordered = sorted(u.get(s, -1 if s != 'gsadf' else -1e300) for u in refs)
            q = ordered[rank-1] if rank <= n else math.inf
            if s != 'gsadf': q = max(0., q)
            near(q, expected[s])
    out['archive_cutoff_months_checked'] = len(C)

    def check_rates(rows, expected):
        assert len(rows) == expected['n']
        result = {s:sum(flags(u)[s] for u in rows) for s in SCORES}
        if rows:
            for s in SCORES: near(result[s]/len(rows), expected[s])
        return {'n':len(rows), **result}

    out['archive_universe_counts'] = check_rates(T, R['universe']['all'])
    for key, rows in (('all',T), ('calm',[u for u in T if u.get('calm')]),
                      ('other',[u for u in T if u.get('calm') is False])):
        check_rates(rows, R['universe'][key])
        check_rates([u for u in rows if math.isfinite(C[u['launch']]['batch'])], R['universe_calibrated_months'][key])
    for period, expected in R['universe']['periods'].items():
        lo = int(period[:4]); hi = lo//100*100+int(period[-2:])
        rows = [u for u in T if lo <= int(u['launch'][:4]) <= hi]
        check_rates(rows,expected['all'])

    # Local, analyst-written object archive; never load untrusted pickles.
    pref = np.load(args.data_root/'d37/exp056/episode_prefixes.npz', allow_pickle=True)
    by_tag = defaultdict(list)
    for u in L:
        if u['tag'].startswith('episode'): by_tag[u['tag']].append(u)
    early = Counter()
    for i, e in enumerate(E):
        rows = [u for u in by_tag[f'episode{i}'] if u['status'] in COMPLETE]
        assert len(rows) == e['launches_scored']
        for s in SCORES:
            assert sum(flags(u)[s] for u in rows) == e['flags'][s]
        for s in ('monitor','gsadf'):
            hits = []
            for u in rows:
                key = f"episode{i}|{u['key']}|{u['k']}"
                if key not in pref.files: continue
                seq = pref[key].item()[s]
                loc = np.flatnonzero(seq>C[u['launch']][s])
                if len(loc):
                    hits.append(u['k']+int(loc[0]))
                    if loc[0] == 0: early[s] += 1
            first = min(hits) if hits else None
            assert (dates[first] if first is not None else None) == e[f'{s}_first_alarm']
            if first is not None and e['peak'] in index:
                assert first-index[e['peak']] == e[f'{s}_sessions_from_peak']
    out['episode_launch_first_checkpoint_flags'] = dict(early)

    # Recompute point estimates from archived forward outcomes. Preserve the
    # implemented ordinal tie convention, and disclose it instead of changing it.
    F = [u for u in T if 'mdd126' in u and 'mdd63' in u]
    assert len(F) == R['forward']['n']
    groups = defaultdict(list)
    for i,u in enumerate(F): groups[u['launch']].append(i)
    X = np.ones((len(F),4))
    for j,s in enumerate(SCORES,1):
        for ids in groups.values():
            order = sorted(ids, key=lambda i:(F[i][s],i))
            for rank,i in enumerate(order): X[i,j] = (rank+.5)/len(ids)
    train = np.array([dates[u['k']+251+126]<'2011-01-01' for u in F])
    test = np.array([dates[u['k']-253]>='2011-01-01' for u in F])
    count = 0
    for outcome in ('mdd63','mdd126','ret63','ret126'):
        y = np.array([u[outcome] for u in F])
        for cols in ([1],[2],[3],[1,2,3]):
            matrix = X[:,[0]+cols]
            expected = R['forward']['regressions'][outcome+'|'+'+'.join(SCORES[i-1] for i in cols)]
            b = np.linalg.solve(matrix.T@matrix, matrix.T@y)
            for a,z in zip(b[1:],expected['coef']): near(a,z)
            bt = np.linalg.solve(matrix[train].T@matrix[train],matrix[train].T@y[train])
            prediction = matrix[test]@bt
            r2 = 1-np.sum((y[test]-prediction)**2)/np.sum((y[test]-y[train].mean())**2)
            near(r2,expected['oos_r2'])
            assert train.sum() == expected['n_train'] and test.sum() == expected['n_test']
            count += 1
    out['regression_point_estimates_checked'] = count
    out['batch_zero_rows_in_forward_sample'] = sum(u['batch'] == 0 for u in F)

print(json.dumps(out, indent=2, sort_keys=True))
print('PASS: independent saved-output reconciliation; no fitting, raw-price outcomes, DK or bootstrap reproduction.')
