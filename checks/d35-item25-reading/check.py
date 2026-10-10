"""Independent archive arithmetic for 051; no fitter, simulator or experiment import.

Checks saved score/rank/count/regression arithmetic. Tie sensitivity is a diagnostic
on the same saved outputs, not a replacement registered analysis or new experiment.
Does not replay raw prices, optimization or bootstrap confidence intervals.
"""
from collections import Counter, defaultdict
from fractions import Fraction
import csv
import gzip
import hashlib
import json
import math
from pathlib import Path

import numpy as np
from scipy.stats import rankdata

ROOT = Path(__file__).resolve().parents[2]
P = ROOT / 'experiments/051'
M = json.loads((P / 'manifest.json').read_text())
R = json.loads((P / 'results.json').read_text())
W = json.loads(gzip.decompress((P / 'windows.json.gz').read_bytes()))
SC = ('new', 'v1', 'gsadf')
A = ('1/20', '1/100', '1/10')


def close(x, y):
    assert np.allclose(x, y, rtol=1e-9, atol=2e-11), (x, y)


def cutoff(v, a):
    k = math.ceil((len(v) + 1) * (1 - Fraction(a)))
    return sorted(v)[k - 1] if k <= len(v) else math.inf


def rates(rows, saved):
    assert len(rows) == saved['n']
    for sc in SC:
        for a in A:
            k = sum(x[sc] > Q[sc][a] for x in rows)
            v = saved[f'{sc}|{a}']
            assert k == v['flags']
            if rows:
                close(k / len(rows), v['rate'])
            else:
                assert v['rate'] is None


def fit(y, X, month):
    b = np.linalg.lstsq(X, y, rcond=None)[0]
    u = y - X @ b
    h = np.array([np.sum(X[month == t] * u[month == t, None], axis=0)
                  for t in sorted(set(month))])
    meat = h.T @ h
    for lag in range(1, 28):
        v = h[lag:].T @ h[:-lag]
        meat += (1 - lag / 28) * (v + v.T)
    bread = np.linalg.inv(X.T @ X)
    se = np.sqrt(np.diag(bread @ meat @ bread))
    return b, se


assert hashlib.sha256((P/'manifest.json').read_bytes()).hexdigest() == R['settings']['manifest_sha256']
assert len(W) == len({(w['kind'], w['i']) for w in W}) == 11132
by = {k: sorted([w for w in W if w['kind'] == k], key=lambda w: w['i'])
      for k in ('reference', 'sample', 'consensus')}
for kind in ('reference', 'sample'):
    assert [w['i'] for w in by[kind]] == list(range(len(M[kind])))
assert [w['i'] for w in by['consensus']] == [i for i,c in enumerate(M['consensus']) if 'id' in c]
assert len(by['reference']) == 999 and len(by['sample']) == 10000
refids = {tuple(x) for x in M['reference']}
evalids = {tuple(x) for x in M['sample']} | {tuple(x['id']) for x in M['consensus'] if 'id' in x}
assert len(refids) == 999 and not refids & evalids
intervals = defaultdict(list)
for wid,f in zip(M['reference'], M['reference_features']):
    name,start,end = wid
    assert '1995-01-01' <= end <= '2010-12-31'
    assert f['stock'][0] <= .30 and f['stock'][1] <= .15
    assert f['mkt'][0] <= .20 and f['mkt'][1] <= .10
    assert all(end < a or start > b for a,b in intervals[name])
    intervals[name].append((start,end))
assert len(intervals) == M['reference_names'] == 333
assert all(x['ke'] - x['k0'] == 378 for x in M['sample_meta'])
for w in W:
    assert w['new_status'] == 'finite_numerical_fit'
    close(w['new'], 2/math.pi*math.atan(max(0,w['gap'])))
    assert -10 <= w['null_beta'] <= 0 <= w['alt_beta'] <= 10
    assert w['v1_status'] == w['gsadf_status'] == 'ok'
for k in ('runs', 'runs_accepted', 'runs_not_success', 'penalty_evals'):
    assert sum(w[k] for w in W) == R['fits'][k]
Q = {s:{a:cutoff([w[s] for w in by['reference']], a) for a in A} for s in SC}
for s in SC:
    for a in A:
        close(Q[s][a], R['cutoffs'][s][a])
        assert math.ceil(1000*(1-Fraction(a))) == R['rank_index'][a]
S = by['sample']
for w,wid in zip(S,M['sample']):
    w['sym'],w['start'],w['end'] = wid
G = {'all':S, 'holdout (start >= 2011)':[w for w in S if w['start'] >= '2011-01-01'],
     'retrospective (start < 2011)':[w for w in S if w['start'] < '2011-01-01']}
for name,g in G.items():
    b = R['universe'][name]
    for label,rows in [('all starts',g),('calm starts',[w for w in g if w['calm']]),
                       ('other starts',[w for w in g if not w['calm']])]:
        rates(rows,b[label])
    for p,(a,z) in {'1995-99':(1995,1999),'2003-07':(2003,2007),'2009-19':(2009,2019),'2023-26':(2023,2026)}.items():
        rates([w for w in g if a<=int(w['end'][:4])<=z],b['periods'][p])
for y,v in R['universe_by_end_year'].items():
    rates([w for w in S if w['end'][:4]==y],v)
with (P/'summary.csv').open() as f:
    csvrows=list(csv.DictReader(f))
assert len(csvrows)==81
for row in csvrows:
    v=R['universe'][row['block']][row['subset']]
    assert int(row['n']) == v['n']
    z=v[f"{row['score']}|{row['level']}"]
    assert int(row['flags'])==z['flags']
    close(float(row['rate']),z['rate'])
C = by['consensus']
pos=[w for w in C if M['consensus'][w['i']]['sign']=='positive']
neg=[w for w in C if M['consensus'][w['i']]['sign']!='positive']
assert len(pos)==30 and len(neg)==103
for s in SC:
    auc=sum((p[s]>n[s])+.5*(p[s]==n[s]) for p in pos for n in neg)/(len(pos)*len(neg))
    close(auc,R['consensus']['roc'][s]['auc'])
    for a in A:
        z=R['consensus']['flags'][f'{s}|{a}']
        assert sum(w[s]>Q[s][a] for w in pos)==z['positives']
        assert sum(w[s]>Q[s][a] for w in neg)==z['negatives']
print('Archive: 11132 scores, 9 cutoffs, all groups/years, 81 CSV rows and consensus AUC/counts agree.')
# The first session of 2011 is present in the manifest, so use its calendar index
# for the pre-2011 full-outcome embargo without depending on an external cache.
split={meta['ke'] for wid,meta in zip(M['sample'],M['sample_meta']) if wid[2]=='2011-01-03'}
assert len(split)==1
split=split.pop()
month=np.array([w['end'][:7] for w in S]);ends=np.array([w['end'] for w in S])
test=np.array([w['start']>='2011-01-01' for w in S])
ranks={}
for method in ('ordinal','average'):
    ranks[method]={}
    for s in SC:
        v=np.array([w[s] for w in S]);rk=np.empty(len(S))
        for t in sorted(set(ends)):
            ix=np.flatnonzero(ends==t)
            rk[ix]=(rankdata(v[ix],method=method)-.5)/len(ix)
        ranks[method][s]=rk
for h in (63,126):
    tr=np.array([x['ke']+h<split for x in M['sample_meta']])
    for oc in (f'mdd{h}',f'ret{h}'):
        y=np.array([w[oc] for w in S])
        for method in ('ordinal','average'):
            for spec in [('new',),('v1',),('gsadf',),SC]:
                X=np.column_stack([np.ones(len(S))]+[ranks[method][s] for s in spec])
                b,se=fit(y,X,month)
                bt=np.linalg.lstsq(X[tr],y[tr],rcond=None)[0]
                oos=1-np.sum((y[test]-X[test]@bt)**2)/np.sum((y[test]-y[tr].mean())**2)
                if method=='ordinal':
                    z=R['regressions'][oc+'|'+'+'.join(spec)]
                    close(b[1:],z['coef']);close(se[1:],z['se_dk']);close(oos,z['oos_r2'])
                    assert (int(tr.sum()),int(test.sum()))==(z['n_train'],z['n_test'])
                if spec==('new',):
                    print(f'{method} {oc}: beta={b[1]:.9f}, t_DK={b[1]/se[1]:.6f}, OOS_R2={oos:.9f}')
print('All 16 registered coefficient/DK/OOS point estimates agree; bootstrap intervals not replayed.')
print('Zero scores:',{s:sum(w[s]==0 for w in S) for s in SC})
print('Forward-coverage counts:',dict(Counter(x['fwd_sessions'] for x in M['sample_meta'])))
for i,x in enumerate(M['sample_meta']):
    if x['fwd_sessions']<126: print('Incomplete forward record:',i,M['sample'][i])
