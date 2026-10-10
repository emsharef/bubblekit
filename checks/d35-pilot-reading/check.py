"""Reconcile experiment 050 archives without importing its fitter or simulator.

Optional --optimizer-archive PATH checks the hash-addressed local data artifact.
Without it, only committed per-path records and summaries are checked.
No simulation, optimization, reproduction or global-error certification.
"""
import argparse
from collections import Counter
import csv
from fractions import Fraction
import gzip
import hashlib
import json
import math
from pathlib import Path

DATA = Path(__file__).resolve().parents[2] / 'experiments/050'
SCORES = ('new', 'v1', 'gsadf', 'known')


def key(r):
    return r['law'], r['role'], r['idx']


def q(v, p):
    v = sorted(v)
    x = (len(v)-1)*p
    a, b = math.floor(x), math.ceil(x)
    return v[a]+(x-a)*(v[b]-v[a])


def score(r, name, ref):
    if name != 'known':
        return r[name]
    k = '10|0.9' if ref in ('C2','C4') else '6|0.7' if ref == 'C5' else '6|0.9'
    return r['known'][k]


def cutoff(values, alpha):
    rank = math.ceil((len(values)+1)*(1-alpha))
    return sorted(values)[rank-1] if rank <= len(values) else math.inf


def close(a,b):
    assert math.isclose(a,b,rel_tol=1e-12,abs_tol=2e-10), (a,b)


def wilson(k,n):
    z=1.959963984540054
    den=1+z*z/n
    mid=(k/n+z*z/(2*n))/den
    rad=z*math.sqrt(k/n*(1-k/n)/n+z*z/(4*n*n))/den
    return mid-rad,mid+rad


def binomial_cdf(n,k,p):
    # Direct finite sum in log form: claim 045 (6), no simulation.
    return math.fsum(math.exp(math.lgamma(n+1)-math.lgamma(j+1)-math.lgamma(n-j+1)
                    +j*math.log(p)+(n-j)*math.log1p(-p)) for j in range(k+1))


def optimizer_check(path, records, summary):
    with path.open('rb') as f:
        assert hashlib.file_digest(f,'sha256').hexdigest() == summary['archive_sha256']
    with gzip.open(path,'rt') as f:
        data=json.load(f)
    lookup={key(r):r for r in records}
    assert len(data)==len(lookup) and {key(r) for r in data}==lookup.keys()
    counts=Counter()
    messages=Counter()
    for item in data:
        saved=lookup[key(item)]
        runs=item['runs']
        if 'sim_failure' in saved:
            assert not runs
            continue
        for run in runs:
            counts['total']+=1
            counts['accepted']+=run['accepted']
            counts['not_success']+=not run['success']
            counts['penalty_evals']+=run['penalty_evals']
            counts['with_bound_hit']+=bool(run['bound_hits'])
            messages[run['message']]+=1
            if run['accepted']:
                assert run['success'] and math.isfinite(run['loglik'])
                beta=run['params']['beta']
                assert ((run['sign']=='boundary' and beta==0) or
                        (run['sign']=='null' and -10<=beta<=0) or
                        (run['sign']=='alt' and 0<=beta<=10))
        for sign in ('null','alt'):
            candidates=[r for r in runs if r['accepted'] and r['sign'] in ('boundary',sign)]
            candidates.sort(key=lambda r:(r['nu'],0 if r['kind']=='boundary' else int(r['kind'][-1])))
            best=max(candidates,key=lambda r:r['loglik'])
            for field in ('nu','kind','params','loglik','bound_hits'):
                assert best[field]==saved[sign][field]
    for field,value in counts.items():
        assert value==summary[field],(field,value,summary[field])
    assert dict(messages)==summary['messages']
    print('Optimizer archive hash, all endpoint candidate selections and totals match:',dict(counts))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--optimizer-archive',type=Path)
    args=parser.parse_args()
    with gzip.open(DATA/'records.json.gz','rt') as f:
        records=json.load(f)
    summary=json.loads((DATA/'results.json').read_text())
    assert len(records)==len({key(r) for r in records})==12490
    assert Counter(r['role'] for r in records)=={0:4990,1:7500}
    calibration={ref:[r for r in records if r['role']==0 and r['law']==ref] for ref in summary['cutoffs']}
    expected_csv={}
    for ref,rows in calibration.items():
        assert len(rows)==499 and {r['idx'] for r in rows}==set(range(499))
        for name in SCORES:
            for alpha in ('1/20','1/10'):
                close(cutoff([score(r,name,ref) for r in rows],Fraction(alpha)),summary['cutoffs'][ref][name][alpha])
    failures=Counter()
    for r in records:
        if 'sim_failure' in r:
            failures[(r['law'],r['role'])]+=1
            assert r['new']==-1 and r['new_status']=='simulation_failure'
            assert r['v1']==r['gsadf']==-1e300 and set(r['known'].values())=={-1e300}
        else:
            assert r['new_status']=='finite_numerical_fit'
            delta=r['alt']['loglik']-r['null']['loglik']
            close(delta,r['gap'])
            close(2/math.pi*math.atan(max(0,delta)),r['new'])
            assert -10<=r['null']['params']['beta']<=0<=r['alt']['params']['beta']<=10
    positive=[]
    for cell,s in summary['cells'].items():
        rows=[r for r in records if r['role']==1 and r['law']==cell]
        assert len(rows)==s['evaluations']==500 and {r['idx'] for r in rows}==set(range(500))
        assert s['new_status']==dict(Counter(r['new_status'] for r in rows))
        assert s['simulation_failures']==sum('sim_failure' in r for r in rows)
        for kind,ref in (('matched',s['matched_reference']),('transported',s['transported_reference'])):
            if ref is None:continue
            for name in SCORES:
                for alpha in ('1/20','1/10'):
                    cut=summary['cutoffs'][ref][name][alpha]
                    k=sum(score(r,name,ref)>cut for r in rows)
                    rate=s[kind][name+'|'+alpha]
                    assert k==rate['flags'] and k/500==rate['rate']
                    close(cut,rate['cutoff'])
                    for a,b in zip(wilson(k,500),rate['wilson95']):close(a,b)
                    expected_csv[cell,kind,name,alpha]=rate
        requested=[r for r in rows if r['idx']<50]
        pred=[r for r in requested if 'predictable' in r]
        good=[r for r in pred if r['predictable']['status']=='ok']
        ps=s['predictable_diagnostic']
        assert len(requested)==ps['requested_paths']==50
        assert len(pred)==ps['diagnostic_created']
        assert len(requested)-len(pred)==ps['failed_before_diagnostic']
        assert len(good)==ps['ratio_available']
        assert not ps['diagnostic_failures'] and len(good)==len(pred)
        values=[r['predictable']['signed_log_ratio'] for r in good]
        for a,b in zip((q(values,p) for p in (.05,.5,.95)),ps['signed_log_ratio_quantiles']):close(a,b)
        for r in good:
            p=r['predictable']
            close(p['logQ']-r['null']['loglik'],p['signed_log_ratio'])
            close(r['alt']['loglik']-p['logQ'],p['C_n'])
            close(math.fsum(p['terms'].values()),p['signed_log_ratio'])
            if p['signed_log_ratio']>0:positive.append((cell,r['idx'],p['signed_log_ratio']))
        print(cell,'new/GSADF flags=',s['matched']['new|1/20']['flags'],s['matched']['gsadf|1/20']['flags'],
              'predictable available/max=',len(good),max(values))
        if cell.startswith('A'):
            ref=s['matched_reference']
            nc=summary['cutoffs'][ref]['new']['1/20'];gc=summary['cutoffs'][ref]['gsadf']['1/20']
            discord=Counter((r['new']>nc,r['gsadf']>gc) for r in rows)
            print(' paired new-only/GSADF-only:',discord[True,False],discord[False,True])
    with (DATA/'summary.csv').open(newline='') as f:csv_rows=list(csv.DictReader(f))
    assert len(csv_rows)==len(expected_csv)==192
    assert len({(r['cell'],r['calibration'],r['score'],r['alpha']) for r in csv_rows})==192
    for r in csv_rows:
        result=expected_csv[r['cell'],r['calibration'],r['score'],r['alpha']]
        assert int(r['flags'])==result['flags'] and int(r['evaluations'])==500
        close(float(r['rate']),result['rate'])
        for label,value in zip(('wilson_lo','wilson_hi'),result['wilson95']):close(float(r[label]),value)
    assert sum(failures.values())==134
    assert len(positive)==1 and positive[0][:2]==('A4',19) and positive[0][2]>math.log(20)
    print('Retained simulation failures:',dict(failures))
    print('Only positive endpoint diagnostic:',positive)
    print('Additional forecast optimization slots (not in endpoint archive):',sum(x['runs'] for r in records for x in r.get('predictable',{}).get('refits',[])))
    print('Claim045 binomial bound at conditional risk .07:',binomial_cdf(499,24,.07))
    assert binomial_cdf(499,24,.07)<.05
    if args.optimizer_archive:optimizer_check(args.optimizer_archive,records,summary['optimizations'])
    else:print('Local per-optimization archive not checked; supply --optimizer-archive to verify it.')
    print('PASS: 12490 records, 80 rank cutoffs, 192 rate/CSV rows, failures and 750 requested diagnostics.')


if __name__=='__main__':main()
