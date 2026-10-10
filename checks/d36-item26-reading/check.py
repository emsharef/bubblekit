"""Independent 052 archive recount and finite profiled-scale identity checks.
No raw-price fitting, bootstrap, simulator, or experiment-code imports.
"""
import csv
import json
import math
from pathlib import Path
from statistics import median
import numpy as np

P=Path(__file__).resolve().parents[2]/'experiments/052'
R=json.loads((P/'results.json').read_text())
rows=R['records']
key=lambda r:(r['kind'],r['group'],r['sym'],r['start'],r['end'])
assert len(rows)==len({key(r) for r in rows})==113
ok=[r for r in rows if r['status']=='ok']
assert len(ok)==112
assert [(r['sym'],r['status']) for r in rows if r['status']!='ok']==[('CRCL','insufficient bars')]
pos=[r for r in ok if r['kind']=='positive']
ctrl=[r for r in ok if r['kind']=='control']
assert len(pos)==28 and len(ctrl)==84
G={g:[r for r in pos if r['group']==g] for g in ('E5','E9','033-B')}
G.update(positives=pos,controls=ctrl)
G['controls SPY/DIA']=[r for r in ctrl if r['sym'] in ('SPY','DIA')]
G['controls members']=[r for r in ctrl if r['sym'] not in ('SPY','DIA')]


def close(a,b):
    assert math.isclose(a,b,rel_tol=1e-10,abs_tol=1e-10),(a,b)


def summary(vals,saved):
    vals=[x for x in vals if x is not None and math.isfinite(x)]
    assert saved['n']==len(vals)
    close(median(vals),saved['median'])
    for q,k in ((.25,'q25'),(.75,'q75')):close(float(np.quantile(vals,q)),saved[k])
    close(sum(x>0 for x in vals)/len(vals),saved['share_pos'])


for name,rr in G.items():
    s=R['groups'][name]
    assert s['records']==len(rr)
    for field,vals in {
        'a1_beta':[r['a1']['beta'] for r in rr],
        'a2_beta':[r['a2']['beta'] for r in rr if r['a2']],
        'b_beta_alt':[r['b']['beta_alt'] for r in rr],
        'b_loglr':[r['b']['loglr'] for r in rr],
        'subcent_share':[r['subcent_share'] for r in rr],
        'zero_return_share':[r['zero_return_share'] for r in rr]}.items():summary(vals,s[field])
    for threshold,label in ((0,'b_gt0'),(1e-6,'b_gt_1e-6'),(math.log(20),'b_gt_log20')):
        assert sum(r['b']['loglr']>threshold for r in rr)==s[label]
    assert sum(r['a1']['beta']/r['a1']['se']>2 for r in rr)==s['a1_t_pos_gt2']
    assert sum(r['a1']['beta']/r['a1']['se'] < -2 for r in rr)==s['a1_t_neg_lt-2']
    assert sum(r['a2']['beta']/r['a2']['se_nw']>2 for r in rr if r['a2'])==s['a2_t_pos_gt2']
    assert sum(r['a1']['bound_hit'] for r in rr)==s['a1_bound_hits']
    assert sum(r['b']['alt_bound_hit'] for r in rr)==s['b_alt_bound_hits']
for r in ok:
    assert r['a1']['success'] and r['b']['success']
    assert -20<=r['a1']['beta']<=20
    assert -20<=r['b']['beta_null']<=0 and -20<=r['b']['beta_alt']<=20
    assert r['b']['loglr']>=0  # archived enforced nesting, not optimizer certificate
    assert all(0<=r[f]<=1 for f in ('subcent_share','zero_return_share'))
segments=[r['runup'] for r in pos if 'a1' in r.get('runup',{})]
s=R['groups']['runup segments'];assert len(segments)==s['records']==19
summary([r['a1']['beta'] for r in segments],s['a1_beta'])
summary([r['b']['beta_alt'] for r in segments],s['b_beta_alt'])
assert sum(r['b']['loglr']>math.log(20) for r in segments)==s['b_gt_log20']
paired=[]
for r,stored in zip(pos,R['paired']['rows']):
    cc=[c for c in ctrl if (c['start'],c['end'])==(r['start'],r['end'])]
    assert len(cc)==7
    assert (r['sym'],r['group'])==(stored['sym'],stored['group'])
    diffs={}
    for out,part,field in [('a1_diff','a1','beta'),('b_diff','b','beta_alt')]:
        diffs[out]=r[part][field]-sum(c[part][field] for c in cc)/len(cc)
        close(diffs[out],stored[out])
    paired.append(diffs)
for f in ('a1_diff','b_diff'):summary([r[f] for r in paired],R['paired'][f])
with (P/'summary.csv').open() as f:csvrows=list(csv.DictReader(f))
assert len(csvrows)==113
lookup={key(r):r for r in rows}
for row in csvrows:
    r=lookup[key(row)];assert r['status']==row['status']
    if r['status']!='ok':continue
    assert r['clock']==row['clock']
    for col,part,field in [('a1_beta','a1','beta'),('a1_se','a1','se'),('a2_beta','a2','beta'),
                           ('a2_se_nw','a2','se_nw'),('b_beta_alt','b','beta_alt'),('b_loglr','b','loglr')]:
        if r[part]:close(float(row[col]),r[part][field])
    for f in ('subcent_share','zero_return_share'):close(float(row[f]),r[f])
    if 'a1' in r.get('runup',{}):close(float(row['runup_a1_beta']),r['runup']['a1']['beta'])
print('PASS: 113 requested records, 112 available, all 8 group summaries, 28 pairs and 113 CSV rows agree.')
for label,rr in [('prior-clock positives',[r for r in pos if r['clock']=='prior year']),
                 ('in-record-clock positives',[r for r in pos if r['clock']=='in-record'])]:
    print(label,len(rr),'positive a1',sum(r['a1']['beta']>0 for r in rr),
          'oracle > log20',sum(r['b']['loglr']>math.log(20) for r in rr))
print('Across-day medians:',{k:R['groups'][k]['a2_beta']['median'] for k in ('E5','E9','033-B','controls')})
print('Positive used sessions:',min(r['used_sessions'] for r in pos),max(r['used_sessions'] for r in pos))
print('Within-day median / 2 (D36 half-slope units):',median(r['a1']['beta'] for r in pos)/2)
# Own finite calculation: arbitrary day scale and day-level centering both
# disappear from the beta comparison when each day has a free profiled scale.
z=[np.array([-.03,.01,.04]),np.array([.02,-.01,.03,.05])]
a=[np.array([.002,.004,.001]),np.array([.001,.003,.008,.002])]
shifts=(.7,-.4);scales=(.3,2.5)
def prof(beta,shift=False,rescale=False):
    ans=0.
    for i,(zz,aa) in enumerate(zip(z,a)):
        xx=zz-shifts[i] if shift else zz
        rr=aa/scales[i] if rescale else aa
        sig=np.mean(rr*np.exp(-beta*xx))
        ans+=.5*(len(xx)*math.log(sig)+beta*sum(xx)+len(xx))
    return ans
for b in (-20,-3,0,2,20):
    close(prof(b,shift=True),prof(b))
    close(prof(b,rescale=True)-prof(0,rescale=True),prof(b)-prof(0))
print('PASS: finite day-centering and free-day-scale invariance checks; no fitted-prefit power guarantee.')
