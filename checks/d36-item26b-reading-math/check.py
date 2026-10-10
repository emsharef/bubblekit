"""Independent 053 saved-archive checks; no estimator imports or simulation rerun."""
import csv
import json
import math
from pathlib import Path
from statistics import median

ROOT = Path(__file__).resolve().parents[2]
R = json.loads((ROOT/'experiments/053/results.json').read_text())
R52 = json.loads((ROOT/'experiments/052/results.json').read_text())
rows = R['real_records']
key = lambda r: tuple(r[k] for k in ('kind','group','sym','start','end'))
assert len(rows) == len({key(r) for r in rows}) == 112
assert {key(r) for r in rows} == {key(r) for r in R52['records'] if r['status']=='ok'}
pos = [r for r in rows if r['kind']=='positive']
ctrl = [r for r in rows if r['kind']=='control']
assert (len(pos),len(ctrl)) == (28,84)
groups = {g:[r for r in pos if r['group']==g] for g in ('E5','E9','033-B')}
groups.update(positives=pos,controls=ctrl)
groups['controls SPY/DIA'] = [r for r in ctrl if r['sym'] in ('SPY','DIA')]
groups['controls members'] = [r for r in ctrl if r['sym'] not in ('SPY','DIA')]
groups['runup segments'] = [r['runup'] for r in pos if 'runup' in r]
assert len(groups['runup segments']) == 19
def close(a,b):
    assert math.isclose(a,b,rel_tol=1e-11,abs_tol=1e-12),(a,b)
def summary(values, saved):
    values=[v for v in values if v is not None and math.isfinite(v)]
    assert saved['n']==len(values)
    close(saved['median'],median(values))
    close(saved['share_pos'],sum(v>0 for v in values)/len(values))
for name,rr in groups.items():
    g=R['real_groups'][name]
    assert g['records']==len(rr)
    summary([(r['a2_nostate'] or {}).get('beta') for r in rr],g['a2_nostate'])
    summary([(r['b_nostate'] or {}).get('beta_alt') for r in rr],g['b_nostate_beta'])
    assert g['b_nostate_gt_log20']==sum(r['b_nostate']['loglr']>math.log(20) for r in rr)
    for scale in ('5m','1h','1d'):
        summary([r['cross'][scale] for r in rr],g['cross'][scale])
    if name!='runup segments':
        assert g['a2_nostate_t_gt2']==sum(r['a2_nostate']['beta']/r['a2_nostate']['se_nw']>2 for r in rr)
        assert g['b_nostate_alt_bound_hits']==sum(r['b_nostate']['alt_bound_hit'] for r in rr)
    for r in rr:
        b=r['b_nostate']
        assert b['success'] and b['loglr']>=0
        assert -20<=b['beta_alt']<=20 and -3<=b['gamma_alt']<=3
        assert all(r['cross'][s] is None or -1<=r['cross'][s]<=1 for s in ('5m','1h','1d'))

sim=R['simulation']
assert set(sim)=={'L2','Z0','ZL','P1','P2','P1U','P2U'}
assert sum(v['paths'] for v in sim.values())==140
assert sum(v['simulation_failures'] for v in sim.values())==3
for name,v in sim.items():
    assert v['paths']==20
    assert v['simulation_failures']==(3 if name=='L2' else 0)
    for stat in [v[k] for k in ('a1','a2','b','a049','b2_049','record_log_range')]+list(v['cross'].values()):
        assert stat['n']==20-v['simulation_failures']
        assert 0<=stat['share_pos']<=1
        close(stat['share_pos']*stat['n'],round(stat['share_pos']*stat['n']))
        if 'q25' in stat: assert stat['q25']<=stat['median']<=stat['q75']
# Per-path simulation rows are NOT archived; these are aggregate consistency checks.
expected={}
for name,v in sim.items():
    for stat in ('a1','a2','b','a049','b2_049'):
        expected[('simulation',name,stat)]=v[stat]
for name,v in R['real_groups'].items():
    for stat in ('a2_nostate','b_nostate_beta'):
        expected[('real',name,stat)]=v[stat]
    for scale in ('5m','1h','1d'):
        expected[('real',name,'cross_'+scale)]=v['cross'][scale]
with (ROOT/'experiments/053/summary.csv').open() as f:
    csvrows=list(csv.DictReader(f))
assert len(csvrows)==len(expected)==75
assert len({(r['block'],r['name'],r['estimator']) for r in csvrows})==75
for r in csvrows:
    e=expected[r['block'],r['name'],r['estimator']]
    for k in ('median','share_pos'):close(float(r[k]),e[k])
    assert int(r['n'])==e['n']
print('PASS: 112 real records, 19 segments, all 8 real groups and 75 CSV rows.')
print('PASS: simulation aggregate consistency (140 requested, 3 failures); no path-level reproduction.')
print('Zero-slope medians:',{k:sim['Z0'][k]['median'] for k in ('a1','a2','b','a049','b2_049')})
for name,rr in [('whole',rows),('segments',groups['runup segments'])]:
    print(name,'null beta boundary hits',sum(r['b_nostate']['null_bound_hit'] for r in rr),
          'alt beta boundary hits',sum(r['b_nostate']['alt_bound_hit'] for r in rr),
          'gamma at boundary',sum(abs(abs(r['b_nostate']['gamma_alt'])-3)<1e-6 for r in rr))
print('Daily positive-correlation counts:',len([r for r in pos if r['cross']['1d']>0]),
      'of 28;',len([r for r in ctrl if r['cross']['1d']>0]),'of 84.')
