"""Independent archive recount, not raw-data fitting or simulation reproduction."""
import csv
import json
import math
from pathlib import Path
from statistics import median

ROOT = Path(__file__).resolve().parents[2]


def summary(values):
    values = [v for v in values if v is not None and math.isfinite(v)]
    return None if not values else dict(median=median(values),
                                      share_pos=sum(v > 0 for v in values)/len(values), n=len(values))


def same(got, expected):
    if isinstance(expected, dict):
        assert set(got) == set(expected), (got, expected)
        for k in expected:
            same(got[k], expected[k])
    elif isinstance(expected, float):
        assert math.isclose(got, expected, abs_tol=1e-12, rel_tol=1e-12), (got, expected)
    else:
        assert got == expected, (got, expected)


def key(r):
    return tuple(r[k] for k in ('kind', 'group', 'sym', 'start', 'end'))


def main():
    data = json.loads((ROOT/'experiments/053/results.json').read_text())
    old = json.loads((ROOT/'experiments/052/results.json').read_text())['records']
    records = data['real_records']
    old_ok = {key(r): r for r in old if r['status'] == 'ok'}
    assert len(old) == 113 and len(records) == len(old_ok) == 112
    assert len({key(r) for r in records}) == 112 and {key(r) for r in records} == set(old_ok)
    predicates = {
        'E5': lambda r: r['group'] == 'E5', 'E9': lambda r: r['group'] == 'E9',
        '033-B': lambda r: r['group'] == '033-B',
        'positives': lambda r: r['kind'] == 'positive',
        'controls': lambda r: r['kind'] == 'control',
        'controls SPY/DIA': lambda r: r['kind'] == 'control' and r['sym'] in ('SPY', 'DIA'),
        'controls members': lambda r: r['kind'] == 'control' and r['sym'] not in ('SPY', 'DIA'),
    }
    groups = {}
    for name, pred in predicates.items():
        rows = [r for r in records if pred(r)]
        g = dict(records=len(rows), a2_nostate=summary([r['a2_nostate']['beta'] for r in rows]),
                 a2_nostate_t_gt2=sum(r['a2_nostate']['beta'] > 2*r['a2_nostate']['se_nw'] for r in rows),
                 b_nostate_beta=summary([r['b_nostate']['beta_alt'] for r in rows]),
                 b_nostate_gt_log20=sum(r['b_nostate']['loglr'] > math.log(20) for r in rows),
                 b_nostate_alt_bound_hits=sum(r['b_nostate']['alt_bound_hit'] for r in rows),
                 cross={sc:summary([r['cross'][sc] for r in rows]) for sc in ('5m','1h','1d')})
        groups[name] = g
        # Paired comparison at the same record IDs, without importing either fitter.
        pairs = [(old_ok[key(r)]['a2']['beta'], r['a2_nostate']['beta']) for r in rows]
        print(name, 'a2 old/new medians', median(x for x,y in pairs), median(y for x,y in pairs),
              'increases', sum(y>x for x,y in pairs), '/',len(pairs),
              'daily corr', g['cross']['1d']['median'])
    segments = [r['runup'] for r in records if r.get('runup')]
    assert len(segments) == 19
    groups['runup segments'] = dict(records=19,
        a2_nostate=summary([r['a2_nostate']['beta'] for r in segments]),
        b_nostate_beta=summary([r['b_nostate']['beta_alt'] for r in segments]),
        b_nostate_gt_log20=sum(r['b_nostate']['loglr'] > math.log(20) for r in segments),
        cross={sc:summary([r['cross'][sc] for r in segments]) for sc in ('5m','1h','1d')})
    same(groups, data['real_groups'])
    fits = [r['b_nostate'] for r in records+segments]
    assert all(r and r['success'] for r in fits)
    assert not any(r['alt_bound_hit'] for r in fits)
    print('Fit statuses: all', len(fits), 'successful; null boundary flags',sum(r['null_bound_hit'] for r in fits))

    # Simulation file contains summaries only: check consistency, NOT their estimates.
    sim = data['simulation']
    assert len(sim) == 7 and sum(c['paths'] for c in sim.values()) == 140
    assert sum(c['simulation_failures'] for c in sim.values()) == 3
    for name, c in sim.items():
        n = c['paths'] - c['simulation_failures']
        for estimator in ('a1','a2','b','a049','b2_049','record_log_range'):
            a = c[estimator]
            assert a['n'] == n and a['q25'] <= a['median'] <= a['q75']
            assert math.isclose(a['share_pos']*n, round(a['share_pos']*n), abs_tol=1e-10)
        print(name, 'a1 median', c['a1']['median'], 'positive count',round(c['a1']['share_pos']*n), '/', n,
              'cross-scale positive counts', [round(c['cross'][sc]['share_pos']*n) for sc in ('5m','1h','1d')])
    assert sim['Z0']['a1']['median'] < 0 and sim['Z0']['a1']['share_pos'] == .5
    assert sim['ZL']['a1']['q25'] != sim['ZL']['a1']['q75'] and sim['ZL']['a1']['share_pos'] == 0
    assert all(c['truth']['rho'] <= 0 for c in sim.values())  # No positive-SV-only cell.

    expected = {}
    for name,c in sim.items():
        for k in ('a1','a2','b','a049','b2_049'):
            expected['simulation',name,k] = c[k]
    for name,g in groups.items():
        for k in ('a2_nostate','b_nostate_beta'):
            expected['real',name,k] = g[k]
        for sc in ('5m','1h','1d'):
            expected['real',name,'cross_'+sc] = g['cross'][sc]
    rows = list(csv.DictReader((ROOT/'experiments/053/summary.csv').open()))
    assert len(rows) == len(expected) == 75
    assert {(r['block'],r['name'],r['estimator']) for r in rows} == set(expected)
    for r in rows:
        target = expected[r['block'],r['name'],r['estimator']]
        for k in ('median','share_pos','n'):
            same(float(r[k]), float(target[k]))
    print('PASS: 112 real records, 19 nested segments, eight groups and 75 CSV rows reconciled.')
    print('Simulation aggregates checked for consistency only; 140 individual path records are not archived.')


if __name__ == '__main__':
    main()
