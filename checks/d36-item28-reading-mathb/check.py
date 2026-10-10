"""Independent archive recount for reported experiment 054; no refitting.

Default: committed target records only. Optional --data-root PATH uses the
analyst's existing data/ cache for reference-prefix and forward-OLS checks.
Single process. Set OMP/OPENBLAS/MKL/VECLIB thread limits to 1 before uv run.
"""
import argparse
from collections import Counter
import csv
import datetime as dt
from functools import lru_cache
import gzip
import hashlib
import json
import math
from pathlib import Path
from zoneinfo import ZoneInfo
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT/'experiments/054'


def read(path):
    with (gzip.open(path, 'rt') if path.suffix == '.gz' else path.open()) as f:
        return json.load(f)


def shares(rows):
    return dict(n=len(rows), monitor=sum(r['monitor_alarm'] is not None for r in rows),
                gsadf=sum(r['gsadf_alarm_session'] is not None for r in rows),
                training_failure=sum(not r['fit_ok'] for r in rows))


def main(data):
    rows, res, manifest = read(EXP/'targets.json.gz'), read(EXP/'results.json'), read(EXP/'manifest.json')
    assert len(rows) == len(manifest['targets'])
    bykind = {kind: [r for r in rows if r['kind'] == kind] for kind in ('positive', 'control', 'unselected')}
    report = {'target_sha256': hashlib.sha256((EXP/'targets.json.gz').read_bytes()).hexdigest(),
              'registered_rows': {k: shares(v) for k, v in bykind.items()}}
    for kind, label in (('positive', 'positive_launches'), ('control', 'controls'), ('unselected', 'unselected')):
        s = shares(bykind[kind]); expected = res[label]['all']
        assert s['n'] == expected['launches'] and s['training_failure'] == expected['fit_failures']
        assert s['monitor']/s['n'] == expected['monitor_alarm_share']
        assert s['gsadf']/s['n'] == expected['gsadf_alarm_share']
    cut, gc = res['calibration']['monitor_cutoff'], res['calibration']['gsadf_cutoff']
    for r in rows:
        assert (r['monitor'] > cut) == (r['monitor_alarm'] is not None)
        assert (r['gsadf'] > gc) == (r['gsadf_alarm_session'] is not None)
        assert r['fit_ok'] or (r['monitor'] == -1 and r['monitor_alarm'] is None)
    controls = list({(r['sym'], r['k']): r for r in bykind['control']}.values())
    report['unique_controls_diagnostic'] = {'all': shares(controls),
        'SPY/DIA': shares([r for r in controls if r['sym'] in ('SPY', 'DIA')]),
        'members': shares([r for r in controls if r['sym'] not in ('SPY', 'DIA')])}
    report['common_fit_positive_diagnostic'] = shares([r for r in bykind['positive'] if r['fit_ok']])
    report['unselected_ties'] = dict(Counter(str(r['monitor']) for r in bykind['unselected']).most_common(3))
    report['record_counts_from_target_alarm_dates'] = dict(before=0, on_peak=0, after=0, never=0,
                                                        never_all_training_failed=0, before_onset=0)
    for record in res['positives']:
        selected = [r for r in bykind['positive'] if (r['sym'], r['group'], r['record']) ==
                    (record['sym'], record['group'], record['record'])]
        assert len(selected) == record['launches']
        dates = [r['monitor_alarm_day'] for r in selected if r['monitor_alarm'] is not None]
        first = min(dates) if dates else None
        assert first == record['monitor']['first_alarm']
        category = ('never' if first is None else 'before' if first < record['peak'] else
                    'after' if first > record['peak'] else 'on_peak')
        report['record_counts_from_target_alarm_dates'][category] += 1
        if first is None and all(not r['fit_ok'] for r in selected):
            report['record_counts_from_target_alarm_dates']['never_all_training_failed'] += 1
        if first is not None and first < record['onset']:
            report['record_counts_from_target_alarm_dates']['before_onset'] += 1
    report['aggregate_scope'] = 'reported peak/onset dates held fixed; no peak recomputation or refitting'
    if data is not None:
        report.update(cache_checks(data, bykind['unselected'], res, manifest))
    print(json.dumps(report, indent=2, sort_keys=True))
    print('PASS: archive checks only, not independent reproduction of the fitted experiment or empirical size proof.')


def cache_checks(data, unselected, res, manifest):
    archive = data/'d36/exp054'
    saved = read(archive/'launches.json.gz')
    launches = {(r['sym'], r['k'], r['tag']): r for r in saved['launches']}
    maxima, gmax = [], []
    for ref in manifest['reference']:
        row = launches[(ref['sym'], ref['k'], 'ref')]
        with np.load(archive/row['archive']) as z:
            assert len(z['status']) == 1617
            valid = ((z['status'] == 0) & np.isfinite(z['logq']) & np.isfinite(z['logd']))
            scores = np.full(1617, -1.)
            delta = z['logq'][valid]-z['logd'][valid]
            assert np.isfinite(delta).all()
            scores[valid] = 2/np.pi*np.arctan(np.maximum(0., delta))
            maxima.append(float(scores.max()))
        gmax.append(max(row['gsadf']))
    rank = (19*(len(maxima)+1)+19)//20
    cutoff = max(0., sorted(maxima)[rank-1])
    assert math.isclose(cutoff, res['calibration']['monitor_cutoff'], abs_tol=1e-14)
    assert sorted(gmax)[rank-1] == res['calibration']['gsadf_cutoff']

    # Extract the session calendar directly from cached SPY timestamps, without
    # importing the author's analysis, scores, data loader or regression code.
    ny = ZoneInfo('America/New_York')
    days = set()
    with gzip.open(data/'d29/sip/SPY.csv.gz', 'rt') as f:
        reader = csv.reader(f); next(reader)
        for stamp, *_ in reader:
            date = dt.datetime.fromisoformat(stamp.replace('Z', '+00:00')).astimezone(ny)
            if 570 <= date.hour*60+date.minute < 960:
                days.add(date.date())
    calendar = sorted(days)

    @lru_cache(None)
    def daily(sym):
        j = read(data/'d24'/f'yahoo_{sym}.json')['chart']['result'][0]
        timezone = j['meta'].get('gmtoffset', 0)
        values = [(dt.datetime.fromtimestamp(t+timezone, dt.timezone.utc).date(), p)
                  for t, p in zip(j['timestamp'], j['indicators']['adjclose'][0]['adjclose'])
                  if p is not None and math.isfinite(p) and p > 0]
        return np.array([v[0] for v in values]), np.array([v[1] for v in values])

    grid, _ = daily('^GSPC')
    records = []
    for row in unselected:
        end = calendar[row['k']+20]
        k = np.searchsorted(grid, end, side='right')-1
        dates, prices = daily(row['sym'])
        start = np.searchsorted(dates, grid[k], side='right')
        finish = np.searchsorted(dates, grid[k+126], side='right')
        if start == 0 or finish-start < .99*126:
            continue
        r = dict(row)
        for h in (63, 126):
            path = prices[start-1:min(start+h, finish)]
            r[f'mdd{h}'] = max(1-path/np.maximum.accumulate(path))
            r[f'ret{h}'] = math.log(path[-1]/path[0])
            r[f'out_end{h}'] = grid[k+h].isoformat()
        records.append(r)
    assert len(records) == res['forward']['n']
    dates = np.array([r['launch'] for r in records])
    ranks = {}
    for name in ('monitor', 'gsadf'):
        rankvals = np.empty(len(records))
        for date in sorted(set(dates)):
            inds = np.flatnonzero(dates == date)
            order = sorted(inds, key=lambda i: (records[i][name], i))
            for j, i in enumerate(order):
                rankvals[i] = (j+.5)/len(order)
        ranks[name] = rankvals
    checked = {}
    for h in (63, 126):
        tr = np.array([r[f'out_end{h}'] < '2023-01-01' for r in records])
        te = dates >= '2023-01-01'
        for outcome in (f'mdd{h}', f'ret{h}'):
            y = np.array([r[outcome] for r in records])
            for names in (('monitor',), ('gsadf',), ('monitor', 'gsadf')):
                X = np.column_stack([np.ones(len(y))]+[ranks[n] for n in names])
                beta = np.linalg.solve(X.T@X, X.T@y)
                fitted = np.linalg.solve(X[tr].T@X[tr], X[tr].T@y[tr])
                prediction = X[te]@fitted
                oos = 1-np.sum((y[te]-prediction)**2)/np.sum((y[te]-y[tr].mean())**2)
                key = outcome+'|'+'+'.join(names)
                expected = res['forward']['full'][key]
                np.testing.assert_allclose(beta[1:], expected['coef'], rtol=1e-9, atol=1e-10)
                assert math.isclose(oos, expected['oos_r2'], rel_tol=1e-8, abs_tol=1e-10)
                checked[key] = {'coef': beta[1:].tolist(), 'oos_r2': float(oos)}
    return {'cache_reference_check': {'n': len(maxima), 'rank': rank, 'cutoff': cutoff,
                                      'strict_exceedances': sum(x > cutoff for x in maxima)},
            'independent_forward_ols': checked,
            'regression_scope': 'full-sample coefficients and OOS point R2 only; DK SE/bootstrap not rerun'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--data-root', type=Path)
    main(parser.parse_args().data_root)
