"""Independent recount of committed 054 outputs, not a price/fit/regression reproduction."""
import csv
import gzip
import json
import math
from collections import Counter
from pathlib import Path
from statistics import median

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / 'experiments/054'
results = json.loads((HERE / 'results.json').read_text())
manifest = json.loads((HERE / 'manifest.json').read_text())
with gzip.open(HERE / 'targets.json.gz', 'rt') as f:
    targets = json.load(f)


def identity(r):
    return r['kind'], r['group'], r['sym'], r['k'], r['launch'], tuple(r.get('record', []))


assert Counter(map(identity, targets)) == Counter(map(identity, manifest['targets']))
assert len(targets) == 10176
assert len({(r['kind'], r['sym'], r['k']) for r in targets}) + 499 == 10158
assert len(manifest['reference']) == 499
assert max(r['ends'] for r in manifest['reference']) < min(r['launch'] for r in targets)
cut = results['calibration']['monitor_cutoff']
gcut = results['calibration']['gsadf_cutoff']
for row in targets:
    assert sum(row['status_counts'].values()) == 1617
    assert (row['monitor'] > cut) == (row['monitor_alarm'] is not None)
    assert (row['gsadf'] > gcut) == (row['gsadf_alarm_session'] is not None)
    if row['monitor_alarm'] is not None:
        assert 1 <= row['monitor_alarm'] <= 1617
        assert (row['monitor_alarm'] - 1) // 77 == row['monitor_alarm_session']


def shares(rows, saved):
    assert saved['launches'] == len(rows)
    assert saved['fit_failures'] == sum(not r['fit_ok'] for r in rows)
    for method, field in [('monitor', 'monitor_alarm'), ('gsadf', 'gsadf_alarm_session')]:
        actual = sum(r[field] is not None for r in rows) / len(rows)
        assert math.isclose(actual, saved[method + '_alarm_share'], abs_tol=1e-14)


blocks = {kind: [r for r in targets if r['kind'] == kind]
          for kind in ('positive', 'control', 'unselected')}
for kind, name in [('positive', 'positive_launches'), ('control', 'controls'), ('unselected', 'unselected')]:
    shares(blocks[kind], results[name]['all'])
for group in ('E5', 'E9', '033-B'):
    shares([r for r in blocks['positive'] if r['group'] == group], results['positive_launches'][group])
for label in ('SPY/DIA', 'members'):
    rows = [r for r in blocks['control'] if (r['sym'] in ('SPY', 'DIA')) == (label == 'SPY/DIA')]
    shares(rows, results['controls'][label])
shares([r for r in blocks['unselected'] if not r['overlap_052']], results['unselected']['unexposed'])
for group, saved in results['controls']['by_window'].items():
    shares([r for r in blocks['control'] if r['group'] == group], saved)
for year, saved in results['unselected']['by_year'].items():
    shares([r for r in blocks['unselected'] if r['launch'].startswith(year)], saved)
with (HERE / 'summary.csv').open() as f:
    for row in csv.DictReader(f):
        saved = (results['unselected']['by_year'][row['name']] if row['block'] == 'unselected'
                 else results[row['block']][row['name']])
        for field in ('launches', 'fit_failures', 'monitor_alarm_share', 'gsadf_alarm_share'):
            assert math.isclose(float(row[field]), saved[field], abs_tol=1e-14)

for record in results['positives']:
    rows = [r for r in blocks['positive'] if (r['sym'], r['group'], r['record']) ==
            (record['sym'], record['group'], record['record'])]
    assert record['launches'] == len(rows)
    assert record['fit_failures'] == sum(not r['fit_ok'] for r in rows)
    dates = [r['monitor_alarm_day'] for r in rows if r['monitor_alarm'] is not None]
    assert record['monitor']['first_alarm'] == (min(dates) if dates else None)
    for method, field in [('monitor', 'monitor_alarm'), ('gsadf', 'gsadf_alarm_session')]:
        assert record[method]['launches_alarmed'] == sum(r[field] is not None for r in rows)
        day = record[method]['first_alarm']
        offset = record[method]['sessions_from_peak']
        assert (day is None) == (offset is None)
        if day is not None:
            assert (day < record['peak'], day == record['peak']) == (offset < 0, offset == 0)

for method, expected in [('monitor', (14, 0, 6, 9)), ('gsadf', (20, 1, 1, 7))]:
    offsets = [r[method]['sessions_from_peak'] for r in results['positives']]
    counts = (sum(x is not None and x < 0 for x in offsets), sum(x == 0 for x in offsets),
              sum(x is not None and x > 0 for x in offsets), sum(x is None for x in offsets))
    assert counts == expected
    print(method, 'strictly-before/on/after/never:', counts,
          'strictly-before median lead:', median(-x for x in offsets if x is not None and x < 0))

controls_unique = list({(r['sym'], r['k']): r for r in blocks['control']}.values())
assert len(controls_unique) == 610
assert sum(r['monitor_alarm'] is not None for r in controls_unique) == 30
print('Controls: 36/1127 record-weighted, 30/610 unique launches; GSADF 0 in both.')
for kind in blocks:
    rows = blocks[kind]
    day0 = sum(r['gsadf_alarm_session'] == 0 for r in rows)
    failed = [r for r in rows if not r['fit_ok']]
    assert all(r['status_counts'] == {'clock_failure': 1617} for r in failed)
    print(kind, 'GSADF first-session alarms:', day0, 'pre-fit clock failures:', len(failed))

for h in (63, 126):
    f = results['forward']['full']
    m, g, both = [f[f'mdd{h}|{s}'] for s in ('monitor', 'gsadf', 'monitor+gsadf')]
    print('Reported drawdown', h, 't:', m['coef'][0] / m['se_dk'][0],
          'OOS R2 gain over GSADF, percentage points:', 100 * (both['oos_r2'] - g['oos_r2']))
print('PASS: manifest, target summaries, CSV, first-monitor dates and timing categories reconcile.')
print('Scope: no raw-price, prefix, peak-calendar, regression or bootstrap reproduction.')
