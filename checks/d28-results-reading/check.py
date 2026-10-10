"""Recount experiment 043's saved records; no simulation or evaluator imports.

This checks archived aggregation and the D28 decision inputs, not floating-point
score certification, generation of the records, or a full experiment reproduction.
"""
from collections import defaultdict
import csv
import gzip
import json
import math
from pathlib import Path
from statistics import median

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'experiments' / '043'


def wilson(k, n):
    z = 1.959963984540054
    p = k / n
    a = 1 + z*z/n
    center = (p + z*z/(2*n)) / a
    half = z * math.sqrt(p*(1-p)/n + z*z/(4*n*n)) / a
    return [max(0, center-half), min(1, center+half)]


def main():
    results = json.loads((DATA / 'results.json').read_text())
    statuses = json.loads((DATA / 'statuses.json').read_text())
    with (DATA / 'summary.csv').open() as f:
        csv_rows = {row['cell']: row for row in csv.DictReader(f)}
    with gzip.open(DATA / 'paths.json.gz', 'rt') as f:
        batches = json.load(f)
    bands = list(results['bands'])
    assert list(results['bands'].values()) == [[.3, 1.0], [.25, 1.25], [.5, 1.0]]
    by = defaultdict(list)
    paired = defaultdict(dict)
    for batch in batches:
        name, n, b = batch['cell'], batch['N'], batch['b']
        assert len(batch['paths']) == 50
        assert {p['i'] for p in batch['paths']} == set(range(50*b, 50*(b+1)))
        by[f'{name}|N={n}'].extend(batch['paths'])
        if name.startswith('CEV|'):
            base, track = name.rsplit('|', 1)
            paired[base, n, b][track] = batch
    assert len(by) == 182 and len(batches) == 7280
    assert set(by) == set(results['summary']) == set(csv_rows) == set(statuses)
    counts = {}
    failures = []
    comparisons = 0
    for key, paths in by.items():
        n = int(key.rsplit('=', 1)[1])
        summary = results['summary'][key]
        assert len(paths) == summary['paths'] == int(csv_rows[key]['paths']) == 2000
        assert {p['i'] for p in paths} == set(range(2000))
        failed = [p for p in paths if p['status'] != 'ok']
        assert len(failed) == summary['failed'] == statuses[key]['failed'] == int(csv_rows[key]['failed'])
        failures.extend({'cell': key, 'status': p['status'], 'fail_at': p['fail_at'],
                         'primary_cross': p['b0']['cross']['0.05'][0]} for p in failed)
        for p in paths:
            for field in ('max', 'final'):
                vals = [p[f'b{i}'][field] for i in (1, 0, 2)]
                vals = [-math.inf if x is None else x for x in vals]
                assert vals[0] <= vals[1] + 1e-7 and vals[1] <= vals[2] + 1e-7
        for i, band in enumerate(bands):
            for alpha in ('0.05', '0.1'):
                delays = []
                for p in paths:
                    row = p[f'b{i}']
                    cross, near = row['cross'][alpha]
                    assert not near, (key, i, alpha, 'unexpected unresolved checkpoint')
                    mx = -math.inf if row['max'] is None else row['max']
                    threshold = -math.log(float(alpha))
                    if cross is not None:
                        assert 126 < cross <= 126 + n
                        assert mx > threshold - 1e-8
                        delays.append(cross-126)
                    else:
                        assert mx <= threshold + 1e-8
                k = len(delays)
                counts[key, i, alpha] = k
                row = summary[band][alpha]
                assert k/2000 == row['rate'] == float(csv_rows[key][f'{band} cross {alpha}'])
                assert row['identified_first']['count'] == k
                assert row['identified_first']['delay_median'] == (median(delays) if delays else None)
                assert row['first_date_unresolved']['count'] == row['detection_unresolved_near_only'] == 0
                comparisons += 1
    assert sum(map(len, by.values())) == 364000
    assert len(failures) == 1
    # Paired seed identity and price-only comparator agreement; not price-path regeneration.
    assert len(paired) == 720
    for group in paired.values():
        assert set(group) == {'background', 'partial', 'full'}
        ref = group['background']
        for arm in ('partial', 'full'):
            assert ref['seed'] == group[arm]['seed']
            for p, q in zip(ref['paths'], group[arm]['paths']):
                assert p['gsadf'] == q['gsadf'] and p.get('v1') == q.get('v1')

    def in_band(key, i=0):
        if not key.startswith('C-'):
            return False
        w = float(key.split('|w=')[1].split('|')[0])
        low, high = results['bands'][bands[i]]
        return low <= w <= high

    report = {'records': 364000, 'cell_horizons': 182,
              'band_level_aggregations_checked': comparisons,
              'paired_seed_groups': len(paired), 'failures': failures,
              'unresolved_archived': 0,
              'replay_mismatches_reported_not_rerun': results['replay_mismatches']}
    report['control_maxima'] = {}
    for i, band in enumerate(bands):
        eligible = [k for k in by if in_band(k, i)]
        key = max(eligible, key=lambda k: counts[k, i, '0.05'])
        k = counts[key, i, '0.05']
        report['control_maxima'][band] = {'cells': len(eligible), 'cell': key,
                                        'count': k, 'n': 2000, 'rate': k/2000,
                                        'wilson95_pointwise': wilson(k, 2000)}
    switch = [k for k in by if k.startswith('C-switch|') and in_band(k)]
    skey = max(switch, key=lambda k: counts[k, 0, '0.05'])
    report['in_band_switch_max'] = {'cell': skey, 'count': counts[skey, 0, '0.05'],
                                   'rate': counts[skey, 0, '0.05']/2000}
    report['a_switch'] = {}
    for key in sorted(k for k in by if k.startswith('A-switch|')):
        k = counts[key, 0, '0.05']
        report['a_switch'][key] = {'count': k, 'n': 2000, 'rate': k/2000,
                                  'wilson95_pointwise': wilson(k, 2000),
                                  'detected_delay_median': results['summary'][key][bands[0]]['0.05']['identified_first']['delay_median']}
    report['empirical'] = {}
    for n, saved in results['heldout_at_empirical_threshold'].items():
        threshold = saved['threshold_log']
        selected = {k: ps for k, ps in by.items() if k.endswith(f'|N={n}')}
        individual = {k: sum(p['b0']['max'] is not None and p['b0']['max'] > threshold for p in ps)
                      for k, ps in selected.items()}
        for key, k in individual.items():
            name = key.rsplit('|N=', 1)[0]
            if name in saved['cells']:
                assert k/2000 == saved['cells'][name]['rate']
            if key.startswith('A-switch|'):
                assert k/2000 == results['a_switch_empirical'][key]['power']
        pools = {}
        for label, keys in (
                ('pooled C-switch b=0, w in {0.3, 1.0}',
                 [k for k in selected if k.startswith('C-switch|b=0.0|') and
                  float(k.split('|w=')[1].split('|')[0]) in (.3, 1.0)]),
                ('pooled all controls in primary band', [k for k in selected if in_band(k)])):
            k, size = sum(individual[key] for key in keys), 2000*len(keys)
            assert size == saved['cells'][label]['paths'] and k/size == saved['cells'][label]['rate']
            pools[label] = {'count': k, 'n': size, 'rate': k/size}
        worst = max((k for k in selected if in_band(k)), key=individual.get)
        report['empirical'][n] = {'threshold_log': threshold, 'pools': pools,
                                  'worst_cell': worst, 'worst_count': individual[worst],
                                  'worst_rate': individual[worst]/2000}
    report['primary_ranges'] = {}
    for label, eligible in (
            ('CEV full', [k for k in by if k.startswith('CEV|') and '|full|' in k]),
            ('CEV background', [k for k in by if k.startswith('CEV|') and '|background|' in k]),
            *[(model, [k for k in by if k.startswith(model+'|')])
              for model in ('Heston', 'Switch-intraday', 'Merton')]):
        vals = [counts[k, 0, '0.05']/2000 for k in eligible]
        report['primary_ranges'][label] = [min(vals), max(vals)]
    print(json.dumps(report, indent=2))
    print('PASS: archived aggregation and decision inputs; no simulation rerun or score certificate')


if __name__ == '__main__':
    main()
