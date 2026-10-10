"""Reaggregate committed experiment-021 scores; no price rerun or new experiment.

Verify the stored flags from log scores independently of the report's summary.
Descriptive controls only: neither calibration nor a numerical error certificate.
"""
import json
import math
from pathlib import Path


def main():
    data = json.loads((Path(__file__).resolve().parents[2]/'experiments/021/results.json').read_text())
    records, missing = [], []
    for row in data['rows']:
        for series in row['series']:
            if 'log_e' not in series:
                missing.append((row['row'], row['variant'], series['name'], series['kind']))
                continue
            assert series['status'] == ['ok']
            assert math.isfinite(series['log_e']) and math.isfinite(series['raw_log_e'])
            assert series['log_e'] <= series['raw_log_e']
            for alpha in (.05, .1):
                for field, prefix in (('log_e', 'lab'), ('raw_log_e', 'lab054')):
                    assert series['flags'][f'{prefix}_{alpha}'] == (series[field] > -math.log(alpha))
            records.append((row, series))
    assert len(records) == 542
    assert missing == [('E3', 'to_peak', 'XHB', 'adj'), ('E3', 'to_peak', 'XHB', 'close')]
    for kind in ('adj', 'close'):
        for variant in ('full', 'to_peak'):
            for sign in ('positive', 'negative'):
                group = [(r, s) for r, s in records if r['variant'] == variant
                         and r['sign'] == sign and s['kind'] == kind]
                counts = (len(group), sum(s['log_e'] > math.log(20) for _, s in group),
                          sum(s['raw_log_e'] > math.log(20) for _, s in group))
                if sign == 'negative':
                    expected = (103, 0, 1 if variant == 'full' else 2)
                elif variant == 'full':
                    expected = (33, 2, 9)
                else:
                    expected = (32, 3 if kind == 'adj' else 4, 10)
                assert counts == expected
                print(kind, variant, sign, 'count / drift flags / raw flags:', counts)
        negatives = [(s['log_e'], r['row'], r['variant'], s['name']) for r, s in records
                     if r['sign'] == 'negative' and s['kind'] == kind]
        print(kind, 'largest negative log score:', max(negatives))
    flagged = {(r['row'], s['name'], s['fit']) for r, s in records if s['log_e'] > math.log(10)}
    assert flagged == {('E5', 'BB', 17), ('E5', 'GME', 17), ('E5', 'KOSS', 17), ('E6', '000660.KS', 13)}
    print('PASS: 542 score records; thresholds, ordering, statuses and descriptive counts')


if __name__ == '__main__':
    main()
