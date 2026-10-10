"""Recompute summaries from committed experiment 027 outputs; no simulation."""
import json
from math import isclose, sqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
cells = json.loads((ROOT/'experiments/027/results.json').read_text())['cells']
rows = []
for key, frequencies in cells.items():
    truth, horizon = key.split('|')
    for freq, record in frequencies.items():
        for alpha in ('0.05', '0.1'):
            for column in ('v1flat', 'raw', 'd055', 'c033', 'c034'):
                if column not in record[alpha]:
                    continue
                row = record[alpha][column]
                rate, n = row['rate'], row['n']
                assert 0 <= rate <= 1 and n == (2000 if truth.startswith('G-') else 1000)
                assert isclose(rate*n, round(rate*n), abs_tol=1e-8)
                assert isclose(row['se'], sqrt(rate*(1-rate)/n), abs_tol=1e-12)
                rows.append((truth, int(horizon), freq, alpha, column, rate))


def rates(column, alpha='0.05', null=None, horizon=None, freq=None, truths=None):
    return [r for t, h, f, a, c, r in rows if c == column and a == alpha
            and (null is None or t.startswith('G-') == null)
            and (horizon is None or h == horizon) and (freq is None or f == freq)
            and (truths is None or t in truths)]


assert len(cells) == 18 and len(rows) == 324
for horizon in (60, 250):
    for freq in ('5m', '60m'):
        data = rates('c033', null=False, horizon=horizon, freq=freq)
        print('033 alternative range, alpha=.05:', horizon, freq, min(data), max(data))
for a in ('0.05', '0.1'):
    print('Null maxima, alpha='+a, {c: max(rates(c, a, null=True))
          for c in ('v1flat', 'raw', 'd055', 'c033', 'c034')})
print('034 alternative maximum, alpha=.05:', max(rates('c034', null=False)))
print('055 shared numerator on out-of-set clocks, alpha=.05:',
      {f: (min(rates('d055', truths=('G-out-U', 'G-out-ON'), freq=f)),
           max(rates('d055', truths=('G-out-U', 'G-out-ON'), freq=f))) for f in ('5m', '60m')})
records = [r for freqs in cells.values() for r in freqs.values()]
assert len(records) == 36
print('Recorded exact-column failure/singular totals:',
      {name: sum(r[name] for r in records) for name in ('fail', 'unbounded055', 'unbounded033')})
print('Max stored reference discrepancy:', max(r['max_check_absdiff'] for r in records))
# All same-numerator exact columns have nested rejection events by denominator.
for freqs in cells.values():
    for r in freqs.values():
        for a in ('0.05', '0.1'):
            assert r[a]['c033']['rate'] <= r[a]['d055']['rate'] <= r[a]['raw']['rate']
print('PASS: 324 rates/counts/SEs, denominator-order rates and stored diagnostics checked. '
      'No simulation reproduction or population guarantee inferred.')
