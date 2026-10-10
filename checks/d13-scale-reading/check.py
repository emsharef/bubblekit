"""Reaggregate experiment 024's saved summaries; no simulation/likelihood rerun."""
import json
import math
import re
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[2] / 'experiments/024'
    result = json.loads((root / 'results.json').read_text())
    statuses = json.loads((root / 'statuses.json').read_text())
    rectangles = {f'r{lo:.2f}-{hi:.2f}': (lo, hi)
                  for lo, hi in result['scale_intervals']}
    order = ['d055', 'b056'] + list(reversed(rectangles)) + ['raw']
    primary, wide = 'r0.20-0.45', 'r0.15-0.60'
    gains = {c: (-1, None) for c in (primary, wide)}
    maxima = {c: {'covered': 0, 'outside': 0} for c in (primary, wide)}
    ties = records = 0
    for name, frequencies in result['cells'].items():
        alternative = name.startswith('cevalt')
        gaussian = re.match(r'gauss_b([+-][\d.]+)_k([\d.]+)\|', name)
        for frequency, cell in frequencies.items():
            status = statuses[f'{name}|{frequency}']
            n = status['n']
            records += n
            assert not status['not_ok'] and cell['status_counts'] == {'ok': n}
            assert sum(cell['fit_counts'].values()) == n
            assert not any(cell['rect_failures'].values())
            for column in order:
                if gaussian:
                    b, scale = map(float, gaussian.groups())
                    retained = b == 0 and scale in (.2, .3, .45)
                    in_drift = -.2 <= b <= .2
                    if column == 'raw':
                        covered = retained
                    elif column == 'd055':
                        covered = True
                    elif column == 'b056':
                        covered = retained or in_drift
                    else:
                        lo, hi = rectangles[column]
                        covered = retained or (in_drift and lo <= scale <= hi)
                else:
                    covered = not alternative
                assert cell['coverage'][column] == covered, (name, column)
            for alpha in ('0.05', '0.1'):
                scores = cell[alpha]
                rates = [scores[c]['rate'] for c in order]
                assert all(a <= b for a, b in zip(rates, rates[1:]))
                for column in order:
                    rate = scores[column]['rate']
                    assert scores[column]['n'] == n
                    assert abs(rate*n - round(rate*n)) < 1e-9
                    assert abs(scores[column]['se'] - math.sqrt(rate*(1-rate)/n)) < 1e-12
                for baseline in ('raw', 'd055', 'b056'):
                    for column in rectangles:
                        delta = scores[column]['rate'] - scores[baseline]['rate']
                        pair = scores[f'paired_vs_{baseline}'][column]
                        assert abs(delta - pair['diff']) < 1e-12
                        # Nested indicators: the signed difference has one
                        # nonzero value, giving this sample standard error.
                        se = math.sqrt(abs(delta)*(1-abs(delta))/(n-1))
                        assert abs(se - pair['se']) < 1e-12
            categories = cell[f'{primary}_profile_kind']
            assert sum(categories.values()) == n
            ties += sum(count for kind, count in categories.items() if '+' in kind)
            if frequency == 'daily':
                scores = cell['0.05']
                for column in gains:
                    if alternative:
                        delta = scores[column]['rate'] - scores['b056']['rate']
                        if delta > gains[column][0]:
                            gains[column] = (delta, name)
                    else:
                        label = 'covered' if cell['coverage'][column] else 'outside'
                        maxima[column][label] = max(maxima[column][label], scores[column]['rate'])
    assert records == 240000 and len(statuses) == 240
    print('Daily alternative maximal gains over claim 056:', gains)
    print('Daily null maximum rejection rates at alpha=.05:', maxima)
    for name in ('cevalt_p1.50_k0.30|5', 'gauss_b+0.00_k0.15|2',
                 'gauss_b+0.00_k0.60|2', 'gauss_b-0.20_k0.15|2'):
        scores = result['cells'][name]['daily']['0.05']
        print(name, {c: scores[c]['rate'] for c in ('raw','b056',primary,wide)})
    print('Primary category ties:', ties)
    print('PASS: 240000 records; coverage union, aggregate nesting and paired-rate/SE consistency')


if __name__ == '__main__':
    main()
