"""Consistency/reaggregation of committed experiment 023, not a simulation rerun."""
import json
import math
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[2]/'experiments/023'
    result = json.loads((root/'results.json').read_text())
    statuses = json.loads((root/'statuses.json').read_text())
    assert sum(r['n'] for r in statuses.values()) == 184000
    assert all(not r['not_ok'] for r in statuses.values())
    columns = [f'h{h}' for h in result['hs']]
    maxima = {column: (-1, None) for column in ('h0.2', 'h0.0')}
    null_max = {'covered': 0, 'outside': 0}
    for name, frequencies in result['cells'].items():
        for frequency, cell in frequencies.items():
            for alpha in ('0.05', '0.1'):
                scores = cell[alpha]
                ordered = [scores[k]['rate'] for k in ['raw']+columns+['d055']]
                assert all(x >= y for x, y in zip(ordered, ordered[1:]))
                for column in columns:
                    n = scores[column]['n']
                    difference = scores[column]['rate']-scores['d055']['rate']
                    paired = scores['paired_vs_055'][column]
                    assert abs(difference-paired['diff']) < 1e-12
                    # Nested rejection indicators make the paired difference
                    # Bernoulli; derive its sample SE without the report code.
                    se = math.sqrt(max(0, difference*(1-difference)/(n-1)))
                    assert abs(se-paired['se']) < 1e-12
            scores = cell['0.05']
            if name.startswith('cevalt') and frequency == 'daily':
                for column in maxima:
                    difference = scores[column]['rate']-scores['d055']['rate']
                    if difference > maxima[column][0]:
                        maxima[column] = (difference, name)
            elif name.startswith(('gauss', 'cevnull')):
                drift = float(name.split('_b')[1].split('_')[0]) if name.startswith('gauss') else 0
                for h in result['hs']:
                    label = 'covered' if abs(drift) <= h else 'outside'
                    null_max[label] = max(null_max[label], scores[f'h{h}']['rate'])
    print('Daily alternative maximal paired gains:', maxima)
    print('Gaussian/CEV null maximum observed rejection rates, alpha=.05:', null_max)
    cell = result['cells']['cevalt_p1.50_k0.30|5']['daily']['0.05']
    print('p=1.5, scale=.30, T=5 daily:', {k: cell[k]['rate'] for k in ('raw','h0.2','d055')})
    print('PASS: 184000 status records; aggregate ordering and paired-rate/SE consistency')


if __name__ == '__main__':
    main()
