"""Read committed experiment-025 summaries; no simulation or independent rerun.

Recompute extrema by null type, level and panel composition. The switch
probabilities are deterministic calculations for run.py's daily Bernoulli
flips; they are not measured false-alarm rates or a new experiment.
"""
import json
import math
from pathlib import Path

root = Path(__file__).resolve().parents[2]
cells = json.loads((root / 'experiments/025/results.json').read_text())['cells']
assert len(cells) == 80

for null in ('gbm', 'merton', 'regime', 'heston'):
    for q in ('0.05', '0.1'):
        rows = [(key, cell, cell['tests']['v1_ebh'][q]) for key, cell in cells.items()
                if cell['null_type'] == null]
        all_null = [(key, cell, row) for key, cell, row in rows if cell['bubbly_fraction'] == 0]
        mixed = [(key, cell, row) for key, cell, row in rows if cell['bubbly_fraction'] > 0]
        assert len(all_null) == 4 and len(mixed) == 16
        assert all(row['FDR']['mean'] == row['FWER_allnull']['mean'] for _, _, row in all_null)
        assert all(cell['covered_for_v1'] == (null == 'gbm') for _, cell, _ in rows)
        rates = [row['FWER_allnull']['mean'] for _, _, row in all_null]
        worst_key, _, worst = max(mixed, key=lambda item: item[2]['FDR']['mean'])
        powers = [row['power_per_name'] for _, _, row in mixed]
        # The power is already aggregated in the committed cell summary.
        powers = [x['mean'] if isinstance(x, dict) else x for x in powers]
        print(null, 'q=', q,
              'all-null FDR=FWER range=', tuple(round(x, 6) for x in (min(rates), max(rates))),
              'mixed FDR max=', round(worst['FDR']['mean'], 6),
              'SE=', round(worst['FDR']['se'], 6), 'cell=', worst_key,
              'mixed power range=', tuple(round(x, 6) for x in (min(powers), max(powers))))

# In run.py, a flip after a day changes the next day's volatility. Hence a
# block of n_e increments has n_e-1 internal boundaries. Future flips are
# independent of training, with probability 1-exp(-1/252) at each boundary.
p = -math.expm1(-1 / 252)
for years in (5, 10):
    n_e = 252 * years // 2
    boundaries = n_e - 1
    p_zero = math.exp(-boundaries / 252)
    p_one = boundaries * p * math.exp(-(boundaries - 1) / 252)
    repeated = 1 - p_zero - p_one
    # Even the broadest single-cut set excludes the first/last boundary:
    # each segment needs at least two increments (claim 059).
    admitted_components = p_zero + (n_e - 3) * p * math.exp(-(boundaries - 1) / 252)
    assert 0 < admitted_components < 1 - repeated < 1
    # Direct finite-binomial sum independently checks the complement.
    direct = math.fsum(math.comb(boundaries, k) * p ** k * (1 - p) ** (boundaries - k)
                       for k in range(2, 80))
    # Bound the omitted binomial tail by its first term and the largest
    # subsequent term ratio. It is negligible for both fixed designs.
    first_omitted = math.comb(boundaries, 80) * p ** 80 * (1 - p) ** (boundaries - 80)
    ratio = (boundaries - 80) * p / (81 * (1 - p))
    assert ratio < 1 and first_omitted / (1 - ratio) < 1e-50
    assert abs(direct - repeated) < 1e-13
    print('T=', years, 'evaluation steps=', n_e, 'P(at least two internal flips)=',
          f'{repeated:.12f}', 'P(no flip or one cut in 2..n_e-2)=', f'{admitted_components:.12f}')

print('PASS: 80 committed cells; all-null FDR/FWER equality; correct covered-law labels; switch-count arithmetic.')
print('This is a reading of stored summaries, not a reproduction of experiment 025 or a result for claim 059.')
