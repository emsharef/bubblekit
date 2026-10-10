"""Check committed experiment-017 summaries, not its simulation or stochastic laws.

No paths are generated. The clipped payoff equals the sampled execution payoff
plus its recorded breach amount, path by path; hence its sample defect is the
reported discrete defect minus the mean breach. This uses neither bridge law
nor a stochastic approximation bound. Sample SE/ESS remain descriptive.
"""
import csv
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
r = json.loads((ROOT / 'experiments/017/results.json').read_text())
rows = list(csv.DictReader((ROOT / 'experiments/017/summary.csv').open()))
assert len(rows) == 150
assert len({(s['model'], s['pi'], s['a'], s['N']) for s in rows}) == 150
strict_long, gbm_long, strict_inverse, inverse_ess, clip_gaps = [], [], [], [], []
n1_errors = []
for s in rows:
    model, p, a, n = s['model'], float(s['pi']), float(s['a']), int(s['N'])
    c = r['cells'][model][f'{p}|{a}|{n}']
    tag = 'px_bridge' if p > 1 else 'bridge'
    assert s['primary'] == tag
    z = c[tag]
    for name in ('d_H', 'se', 'liq_prob'):
        assert math.isclose(float(s[name]), z[name], abs_tol=1e-12)
    for col, group, key in (
        ('d_H_Q', 'bridge', 'd_H'), ('se_Q', 'bridge', 'se'),
        ('d_H_PX', 'px_bridge', 'd_H'), ('ess_PX', 'px_bridge', 'ess'),
        ('d_H_discrete_Q', 'discrete', 'd_H'),
        ('breach_mean_Q', 'discrete', 'breach_mean'),
        ('d_H_coarse_Q', 'bridge_coarse', 'd_H'),
        ('d_H_coarse_PX', 'px_bridge_coarse', 'd_H'),
    ):
        assert math.isclose(float(s[col]), c[group][key], abs_tol=1e-12)
    # Q floor-valued paths obey the sample cap exactly; numeraire weights
    # need not obey that cap in a finite sample when a > 0.
    assert c['bridge']['d_H'] <= 1 - a + 1e-12
    clipped = c['discrete']['d_H'] - c['discrete']['breach_mean']
    gap = c['bridge']['d_H'] - clipped
    assert gap >= -1e-12
    clip_gaps.append(gap)
    if n == 1:
        n1_errors.append(abs(c['bridge']['d_H'] - c['n1_formula_d_H']))
    if p > 1:
        (gbm_long if model == 'gbm' else strict_long).append(z)
    elif model != 'gbm':
        strict_inverse.append(z)
    if model == 'gbm' and p == -3 and n >= 12:
        mean = 1 - z['d_H']
        # Reconstruct (sum H)^2 / sum H^2 from sample mean and unbiased SE.
        size = r['paths']
        inverse_ess.append(size * mean**2 / (mean**2 + (size - 1)*z['se']**2))
    if model in ('bes3', 'cev1.5') and p == 3 and a == 0 and n == 252:
        print(f'{model}: Q discrete={c["discrete"]["d_H"]:.9f}, '
              f'clipped={clipped:.9f}, bridge={c["bridge"]["d_H"]:.9f}')
assert max(n1_errors) < 1e-12
for label, group in [('strict long', strict_long), ('GBM long', gbm_long),
                     ('strict inverse', strict_inverse)]:
    print(f'{label}: max sample SE={max(z["se"] for z in group):.9f}; '
          f'max |estimate|/SE={max(abs(z["d_H"])/z["se"] for z in group):.6f}')
# A direct counterexample to monotonicity of the reported primary estimates.
for model in ('bes3', 'cev1.5'):
    c = r['cells'][model]
    assert c['3.0|0.0|252']['px_bridge']['d_H'] < c['3.0|0.0|52']['px_bridge']['d_H']
print(f'GBM inverse primary Q ESS range: {min(inverse_ess):.6f}--{max(inverse_ess):.6f}')
print(f'Bridge-minus-clipped sample defect range: {min(clip_gaps):.3g}--{max(clip_gaps):.9f}')
print(f'PASS: {len(rows)} stored cells; N=1 max identity error {max(n1_errors):.3g}. '
      'No independent simulation reproduction or coverage certification.')
