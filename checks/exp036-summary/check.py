"""Recompute pilot summaries from saved paths; no simulation or calibration proof."""
import json
import math
from collections import Counter
from pathlib import Path
from statistics import median

root = Path(__file__).resolve().parents[2]
data = json.loads((root / 'experiments/036/results.json').read_text())
expected = {
    'N-in': ((0, 0), (0, 0), 1427),
    'N-switch': ((1, 2), (0, 1), 1125),
    'L-15': ((0, 0), (0, 0), 643),
    'L-20': ((0, 0), (0, 0), 664),
}
for cell, (expanding, frozen, exhausted) in expected.items():
    paths = [p for part in data['parts'] if part['cell'] == cell for p in part['paths']]
    assert len(paths) == 100
    statuses = Counter(s for p in paths for s in p['den_status'])
    assert statuses == {'budget exhausted': exhausted, 'tolerance met': 2000-exhausted}
    assert all(p['zero_labels'] == 0 for p in paths)
    for mode, counts in (('expanding', expanding), ('frozen', frozen)):
        assert all(p['modes'][mode]['zero_factors'] == 0 for p in paths)
        for alpha, expected_count in zip((0.05, 0.1), counts):
            crossings = 0
            for p in paths:
                m = p['modes'][mode]
                assert len(m['score']) == len(m['log_q']) == len(p['log_D_upper']) == 20
                scores = [q-d for q, d in zip(m['log_q'], p['log_D_upper'])]
                assert scores == m['score']
                threshold = -math.log(alpha)
                first = next((j for j, value in enumerate(scores) if value >= threshold), None)
                # The pilot used >; no saved value is on the boundary.
                assert all(value != threshold for value in scores)
                assert first == m['first_cross'][str(alpha)]
                crossings += first is not None
            assert crossings == expected_count
            assert data['summary'][cell][mode][str(alpha)]['cross_rate']['rate'] == crossings/100
        final = median(p['modes'][mode]['score'][-1] for p in paths)
        assert math.isclose(final, data['summary'][cell][mode]['final_score_median'], abs_tol=1e-12)
        print(f'{cell} {mode}: crossings={counts}/100; median final log score={final:.3f}')
    print(f'  budget exhausted: {exhausted}/2000; no zero labels/factors or fallbacks')
print('Saved-record aggregation only; neither a rerun nor evidence isolating numerical power loss.')
