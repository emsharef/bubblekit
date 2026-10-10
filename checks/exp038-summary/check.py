"""Independent saved-path aggregation, not an experiment/enclosure rerun."""
from collections import Counter
import json
import math
from pathlib import Path
from statistics import median

root = Path(__file__).resolve().parents[2]/'experiments/038'
data = json.loads((root/'results.json').read_text())
enc = json.loads((root/'enclosure.json').read_text())
statuses = json.loads((root/'statuses.json').read_text())
checks = list(range(87,240,8))
exhausted = {'N-in': (1344,1267,931), 'N-switch': (1161,992,769),
             'L-15': (665,238,335), 'L-20': (631,254,325)}
all_exhausted = 0
for cell, expected in exhausted.items():
    batches = [part for part in data['parts'] if part['cell'] == cell]
    assert sorted(part['b'] for part in batches) == list(range(10))
    paths = [p for part in batches for p in part['paths']]
    assert len(paths) == 100
    for path in paths:
        assert path['checks'] == checks and path['zero_labels'] == 0
        assert len(path['scan_log']) == len(path['single_log']) == len(checks)
        assert all(math.isfinite(v) for key in ('scan_log','single_log') for v in path[key])
        for alpha in (0.05,0.1):
            threshold = -math.log(alpha)
            for proc,key in (('P1','scan_log'),('P0','single_log')):
                first = next((t for t,value in zip(checks,path[key]) if value >= threshold),None)
                assert all(abs(value-threshold)>1e-8 for value in path[key])
                assert first == path[str(alpha)][proc] is None
            # Equal 1/3 weights recover the largest anchor LOWER score by
            # adding log 3 to the scan log; inactive scores are one, below
            # both thresholds, so they cannot alter this crossing check.
            unweighted = any(value+math.log(3) >= threshold for value in path['scan_log'])
            assert not unweighted
            assert path[str(alpha)]['unweighted_crossed_scan_missed'] == unweighted
            # Frozen per-checkpoint scores are not saved: only aggregate
            # their recorded decisions, without claiming to recompute them.
            assert path[str(alpha)]['S1'] is None and path[str(alpha)]['S0'] is None
    for anchor,active,want in zip(('79','119','159'),(2000,1500,1000),expected):
        count = Counter(s for path in paths for s in path['anchor_status'][anchor])
        assert count['budget exhausted'] == want
        assert count['tolerance met'] == active-want
        assert count['inactive'] == 2000-active
        assert set(count) <= {'budget exhausted','tolerance met','inactive'}
        assert dict(count) == statuses[cell]['anchor_status'][anchor]
        all_exhausted += want
    finals = tuple(median(p[key][-1] for p in paths) for key in ('scan_log','single_log'))
    assert finals[0] == data['summary'][cell]['final_log_median']['scan']
    assert finals[1] == data['summary'][cell]['final_log_median']['single']
    for alpha in ('0.05','0.1'):
        for proc in ('P1','P0','S1','S0'):
            assert data['summary'][cell][alpha][proc]['cross_rate']['rate'] == 0
            # Consistency of REPORTED enclosure counts only: individual
            # upper score certificates are not retained in enclosure.json.
            assert enc['cells'][cell][alpha][proc] == {
                'certified crossing':0,'certified no crossing':100,'unresolved':0}
    print(f'{cell}: primary crossings=0/100 at both levels; final scan/single logs={finals[0]:.3f}/{finals[1]:.3f}')
assert all_exhausted == 8912
assert enc['lower_score_mismatches'] == 0
print('Active certificate statuses: 8912/18000 budget exhausted; no recorded fallbacks.')
print('No lost computed-lower-score decision from the 1/3 weights.')
print('Frozen decisions/enclosure counts aggregated as reported; upper bounds not independently reproduced.')
