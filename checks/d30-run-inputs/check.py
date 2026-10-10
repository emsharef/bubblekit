"""Deterministic experiment-044 integration checks; no simulation or smoke run.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d30-run-inputs/check.py

Uses fixed price arrays and injected numerical failures. No model samples,
comparator calibration, experimental outputs or pool workers are created.
"""
from fractions import Fraction as F
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

import numpy as np

root = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('d30_run_inputs', root/'experiments/044/run.py')
run = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = run
spec.loader.exec_module(run)

prices = np.array([1., 1.01, .99, 1.02])
durations = np.full(3, 1/3)
z = np.array([0., .2, -.1])
qz = [F.from_float(float(x)) for x in z]
qtv = sum(abs(b-a) for a, b in zip(qz, qz[1:]))
assert np.abs(np.diff(z)).sum() == .5
assert qtv > F(1, 2)
exact_prices = [F.from_float(float(x)) for x in prices]
exact_dt = [F.from_float(float(x)) for x in durations]
unrepaired = run.cert072.certify(exact_prices, exact_dt, F(1, 2), (0, 0), qz)
assert unrepaired.status == 'invalid witness'

# Supply a fixed candidate instead of drawing a path or benchmarking a solver.
# The real checker must see exact feasibility, including after conversion.
with patch.object(run, 'solve', return_value=(np.zeros(2), z, 0., 0., 0.)), \
     patch.object(run.cert072, 'certify', wraps=run.cert072.certify) as checker:
    result, info = run.profile(prices, durations, .5)
    repaired = checker.call_args.kwargs['primal']
    assert sum(abs(b-a) for a, b in zip(repaired, repaired[1:])) == F(1, 2)
    assert sum(repaired) == sum(qz)
    assert info['primal_repaired_exactly'] is True
    assert result.status == 'enclosed supplied witness'

# An already feasible witness stays unchanged.
with patch.object(run, 'solve', return_value=(np.zeros(2), np.zeros(3), 0., 0., 0.)), \
     patch.object(run.cert072, 'certify', wraps=run.cert072.certify) as checker:
    result, info = run.profile(prices, durations, .5)
    assert checker.call_args.kwargs['primal'] == [F(0)]*3
    assert info['primal_repaired_exactly'] is False

cell = dict(name='fixed-integration-array', kind='null', n=3, V=.5, shape='flat', k=.3, reps=2)
for failure in (np.linalg.LinAlgError('fixed singular system'),
                ValueError('fixed nonfinite witness'),
                FloatingPointError('fixed floating-point failure')):
    with patch.object(run, 'profile', side_effect=failure):
        result = run.score(prices, cell, .5, None)
        assert result['decision'] == 'unresolved profile'
        assert result['float_reject'] is False and result['gap_above_target'] is True
        assert result['profile_status'].endswith(type(failure).__name__)

# Batch retention: one numerical failure must not discard its neighbour.
# The simulation entry point is replaced completely by the two fixed arrays.
cell = cell | {'V': 0.}
real_profile = run.profile
calls = 0


def fail_first(*args):
    global calls
    calls += 1
    if calls == 1:
        raise np.linalg.LinAlgError('fixed first record failure')
    return real_profile(*args)


comparison = {'gsadf': None, 'jkp_m2': 'not run', 'jkp_m1': 'not run'}
with patch.object(run, 'simulate', return_value=np.stack([prices, prices])), \
     patch.object(run, 'profile', side_effect=fail_first), \
     patch.object(run, 'comparators', return_value=comparison):
    part = run.job((cell, 0, [1, 2], 2))
assert len(part['records']) == 2
assert [row['i'] for row in part['records']] == [0, 1]
assert part['records'][0]['scores'][0]['decision'] == 'unresolved profile'
assert part['records'][0]['scores'][0]['privileged_decision'] == 'unresolved profile'
assert part['records'][1]['scores'][0]['decision'] == 'certified noncrossing'
with patch.object(run, 'cells', return_value=[cell]):
    summary, _ = run.summarize([part], {}, set())
row = summary[cell['name']]
assert row['records'] == 2 and row['complete']
assert row['V=0.0']['decisions'] == {'unresolved profile': 1, 'certified noncrossing': 1}
assert row['V=0.0']['certified_rejection_rate'] == 0
assert row['V=0.0']['wilson95'] == run.wilson(0, 2)

# The existing comparator wrappers already retain their expected exceptions.
with patch.object(run.r021.psy, 'sadf_gsadf', side_effect=ArithmeticError('fixed GSADF failure')), \
     patch.object(run.r021.jkp, 'grid', side_effect=ValueError('fixed JKP failure')):
    out = run.comparators(prices, 3)
    assert out['gsadf'] is None and out['gsadf_status'] == 'error: ArithmeticError'
    assert out['jkp_m2'] == 'failed' and out['jkp_m1'] == 'failed'

print('PASS: rational TV boundary repaired, feasible witness unchanged, '
      'three numerical failure types retained, two-record batch/denominator preserved, '
      'existing comparator failure guards verified; no model draws')
