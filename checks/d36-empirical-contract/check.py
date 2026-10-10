"""Independent finite checks of the numerical-to-empirical D36 handoff.
No data fitting, simulator, or sequential-validity claim.
"""
from fractions import Fraction
import importlib.util
from itertools import product
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    'd36_contract_backend', ROOT/'checks/d36-monitor-calibration/monitor.py')
m = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = m
spec.loader.exec_module(m)
P = m.PrefixLog
# Expectations are calculated here without calling the inherited score/rank code.
cases = [
    (None, -1.),
    (P(status='failure'), -1.),
    (P(1., 0., 'unsupported'), -1.),
    (P(-1., 0., 'finite'), 0.),
    (P(0., 0., 'finite'), 0.),
    (P(1., 0., 'finite'), 0.5),
    (P(2., math.inf, 'infinite_profile'), -1.),
    (P(2., math.inf, 'finite'), -1.),
]
schedule = (1, 2, 3)
n = 0
for trace in product(cases, repeat=3):
    expected = [x[1] for x in trace]
    for cutoff in (0., 0.25, 0.5, math.inf):
        monitor = m.Monitor(schedule, cutoff)
        for t, (result, value) in zip(schedule, trace):
            got = monitor.update(t, result)
            assert math.isclose(got.value, value, abs_tol=1e-15)
            assert math.isclose(monitor.maximum, max(expected[:t]), abs_tol=1e-15)
            first = next((i+1 for i, x in enumerate(expected[:t]) if x>cutoff), None)
            assert monitor.first_alarm == first
        n += 1
# Failed references stay in the rank denominator. Cutoff flooring removes,
# rather than creates, rejections. Check each possible held-out value directly.
for sample in product((-1., 0., 0.5), repeat=4):
    paths = []
    for score in sample:
        obj = { -1.: None, 0.: P(0., 0., 'finite'), 0.5: P(1., 0., 'finite') }[score]
        paths.append({1: obj})
    # ceil((n+1)(1-alpha)) = ceil(5*1/2) = 3, for this fixture.
    raw = sorted(sample)[2]
    cutoff, summaries = m.calibrate(paths, (1,), Fraction(1, 2))
    assert cutoff == max(0., raw)
    assert [s.maximum for s in summaries] == list(sample)
    for value in (-1., 0., 0.5):
        assert not value>cutoff or value>raw
        assert not (value<=0 and value>cutoff)
# Strict ties and interruption keep the earlier crossing and every missing slot.
a = m.Monitor(schedule, 0.)
a.update(1, P(1., 0., 'finite'))
a.finish_missing()
assert a.first_alarm == 1 and a.maximum == 0.5
assert [a.details[t].value for t in schedule] == [0.5, -1., -1.]
assert m.prefix_score(P(2., math.inf, 'infinite_profile')).status == 'infinite_profile'
assert m.prefix_score(P(2., math.inf, 'finite')).value == -1.
cutoff, summaries = m.calibrate([{1: None}]*499, (1,), Fraction(1, 20))
assert len(summaries) == 499 and all(s.maximum == -1. for s in summaries)
assert cutoff == 0.
print(f'PASS: {n} prefix-trace/cutoff cases, 81 rank samples, and failure/infinity/first-alarm fixtures.')

# Provenance is a guard on declarations, not a proof of the backend calculation.
for result in (P(1., 0., 'finite', channel='certified'),
               P(1., 0., 'finite', numerator_kind='optimized_alternative')):
    score = m.prefix_score(result)
    assert score.value == -1. and score.status == 'invalid_score_channel'
reason = P(status='unsupported_history', reason='missing_bar_before_prefix')
monitor = m.Monitor((1,), 0.)
monitor.update(1, reason)
assert monitor.records[1] is reason
assert monitor.details[1].status == 'unsupported_history'
assert monitor.records[1].reason == 'missing_bar_before_prefix'
print('PASS: certified/optimized channels excluded; original history reason retained.')
