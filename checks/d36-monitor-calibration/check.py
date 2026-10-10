"""Finite D36 empirical-monitor interface fixtures, using the D35 adapter.

No intraday model, horizon, data selection or experiment is chosen here.
The checkpoint lists are synthetic interface tests, not the future design.
"""
from fractions import Fraction
import importlib.util
from itertools import product
import math
from pathlib import Path
import sys
from monitor import PrefixLog, Monitor, prefix_score, summarize, calibrate


ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    'd36_calibration', ROOT/'checks/d35-empirical-review/calibrate.py')
cal = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = cal
spec.loader.exec_module(cal)


def main():
    schedule = [1, 2, 3, 4, 5]
    choices = (None, cal.FitPair(0., 0.), cal.FitPair(0., 1.))
    checked = 0
    for fits in product(choices, repeat=5):
        full, _ = cal.score_window(dict(zip(schedule, fits)), schedule, mode='maximum')
        for cutoff in (-1., 0., .5, 1., math.inf):
            first = None
            prefix_max = -math.inf
            for t, fit in zip(schedule, fits):
                current = cal.score_fit(fit).value
                prefix_max = max(prefix_max, current)
                if first is None and cal.flag(current, cutoff):
                    first = t
                # Only observed fits enter here; future failure cannot erase first.
                offline_prefix, _ = cal.score_window(
                    dict(zip(schedule[:t], fits[:t])), schedule[:t], mode='maximum')
                assert prefix_max == offline_prefix
                assert (first is not None) == cal.flag(prefix_max, cutoff)
            assert (first is not None) == cal.flag(full, cutoff)
            checked += 1
    # Explicit persistence: future missing or unsuccessful fit does not undo a flag.
    high = cal.FitPair(0., 1.)
    bad = cal.FitPair(0., 1., null_ok=False)
    score, detail = cal.score_window({1:high,2:bad},[1,2,3],mode='maximum')
    assert cal.flag(score,0.) and detail[2].value == detail[3].value == -1.

    # A finite exchangeable window law showing why pointwise ranks are insufficient.
    # 500 windows: each has a single high score, at one of 25 times, 20 per time.
    # Designate each window as test and all other 499 as calibration in turn.
    alpha = Fraction(1,20)
    point_flags = [0]*25
    any_point_flags = max_flags = 0
    for test_id in range(500):
        high_time = test_id//20
        crossed = False
        for t in range(25):
            calibration = [float(i//20 == t) for i in range(500) if i != test_id]
            cutoff = cal.rank_cutoff(calibration,alpha)
            flag = cal.flag(float(high_time == t),cutoff)
            point_flags[t] += flag
            crossed = crossed or flag
        any_point_flags += crossed
        max_flags += cal.flag(1.,cal.rank_cutoff([1.]*499,alpha))
    assert point_flags == [20]*25
    assert all(Fraction(count,500) <= alpha for count in point_flags)
    assert any_point_flags == 500 and max_flags == 0
    # Streaming adapter: finite scores reuse D35; infinite profiles are valid
    # empirical nonfinite cases, distinct from unresolved/malformed numerics.
    high = PrefixLog(2., 1., 'finite')
    low = PrefixLog(-2., 1., 'finite')
    infinite = PrefixLog(0., math.inf, 'infinite_profile')
    assert prefix_score(high).value == .5
    assert prefix_score(low).value == 0.
    assert prefix_score(infinite).value == -1.
    assert prefix_score(infinite).status == 'infinite_profile'
    for changed in (
        PrefixLog(2.,1.,'finite',channel='certified'),
        PrefixLog(2.,1.,'finite',numerator_kind='optimized_alternative'),
    ):
        assert prefix_score(changed).value == -1.
        assert prefix_score(changed).status == 'invalid_score_channel'
    gap = PrefixLog(status='unsupported_history',reason='missing required bar')
    failed_monitor = summarize({1:gap},[1,2])
    assert failed_monitor.details[1].status == 'unsupported_history'
    assert failed_monitor.records[1].reason == 'missing required bar'
    assert failed_monitor.records[2] is None
    for invalid in (PrefixLog(), PrefixLog(math.inf,math.inf,'finite'),
                    PrefixLog(0.,0.,'infinite_profile'),
                    PrefixLog(0.,math.inf,'finite'), PrefixLog(status='unknown')):
        assert prefix_score(invalid).value == -1.
    for trace in product((None, low, high, infinite),repeat=4):
        for threshold in (0.,.25,.5,math.inf):
            scores = [prefix_score(value).value for value in trace]
            expected_first = next((i+1 for i,value in enumerate(scores)
                                   if value>threshold),None)
            streamed = Monitor([1,2,3,4],threshold)
            for i,value in enumerate(trace,1):
                streamed.update(i,value)
                assert streamed.first_alarm == next((j+1 for j in range(i)
                                                     if scores[j]>threshold),None)
            offline = summarize(dict(enumerate(trace,1)),[1,2,3,4],cutoff=threshold)
            assert streamed.first_alarm == offline.first_alarm == expected_first
            assert streamed.maximum == offline.maximum == max(scores)
    stopped = Monitor([1,2,3],0.)
    stopped.update(1,high)
    stopped.finish_missing()
    assert stopped.first_alarm == 1 and stopped.maximum == .5
    assert len(stopped.details) == 3
    assert all(stopped.details[t].value == -1 for t in (2,3))
    cutoff, paths = calibrate([{}]*19,[1,2],alpha)
    assert cal.rank_cutoff([p.maximum for p in paths],alpha) == -1
    assert cutoff == 0 and len(paths) == 19
    assert all(p.maximum == -1 for p in paths)
    assert summarize({1:low},[1,2],cutoff=cutoff).first_alarm is None
    assert summarize({1:infinite},[1,2],cutoff=cutoff).first_alarm is None
    assert summarize({1:high},[1,2],cutoff=cutoff).first_alarm == 1
    assert calibrate([{}]*18,[1,2],alpha)[0] == math.inf
    # Calibration must retain the later maximum even after an early crossing.
    later = PrefixLog(4.,1.,'finite')
    complete = summarize({1:high,2:later},[1,2],cutoff=.25)
    assert complete.first_alarm == 1
    assert complete.maximum == prefix_score(later).value > .5
    for operation in (
        lambda: Monitor([2,1],0.),
        lambda: Monitor([1],-1.),
        lambda: Monitor([1],0.).update(2,high),
        lambda: stopped.update(3,high),
        lambda: summarize({3:high},[1,2]),
    ):
        try:
            operation()
        except ValueError:
            pass
        else:
            raise AssertionError('invalid schedule use accepted')
    print(f'PASS: {checked} finite trace/cutoff cases; first alarms persist through failures.')
    print('Exchangeable fixture: pointwise 20/500 at each time, union 500/500,')
    print('maximum-calibrated crossing 0/500 (strict ties retained). No real-data guarantee.')
    print('PASS: 1,024 streaming trace/cutoff cases, infinite-profile distinction,')
    print('retained truncated paths, score-channel provenance, full-path calibration,')
    print('strict calibration and schedule enforcement.')


if __name__ == '__main__':
    main()
