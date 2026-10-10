"""Causal, finite-horizon empirical monitor; no likelihood or e-value evaluator.

The caller fixes one common schedule and scoring backend before calibration.
An infinite_profile label requires an established infinite denominator, not a
failed optimizer. Every failed/missing prefix remains in the path summary.
"""
from dataclasses import dataclass
from fractions import Fraction
import importlib.util
import math
from pathlib import Path
import sys
from typing import Mapping, Sequence


ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    'd36_monitor_base', ROOT/'checks/d35-empirical-review/calibrate.py')
base = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = base
spec.loader.exec_module(base)


@dataclass(frozen=True)
class PrefixLog:
    log_numerator: float | None = None
    log_denominator: float | None = None
    status: str = 'failure'
    channel: str = 'numerical'
    numerator_kind: str = 'predictive_mixture'
    reason: str | None = None


def prefix_score(result: PrefixLog | None):
    if result is None:
        return base.Score(-1., None, 'missing_prefix')
    if result.channel != 'numerical' or result.numerator_kind != 'predictive_mixture':
        return base.Score(-1., None, 'invalid_score_channel')
    if result.status in {'failure', 'numerical_failure', 'unsupported_history',
                         'unsupported_observation', 'fit_failure', 'clock_failure'}:
        return base.Score(-1., None, result.status)
    q, d = result.log_numerator, result.log_denominator
    if (result.status == 'infinite_profile' and q is not None
            and math.isfinite(q) and d == math.inf):
        # Zero certified parametric evidence belongs to a separate channel.
        return base.Score(-1., None, 'infinite_profile')
    if result.status != 'finite' or q is None or d is None:
        return base.Score(-1., None, 'invalid_prefix_result')
    # The finite numerical backend is fixed for every calibration/target path.
    # This transforms log Q - log D; it does not certify either likelihood.
    return base.score_fit(base.FitPair(d, q))


def fixed_schedule(schedule):
    out = tuple(schedule)
    if (not out or any(type(t) is not int or t <= 0 for t in out)
            or list(out) != sorted(set(out))):
        raise ValueError('fix positive increasing distinct checkpoints')
    return out


class Monitor:
    def __init__(self, schedule, cutoff):
        self.schedule = fixed_schedule(schedule)
        base.flag(-1., cutoff)  # validate once; +infinity is a valid cutoff
        if cutoff < 0:
            raise ValueError('monitor cutoff must include the zero floor')
        self.cutoff = cutoff
        self.details = {}
        self.records = {}
        self.maximum = -1.
        self.first_alarm = None

    def update(self, checkpoint, result: PrefixLog | None):
        index = len(self.details)
        if (index == len(self.schedule) or type(checkpoint) is not int
                or checkpoint != self.schedule[index]):
            raise ValueError('consume exactly the next declared checkpoint')
        score = prefix_score(result)
        self.records[checkpoint] = result
        self.details[checkpoint] = score
        self.maximum = max(self.maximum, score.value)
        if self.first_alarm is None and base.flag(score.value, self.cutoff):
            self.first_alarm = checkpoint
        return score

    def finish_missing(self):
        """Retain genuinely unavailable suffix slots, never stop calibration at an alarm."""
        for t in self.schedule[len(self.details):]:
            self.update(t, None)
        return self


def summarize(results: Mapping[int, PrefixLog | None], schedule, *, cutoff=math.inf):
    monitor = Monitor(schedule, cutoff)
    if any(key not in monitor.schedule for key in results):
        raise ValueError('result outside the declared checkpoint schedule')
    for t in monitor.schedule:
        monitor.update(t, results.get(t))
    return monitor


def calibrate(paths: Sequence[Mapping[int, PrefixLog | None]], schedule,
              alpha: Fraction):
    schedule = fixed_schedule(schedule)
    summaries = [summarize(path, schedule) for path in paths]
    cutoff = max(0., base.rank_cutoff([path.maximum for path in summaries], alpha))
    return cutoff, summaries
