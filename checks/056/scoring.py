"""Total diagnostic bounded-drift score; no numerical certification.

Keep every record and the original family size. Invalid fixed configuration
stops a run. Returned numerical failures receive zero evidence, never the raw
score. Exact nonnegative prices are the mathematical observation domain.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp


def load(name, relative):
    spec = spec_from_file_location(name, Path(__file__).resolve().parents[1]/relative)
    result = module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


cev = load('cev056', 'd14-cev-domain/total.py')
profile = load('profile056', '056/profile.py')


def score_total_path(catalogue, times, prices, split, lower, upper):
    lower, upper = profile.interval(lower, upper)  # configuration, not a data failure
    catalogue = tuple(tuple(pair) for pair in catalogue)
    times, prices = tuple(times), tuple(prices)
    base = cev.score_total_path(catalogue, times, prices, split)
    result = {key: base[key] for key in ('fit', 'training', 'evaluation', 'status', 'detail')}
    result.update(raw_log_e=base['log_e'], log_e=base['log_e'], log_gaussian_sup=None)
    if 'outside_domain' in base['status'] or 'numerical_failure' in base['status']:
        return result
    statuses = [status for status in base['status'] if status != 'ok']
    try:
        bound = profile.log_null_sup(times[split:], prices[split:], lower, upper)
        nulls = tuple(i for i, (p, _) in enumerate(catalogue) if mp.mpf(p) <= 1)
        numerator = base['evaluation'][base['fit']]
        old = max(base['evaluation'][i] for i in nulls)
        score = profile.gaussian.enlarged_log_score(numerator, old, bound)
        if mp.isnan(score) or score == mp.inf or score > base['log_e']:
            raise ArithmeticError('computed score violates finiteness or raw-score domination')
        result.update(log_e=score, log_gaussian_sup=bound)
        if bound == mp.inf:
            statuses.append('gaussian_sup_unbounded')
    except (ArithmeticError, ValueError) as error:
        result.update(log_e=-mp.inf, detail=f'Bounded Gaussian profile: {type(error).__name__}: {error}')
        statuses.append('numerical_failure')
    result['status'] = tuple(statuses) or ('ok',)
    return result
