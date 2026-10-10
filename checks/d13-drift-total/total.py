"""Total diagnostic records for claim 055, reusing the D14 CEV adapter.

log_e is the enlarged-null score; raw_log_e is claim 054's score for
comparison only. Neither floating-point value is a certified e-value.
Keep every returned record and the original panel size. Configuration
errors and unhandled exceptions must stop a run, never delete its rows.
These are exact-price likelihood formulas, not rounded-cell likelihoods.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp


def load(name, relative):
    spec = spec_from_file_location(name, Path(__file__).resolve().parents[1]/relative)
    result = module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


cev = load('drift_total_cev', 'd14-cev-domain/total.py')
gaussian = load('drift_total_gaussian', 'd13-drift-null-input/profile.py')


def score_total_path(catalogue, times, prices, split):
    """Preserve claim 054's domain/status contract, then enlarge its null.

    An infinite Gaussian supremum is a valid boundary with zero evidence,
    recorded as gaussian_sup_unbounded, not as a numerical failure.
    No candidate confidence set for the enlarged null is returned.
    """
    # Materialize iterators once; the base adapter validates the fixed design.
    catalogue = tuple(tuple(pair) for pair in catalogue)
    times, prices = tuple(times), tuple(prices)
    base = cev.score_total_path(catalogue, times, prices, split)
    result = {key: base[key] for key in ('fit', 'training', 'evaluation', 'status', 'detail')}
    result.update(raw_log_e=base['log_e'], log_e=base['log_e'], log_gaussian_sup=None)
    if 'outside_domain' in base['status'] or 'numerical_failure' in base['status']:
        return result
    statuses = [status for status in base['status'] if status != 'ok']
    try:
        # Include the final TRAINING price but no earlier training increment.
        bound = gaussian.log_null_sup(times[split:], prices[split:])
        nulls = tuple(i for i, (p, _) in enumerate(catalogue) if mp.mpf(p) <= 1)
        numerator = base['evaluation'][base['fit']]
        old_maximum = max(base['evaluation'][i] for i in nulls)
        score = gaussian.enlarged_log_score(numerator, old_maximum, bound)
        if mp.isnan(score) or score == mp.inf:
            raise ArithmeticError('computed enlarged score violates finiteness')
        if score > base['log_e']:
            raise ArithmeticError('computed enlarged score exceeds the raw score')
        result.update(log_e=score, log_gaussian_sup=bound)
        if bound == mp.inf:
            statuses.append('gaussian_sup_unbounded')
    except (ArithmeticError, ValueError) as error:
        # Never fall back to the raw score: it lacks the enlarged-null guarantee.
        result.update(log_e=-mp.inf, detail=f'Gaussian profile: {type(error).__name__}: {error}')
        statuses.append('numerical_failure')
    result['status'] = tuple(statuses) or ('ok',)
    return result
