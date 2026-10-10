"""Claim 059 total diagnostic adapter; keep all records and original m.

log_e is the switch-null score, drift_log_e is claim 055, raw_log_e is
claim 054. The predeclared cuts index evaluation increments, not full-path
observations. No null coverage is inferred from a fitted cut or an ok status.
Configuration errors stop; observed/numerical failures give zero evidence.
"""
from mpmath import mp
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

_spec = spec_from_file_location('profile059', Path(__file__).with_name('profile.py'))
profile = module_from_spec(_spec)
_spec.loader.exec_module(profile)
load, validate_cuts = profile.load, profile.validate_cuts
log_null_sup, gaussian = profile.log_null_sup, profile.gaussian

drift = load('drift059', 'd13-drift-total/total.py')


def score_total_path(catalogue, times, prices, split, cuts):
    catalogue = tuple(tuple(pair) for pair in catalogue)
    times, prices = tuple(times), tuple(prices)
    if isinstance(split, bool) or not isinstance(split, int):
        raise ValueError('integer training split required')
    cuts = validate_cuts(cuts, len(times)-1-split, minimum=2)
    base = drift.score_total_path(catalogue, times, prices, split)
    result = {key: base[key] for key in ('fit','training','evaluation','status','detail','raw_log_e')}
    result.update(log_e=base['log_e'], drift_log_e=base['log_e'], log_switch_sup=None)
    if 'outside_domain' in base['status'] or 'numerical_failure' in base['status']:
        return result
    statuses = [s for s in base['status'] if s != 'ok']
    try:
        bound = log_null_sup(times[split:], prices[split:], cuts)
        if mp.isnan(bound) or bound < base['log_gaussian_sup']:
            raise ArithmeticError('switch supremum violates stationary-family domination')
        nulls = tuple(i for i,(p,_) in enumerate(catalogue) if mp.mpf(p) <= 1)
        numerator = base['evaluation'][base['fit']]
        old = max(base['evaluation'][i] for i in nulls)
        score = gaussian.enlarged_log_score(numerator, old, bound)
        if mp.isnan(score) or score == mp.inf or score > base['log_e']:
            raise ArithmeticError('switch score violates finiteness or drift-score ordering')
        result.update(log_e=score, log_switch_sup=bound)
        if bound == mp.inf:
            statuses.append('switch_sup_unbounded')
    except (ArithmeticError, ValueError) as error:
        result.update(log_e=-mp.inf, detail=f'Switch profile: {type(error).__name__}: {error}')
        statuses.append('numerical_failure')
    result['status'] = tuple(dict.fromkeys(statuses)) or ('ok',)
    return result
