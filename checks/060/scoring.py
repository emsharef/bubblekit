"""Total claim-060 diagnostic records; retain failures and the original m.

log_e is claim 060, drift_log_e claim 055, raw_log_e claim 054.
No fitted parameter establishes the fixed floor/cap or actual-law premise.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

_spec = spec_from_file_location('envelope060', Path(__file__).with_name('envelope.py'))
envelope = module_from_spec(_spec)
_spec.loader.exec_module(envelope)
drift = envelope.load('drift060', 'd13-drift-total/total.py')
log_envelope = envelope.log_envelope


def score_total_path(catalogue, times, prices, split, floor, cap):
    floor, cap = envelope.declaration(floor, cap)
    catalogue = tuple(tuple(pair) for pair in catalogue)
    times, prices = tuple(times), tuple(prices)
    if isinstance(split, bool) or not isinstance(split, int) or len(times)-1-split < 2:
        raise ValueError('integer split leaving at least two evaluation increments required')
    base = drift.score_total_path(catalogue,times,prices,split)
    result = {key: base[key] for key in ('fit','training','evaluation','status','detail','raw_log_e')}
    result.update(log_e=base['log_e'], drift_log_e=base['log_e'], log_jump_envelope=None)
    if 'outside_domain' in base['status'] or 'numerical_failure' in base['status']:
        return result
    statuses = [s for s in base['status'] if s != 'ok']
    try:
        bound = log_envelope(times[split:],prices[split:],floor,cap)
        if mp.isnan(bound) or bound == mp.inf:
            raise ArithmeticError('jump envelope must be finite or zero')
        if all(mp.mpf(x) > 0 for x in prices[split:]) and bound == -mp.inf:
            raise ArithmeticError('positive path has zero jump envelope')
        nulls = tuple(i for i,(p,_) in enumerate(catalogue) if mp.mpf(p) <= 1)
        old = max(base['evaluation'][i] for i in nulls)
        numerator = base['evaluation'][base['fit']]
        score = envelope.gaussian.enlarged_log_score(
            numerator,old,max(base['log_gaussian_sup'],bound))
        if mp.isnan(score) or score == mp.inf or score > base['log_e']:
            raise ArithmeticError('jump score violates finiteness or ordering')
        result.update(log_e=score,log_jump_envelope=bound)
    except (ArithmeticError,ValueError) as error:
        result.update(log_e=-mp.inf, detail=f'Jump envelope: {type(error).__name__}: {error}')
        statuses.append('numerical_failure')
    result['status'] = tuple(dict.fromkeys(statuses)) or ('ok',)
    return result
