"""Claim 061 diagnostic finite-budget score; failures retain zero and original m."""
from importlib.util import module_from_spec,spec_from_file_location
from pathlib import Path
from mpmath import mp

_spec = spec_from_file_location('profile061',Path(__file__).with_name('profile.py'))
profile = module_from_spec(_spec)
_spec.loader.exec_module(profile)
coarse = profile.load('coarse061','060/scoring.py')
log_enclosure = profile.log_enclosure


def score_total_path(catalogue,times,prices,split,floor,cap,max_boxes=128,log_tolerance=0):
    floor,cap = profile.old.declaration(floor,cap)
    if isinstance(max_boxes,bool) or not isinstance(max_boxes,int) or max_boxes < 1:
        raise ValueError('positive integer box budget required')
    tolerance = mp.mpf(log_tolerance)
    if not mp.isfinite(tolerance) or tolerance < 0:
        raise ValueError('finite nonnegative log-gap tolerance required')
    catalogue = tuple(tuple(pair) for pair in catalogue)
    times,prices = tuple(times),tuple(prices)
    base = coarse.score_total_path(catalogue,times,prices,split,floor,cap)
    result = dict(base,coarse_log_e=base['log_e'],enclosure=None)
    if 'outside_domain' in base['status'] or 'numerical_failure' in base['status']:
        return result
    statuses = [s for s in base['status'] if s != 'ok']
    try:
        enclosed = log_enclosure(times[split:],prices[split:],floor,cap,max_boxes,tolerance)
        bound = enclosed['log_upper']
        if mp.isnan(bound) or bound == mp.inf:
            raise ArithmeticError('enclosure must be finite or zero')
        if all(mp.mpf(x) > 0 for x in prices[split:]) and bound == -mp.inf:
            raise ArithmeticError('positive path has zero envelope')
        # The old analytic envelope is itself a valid upper bound. Taking
        # this minimum also preserves its support conventions explicitly.
        bound = min(bound,base['log_jump_envelope'])
        g = profile.gaussian.log_null_sup(times[split:],prices[split:])
        old = max(base['evaluation'][j] for j,(p,_) in enumerate(catalogue) if mp.mpf(p) <= 1)
        score = profile.gaussian.enlarged_log_score(base['evaluation'][base['fit']],old,max(g,bound))
        if mp.isnan(score) or score == mp.inf or not base['log_e'] <= score <= base['drift_log_e']:
            raise ArithmeticError('profile score violates finiteness or ordering')
        result.update(log_e=score,enclosure=enclosed)
    except (ArithmeticError,ValueError) as error:
        result.update(log_e=-mp.inf,detail=f'Jump profile: {type(error).__name__}: {error}')
        statuses.append('numerical_failure')
    result['status'] = tuple(dict.fromkeys(statuses)) or ('ok',)
    return result
