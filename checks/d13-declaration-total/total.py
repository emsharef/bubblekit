"""Claim 058 diagnostic pipeline; exact prices, not certified arithmetic.

log_e is E^safe; raw_log_e is E^dec, for comparison only. The fixed catalogue,
grids, split, reference density, cap and failure budget must precede all data.
Earlier prices end no later than time zero; their increments precede the test.
This checks chronology, NOT the unchanged-parameter or full-record conditional
law premises of claim 058. Its guarantee is unconditional across earlier
records, not conditional on the observed declaration. Retain every record and
the original panel size. Configuration errors stop a run.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp


def load(name, relative):
    spec = spec_from_file_location(name, Path(__file__).resolve().parents[1]/relative)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


declaration = load('total_declaration058', '058/declaration.py')
rectangle = load('total_rectangle058', '057/scoring.py')
drift = load('total_drift058', 'd13-drift-total/total.py')


def score_total_path(catalogue, times, prices, split, earlier_times, earlier_prices,
                     failure_budget, cap, reference_drift=0, reference_scale='.3'):
    """Compose the declaration, rectangle/fallback scorer and coverage correction.

    Q_dec=0 is a mathematical unrestricted-null fallback. A numerical failure
    in the declaration is instead a zero record, never an uncorrected score.
    A shared endpoint at zero must agree with the test's known start.
    """
    catalogue = tuple(tuple(pair) for pair in catalogue)
    times, prices = tuple(times), tuple(prices)
    earlier_times = tuple(mp.mpf(t) for t in earlier_times)
    earlier_prices = tuple(earlier_prices)
    delta, c, b0, s0 = map(mp.mpf, (failure_budget, cap, reference_drift, reference_scale))
    if not all(mp.isfinite(x) for x in (delta, c, b0, s0)) or not 0 < delta < 1 or c < 1 or s0 <= 0:
        raise ValueError('finite reference, positive scale, cap>=1 and 0<budget<1 required')
    if len(earlier_times) != len(earlier_prices) or len(earlier_times) < 3:
        raise ValueError('at least two earlier increments with matching prices required')
    if (any(not mp.isfinite(t) for t in earlier_times) or earlier_times[-1] > 0
            or any(a >= b for a, b in zip(earlier_times, earlier_times[1:]))):
        raise ValueError('earlier grid must increase finitely and end no later than zero')
    # Validate the entire test configuration even when earlier observations fail.
    # Reuse this unrestricted result if the declaration has zero residuals.
    base = drift.score_total_path(catalogue, times, prices, split)
    result = {key: base[key] for key in ('fit', 'training', 'evaluation', 'status', 'detail')}
    result.update(log_e=-mp.inf, raw_log_e=-mp.inf, log_gaussian_sup=None,
                  declaration=None, failure_budget=delta, cap=c)

    def masked(status, detail):
        statuses = tuple(s for s in result['status'] if s != 'ok')
        result.update(log_e=-mp.inf, raw_log_e=-mp.inf,
                      status=tuple(dict.fromkeys(statuses+(status,))), detail=detail)
        return result

    try:
        earlier = tuple(mp.mpf(x) for x in earlier_prices)
    except (TypeError, ValueError):
        return masked('earlier_outside_domain', 'non-real earlier observation')
    if any(not mp.isfinite(x) or x <= 0 for x in earlier):
        return masked('earlier_outside_domain', 'earlier observations must be finite and positive')
    if earlier_times[-1] == 0 and earlier[-1] != mp.mpf(prices[0]):
        return masked('earlier_outside_domain', 'shared endpoint differs from known test start')
    try:
        durations = tuple(b-a for a, b in zip(earlier_times, earlier_times[1:]))
        returns = tuple(mp.log(b)-mp.log(a) for a, b in zip(earlier, earlier[1:]))
        chosen = declaration.declare(returns, durations, delta, b0, s0)
        if chosen['mode'] == 'rectangle':
            # Validate computed bounds before they become scorer configuration.
            bounds = rectangle.profile.rectangle(*chosen['bounds'])
            base = rectangle.score_total_path(catalogue, times, prices, split, *bounds)
        elif chosen['mode'] != 'unrestricted' or chosen['bounds'] is not None:
            raise ArithmeticError('invalid declaration mode or fallback bounds')
        result.update({key: base[key] for key in
                       ('fit', 'training', 'evaluation', 'status', 'detail', 'log_gaussian_sup')})
        result.update(declaration=chosen, raw_log_e=base['log_e'])
        result['log_e'] = declaration.corrected_log_score(base['log_e'], c, delta)
    except (ArithmeticError, ValueError) as error:
        return masked('numerical_failure', f'Declaration pipeline: {type(error).__name__}: {error}')
    return result
