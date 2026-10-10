"""Claim 062 diagnostics: joint Gaussian profile and shared-power forecast.

Exact-price formulas evaluated with mpmath, NOT certified upper arithmetic.
Numerical rank uncertainty returns zero evidence; no ridge or fitted-covariance
fallback. One record is a global panel score, not a vector of name discoveries.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp


spec = spec_from_file_location('pool_cev', Path(__file__).resolve().parents[1]
                              / 'd13-cev-input/kernels.py')
kernels = module_from_spec(spec)
spec.loader.exec_module(kernels)


def profile_returns(rows, gaps):
    """Rows are increments, columns names; omit the price Jacobian."""
    gaps = tuple(kernels.number(d, 'gap', True) for d in gaps)
    rows = tuple(tuple(mp.mpf(x) for x in row) for row in rows)
    if any(not mp.isfinite(x) for row in rows for x in row):
        raise ValueError('finite signed returns required')
    if not gaps or len(rows) != len(gaps) or not rows[0]:
        raise ValueError('nonempty matching returns and gaps required')
    n, m = len(gaps), len(rows[0])
    if any(len(row) != m for row in rows):
        raise ValueError('rectangular returns required')
    a = tuple(mp.fsum(row[i] for row in rows)/mp.fsum(gaps) for i in range(m))
    z = mp.matrix([[ (rows[j][i]-a[i]*gaps[j])/mp.sqrt(gaps[j])
                     for j in range(n)] for i in range(m)])
    s = z*z.T/n
    result = {'mean': a, 'covariance': s, 'log_sup': mp.inf,
              'status': 'rank_barrier'}
    if m >= n:
        return result
    values = mp.eigsy(s, eigvals_only=True)
    # Dropping an uncertain record is conservative, but does not certify
    # arithmetic on the records retained below.
    if min(values) <= 100*mp.eps*max(abs(s[i, i]) for i in range(m)):
        result['status'] = 'singular_or_uncertain'
        return result
    factor = mp.cholesky(s)
    logdet = 2*mp.fsum(mp.log(factor[i, i]) for i in range(m))
    value = -mp.mpf(n*m)/2*(mp.log(2*mp.pi)+1)
    value -= mp.mpf(n)/2*logdet + mp.mpf(m)/2*mp.fsum(mp.log(d) for d in gaps)
    result.update(log_sup=value, status='ok')
    return result


def score_panel(powers, scales, times, prices, split):
    """Scales[i] is name i's ordered scale catalogue; powers are shared.

    Fixed configuration errors stop the run. Observation/numerical failures
    are retained as zero global evidence, with explicit status. All training
    maximizations use only the training prefix. The complete result is still
    a diagnostic, not a numerical certification of claim 062.
    """
    powers = tuple(kernels.number(p, 'power', True) for p in powers)
    scales = tuple(tuple(kernels.number(k, 'scale', True) for k in row) for row in scales)
    times = tuple(kernels.number(t, 'time') for t in times)
    prices = tuple(tuple(row) for row in prices)
    if not powers or len(set(powers)) != len(powers) or any(p <= 1 for p in powers):
        raise ValueError('distinct shared powers greater than one required')
    if not scales or any(not row or len(set(row)) != len(row) for row in scales):
        raise ValueError('nonempty distinct scales per name required')
    if len(times) < 3 or times[0] != 0 or any(a >= b for a, b in zip(times, times[1:])):
        raise ValueError('fixed grid must start at zero and increase')
    if isinstance(split, bool) or not isinstance(split, int) or not 1 <= split < len(times)-1:
        raise ValueError('fixed split must leave training and evaluation')
    if len(prices) != len(scales) or any(len(row) != len(times) for row in prices):
        raise ValueError('matching fixed panel and grid dimensions required')
    starts = tuple(kernels.number(row[0], 'known start', True) for row in prices)
    result = {'fit': None, 'training': None, 'log_numerator': None,
              'log_sup': None, 'log_e': -mp.inf, 'status': 'outside_domain', 'detail': None}
    try:
        observed = tuple((starts[i],)+tuple(mp.mpf(x) for x in row[1:])
                         for i, row in enumerate(prices))
    except (ValueError, TypeError):
        return result
    if any(not mp.isfinite(x) or x <= 0 for row in observed for x in row):
        return result
    try:
        selections, training = [], []
        for p in powers:
            chosen, best = [], []
            for i, choices in enumerate(scales):
                likelihoods = tuple(mp.fsum(kernels.log_transition(
                    p, k, times[j]-times[j-1], observed[i][j-1], observed[i][j])
                    for j in range(1, split+1)) for k in choices)
                if any(not mp.isfinite(x) for x in likelihoods):
                    raise ArithmeticError('positive-path training density not finite')
                index = max(range(len(choices)), key=likelihoods.__getitem__)
                chosen.append(index)
                best.append(likelihoods[index])
            selections.append(tuple(chosen))
            training.append(mp.fsum(best))
        power_index = max(range(len(powers)), key=training.__getitem__)
        selected = selections[power_index]
        result.update(fit=(power_index, selected), training=tuple(training))
        logq = mp.fsum(kernels.log_transition(
            powers[power_index], scales[i][selected[i]], times[j]-times[j-1],
            observed[i][j-1], observed[i][j])
            for i in range(len(scales)) for j in range(split+1, len(times)))
        rows = tuple(tuple(mp.log(row[j]/row[j-1]) for row in observed)
                     for j in range(split+1, len(times)))
        gaps = tuple(times[j]-times[j-1] for j in range(split+1, len(times)))
        profiled = profile_returns(rows, gaps)
        jacobian = -mp.fsum(mp.log(row[j]) for row in observed
                           for j in range(split+1, len(times)))
        bound = profiled['log_sup'] + jacobian
        value = logq-bound
        if not mp.isfinite(logq) or mp.isnan(value) or value == mp.inf:
            raise ArithmeticError('nonfinite numerator or score')
        result.update(log_numerator=logq, log_sup=bound, log_e=value,
                      status=profiled['status'])
    except (ArithmeticError, ValueError) as error:
        result.update(log_e=-mp.inf, status='numerical_failure', detail=str(error))
    return result
