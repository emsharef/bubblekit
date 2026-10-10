"""Claim 054 total-domain diagnostic adapter for D14 comparisons.

On nonnegative finite arrays, implement claim 054 including impossible paths.
Negative/nonfinite observations and reported numerical failures return zero
evidence with an explicit status; callers must retain the name and original
panel denominator. Invalid fixed configuration raises and must stop the run.
No certified numerical accuracy or arbitrary-law calibration is asserted.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp


def load(name, relative):
    spec = spec_from_file_location(name, Path(__file__).resolve().parents[1]/relative)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


kernels = load('d14_cev_kernels', 'd13-cev-input/kernels.py')
arithmetic = load('d14_support_arithmetic', 'd13-support-input/scoring.py')


def masked(status, detail=None):
    return {'fit': None, 'log_e': -mp.inf, 'scores': None,
            'training': None, 'evaluation': None, 'status': (status,), 'detail': detail}


def score_total_path(catalogue, times, prices, split):
    """A score record, not an exception-based sample selection procedure.

    prices[0] is the known positive start, part of fixed configuration.
    status 'ok' denotes completion of diagnostic arithmetic, not certification.
    All-zero training likelihoods select catalogue index 0; they are not masked.
    """
    catalogue = tuple((kernels.number(p, 'power', True), kernels.number(k, 'scale', True))
                      for p, k in catalogue)
    nulls = tuple(i for i, (p, _) in enumerate(catalogue) if p <= 1)
    if not catalogue or len(set(catalogue)) != len(catalogue) or not nulls:
        raise ValueError('fixed catalogue must be nonempty, distinct and contain a null')
    times = tuple(mp.mpf(t) for t in times)
    prices = tuple(prices)
    if len(times) != len(prices) or len(times) < 3 or times[0] != 0:
        raise ValueError('matching fixed grid and price dimensions required')
    if any(not mp.isfinite(t) for t in times) or any(a >= b for a, b in zip(times, times[1:])):
        raise ValueError('fixed times must be finite and strictly increasing')
    if isinstance(split, bool) or not isinstance(split, int) or not 1 <= split < len(times)-1:
        raise ValueError('fixed split must leave nonempty training and evaluation')
    start = kernels.number(prices[0], 'known starting price', True)
    try:
        observed = tuple(mp.mpf(x) for x in prices[1:])
    except (TypeError, ValueError):
        return masked('outside_domain', 'non-real observation')
    if any(not mp.isfinite(x) or x < 0 for x in observed):
        return masked('outside_domain', 'negative or nonfinite observation')
    prices = (start,)+observed
    statuses = []
    if any(x == 0 and y > 0 for x, y in zip(prices, prices[1:])):
        statuses.append('resurrection')
    try:
        training, evaluation = [], []
        for p, k in catalogue:
            terms = arithmetic.logs(tuple(kernels.log_transition(p, k, times[j]-times[j-1],
                                                                   prices[j-1], prices[j])
                                          for j in range(1, len(times))))
            training.append(mp.fsum(terms[:split]))
            evaluation.append(mp.fsum(terms[split:]))
        # Deliberately do not call the prototype's split_scores, which raises
        # for all-zero training likelihoods. max returns the first tied index.
        fit = max(range(len(catalogue)), key=training.__getitem__)
        if max(training) == -mp.inf:
            statuses.append('zero_training_likelihood')
        if max(evaluation) == -mp.inf:
            statuses.append('zero_evaluation_likelihood')
        numerator = evaluation[fit]
        if numerator == -mp.inf:
            statuses.append('zero_selected_evaluation')
        scores = tuple(arithmetic.log_ratio(numerator, value) for value in evaluation)
        log_e = min(scores[i] for i in nulls)
        if mp.isnan(log_e) or log_e == mp.inf:
            raise ArithmeticError('computed composite score violates claim 054 finiteness')
        return {'fit': fit, 'log_e': log_e, 'scores': scores,
                'training': tuple(training), 'evaluation': tuple(evaluation),
                'status': tuple(statuses) or ('ok',), 'detail': None}
    except (ArithmeticError, ValueError) as error:
        # A retained zero score, not a discarded name. Remaining computed
        # values still need numerical certification before theorem-level use.
        return masked('numerical_failure', f'{type(error).__name__}: {error}')
