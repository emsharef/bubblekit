"""Claim 055 diagnostic scorer: total mathematical support conventions.

Finite-precision Bessel/gamma/profile calculations are NOT certified bounds.
Invalid design or negative/nonfinite data are reported; no path is filtered.
Model-impossible nonnegative arrays use the claim's explicit conventions.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp


def module(name, path):
    spec = spec_from_file_location(name, path)
    result = module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


ROOT = Path(__file__).resolve().parents[1]
kernels = module('kernels055', ROOT / 'd13-cev-input/kernels.py')
gaussian = module('gaussian055', ROOT / 'd13-drift-null-input/profile.py')


def score_path(catalogue, times, prices, split):
    catalogue = tuple((kernels.number(p, 'power', True), kernels.number(k, 'kappa', True))
                      for p, k in catalogue)
    if not catalogue or len(set(catalogue)) != len(catalogue):
        raise ValueError('nonempty ordered catalogue without duplicates required')
    nulls = tuple(i for i, (p, _) in enumerate(catalogue) if p <= 1)
    if not nulls:
        raise ValueError('catalogue must contain a null')
    times = gaussian.finite_vector(times)
    prices = tuple(kernels.number(x, 'price') for x in prices)
    if len(times) != len(prices) or len(times) < 3 or times[0] != 0 or prices[0] <= 0:
        raise ValueError('matching grid with positive known time-zero price required')
    if any(b <= a for a, b in zip(times, times[1:])):
        raise ValueError('strictly increasing times required')
    if isinstance(split, bool) or not isinstance(split, int) or not 1 <= split < len(times)-1:
        raise ValueError('split must leave nonempty training and evaluation')
    training, evaluation = [], []
    for p, k in catalogue:
        terms = tuple(kernels.log_transition(p, k, times[j]-times[j-1], prices[j-1], prices[j])
                      for j in range(1, len(times)))
        training.append(mp.fsum(terms[:split]))
        evaluation.append(mp.fsum(terms[split:]))
    # First maximizer includes the all-minus-infinity training case.
    fit = max(range(len(catalogue)), key=lambda i: training[i])
    numerator = evaluation[fit]
    old_null = max(evaluation[i] for i in nulls)
    gaussian_sup = gaussian.log_null_sup(times[split:], prices[split:])
    old_score = gaussian.enlarged_log_score(numerator, old_null, -mp.inf)
    score = gaussian.enlarged_log_score(numerator, old_null, gaussian_sup)
    return dict(fit=fit, training=tuple(training), evaluation=tuple(evaluation),
                log_fitted=numerator, log_null=old_null, log_gaussian=gaussian_sup,
                log_e_old=old_score, log_e=score)
