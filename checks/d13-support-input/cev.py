"""Diagnostic implementation of proposed claim 054, not yet reviewed.

Uses the full absorbed law. P=Q and exact catalogue truth are intended model
premises, not properties inferred from the input path. No zero-price flooring.
Prices are exact latent states. Rounded quotes require their own conditional
observation likelihood given the entire rounded training prefix (claim 024);
starting this kernel at a rounded representative is not that correction.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp
from scoring import split_scores, null_log_e, confidence_set

path = Path(__file__).resolve().parents[1] / 'd13-cev-input' / 'kernels.py'
spec = spec_from_file_location('cev_mixed_kernels', path)
kernels = module_from_spec(spec)
spec.loader.exec_module(kernels)


def score_path(catalogue, times, prices, split, alpha):
    catalogue = tuple((kernels.number(p, 'power', True), kernels.number(k, 'kappa', True))
                      for p, k in catalogue)
    if not catalogue or len(set(catalogue)) != len(catalogue):
        raise ValueError('nonempty catalogue without duplicates required')
    nulls = tuple(i for i, (p, _) in enumerate(catalogue) if p <= 1)
    if not nulls:
        raise ValueError('catalogue must contain a null candidate')
    times = tuple(mp.mpf(t) for t in times)
    prices = tuple(kernels.number(x, 'price') for x in prices)
    if len(times) != len(prices) or len(times) < 3 or times[0] != 0 or prices[0] <= 0:
        raise ValueError('matching vectors with known positive time-zero price required')
    if any(not mp.isfinite(t) for t in times) or any(b <= a for a, b in zip(times, times[1:])):
        raise ValueError('finite strictly increasing times required')
    if not isinstance(split, int) or not 1 <= split < len(times)-1:
        raise ValueError('split must leave nonempty training and evaluation')
    if any(x == 0 and y != 0 for x, y in zip(prices, prices[1:])):
        raise ValueError('positive observation after absorption is outside this catalogue')
    training, evaluation = [], []
    for p, k in catalogue:
        terms = tuple(kernels.log_transition(p, k, times[j]-times[j-1], prices[j-1], prices[j])
                      for j in range(1, len(times)))
        training.append(mp.fsum(terms[:split]))
        evaluation.append(mp.fsum(terms[split:]))
    if max(evaluation) == -mp.inf:
        raise ValueError('evaluation path is impossible under the entire catalogue')
    fit, scores = split_scores(training, evaluation)
    return {'fit': fit, 'training': tuple(training), 'evaluation': tuple(evaluation),
            'scores': scores, 'kept': confidence_set(scores, alpha),
            'log_e': null_log_e(scores, nulls)}
