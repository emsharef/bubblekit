"""Support-aware split likelihood arithmetic; AX-57 source-audited at 92dbf72.

No diffusion theorem or numerical certification is asserted by this module.
Logs can be -infinity (zero likelihood). Positive-infinity log likelihoods,
NaNs and empty catalogues are invalid. Scores themselves may be infinite.
"""
from mpmath import mp


def logs(values):
    values = tuple(mp.mpf(v) for v in values)
    if not values or any(mp.isnan(v) or v == mp.inf for v in values):
        raise ValueError('nonempty finite-or-negative-infinity log likelihoods required')
    return values


def log_ratio(numerator, denominator):
    """0/0=0, positive/0=infinity, ordinary ratio otherwise, in log space."""
    a, b = logs((numerator, denominator))
    if a == -mp.inf:
        return -mp.inf
    if b == -mp.inf:
        return mp.inf
    return a-b


def split_scores(training, evaluation):
    """Fixed-order training argmax; returns fit and extended log T values.

    An all-zero training likelihood is diagnosed, not silently discarded.
    If the selected evaluation likelihood is zero, all ratios are zero.
    """
    training, evaluation = logs(training), logs(evaluation)
    if len(training) != len(evaluation):
        raise ValueError('matching catalogue dimensions required')
    if max(training) == -mp.inf:
        raise ValueError('training path is impossible under the entire catalogue')
    fit = max(range(len(training)), key=training.__getitem__)
    return fit, tuple(log_ratio(evaluation[fit], v) for v in evaluation)


def confidence_set(scores, alpha):
    alpha = mp.mpf(alpha)
    scores = tuple(mp.mpf(v) for v in scores)
    if not 0 < alpha < 1 or not scores or any(mp.isnan(v) for v in scores):
        raise ValueError('valid alpha and nonempty non-NaN scores required')
    return tuple(i for i, v in enumerate(scores) if v <= -mp.log(alpha))


def null_log_e(scores, nulls):
    scores, nulls = tuple(scores), tuple(nulls)
    if not nulls or any(not isinstance(i, int) or not 0 <= i < len(scores) for i in nulls):
        raise ValueError('nonempty valid null indices required')
    return min(scores[i] for i in nulls)
