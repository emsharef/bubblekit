"""Explicit P=Q catalogue likelihoods; AX-54/55 source-audited at 8d7e4a3.

High-precision evaluation of exact formulas, not certified interval arithmetic.
Models: dS = kappa S**p dW, p in {1, 2}, kappa > 0, positive start.
No Euler likelihood, physical drift fitting, or off-catalogue coverage is implied.
"""
from mpmath import mp


def positive(value, name):
    value = mp.mpf(value)
    if not mp.isfinite(value) or value <= 0:
        raise ValueError(f"{name} must be finite and strictly positive")
    return value


def log_transition(power, kappa, delta, x, y):
    """Log density with respect to dy, not log-price or reciprocal-price dy."""
    kappa, delta, x, y = (positive(v, n) for v, n in
                          ((kappa, 'kappa'), (delta, 'delta'), (x, 'x'), (y, 'y')))
    v = kappa**2 * delta
    if power == 1:
        return -mp.log(y) - mp.log(2 * mp.pi * v) / 2 - (mp.log(y / x) + v / 2)**2 / (2 * v)
    if power == 2:
        # Factor the larger Gaussian term; expm1 avoids subtracting near equals.
        gap = 2 / (x * y * v)
        return (mp.log(x) - 3 * mp.log(y) - mp.log(2 * mp.pi * v) / 2
                - (1 / y - 1 / x)**2 / (2 * v) + mp.log(-mp.expm1(-gap)))
    raise ValueError('only powers 1 and 2 have registered kernels here')


def mean_price(power, kappa, horizon, start):
    kappa, horizon, start = (positive(v, n) for v, n in
                            ((kappa, 'kappa'), (horizon, 'horizon'), (start, 'start')))
    if power == 1:
        return start
    if power == 2:
        return start * mp.erf(1 / (start * kappa * mp.sqrt(2 * horizon)))
    raise ValueError('only powers 1 and 2 are supported')


def defect(power, kappa, horizon, start):
    kappa, horizon, start = (positive(v, n) for v, n in
                            ((kappa, 'kappa'), (horizon, 'horizon'), (start, 'start')))
    if power == 1:
        return mp.mpf(0)
    if power == 2:
        # Avoid subtracting nearly equal mean and initial price.
        return start * mp.erfc(1 / (start * kappa * mp.sqrt(2 * horizon)))
    raise ValueError('only powers 1 and 2 are supported')


def block_integrals(power, kappa, onset, ratio):
    kappa, onset, ratio = (positive(v, n) for v, n in
                          ((kappa, 'kappa'), (onset, 'onset'), (ratio, 'ratio')))
    if ratio <= 1:
        raise ValueError('ratio must exceed one')
    if power == 1:
        b1 = mp.log(ratio) / kappa**2
        return b1, b1
    if power == 2:
        b1 = (1 - ratio**(-2)) / (2 * kappa**2 * onset**2)
        return b1, b1 / ratio**2
    raise ValueError('only powers 1 and 2 are supported')


def split_scores(catalogue, times, prices, split):
    """Own-name prefix fit; future conditional likelihood starts at prices[split].

    times/prices include the known starting price at time zero. The finite
    catalogue must be the true model family, not a numerical parameter grid.
    Returned log-ratios represent claim 051's T(theta).
    """
    catalogue = tuple((p, positive(k, 'kappa')) for p, k in catalogue)
    if not catalogue or any(p not in (1, 2) for p, _ in catalogue):
        raise ValueError('nonempty catalogue using powers 1 and 2 required')
    if len(set(catalogue)) != len(catalogue):
        raise ValueError('duplicate catalogue parameters')
    times = tuple(mp.mpf(t) for t in times)
    prices = tuple(positive(x, 'price') for x in prices)
    if len(times) != len(prices) or len(times) < 3 or times[0] != 0:
        raise ValueError('matching time/price vectors with a time-zero start required')
    if any(not mp.isfinite(t) for t in times) or any(b <= a for a, b in zip(times, times[1:])):
        raise ValueError('finite strictly increasing times required')
    if not isinstance(split, int) or not 1 <= split < len(times) - 1:
        raise ValueError('split must leave nonempty training and evaluation increments')
    train, evaluation = [], []
    for p, k in catalogue:
        steps = tuple(log_transition(p, k, times[j] - times[j - 1], prices[j - 1], prices[j])
                      for j in range(1, len(times)))
        train.append(mp.fsum(steps[:split]))
        evaluation.append(mp.fsum(steps[split:]))
    # Fixed catalogue order breaks ties. No evaluation score enters this choice.
    fit_index = max(range(len(catalogue)), key=lambda i: train[i])
    log_ratios = tuple(evaluation[fit_index] - value for value in evaluation)
    return fit_index, log_ratios


def project(catalogue, log_ratios, alpha, onset, ratio):
    """Diagnostic projections of claim 051's confidence set and null score."""
    alpha = positive(alpha, 'alpha')
    if alpha >= 1 or len(catalogue) != len(log_ratios):
        raise ValueError('alpha < 1 and matching catalogue/score lengths required')
    kept = tuple(i for i, score in enumerate(log_ratios) if score <= -mp.log(alpha))
    if not kept:
        raise ValueError('empty set: scores do not come from the stated split construction')
    blocks = tuple(block_integrals(*catalogue[i], onset, ratio) for i in kept)
    bands = tuple((min(b[j] for b in blocks), max(b[j] for b in blocks)) for j in range(2))
    nulls = tuple(i for i, (p, _) in enumerate(catalogue) if p == 1)
    if not nulls:
        raise ValueError('catalogue null must be nonempty')
    log_e = min(log_ratios[i] for i in nulls)
    return kept, bands, log_e, min(mp.mpf(1), mp.exp(-log_e))
