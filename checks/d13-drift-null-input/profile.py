"""Diagnostic continuous Gaussian null likelihood; not certified arithmetic.

For log returns R_j and durations d_j, the physical null is
R_j independent Normal((b-kappa**2/2)*d_j, kappa**2*d_j), with
ANY b in R and kappa>0. A pricing-null interpretation is a separate premise.
Inputs represent exact prices/log returns, not rounded quote representatives.
With rounded training, claim 024 requires conditional observation-cell
probabilities using the full rounded prefix; this profile does not compute
that likelihood and must not be treated as its null supremum.
The log-return mean a=b-kappa**2/2 ranges freely for every variance w.
Writing a_hat=sum(R)/sum(d) and Q=sum((R-a_hat*d)**2/d),
sum((R-a*d)**2/d) = Q + sum(d)*(a-a_hat)**2.
Thus the maximum is at a_hat and w=Q/n when Q>0. For Q=0 the
supremum is infinity as w tends to zero; there is no finite maximizer.
Price densities also include the Jacobian product 1/y_j.

This is an exact formula evaluated at arbitrary precision, NOT an upper
rounding certificate. A finite grid or unconverged numerical optimizer
would underestimate this denominator and cannot certify calibration.
"""

from mpmath import mp


def finite_vector(values):
    result = tuple(mp.mpf(x) for x in values)
    if not result or any(not mp.isfinite(x) for x in result):
        raise ValueError('nonempty finite vector required')
    return result


def profile_returns(returns, durations):
    """Return a_hat, residual Q, and log supremum in return coordinates."""
    returns, durations = finite_vector(returns), finite_vector(durations)
    if len(returns) != len(durations) or any(d <= 0 for d in durations):
        raise ValueError('matching returns and positive durations required')
    n = len(returns)
    mean = mp.fsum(returns)/mp.fsum(durations)
    residual = mp.fsum((r-mean*d)**2/d for r, d in zip(returns, durations))
    # One observation always fits exactly, independently of roundoff in r/d*d.
    if n == 1 or residual == 0:
        return mean, mp.mpf(0), mp.inf
    variance = residual/n
    log_sup = -n*(mp.log(2*mp.pi*variance)+1)/2-mp.fsum(mp.log(d) for d in durations)/2
    return mean, residual, log_sup


def log_null_sup(times, prices):
    """Gaussian supremum relative to product (Lebesgue on positives + delta_0).

    Includes the trapped extension from a zero training endpoint. Zero
    likelihood means -inf; an unbounded supremum means +inf. This function
    evaluates one conditional block, not the training selection or a test.
    """
    times, prices = finite_vector(times), finite_vector(prices)
    if len(times) != len(prices) or len(times) < 2 or any(x < 0 for x in prices):
        raise ValueError('matching grid and nonnegative prices required')
    durations = tuple(b-a for a, b in zip(times, times[1:]))
    if any(d <= 0 for d in durations):
        raise ValueError('strictly increasing times required')
    if prices[0] == 0:
        return mp.mpf(0) if all(x == 0 for x in prices[1:]) else -mp.inf
    if any(x == 0 for x in prices[1:]):
        return -mp.inf
    returns = tuple(mp.log(y/x) for x, y in zip(prices, prices[1:]))
    _, _, value = profile_returns(returns, durations)
    return value-mp.fsum(mp.log(x) for x in prices[1:])


def enlarged_log_score(log_fitted, log_catalogue_null, log_gaussian_sup):
    """Combine a finite-catalogue null maximum with the Gaussian supremum.

    Inputs must be likelihoods on the SAME observation/reference space.
    The caller supplies a normalized, training-only fitted density and
    checks support domination. No calibration is asserted by this function.
    """
    fitted, old, gaussian = (mp.mpf(x) for x in
                             (log_fitted, log_catalogue_null, log_gaussian_sup))
    if any(mp.isnan(x) for x in (fitted, old, gaussian)) or fitted == mp.inf or old == mp.inf:
        raise ValueError('finite-or-zero fitted and catalogue likelihoods required')
    denominator = max(old, gaussian)
    if fitted == -mp.inf or denominator == mp.inf:
        return -mp.inf
    if denominator == -mp.inf:
        raise ValueError('positive numerator has no null support')
    return fitted-denominator
