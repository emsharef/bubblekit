"""Claim 063 diagnostic Gaussian-copula forecast on claim 062's null.

mpmath marginal/profile arithmetic plus SciPy CDFs; NOT certified. No
probability clipping, covariance change in the null, or evaluation fitting.
Reported numerical failures keep one global zero-evidence record.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import numpy as np
from scipy.special import ndtri_exp
from scipy.stats import ncx2
from mpmath import mp

spec = spec_from_file_location('copula_base', Path(__file__).resolve().parents[1]/'062/pooling.py')
base = module_from_spec(spec)
spec.loader.exec_module(base)


def normal_score(p, k, d, x, y):
    p, k, d, x, y = map(float, (p, k, d, x, y))
    if not np.isfinite([p, k, d, x, y]).all() or p <= 1 or min(k, d, x, y) <= 0:
        raise ArithmeticError('invalid CEV normal-score arguments')
    h = p-1
    a, b = x**(-2*h)/(k*k*h*h*d), y**(-2*h)/(k*k*h*h*d)
    # The price transformation is decreasing. Use both logarithmic tails
    # to avoid subtracting a CDF close to one; never clip a probability.
    lf = ncx2.logsf(b, 2+1/h, a)
    lc = ncx2.logcdf(b, 2+1/h, a)
    if np.isnan(lf) or np.isnan(lc) or lf > 0 or lc > 0:
        raise ArithmeticError('invalid CEV CDF tails')
    tail = lf if lf <= -np.log(2) else lc
    if not np.isfinite(tail):
        raise ArithmeticError('unresolved CEV CDF tail')
    value = ndtri_exp(tail) if lf <= -np.log(2) else -ndtri_exp(tail)
    if not np.isfinite(value):
        raise ArithmeticError('nonfinite CEV normal score')
    return value


def fit_correlation(z, gamma):
    z = np.asarray(z, float)
    if z.ndim != 2 or min(z.shape) < 1 or not np.isfinite(z).all():
        raise ArithmeticError('invalid training normal-score array')
    if not np.isfinite(gamma) or not 0 < gamma <= 1:
        raise ValueError('fixed shrinkage must be in (0,1]')
    m = z.shape[1]
    centered = z-z.mean(axis=0)
    s = centered.T@centered
    if not np.isfinite(s).all():
        raise ArithmeticError('nonfinite training covariance')
    if np.any(np.diag(s) <= 0):
        return np.eye(m)
    corr = s/np.sqrt(np.outer(np.diag(s), np.diag(s)))
    corr = (1-gamma)*corr + gamma*np.eye(m)
    np.fill_diagonal(corr, 1.)
    np.linalg.cholesky(corr)
    return corr


def log_gain(z, correlation):
    z, correlation = np.asarray(z, float), np.asarray(correlation, float)
    if z.ndim != 2 or correlation.shape != (z.shape[1], z.shape[1]):
        raise ValueError('matching score and matrix dimensions required')
    if not np.isfinite(z).all() or not np.isfinite(correlation).all():
        raise ArithmeticError('nonfinite normal scores or correlation')
    if not np.allclose(correlation, correlation.T, rtol=0, atol=1e-13):
        raise ArithmeticError('asymmetric correlation')
    if not np.allclose(np.diag(correlation), 1., rtol=0, atol=1e-13):
        raise ArithmeticError('non-unit correlation diagonal')
    factor = np.linalg.cholesky(correlation)
    gain = -len(z)*np.log(np.diag(factor)).sum()
    gain -= .5*(np.sum(z*np.linalg.solve(correlation, z.T).T)-np.sum(z*z))
    if not np.isfinite(gain):
        raise ArithmeticError('nonfinite copula gain')
    return float(gain)


def score_panel(powers, scales, times, prices, split, gamma=.1, weight=.5):
    """Return pure and fixed-blend global scores; log_e is the blend.

    The exact blend's baseline floor need not survive the optional zero mask
    on a reported numerical failure. The unchanged base score is recorded
    for comparison only; it is not substituted for a failed new score.
    """
    gamma, weight = float(gamma), float(weight)
    if not np.isfinite(gamma) or not 0 < gamma <= 1:
        raise ValueError('fixed shrinkage must be in (0,1]')
    if not np.isfinite(weight) or not 0 < weight < 1:
        raise ValueError('fixed independence weight must be in (0,1)')
    powers, scales = tuple(powers), tuple(tuple(row) for row in scales)
    times, prices = tuple(times), tuple(tuple(row) for row in prices)
    original = base.score_panel(powers, scales, times, prices, split)
    result = dict(original)
    result.update(base_log_e=original['log_e'], log_e=-mp.inf,
                  log_e_cop=-mp.inf, copula_gain=None, correlation=None)
    if original['status'] != 'ok':
        return result
    if gamma == 1 or len(prices) == 1:
        result.update(log_e=original['log_e'], log_e_cop=original['log_e'],
                      copula_gain=0., correlation=np.eye(len(prices)), status='ok')
        return result
    try:
        pi, indices = original['fit']
        p = powers[pi]
        # Subtract exact supplied grid values before float conversion.
        gaps = tuple(mp.mpf(b)-mp.mpf(a) for a, b in zip(times, times[1:]))
        def scores(indices_j):
            return np.array([[normal_score(p, scales[i][indices[i]], gaps[j-1],
                                           prices[i][j-1], prices[i][j])
                              for i in range(len(prices))] for j in indices_j])
        correlation = fit_correlation(scores(range(1, split+1)), gamma)
        gain = (0. if np.array_equal(correlation, np.eye(len(prices))) else
                log_gain(scores(range(split+1, len(times))), correlation))
        mix_gain = np.logaddexp(np.log(weight), np.log1p(-weight)+gain)
        result.update(log_e=original['log_e']+mp.mpf(float(mix_gain)),
                      log_e_cop=original['log_e']+mp.mpf(gain),
                      copula_gain=gain, correlation=correlation, status='ok')
    except (ArithmeticError, ValueError, np.linalg.LinAlgError) as error:
        result.update(log_e=-mp.inf, log_e_cop=-mp.inf,
                      status='numerical_failure', detail=str(error))
    return result
