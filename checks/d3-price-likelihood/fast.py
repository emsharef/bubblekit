"""Vectorized float64 diagnostics for claim 052; not certified inference.

Same mathematical scores as kernels.py, with time chunks to bound temporary
storage. Nonpositive or nonfinite observations are errors, never floored prices.
Callers must record numerical failures and independently check near-boundary
fits/decisions at higher precision. Float64 errors have no proved envelope here.
"""
import numpy as np


def validate_catalogue(catalogue):
    catalogue = tuple((p, float(k)) for p, k in catalogue)
    if (not catalogue or any(p not in (1, 2) or not np.isfinite(k) or k <= 0 for p, k in catalogue)
            or len(set(catalogue)) != len(catalogue)):
        raise ValueError('distinct finite positive-scale candidates with powers 1 and 2 required')
    return catalogue


def batch_split_scores(catalogue, times, prices, split, chunk_size=1024):
    """Return fitted candidate indices and log T, for prices shaped (paths,N+1).

    Training contains increments 1..split; evaluation split+1..N conditions
    on prices[:,split]. Fixed catalogue order resolves exact numerical ties.
    No evaluation observation enters the training argmax.
    """
    catalogue = validate_catalogue(catalogue)
    times, prices = np.asarray(times, dtype=float), np.asarray(prices, dtype=float)
    if (times.ndim != 1 or times.size < 3 or prices.ndim != 2 or not prices.shape[0]
            or prices.shape[1] != times.size or times[0] != 0
            or not np.isfinite(times).all() or not np.all(np.diff(times) > 0)
            or not np.isfinite(prices).all() or not np.all(prices > 0)):
        raise ValueError('positive finite price rows on a common increasing time-zero grid required')
    if not isinstance(split, int) or not 1 <= split < times.size - 1:
        raise ValueError('split must leave nonempty training and evaluation increments')
    if not isinstance(chunk_size, int) or chunk_size < 1:
        raise ValueError('positive integer chunk size required')

    def likelihood(start, end):
        result = np.zeros((prices.shape[0], len(catalogue)))
        with np.errstate(over='raise', invalid='raise', divide='raise'):
            for lo in range(start, end, chunk_size):
                hi = min(lo + chunk_size, end)
                x, y = prices[:, lo:hi], prices[:, lo+1:hi+1]
                logx, logy = np.log(x), np.log(y)
                dt = np.diff(times[lo:hi+1])
                for j, (power, kappa) in enumerate(catalogue):
                    variance = kappa*kappa*dt
                    if not np.all(variance > 0):
                        raise FloatingPointError('variance underflow; use higher precision')
                    normalizer = .5 * (np.log(2*np.pi) + np.log(variance))
                    if power == 1:
                        density = -logy - normalizer - (logy-logx+variance/2)**2/(2*variance)
                    else:
                        loggap = np.log(2.) - logx - logy - np.log(variance)
                        factor = np.empty_like(loggap)
                        small = loggap < -36
                        # log(1-exp(-gap)) = log(gap) + O(gap), with gap < exp(-36).
                        # This avoids exp(loggap) underflow and subtracting two Gaussians.
                        factor[small] = loggap[small]
                        factor[~small] = np.log(-np.expm1(-np.exp(np.minimum(loggap[~small], 100.))))
                        density = (logx-3*logy-normalizer
                                   - ((1/y-1/x)/np.sqrt(variance))**2/2 + factor)
                    result[:, j] += np.sum(density, axis=1)
        if not np.isfinite(result).all():
            raise FloatingPointError('nonfinite likelihood; use higher precision')
        return result

    training = likelihood(0, split)
    evaluation = likelihood(split, times.size-1)
    fit = np.argmax(training, axis=1)
    scores = evaluation[np.arange(prices.shape[0]), fit, None] - evaluation
    if not np.isfinite(scores).all():
        raise FloatingPointError('nonfinite log ratio; use higher precision')
    return fit, scores


def batch_project(catalogue, scores, alpha, onset, ratio):
    """Return retained parameters, block bands, log e-values and null rejections.

    No exponentiation of e-values is needed for testing or for retained sets.
    The final axis of bands holds lower/upper endpoints for each block.
    """
    catalogue = validate_catalogue(catalogue)
    scores = np.asarray(scores, dtype=float)
    alpha, onset, ratio = float(alpha), float(onset), float(ratio)
    if (scores.ndim != 2 or scores.shape[1] != len(catalogue) or not np.isfinite(scores).all()
            or not 0 < alpha < 1 or not np.isfinite(onset) or onset <= 0
            or not np.isfinite(ratio) or ratio <= 1):
        raise ValueError('finite matching scores, alpha in (0,1), onset>0 and ratio>1 required')
    nulls = [j for j, (p, _) in enumerate(catalogue) if p == 1]
    if not nulls:
        raise ValueError('a nonempty catalogue null is required')
    cut = -np.log(alpha)
    kept = scores <= cut
    if not np.all(kept.any(axis=1)):
        raise ValueError('empty confidence set: scores do not satisfy the split construction')
    blocks = []
    for p, kappa in catalogue:
        b1 = np.log(ratio)/kappa**2 if p == 1 else -np.expm1(-2*np.log(ratio))/(2*kappa**2*onset**2)
        blocks.append((b1, b1 if p == 1 else b1/ratio**2))
    blocks = np.asarray(blocks)
    if not np.isfinite(blocks).all() or not np.all(blocks > 0):
        raise FloatingPointError('block integral out of float64 range; use higher precision')
    bands = np.stack((np.where(kept[:, :, None], blocks, np.inf).min(axis=1),
                      np.where(kept[:, :, None], blocks, -np.inf).max(axis=1)), axis=-1)
    log_e = scores[:, nulls].min(axis=1)
    return kept, bands, log_e, log_e > cut
