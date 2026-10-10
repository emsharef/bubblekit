"""D32 deterministic histogram evaluation; diagnostic floating-point arithmetic.

No sampler, tuning, independence check, smoothness estimator, or certificate.
Both reported rules are separate, predeclared comparisons, not a union test.
"""
import math
import numpy as np


def _positive_vector(value, name):
    a = np.asarray(value, dtype=float)
    if a.ndim != 1 or a.size == 0 or not np.all(np.isfinite(a)) or np.any(a <= 0):
        raise ValueError(f'{name} must be a nonempty finite positive vector')
    return a


def _cells(values, edges):
    # Left-closed bins; only the last bin includes its right endpoint.
    inside = (values >= edges[0]) & (values <= edges[-1])
    ids = np.searchsorted(edges, values[inside], side='right') - 1
    ids[values[inside] == edges[-1]] = len(edges) - 2
    return inside, ids


def tilted_lipschitz(a, amplitude, phi, epsilon):
    """Analytic bound for the review's g/tilted-mean functions on [a,R].

    g(x)=1/2+amplitude*tanh(log(x)-center), for any fixed center.
    m=g+epsilon*g*(1-g)/((phi+1)*(1+epsilon*g)).
    Inputs specify the functions; this does not validate a stochastic law.
    """
    a, amplitude, phi, epsilon = map(float, (a, amplitude, phi, epsilon))
    if not all(map(math.isfinite, (a, amplitude, phi, epsilon))):
        raise ValueError('nonfinite smoothness inputs')
    if not (a > 0 and 0 < amplitude < .5 and phi > 0 and epsilon >= 0):
        raise ValueError('invalid smoothness inputs')
    gmin = .5-amplitude
    bound = (amplitude/a)*(phi+(1+epsilon)/(1+epsilon*gmin)**2)/(phi+1)
    if not math.isfinite(bound):
        raise ValueError('nonfinite smoothness output')
    return bound


def evaluate(Y, U, X, *, edges, omega, initial_index, lipschitz,
             alpha_reg=.025, alpha_price=.025):
    """Evaluate claim 044's rule and the review's signed per-cell variant.

    U has shape (N,d). Training and pricing samples must be independent
    under the registered experiment; arrays cannot establish that premise.
    Edges, L_B, weights and error allocations must be fixed before samples.
    Simplex checks allow only 1e-12 summation roundoff, reported explicitly.
    No weights, contributions, probabilities or survival mass are normalized.
    """
    with np.errstate(over='raise', divide='raise', invalid='raise'):
        Y = _positive_vector(Y, 'Y')
        X = _positive_vector(X, 'X')
        edges = _positive_vector(edges, 'edges')
        omega = _positive_vector(omega, 'omega')
        U = np.asarray(U, dtype=float)
        I0, L, ar, ap = map(float, (initial_index, lipschitz, alpha_reg, alpha_price))
        if len(edges) < 2 or np.any(np.diff(edges) <= 0):
            raise ValueError('edges must strictly increase')
        if not all(map(math.isfinite, (I0, L, ar, ap))):
            raise ValueError('nonfinite scalar input')
        if not (I0 > 0 and L >= 0 and ar > 0 and ap > 0 and ar+ap < 1):
            raise ValueError('invalid initial index, Lipschitz bound or error allocation')
        if U.shape != (len(Y), len(omega)) or not np.all(np.isfinite(U)):
            raise ValueError('U must be a finite N by d matrix')
        if np.any(U < 0) or np.any(U > 1):
            raise ValueError('weights must lie in [0,1]')
        residual = max(float(np.max(np.abs(U.sum(axis=1)-1))), abs(float(omega.sum())-1))
        if residual > 1e-12:
            raise ValueError('weights must sum to one; no normalization is performed')
        J, d, M = len(edges)-1, len(omega), len(X)
        train_in, train_ids = _cells(Y, edges)
        counts = np.bincount(train_ids, minlength=J)
        sums = np.column_stack([np.bincount(train_ids, weights=U[train_in, i], minlength=J)
                                for i in range(d)])
        fitted = np.tile(omega, (J, 1))
        occupied = counts > 0
        fitted[occupied] = sums[occupied]/counts[occupied, None]
        h = float(np.max(np.diff(edges)))
        # Writing logs separately avoids an unnecessary finite-product overflow.
        log_reg = math.log(2)+math.log(d)+math.log(J)-math.log(ar)
        radii = np.ones(J)
        radii[occupied] = np.minimum(1, L*h + np.sqrt(log_reg/(2*counts[occupied])))
        global_radius = float(np.max(radii))
        price_in, price_ids = _cells(X, edges)
        # The denominator is the full M, including draws outside B.
        cell_mass = np.bincount(price_ids, weights=X[price_in]/I0/M, minlength=J)
        outside_mass = float(np.sum(X[~price_in]/I0/M))
        sample_mass = float(np.sum(X/I0/M))
        theta_B = cell_mass @ fitted
        theta_full = theta_B + outside_mass*omega
        contributions = omega-theta_full
        c = (edges[-1]/I0)*math.sqrt((math.log(2)+math.log(d)-math.log(ap))/(2*M))
        global_lower = theta_B-global_radius-c
        # Signed summands range over [-R/I0,R/I0], hence 2*c, not c.
        cell_penalty = float(cell_mass @ radii)
        cell_lower = theta_B-cell_penalty-2*c
        outputs = np.r_[theta_B, theta_full, contributions, global_lower,
                        cell_lower, radii, cell_mass, c, sample_mass, cell_penalty]
        if not np.all(np.isfinite(outputs)):
            raise ValueError('nonfinite arithmetic output')
        return {
            'status': 'diagnostic_float', 'certified': False,
            'N': len(Y), 'M': M, 'counts': counts.tolist(),
            'training_outside': int((~train_in).sum()),
            'pricing_outside': int((~price_in).sum()),
            'fitted': fitted.tolist(), 'cell_radii': radii.tolist(),
            'common_radius': global_radius, 'pricing_radius': float(c),
            'sample_survival_mass': sample_mass,
            'cell_sample_mass': cell_mass.tolist(),
            'cell_penalty': cell_penalty, 'theta_compact': theta_B.tolist(),
            'theta_full': theta_full.tolist(), 'contributions': contributions.tolist(),
            'sum_identity_residual': float(contributions.sum()-(1-sample_mass)),
            'input_simplex_residual': residual,
            'global_lower': global_lower.tolist(), 'per_cell_lower': cell_lower.tolist(),
            'global_reject_diagnostic': bool(np.any(global_lower > omega)),
            'per_cell_reject_diagnostic': bool(np.any(cell_lower > omega)),
        }


def evaluate_record(*args, **kwargs):
    """Retain invalid/numerically failed records explicitly, with no rejection."""
    try:
        return evaluate(*args, **kwargs)
    except (ValueError, TypeError, ArithmeticError) as exc:
        return {'status': 'failed', 'certified': False,
                'error': f'{type(exc).__name__}: {exc}',
                'global_reject_diagnostic': False, 'per_cell_reject_diagnostic': False}
