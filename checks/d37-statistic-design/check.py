"""Finite D37 handoff fixtures, no fitted/simulated experiment or power evidence.

Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
     VECLIB_MAXIMUM_THREADS=1 uv run python checks/d37-statistic-design/check.py
"""
import importlib.util
import math
from pathlib import Path
import sys
import mpmath as mp

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('d37_reference_kernel', HERE/'model.py')
model = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = model
spec.loader.exec_module(model)
mp.mp.dps = 65


def close(a, b):
    assert math.isclose(float(a), float(b), rel_tol=2e-11, abs_tol=2e-11), (a, b)


def rejected(call):
    try:
        call()
    except (ValueError, ArithmeticError):
        return
    raise AssertionError('invalid input accepted')


def independent_loglik(beta, returns, scales, log_ref, fit):
    # Direct high-precision density, not the production log-density or derivative.
    x, total = mp.mpf(0), mp.mpf(0)
    nu = mp.mpf(fit.nu)
    normalizer = mp.gamma((nu+1)/2)/(mp.gamma(nu/2)*mp.sqrt(mp.pi*(nu-2)))
    for r, scale in zip(returns, scales):
        variance = mp.mpf(fit.w)*(mp.mpf(scale)/mp.exp(log_ref))**fit.g*mp.exp(beta*x)
        residual = mp.mpf(r)-fit.mu
        density = normalizer/mp.sqrt(variance)*(1+residual**2/((nu-2)*variance))**(-(nu+1)/2)
        total += mp.log(density)
        x += r
    return total


# Exact lag direction and contamination counterexample: altering observation j
# first changes M at j+1, never at j or earlier. The full schedule survives gaps.
market = tuple(((-1)**j)*(.004+.0002*(j % 9)) for j in range(50))
scales = model.lagged_market_scales(market)
assert all(v is None for v in scales[:20])
close(scales[20], sum(r*r for r in market[:20])/20)
for j in (20, 29, 40):
    changed = list(market)
    changed[j] = .13
    after = model.lagged_market_scales(changed)
    assert after[:j+1] == scales[:j+1]
    assert after[j+1] != scales[j+1]
    changed[j] = math.nan
    absent = model.lagged_market_scales(changed)
    assert len(absent) == len(scales)
    assert absent[:j+1] == scales[:j+1]
    assert all(v is None for v in absent[j+1:min(j+21, len(scales))])
assert model.lagged_market_scales([0.]*25)[20:] == (None,)*5

# Prior reference is invariant to future market shocks; normalizing a full path
# instead is a leaking alternative, and this fixture distinguishes them.
log_ref = model.prior_log_reference(scales[20:30])
changed = list(market)
changed[40] = .4
later = model.lagged_market_scales(changed)
assert model.prior_log_reference(later[20:30]) == log_ref
assert model.prior_log_reference(later[20:]) != model.prior_log_reference(scales[20:])

returns = (.02, -.015, .0, .031, -.009, .011)
raw = scales[30:36]
for nu in (6, 10):
    for g in (0., .7, 2.):
        fit = model.PriorFit(.001, .0004, g, nu)
        for beta in (-12., -.5, 0., .125, 1., 2., 16.):
            ell, d1, d2 = model.loglik_and_derivatives(returns, raw, log_ref, fit, beta)
            exact = lambda b: independent_loglik(b, returns, raw, log_ref, fit)
            close(ell, exact(mp.mpf(beta)))
            close(d1, mp.diff(exact, mp.mpf(beta)))
            close(d2, mp.diff(exact, mp.mpf(beta), 2))
            assert d2 <= 0
            # Old half-slope b=beta/2: derivative and curvature scale by 2 and 4.
            old = lambda b: exact(2*b)
            close(2*d1, mp.diff(old, mp.mpf(beta)/2))
            close(4*d2, mp.diff(old, mp.mpf(beta)/2, 2))
            # Concavity's tangent upper bound on finite fixtures, not a certificate.
            for shift in (-.3, .4):
                assert exact(beta+shift) <= mp.mpf(ell)+d1*shift+mp.mpf('1e-10')

# Rescaling all raw market units with the corresponding prior normalization
# cannot alter the model. Mutating target returns never refits the frozen fit.
fit = model.PriorFit(.001, .0004, .7, 6)
base = model.loglik_and_derivatives(returns, raw, log_ref, fit, 1.)
scaled_ref = model.prior_log_reference([252*v for v in scales[20:30]])
scaled = model.loglik_and_derivatives(returns, [252*v for v in raw], scaled_ref, fit, 1.)
for a, b in zip(base, scaled):
    close(a, b)
future_stock = returns[:3]+(.1, -.05, .04)
assert model.loglik_and_derivatives(future_stock[:3], raw[:3], log_ref, fit, 1.) == model.loglik_and_derivatives(returns[:3], raw[:3], log_ref, fit, 1.)
assert fit == model.PriorFit(.001, .0004, .7, 6)
# The common baseline is independent of own returns at beta=0; the location
# residual still responds, as it should. Exact likelihoods never splice a gap.
rejected(lambda: model.loglik_and_derivatives(returns, raw[:-1], log_ref, fit, 1.))
rejected(lambda: model.loglik_and_derivatives(returns, (None,)+raw[1:], log_ref, fit, 1.))
rejected(lambda: model.prior_log_reference([1., 0.]))
rejected(lambda: model.loglik_and_derivatives(returns, raw, log_ref, model.PriorFit(0., 0., 1., 6), 1.))

# Flat design cannot identify beta. The fixed-nuisance zero-residual singularity
# persists, with half the ray growth coefficient of the half-slope convention.
flat_fit = model.PriorFit(0., .001, 1., 6)
flat = model.loglik_and_derivatives((0.,)*3, (.001,)*3, math.log(.001), flat_fit, 0.)
assert model.loglik_and_derivatives((0.,)*3, (.001,)*3, math.log(.001), flat_fit, 16.) == flat
assert flat[1:] == (0., 0.)
a = .03
ray = lambda b: model.loglik_and_derivatives((a, 0.), (.001,)*2, math.log(.001), flat_fit, b)[0]
close(ray(-200.)-ray(-100.), 100*a/2)

print('PASS: D37 lag/normalization causality, finite full-exponent kernel and derivative fixtures,')
print('scale invariance, retained invalid inputs, flat-beta and singular-profile counterexamples.')
print('Not checked: a fitter, complete profile search, coefficient recovery, calibration laws or power.')
