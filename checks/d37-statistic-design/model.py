"""Reference daily D37 preprocessing and fixed-nuisance kernel, not a fitter.

No calibration, profile optimizer, simulated data, or pricing-law claim lives here.
Invalid inputs raise; a caller must preserve the registered failure convention.
"""
from dataclasses import dataclass
import importlib.util
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
_spec = importlib.util.spec_from_file_location(
    'd37_d35_kernel', ROOT / 'checks/d35-fitting-protocol/model.py')
_kernel = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _kernel
_spec.loader.exec_module(_kernel)


@dataclass(frozen=True)
class PriorFit:
    mu: float
    w: float
    g: float
    nu: int

    def validate(self):
        if (not all(math.isfinite(v) for v in (self.mu, self.w, self.g))
                or not -.1 <= self.mu <= .1
                or not 1e-8 <= self.w <= .25
                or not 0 <= self.g <= 2 or self.nu not in (6, 10)):
            raise ValueError('outside the declared D37 nuisance domain')


def lagged_market_scales(returns, lookback=20):
    """One scale per return index t, using only returns[t-lookback:t].

    None marks insufficient/invalid history. No slot is dropped. Recovery of a
    market-only rolling window does not authorize recovery of a poisoned launch.
    """
    if type(lookback) is not int or lookback <= 0:
        raise ValueError('positive integer lookback required')
    values = tuple(returns)
    output = []
    for t in range(len(values)):
        past = values[max(0, t-lookback):t]
        if len(past) != lookback or not all(math.isfinite(r) for r in past):
            output.append(None)
            continue
        squares = [r*r for r in past]
        if not all(math.isfinite(v) for v in squares):
            output.append(None)
            continue
        # Divide first so summing finite squares cannot overflow unnecessarily.
        scale = math.fsum(v/lookback for v in squares)
        output.append(scale if math.isfinite(scale) and scale > 0 else None)
    return tuple(output)


def prior_log_reference(prior_scales):
    """Log of geometric mean; caller supplies strictly prior scales only."""
    values = tuple(prior_scales)
    if not values or any(v is None or not math.isfinite(v) or v <= 0 for v in values):
        raise ValueError('incomplete/nonpositive prior market scales')
    return math.fsum(math.log(v)/len(values) for v in values)


def loglik_and_derivatives(returns, raw_market_scales, log_m_ref, fit, beta):
    """Return ell(beta), d ell/d beta, d² ell/d beta² in full-exponent units.

    Inputs are one scored suffix, anchored immediately before its first return;
    neither training returns nor future observations are scored. Evaluate each
    prefix separately using its initial segment and the same frozen fit/ref.
    """
    fit.validate()
    returns, scales = tuple(returns), tuple(raw_market_scales)
    if len(returns) != len(scales):
        raise ValueError('one market scale per scheduled return required')
    if not math.isfinite(beta) or not math.isfinite(log_m_ref):
        raise ValueError('finite exponent and prior reference required')
    ell, first, second = [], [], []
    x = 0.
    for r, scale in zip(returns, scales):
        if (not math.isfinite(r) or scale is None
                or not math.isfinite(scale) or scale <= 0):
            raise ValueError('unsupported stock or market history')
        log_v = math.log(fit.w) + fit.g*(math.log(scale)-log_m_ref) + beta*x
        residual = r-fit.mu
        log_z = (-math.inf if residual == 0 else
                 2*math.log(abs(residual))-math.log(fit.nu-2)-log_v)
        if not math.isfinite(log_v):
            raise ArithmeticError('nonfinite log variance')
        # z/(1+z), stably, including zero residual; no variance floor.
        if log_z >= 0:
            e = math.exp(-log_z)
            weight, complement = 1/(1+e), e/(1+e)
        else:
            e = math.exp(log_z)
            weight, complement = e/(1+e), 1/(1+e)
        ell.append(_kernel.log_density(r, fit.mu, log_v, fit.nu))
        first.append(.5*x*(-1+(fit.nu+1)*weight))
        second.append(-.5*(fit.nu+1)*x*x*weight*complement)
        x += r
        if not all(math.isfinite(v) for v in (ell[-1], first[-1], second[-1], x)):
            raise ArithmeticError('nonfinite kernel or derivative')
    return tuple(math.fsum(values) for values in (ell, first, second))
