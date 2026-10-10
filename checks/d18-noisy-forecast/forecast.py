"""Normalized label/sign CEV forecast, not the actual noisy diffusion law.

Representatives are used only in this numerator. The null denominator must
still enclose the continuous latent law. SciPy arithmetic is diagnostic,
not an outward certificate. No estimated noise contract or power is supplied.
"""
from dataclasses import dataclass
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import math

import numpy as np
from scipy.special import logsumexp
from scipy.stats import ncx2

spec = spec_from_file_location('state_input', Path(__file__).resolve().parents[1]
                              / 'd18-markov-inputs/check.py')
state_input = module_from_spec(spec)
spec.loader.exec_module(state_input)
SIGNS = (-1, 1)


@dataclass(frozen=True)
class Forecast:
    tick: float
    radius: float
    p: float
    kappa: float
    persistence: float

    def __post_init__(self):
        if (not all(math.isfinite(x) for x in
                    (self.tick, self.radius, self.p, self.kappa, self.persistence))
                or self.tick <= 0 or self.radius < 0 or self.p <= 1
                or self.kappa <= 0 or not 0 <= self.persistence < 1):
            raise ValueError('finite tick/scale > 0, radius >= 0, p > 1, persistence in [0,1)')

    def interval(self, label, sign):
        if type(label) is not int or label < 0 or sign not in SIGNS:
            raise ValueError('nonnegative integer label and sign required')
        return state_input.feasible(label, sign, self.tick, self.radius)

    def representative(self, label, sign):
        interval = self.interval(label, sign)
        return None if interval is None else sum(interval) / 2

    def initial(self, label):
        weights = np.array([float(self.interval(label, h) is not None) for h in SIGNS])
        return weights / weights.sum()

    def log_mass(self, x, lower, upper, dt):
        """AX-56 p>1 mass of [lower,upper), using the decreasing Bessel map."""
        if not math.isfinite(dt) or dt <= 0 or x <= 0 or not 0 <= lower < upper:
            raise ValueError('positive start/gap and nonempty nonnegative interval required')
        h = self.p - 1
        scale = self.kappa**2 * h**2 * dt
        nc = x**(-2*h) / scale
        lo = 0. if math.isinf(upper) else upper**(-2*h) / scale
        hi = math.inf if lower == 0 else lower**(-2*h) / scale
        df = 2 + 1/h
        # Choose the tail avoiding subtraction of two probabilities near one.
        if ncx2.logcdf(hi, df, nc) <= -math.log(2):
            big, small = ncx2.logcdf(hi, df, nc), ncx2.logcdf(lo, df, nc)
        else:
            big, small = ncx2.logsf(lo, df, nc), ncx2.logsf(hi, df, nc)
        if not math.isfinite(big) or small >= big:
            raise ArithmeticError('unresolved positive CEV interval mass')
        value = big + math.log(-math.expm1(small - big))
        if not math.isfinite(value) or value > 0:
            raise ArithmeticError('invalid CEV interval mass')
        return value

    def transition(self, previous, following, dt):
        result = np.full((2, 2), -math.inf)
        for h, sign in enumerate(SIGNS):
            x = self.representative(previous, sign)
            if x is None:
                continue
            for t, next_sign in enumerate(SIGNS):
                interval = self.interval(following, next_sign)
                if interval is not None:
                    weight = self.persistence * (h == t) + (1-self.persistence)/2
                    result[h, t] = math.log(weight) + self.log_mass(x, *interval, dt)
        return result

    def tail(self, previous, last_label, dt):
        """Exact-form row mass of labels > last_label, including both signs."""
        if type(last_label) is not int or last_label < 0:
            raise ValueError('nonnegative final label required')
        result = np.zeros(2)
        for h, sign in enumerate(SIGNS):
            x = self.representative(previous, sign)
            if x is None:
                continue
            for t, next_sign in enumerate(SIGNS):
                lower = max(0., self.tick*(last_label+.5)-next_sign*self.radius)
                weight = self.persistence*(h == t) + (1-self.persistence)/2
                result[h] += weight*math.exp(self.log_mass(x, lower, math.inf, dt))
        return result

    def forward(self, labels, durations, initial=None):
        """Return log path mass and conditional sign weights for this forecast.

        Calling on a training prefix and passing its weights to the evaluation
        suffix conditions this same forecast. These are not a posterior for
        the actual efficient-price law, and parameters are not refitted here.
        """
        if len(labels) != len(durations)+1 or len(labels) == 0:
            raise ValueError('one more label than gaps required')
        support = self.initial(labels[0]) > 0
        weights = self.initial(labels[0]) if initial is None else np.asarray(initial, float)
        if (weights.shape != (2,) or not np.isfinite(weights).all()
                or np.any(weights < 0) or abs(weights.sum()-1) > 1e-12
                or np.any(weights[~support] != 0)):
            raise ValueError('normalized weights on feasible initial signs required')
        logs = np.full(2, -math.inf)
        np.log(weights, out=logs, where=weights > 0)
        total = 0.
        for previous, following, dt in zip(labels, labels[1:], durations):
            logs = logsumexp(logs[:, None] + self.transition(previous, following, dt), axis=0)
            step = float(logsumexp(logs))
            if not math.isfinite(step) or step > 1e-12:
                raise ArithmeticError('unresolved or invalid forecast step')
            total += step
            logs -= step  # Exact conditional-state update, not truncation renormalization.
        return total, np.exp(logs)
