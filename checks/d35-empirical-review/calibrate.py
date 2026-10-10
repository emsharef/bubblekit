"""D35 empirical calibration shell, not a likelihood fitter or an e-value.

Fit settings and observation/selection rules must be frozen before calibration.
Nonfinite, missing, or unsuccessful fits remain in the scored population.
"""
from dataclasses import dataclass
from fractions import Fraction
import math
from typing import Mapping, Sequence


@dataclass(frozen=True)
class FitPair:
    null_loglik: float
    alternative_loglik: float
    null_ok: bool = True
    alternative_ok: bool = True


@dataclass(frozen=True)
class Score:
    value: float
    signed_gap: float | None
    status: str


def score_fit(fit: FitPair | None) -> Score:
    """Bounded monotone transform of a finite numerical one-sided LR gain.

    All failure types have score -1, below every successful score (in [0,1]).
    An optimizer's success is not a certificate of global optimality.
    """
    if fit is None:
        return Score(-1.0, None, "missing_fit")
    if not fit.null_ok or not fit.alternative_ok:
        return Score(-1.0, None, "optimizer_failure")
    if not (math.isfinite(fit.null_loglik) and math.isfinite(fit.alternative_loglik)):
        return Score(-1.0, None, "nonfinite_fit")
    gap = fit.alternative_loglik - fit.null_loglik
    if not math.isfinite(gap):
        return Score(-1.0, None, "gap_overflow")
    return Score(2.0 / math.pi * math.atan(max(0.0, gap)), gap, "finite_numerical_fit")


def score_window(fits: Mapping[int, FitPair | None], checkpoints: Sequence[int],
                 *, mode: str = "endpoint") -> tuple[float, dict[int, Score]]:
    """Score one fixed window; preserve each requested checkpoint's status.

    Primary endpoint mode requires exactly one checkpoint. A separately declared
    maximum mode uses the same checkpoint list in calibration and evaluation.
    Missing checkpoints contribute -1 instead of being dropped. Earlier failures
    do not poison a later, separately scored endpoint.
    """
    if (not checkpoints or any(type(t) is not int or t <= 0 for t in checkpoints)
            or list(checkpoints) != sorted(set(checkpoints))):
        raise ValueError("checkpoints must be fixed, positive, increasing, and distinct")
    if mode not in {"endpoint", "maximum"}:
        raise ValueError("unknown scoring mode")
    if mode == "endpoint" and len(checkpoints) != 1:
        raise ValueError("endpoint mode needs exactly one checkpoint")
    details = {t: score_fit(fits.get(t)) for t in checkpoints}
    return max(s.value for s in details.values()), details


def rank_cutoff(calibration: Sequence[float], alpha: Fraction) -> float:
    """Claim 045 cutoff, retaining repetitions and using an exact rank level."""
    if not isinstance(alpha, Fraction) or not 0 < alpha < 1:
        raise ValueError("alpha must be an exact Fraction strictly between zero and one")
    if not calibration or not all(math.isfinite(x) for x in calibration):
        raise ValueError("supply every calibration record's finite score, including failures")
    rank = (len(calibration) + 1) * (1 - alpha)
    k = -(-rank.numerator // rank.denominator)
    return sorted(calibration)[k - 1] if k <= len(calibration) else math.inf


def flag(score: float, cutoff: float) -> bool:
    """Strict exceedance: ties, including shared failure scores, are accepted."""
    if not math.isfinite(score) or math.isnan(cutoff) or cutoff == -math.inf:
        raise ValueError("invalid score or cutoff")
    return score > cutoff
