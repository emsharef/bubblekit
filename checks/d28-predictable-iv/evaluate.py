"""Claim 042 / experiment 043 exact-price floating-point evaluator.

This is not outward-certified arithmetic. Inputs are realized causal lagged
IV values; the caller must establish their predictability and the null law.
No simulator, IV reconstruction, restart or parameter-grid null is supplied.
"""
from dataclasses import dataclass
import math


@dataclass
class Profile:
    """Weighted centered sums, avoiding C-B^2/A cancellation near Q=0."""
    n: int = 0
    A: float = 0.0
    mean_r: float = 0.0
    mean_v: float = 0.0
    Q: float = 0.0
    K: float = 0.0
    H: float = 0.0
    sum_log_v: float = 0.0

    def add(self, r, gap, v):
        if not all(math.isfinite(x) for x in (r, gap, v)) or min(gap, v) <= 0:
            raise ValueError("finite return and positive finite gap/variance required")
        weight, x, y = gap*gap/v, r/gap, v/gap
        total = self.A+weight
        if not math.isfinite(total) or weight <= 0:
            raise ArithmeticError("unrepresentable profile weight")
        dx, dy = x-self.mean_r, y-self.mean_v
        fraction = weight/total
        correction = self.A*fraction
        self.Q += correction*dx*dx
        self.K += correction*dx*dy
        self.H += correction*dy*dy
        self.mean_r += fraction*dx
        self.mean_v += fraction*dy
        self.A = total
        self.n += 1
        self.sum_log_v += math.log(v)
        if not all(math.isfinite(z) for z in self.__dict__.values()):
            raise ArithmeticError("unrepresentable profile statistic")

    def maximum(self, band):
        lo, hi = band
        if not (0 < lo <= hi < math.inf):
            raise ValueError("positive finite ordered band required")
        if not self.n:
            return 0.0, None, None
        root = (2*self.Q/(self.n+math.hypot(self.n, math.sqrt(self.H)*math.sqrt(self.Q)))
                if self.Q else 0.0)
        w = min(hi, max(lo, root))
        b = self.mean_r+w*self.mean_v/2
        logD = (-self.n*math.log(2*math.pi)/2-self.sum_log_v/2
                -self.n*math.log(w)/2-self.Q/(2*w)-self.K/2-w*self.H/8)
        if not all(math.isfinite(z) for z in (root, w, b, logD)):
            raise ArithmeticError("unrepresentable profile")
        return logD, b, w


def _logsumexp(values):
    top = max(values)
    if not math.isfinite(top):
        raise ArithmeticError("unrepresentable forecast")
    return top+math.log(math.fsum(math.exp(x-top) for x in values))


def evaluate(prices, lagged_iv, gaps, training, *,
             bands=((0.3, 1.0), (0.25, 1.25), (0.5, 1.0)),
             powers=(1.0, 1.25, 1.5, 2.0),
             scales=(0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 4.0)):
    """One row per scored return, using experiment 043's registered forecast.

    prices has len(gaps)+1 entries; lagged_iv[j] is known BEFORE return j.
    Zero prices and numerical failures freeze this record at zero evidence;
    they never disappear from the output. Malformed designs raise ValueError;
    negative/nonfinite later observations are retained as failures. Rows use
    absolute one-based return indices. Past scores
    are never recomputed with later fits. Each band is a separate procedure.
    Default columns follow 043 Deviation 2: primary, band M, sensitivity.
    """
    size = len(gaps)
    if len(prices) != size+1 or len(lagged_iv) != size:
        raise ValueError("unaligned arrays")
    if not isinstance(training, int) or not 0 <= training < size:
        raise ValueError("training must leave at least one scored return")
    if not bands or not powers or not scales:
        raise ValueError("nonempty bands and forecast catalogue required")
    if not all(math.isfinite(z) for z in powers):
        raise ValueError("finite forecast powers required")
    if not all(math.isfinite(z) and z > 0 for z in scales):
        raise ValueError("positive finite forecast scales required")
    for band in bands:
        Profile().maximum(band)
    if not math.isfinite(prices[0]) or prices[0] <= 0:
        raise ValueError("positive finite known start required")
    catalogue = [(p, c) for p in powers for c in scales]
    log_weights = [-math.log(len(catalogue))]*len(catalogue)
    drift_sum = elapsed = numerator = 0.0
    profile, rows, failure = Profile(), [], None
    start_log = math.log(prices[0])
    for j, (iv, gap) in enumerate(zip(lagged_iv, gaps)):
        fitted = component_logs = qlog = None
        if failure is None:
            if prices[j] == 0 or prices[j+1] == 0:
                failure = "zero_price"
            elif not all(math.isfinite(z) for z in (prices[j], prices[j+1], iv, gap)) or min(prices[j], prices[j+1], iv, gap) <= 0:
                failure = "invalid_observation"
            else:
                try:
                    prior_log = math.log(prices[j])
                    r = math.log(prices[j+1])-prior_log
                    fitted = min(1., max(-1., drift_sum/elapsed)) if elapsed else 0.
                    component_logs = []
                    for p, c in catalogue:
                        logvar = math.log(c)+2*math.log(iv)+(2*p-2)*(prior_log-start_log)+math.log(gap)
                        variance = math.exp(logvar)
                        if variance <= 0 or not math.isfinite(variance):
                            raise ArithmeticError("unrepresentable forecast variance")
                        z = (r-fitted*gap+variance/2)/math.sqrt(variance)
                        logdensity = -(math.log(2*math.pi)+logvar+z*z)/2
                        if not math.isfinite(logdensity):
                            raise ArithmeticError("unrepresentable forecast density")
                        component_logs.append(logdensity)
                    joint_logs = [a+b for a, b in zip(log_weights, component_logs)]
                    qlog = _logsumexp(joint_logs)
                    next_weights = [x-qlog for x in joint_logs]
                    if j >= training:
                        profile.add(r, gap, iv*iv*gap)
                        numerator += qlog
                        results = [profile.maximum(band) for band in bands]
                        if not math.isfinite(numerator) or not all(math.isfinite(numerator-x[0]) for x in results):
                            raise ArithmeticError("unrepresentable log score")
                    next_drift = drift_sum+r+r*r/2
                    next_elapsed = elapsed+gap
                    if not all(math.isfinite(z) for z in (next_drift, next_elapsed)):
                        raise ArithmeticError("unrepresentable forecast fit")
                    log_weights = next_weights
                    drift_sum, elapsed = next_drift, next_elapsed
                except (ArithmeticError, ValueError):
                    failure = "numerical_failure"
        if j < training:
            continue
        if failure:
            rows.append(dict(index=j+1, status=failure, drift=None, log_forecast=None,
                             log_numerator=-math.inf, log_denominators=(None,)*len(bands),
                             fitted_nulls=(None,)*len(bands), log_scores=(-math.inf,)*len(bands)))
        else:
            rows.append(dict(index=j+1, status="ok", drift=fitted, log_forecast=qlog,
                             log_numerator=numerator, log_denominators=tuple(x[0] for x in results),
                             fitted_nulls=tuple((x[1], x[2]) for x in results),
                             log_scores=tuple(numerator-x[0] for x in results)))
    return rows


def first_crossing(rows, alpha, band=0, relative_tolerance=1e-9):
    """Return (first resolved crossing, threshold-near checkpoint indices).

    This matches 043's floating-point proximity diagnostic, NOT a certified
    numerical error bound. Call separately for every band and alpha.
    """
    if not 0 < alpha < 1 or not math.isfinite(relative_tolerance) or relative_tolerance < 0:
        raise ValueError("invalid level or tolerance")
    boundary, crossing, unresolved = -math.log(alpha), None, []
    for row in rows:
        value = row["log_scores"][band]
        if row["status"] != "ok":
            continue
        if abs(value-boundary) <= relative_tolerance*abs(boundary):
            unresolved.append(row["index"])
        elif value >= boundary and crossing is None:
            crossing = row["index"]
    return crossing, tuple(unresolved)
