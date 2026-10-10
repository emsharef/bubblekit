# Calibration

A bubble score only becomes an alarm through a threshold, and the threshold sets the false-alarm rate. Two
methods with similar rankings can flag very different shares of records. The single most important lesson of the
research behind bubblekit is that **calibration is part of the method**.

## The strict rank rule

Score m reference records that you believe contain no bubble and that resemble the records you will score, for
example calm windows of the same kind of stock over earlier dates. With level α:

```python
from bubblekit import calibration
cut = calibration.rank_cutoff(reference_scores, alpha=0.05)   # the ceil((m+1)(1-alpha))-th smallest score
alarm = target_score > cut                                      # strict exceedance
```

If the references and the target are exchangeable, P(alarm) ≤ α. With m = 499 and α = 0.05 the cutoff is the
475th ordered reference score. If (m + 1)(1 − α) > m the cutoff is +∞. You need at least 19 references for α = 0.05.

`calibration.calibrate(reference_scores, alpha)` also returns the reference count, the rank used and the
in-sample reference exceedance rate.

## Keep failures in the reference set

The likelihood statistics return −1 when a fit or profile fails. Keep those records in the references with their
−1 scores. Dropping them changes the score distribution and breaks the rule.

## Exchangeability is the hard part

Choosing references only from the past prevents look-ahead. It does not make them exchangeable with future
targets. Fitted nuisance parameters, the market proxy, window length and the reference selection rule all shape
the score distribution. For a guarantee that holds given the particular calibration set, at 5% with 95%
confidence, independent references are needed: about 59 of them.

## Calibration transport

```python
calibration.transport_rates(reference_scores, {"other population": scores, ...}, alpha=0.05)
```

calibrates on one set and reports flag rates on others. In the research's simulations, the daily statistic held
about 5% under matched calibration, but a cutoff taken from the baseline no-bubble family flagged:

| Population (no level effect in any of them) | Flag rate |
|---|---|
| market-driven stochastic volatility | 22% |
| own stochastic volatility | 41% |
| own stochastic volatility with positive price–volatility correlation | 70% |

On real data, GSADF's simulated random-walk critical values flagged 12–52% of stock windows. Empirical
cutoffs from calm windows brought that to 6–11% for 13- and 24-month windows, but not for 72-month windows.

Practical advice:

- calibrate per window length and per data frequency;
- draw references from the same universe and era as the targets, using a rule fixed before looking at scores;
- report flag rates by period (`evaluation.rates_by_group`) instead of one pooled number;
- for a monitor, calibrate on the **maximum** of each reference path over the same horizon. The guarantee then
  covers "at least one alarm in the window", not repeated relaunches.

## Multiple names

`multiple.ebh` controls the false discovery rate across names under arbitrary dependence, but only for genuine
e-values such as `split_likelihood_score` under its null. Empirically calibrated scores are not e-values; use rank
p-values (`calibration.p_value`) with `multiple.by` if you need a dependence-robust procedure for them.
