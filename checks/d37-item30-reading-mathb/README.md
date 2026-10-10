# D37 item 30: independent archive reading

This is a recount of experiment 055's committed outcomes, **not a simulation
reproduction**. The script imports neither its analysis nor its fitting code.
It independently recomputes ranks, recovery gates, flag counts, Wilson lower
limits, and resolution summaries from `experiments/055/paths.json.gz`, comparing
them with `results.json`. It does not rerun simulations, fits, prefix scores,
first-alarm dates or the comparator implementations. Experiment 055 remains
reported, pending the reviewer's reproduction.

Run from the repository root:

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d37-item30-reading-mathb/check.py
```

The output includes the archive hash and independently calculated counts. There
are 10,978 calibration, 21,000 evaluation and 2,100 resolution records, totaling
34,078. The ordinary calibration uses 499 paths and rank 475. No new simulation,
fit, tuning or experiment is performed. The resolution alarm-flip calculation
and failure-retention comparison below are labelled post-hoc archive diagnostics.

## Validation disposition

Eleven of the twelve registered recovery gates pass. P1 fitted has 396/500
positive estimates (79.2%, below 80%), with median 0.94034 at true beta 1;
oracle has 451/500 positive estimates. All twelve recovery cells have 500 finite
estimates. The failed gate remains a failure even though the design anticipated
prior-fit contamination. The fitted/oracle contrast is consistent with nuisance
estimation costs; it does not by itself isolate a causal decomposition of that
cost. A six-percent median error is not universal halving of the coefficient.

The matched primary null rates average 4.845% batch and 4.609% monitor across
22 cells. The four exploratory Wilson-lower-limit failures are I100 oracle
monitor (38/500), N_C3 fitted and g0 batch (44/500 each), and N_O1 fitted monitor
(35/500). O1 also has 77/500 simulation failures and is uninformative under the
registered failure gate. An average across cells is not a uniform guarantee;
these gates are not simultaneous tests. A single realized calibration threshold
can have risk above 5% without contradicting claim 045's marginal exchangeable
rank guarantee, which averages over calibration randomness as well.

The archived matched power improvement over GSADF in the in-model and
constant-volatility CEV cells survives the recount. It is evidence on those
cases, not superiority on every stochastic-volatility law or on real data.
Persistent P1 fitted batch power is 184/500 (36.8%), so the shorthand 39–72%
does not cover every in-model alternative. Numerical diffusion paths are not
certified strict-local-martingale samples; the fitted Student-t log-return family
does not supply a pricing law.

Under own stochastic volatility with structural beta zero, fitted beta's median
is 2.53954 at driver correlation +0.7 and −2.58355 at −0.7. Positive estimated
beta is therefore not specific to structural level dependence in these cases.
This numerical observation is not a general impossibility theorem. With I60's
cutoff transported to the positive-correlation cell, batch/monitor flags are
313/500 and 349/500 (62.6%/69.8%), versus matched 32/500 and 27/500. Regime cell
N_S2 similarly has transported 164/500 and 222/500 (32.8%/44.4%), versus matched
24/500 and 25/500. Calibration transfer is a substantive unresolved condition.

Claim 045 requires exchangeability of the actual post-selection score law or
supplied bounds on the actual calibration and conditional future laws. Calm
starts, the same universe and earlier-only inputs do not establish those
conditions; its part 3 gives the relevant selection counterexample. Even a
calibrated single-launch score would not automatically control repeated
launches, a union of batch and monitor flags, or a panel of stocks.

**Recommendation to PM:** continue the already authorized item-31 empirical
comparison with an explicit partial-validation disposition; do not call 055 an
unqualified all-gates pass or claim that real calm references establish 5%
false-alarm control. The narrow P1 miss is not evidence that recovery fails in
every model, and the successful cells justify an empirical comparison. Retain
the failed gate, uninformative O1 and unestimated transport error in its reading.
No new claim, retuning or replacement simulation is requested.

## Corrections needed in the experiment's analysis

The original summary at `f785a87` uses the score getter's −1 default for missing
`beta_hat` as well. Early simulation failures have a variant dictionary but no
coefficient. They are consequently counted as finite coefficient estimates:

| cell | reported fitted finite | actual fitted finite | reported median | actual median |
|---|---:|---:|---:|---:|
| N_C3 | 500 | 489 | −2.48615 | −2.60160 |
| N_C4 | 500 | 489 | −2.62955 | −2.77413 |
| N_O1 | 471 | 394 | −34.99027 | −48.07036 |
| N_S3 | 500 | 499 | −2.74000 | −2.74216 |

The g0 summaries are also affected. The nonexistent oracle even acquires 11,
11, 77 and 1 finite estimates in those cells. Missing coefficients must remain
missing, while positive shares and alarm rates keep the requested denominator.
These bookkeeping errors do **not** affect the twelve in-model recovery gates.
The checker recognizes either the original summary or the corrected finite
counts so the analyst can fix it without invalidating this independent check.

The 051 comparison should retain its first 100 requested reference and evaluation
paths. Early simulation failures return before creating `s051`; filtering on
that key silently removes them. Restoring the registered −1 scores gives:

| cell | missing reference / evaluation | reported flags / denominator | retained flags / denominator |
|---|---:|---:|---:|
| N_C3 | 0 / 1 | 3/99 | 3/100 |
| N_C4 | 1 / 2 | 9/98 | 9/100 |
| N_O1 | 21 / 17 | 4/83 | 9/100 |

O1's corrected reference rank has effective cutoff zero. This is a correction
from saved paths, not a new fit. Its original reference sample was 79, not 100;
the reported scatter cannot be attributed solely to 100-path calibration noise.
The analyst should record the correction and regenerate derived outputs without
overwriting the raw archive or silently changing the design.

Also correct the design's phrase “+∞ if failures push the rank beyond the
sample”: failures remain finite −1 scores and do not change n_cal. They can lower
the order statistic; infinity occurs only when the required rank exceeds the
sample count. Non-in-model oracle results should be unavailable, not evaluated
zero-flag successes.

## Resolution scope

All 2,100 paired diffusion records have coarse and fine outputs and no recorded
failure. The published median terminal-log, log-RV and beta differences reconcile.
Applying each already frozen coarse-grid matched fitted-monitor threshold to
both path maxima yields **four alarm flips out of 2,100**, one each in
SVa_r-0.7_p1.5, SVa_r+0.0_p1.5, SVb_r-0.7_p2.0 and SVb_r+0.0_p1.0. This is a
post-hoc fixed-threshold sensitivity diagnostic, with no fine-grid recalibration.
It supports small observed sensitivity on these paths, not discretization
invariance, a uniform error bound or convergence to the continuous diffusion.
