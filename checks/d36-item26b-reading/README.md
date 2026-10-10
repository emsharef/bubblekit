# D36 item 26b: empirical reading of experiment 053

This is an independent archive recount and model-scope review of a **reported**
experiment. It is not a raw-bar reproduction, a rerun of the 140 simulations,
a new experiment, or a monitor-power claim. The simulation archive stores only
cell summaries; their numerical medians cannot be independently reconstructed
from saved individual paths. The check imports no experiment code and reads no
cached prices.

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d36-item26b-reading/check.py
```

## Recount and corrections

The 112 real records match the available experiment-052 IDs exactly; the missing
113th requested record remains outside this available-record analysis. There are
28 positives, 84 controls and 19 nested, hindsight-selected run-up segments.
All eight real group summaries and 75 CSV rows reconcile. None of these counts
represents independent draws: controls repeat and segments reuse full records.

The simulation has 140 requested paths and three L2 failures. Its L2 estimator
summaries use 17 surviving paths; all other cells use 20. Retaining the failure
count does not turn a survivor median into an unconditional estimator property.
Only seven cells, one clock and one log-variance OU specification were used.
No positive-SV-correlation-only cell was simulated. A log-Euler hybrid with
overnight steps, SV, and a failure barrier is not an exact CEV path law or a
validated strict-local-martingale ground-truth generator. The prescribed local
variance exponent is known; exact pricing-bubble status is not established by
that fact. No discretization/convergence certificate was supplied.

Three specific corrections to the reported reading:

- **Not every estimator has positive zero-effect bias.** Z0 within-day a1 has
  median −0.08590, quartiles [−0.44736,0.71032], and 10/20 positive estimates.
  The other four medians are positive. These are finite-cell summaries, not
  proved estimator biases.
- **−4.143 is a median, not every ZL estimate.** Its quartiles are −4.709 and
  −2.831, with zero positive estimates among 20. This demonstrates a negative
  SV-leverage confound in the implemented within-day statistic. It does not
  quantitatively validate a positive-SV alternative that was never simulated.
- **There is no calibrated power calculation at any scale.** Larger daily
  correlation medians are descriptive sensitivity. Small intraday medians do
  not establish inability to detect: P1U has 16/20 positive five-minute estimates
  and 17/20 positive hourly estimates. There is no registered rejection rule or
  size comparison turning those signs into power. Z0 hourly is positive in
  13/20 too. Avoid both “only daily has power” and claims of intraday power.

All 131 saved no-state oracle fits (112 records plus 19 segments) report success,
with no **alternative** beta-bound hits. There are nevertheless **64 null-bound
flags**. Those may include the legitimate beta=0 null endpoint, but the archive
omits the fitted null beta, so it cannot locate each flag. Do not report “no bound
hits” without specifying the alternative. Solver success is not a certified
global profile; the null here is truncated at −20, unlike the proposed monitor.

## What the change of state control establishes

At the same record IDs, E5's across-day median was already positive in 052:
0.65069 becomes 0.77907 without the own-state regressor; only two of four E5
individual slopes increase. The 033-B median remains slightly negative,
−0.04446 to −0.02290; E9 remains negative, −0.01266 to −0.01964. Across all
positives 16/28 slopes increase. Thus “removal turned the E5 across-day sign
positive” is false, while increased pooled positive median is accurate.

The positive segments' median 0.51321 (16/19 positive) and oracle median 0.74794
(17/19 positive; 15/19 above log20) are descriptive, selected using future peaks.
Full controls have 21/84 oracle exceedances. Neither fraction is calibrated
power/size, and current-day SPY variance is not available as a prior forecast.

At prescribed beta=2, the saved own-state simulation medians near 1 demonstrate
attenuation **in those estimator/specification combinations**. The simulation did
not run matched no-state variants, so it does not isolate the own-state control
as the cause or show removing it recovers truth. Moreover, 053's real oracle
replaces the fixed own-state multiplier with a fitted contemporaneous SPY power;
this is more than dropping one term. The across-day regressions are the cleaner
nested comparison. No tested prefit/session-anchor monitor follows from either.

## Cross-scale interpretation and the Sin condition

The real daily correlations are E5 +0.25478 (4/4 positive), 033-B +0.21377
(15/20), E9 −0.04264 (0/4), and controls −0.14255 (18/84). Whole positives have
median +0.18915 (19/28 positive). Selected segments have +0.11383 daily (14/19),
but their five-minute/hourly medians are negative (−0.00488/−0.00857). A measured
positive association exists beyond intraday sampling in these groups. This is
not a general all-scales sign law, nor exclusion of an order-flow explanation.
The daily statistic is an intraday first-to-last-observed-bar return paired with
a change in estimated realized volatility; it is not the simulation's latent
instantaneous correlation. Shared returns, overlapping RMS windows, drift,
selection and the inherited in-record clocks remain part of the measurement.

The usable source is [sin1995complications], Theorem 3.2 via audited AX-05:
under its particular pricing dynamics a·gamma>0 yields strictness, and
nonpositive dot product gives a true martingale. The exact drift and diffusion
specification matters. Experiment 053's OU **log variance** is not Sin's
linearly mean-reverting multiplicative volatility factor. Its finite-scale
correlations cannot be plugged into AX-05 as its Brownian correlation.
The Andersen–Piterbarg extension remains pending authoritative text/audit as
recorded in FINDINGS; no unavailable source is used here.

Even knowing instantaneous correlation would not decide local versus stochastic
volatility from these summaries, or choose a pricing measure. Formalized claim
003's AX-05 example has identical physical price and volatility observations
under two choices of pricing measure with opposite bubble labels. Consequently,
“mathb's condition decides which mechanism these observations identify” is false.
Positive association can motivate a restricted empirical alternative; it is not
identification of a monetary bubble or a verified null/alternative label.

## Consequence for items 27 and 28

Continue the shared-model specification, preserving the conditional status of the
session-anchor/day-fixed-baseline candidate. Do not present this experiment as
validation of that variant, proof of a prefit advantage, or a reason to remove
needed nuisance variation just to increase likelihood ratios. Math must state
the chosen observation/state family, completed-session recursion and prior-only
training objective, and name the omitted correlated-SV possibilities. The final
empirical monitor must calibrate that exact frozen procedure's full-window
maximum, retaining unsupported histories and failures. Descriptive zero-effect
bias is not a substitute for claim 045's joint-law/transport premises.

The existing fixed-slot, data-reuse, availability and numerical-versus-certified
contracts remain in force. There is one registered experiment slot left for the
final evaluation; this reading requests corrections and model decisions, **no
additional simulation or tuning**. All records used here remain design-used.
