# D36 item 26b: archive reading and implications

Experiment 053 is reported, not independently reproduced at this reading. This
check imports no estimator and runs no simulation or raw-price fit. Run it with:

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d36-item26b-reading-math/check.py

## What was independently checked

All 112 real records match 052's available record IDs. Rebuilding the eight real
group summaries from those rows reproduces the medians, positive shares, t>2
counts, oracle exceedances, boundary counts and cross-scale summaries, including
19 hindsight run-up segments. All 75 summary CSV rows agree with the JSON.

Simulation stores seven cell summaries, not its per-path fitted coefficients or
correlations. The archive records 140 requested paths and three L2 failures;
its n, shares, quartile ordering and CSV are internally consistent. This check
cannot independently reconstruct simulation medians from path-level outputs.
The retained 17 L2 estimates describe surviving paths, not all 20 requested paths.
Ordinary independent reproduction remains necessary.

## Corrections to the interpretation

The full variance exponent beta_053 equals twice D36's beta. At zero exponent,
the saved medians for (a1,a2,b,a049,b2_049) are respectively
(-0.08590,0.43105,0.36701,0.49802,0.31546). Thus “every estimator has +0.3 to +0.5
bias” is false: the within-day estimator has a slightly negative median and
10/20 positive estimates. These are sample medians, not an estimate with an
uncertainty interval for each estimator's expected bias.

P2's daily fit median 2.01 and within-day median 2.74, along with the other cells,
show coefficient recovery in these simulated cases; they do not establish that
the estimators are generally valid or unbiased. The ZL cell's within-day median
is -4.14 and all 20 estimates are negative, not all equal to -4.14. It is a useful
confounding example at beta=0, rho=-0.7. There is no beta=0, positive-rho simulation
cell, so the same experiment does not directly demonstrate the symmetric positive
case or validate a Sin-model detector.

The simulated own-state P2 estimates near one are attenuated relative to the
input exponent two. But 053 does not run its no-own-state estimators on the same
simulated paths. It therefore does not isolate a universal “state control halves
the slope” effect. The real oracle comparison also changes model flexibility:
052 multiplies by the name's estimated state, while 053 fits an exponent on
contemporaneous SPY variance. The real changes are descriptive sensitivity,
not an identified causal decomposition or a pre-fitting power result.

The real archive has 16/28 positive-record and 21/84 control oracle exceedances
of log20, with 15/19 on the selected run-up segments. These are in-sample,
bounded-search scores, not calibrated power or false-alarm probabilities. There
are no alternative-beta boundary hits, but 47 whole-record and 17 segment null
fits hit the beta boundary. Report which boundary is meant; “no bound hits” for
all fits is inaccurate. All recorded fits report success, which is not a global
profile certificate. Same-day SPY variance and some inherited in-record clocks
remain retrospective, and onset-to-peak subsets use future selection.

## Cross-scale evidence and the pricing condition

The saved daily return/estimated-volatility-change correlation is positive for
19/28 positives and 18/84 controls. E5's four are positive and class B has 15/20;
the pooled positive median is about .19 against -.14 for controls. This supports
a descriptive association extending to daily scale in these selected records.
It does not eliminate intraday order flow as a contributor or identify a cause.

No cross-scale rejection threshold, size calibration, power calculation or
dependence-aware uncertainty analysis is in this experiment. Small five-minute
or hourly correlations do not by themselves establish lack of power, just as
larger daily correlations do not establish power. The estimator changes with
scale: the five-minute rolling RMS includes the current return and overlapping
windows; the hourly statistic uses disjoint within-session blocks; the daily
statistic sums available adjacent returns and compares processed eligible days.
That sum need not equal the full first-to-last close return when gaps exist,
and consecutive eligible days need not be consecutive exchange sessions. No
cross-scale invariance theorem is supplied by these different estimators.

Mathb's model-specific reading applies: audited AX-05 [sin1995complications],
Theorem 3.2, concerns instantaneous Brownian driver correlation and the specified
volatility dynamics under a pricing measure. The finite-interval correlations
above are not rho_SV by definition, and the simulator's log-variance OU factor is
not Sin's stated mean-reverting multiplicative factor. The positive-exponent
hybrid simulations are not certified continuous-time strict-local-martingale
samples: they add stochastic volatility, drift, a clock, log-Euler transitions
and an exit/failure rule to a CEV-motivated exponent. An untruncated zero-drift
lognormal step has conditional multiplicative mean one; finite-step simulation
alone does not demonstrate the continuous-time martingale defect. Distinguish
coefficient truth from a proven bubble label.

Formalized claim 003, conditional on its audited upstream inputs, already shows
that even the same physical price and volatility observations can admit true
and strict pricing measures. Sin's condition does not choose between those
pricing measures from these sample correlations. No Andersen–Piterbarg extension
is used; mathb recorded its missing full-text/source-audit limitation.

## Consequence for the monitor

Continue the conditional empirical design and its review. The evidence supports
studying a level/volatility association; it does not validate a unique mechanism,
the proposed 21-session horizon, the chosen baseline half-life, a normalized
Student-t observation law or the real-data calibration premises. A pre-fitted
model with an evolving own-volatility state still has an own-state component;
freezing its coefficients does not prove that it preserves a level effect.
The session-anchor choice also restricts the covariate to within-session moves;
053 does not compare that candidate's detection against a cross-day alternative.
Treat those as explicit candidate choices, not conclusions forced by 053.

Do not spend another experiment merely to restate these limits. Preserve the
remaining registered evaluation budget, shared-model review, profile/certificate
boundary, honest data-reuse labels and the distinction between empirical flags
and a pricing-bubble conclusion. No new claim, fit or simulation is supplied here.
