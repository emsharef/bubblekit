# D35 item 25 calibration reference

Recommendation frozen before item 25 scores: one historical reference of at
most 999 calm-start windows; one 10,000-window universe sample; the fixed
consensus records. This is an empirical comparison under claim 045's explicit
law assumptions, not a verified real-data false-alarm guarantee. No new model,
fit settings, sequential certificate or experiment is introduced here.

## Windows and selection

1. Use the pinned 039 constituent/cache provenance and adjusted daily closes.
   Fix the complete market-session calendar from ^GSPC. Each input contains
   exactly 379 positive finite prices on consecutive market sessions: first
   126 returns train the state and the remaining 252 are scored. No forward
   filling, interpolation or compression across a missing session. Keep the
   revision-1 fitter, fixed initial price reference and total failure score −1.
   Missing-price records are ineligible at the metadata stage; fit failures
   after selection remain in the sample and denominator. Record both counts.
2. Keep PM's 10,000-window simple random sample of the eligible 039-name frame,
   with month-start ends and the analyst's declared forward-coverage rule.
   Sort by (symbol, full-input start, end), then use NumPy default_rng(20261051)
   to sample without replacement. Freeze IDs, cache hashes and coverage counts
   before fitting. Do not filter this evaluation sample by calmness, score,
   future return value or episode label. The reported 144,752 frame count is
   the analyst's metadata count, not independently recounted here.
3. Reference candidates end on the first ^GSPC session of a month, with end
   dates from 1995-01-01 through 2010-12-31 inclusive. They need complete input
   prices but no forward-outcome coverage. Compute both the stock and market
   calm-start metrics on the **first 127 input prices only**, on the same dates:

       annualized RMS volatility = sqrt(252 mean(log(P[j]/P[j−1])²));
       training drawdown = max_j(1 − P[j]/max_(i≤j) P[i]).

   Require stock volatility ≤0.30 and drawdown ≤0.15; market volatility ≤0.20
   and drawdown ≤0.10. All inequalities are inclusive. These are fixed design
   cutoffs, not estimated optimal thresholds, proof of a null, or thresholds
   chosen from 050 scores. Do not inspect scored-period volatility, returns,
   drawdowns or episode outcomes to call a reference window calm.
4. Exclude exact full-window IDs in the universe sample and the fixed consensus
   evaluation set. Order remaining candidates by the SHA-256 digest of UTF-8
   `20261151|symbol|YYYY-MM-DD|YYYY-MM-DD` (start then end), breaking hash ties by
   the ID tuple. Greedily retain a candidate only if its inclusive full input
   interval shares no price date with an already retained window of that name.
   Stop at 999. Calendar overlap across names is allowed and must be reported.
   If fewer survive, use all survivors with the actual calibration count;
   never widen cutoffs, repeat windows or replace failed fits. Zero survivors
   means no calibrated verdict, not a substitute calibration design.
5. Record the full candidate and exclusion counts, selected IDs and features,
   unique-name count, date distribution and same-name overlap check. A cache
   feasibility pass found 18,634 candidates and 999 retained across 332 names
   **before evaluation-ID exclusions**. This is not the final manifest.
   `availability.py DATA_DIR` reproduces that unscored feasibility pass using
   the registered d24 cache. It reads no future outcomes and runs no fitter.

## Cutoffs, comparisons and time ordering

Use the strict order-statistic cutoff from `checks/d35-empirical-review/calibrate.py`
separately for each score, on the same reference IDs. Primary level is 5%; the
predeclared 1% level serves item 16's optimistic ROC/false-alarm comparison;
10% is secondary continuity with 050. Do not select the most favorable level.
With 999 reference records the ascending ranks are respectively 950, 990, 900.
Retain ties and failures; equality never flags. For a smaller reference use
the exact Fraction-based rank, including +infinity when the rank exceeds its
size. A 1% rank needs at least 99 records but that minimum is not precision.

Apply the same fitter and observation map in reference and evaluation. Keep
050's comparator conventions: GSADF and v1 see the full 379 prices, while the
new likelihood conditions on the first 126 returns. This is a declared
algorithm comparison, not equal effective fit lengths or a causal estimate
of the cost of adaptation. Recompute their reference cutoffs here. Old
040/045 interpolated, tie-inclusive thresholds and variable-length 021 calm
scores are not substitutes for this calibration. Report raw scores and
method-specific failures as well as flags; do not silently use common-success
denominators.

Reconstruct each of 021's 33 positive and 103 negative records with 379 prices
ending at its original full-window endpoint. Keep the episode IDs, mark
unavailable histories and disclose that the lookback differs from the original
episode. Do not optimize the endpoint, duration or to-peak variant. Missing
histories remain requested records with an unavailable label, not a favorable
drop from the consensus denominator. These labels support an explicitly
optimistic ROC, not financial-bubble ground truth.

The fixed reference becomes available after 2010. Primary temporal holdout
rows have **full input start ≥2011-01-01**; their inputs cannot overlap the
reference period. Earlier and boundary-crossing evaluation rows remain in
the universe tables but are retrospective comparisons. Consensus evaluations
ending before 2011 likewise use a future historical reference and must not be
called contemporaneous monitoring. Exact-ID exclusion alone does not eliminate
overlap among these retrospective rows.

Report period flag rates separately for all starts, calm starts by the identical
training-only predicate, and other starts. The latter measures transport;
calm-start holdout flags are still empirical rates, not true-null false alarms.
Retain the full unfiltered sample for the registered forward 63/126-session
return/drawdown regressions with the existing Driscoll–Kraay specification.
If predictive coefficients are trained before the split, their entire outcome
interval must end before 2011; embargo incomplete labels. Evaluate the frozen
coefficients only on the full-input holdout. Cross-sectional ranks from the
10,000-window sample are ranks among sampled names at that date, not the full
503-name universe. Register the exact regression/uncertainty choices before
scores. Current constituents and required forward coverage introduce selection
and survivorship limitations even without selecting on outcome values.

## What claim 045 does and does not supply

The mechanism is an application of its existing rank theorem. A common total
score map is necessary; equal lengths, past-only features, nonoverlap within
name, random ID selection and calm labels do **not** prove joint exchangeability
of the selected calibration and evaluation scores. Cross-name common shocks,
selection and the historical/later split remain. Claim 045 part 3 explicitly
shows why training-only calm selection does not license an unselected target.
Even matching the calm predicate later does not establish stationarity or
exchangeability. There is no supplied real-data null law or transport budget.

Conditional on distance at most epsilon_joint from an exchangeable joint score
law, the pointwise marginal bound is min(1,alpha+epsilon_joint). At 5%, assumed
budgets 0, .01, .025, .05 give .05, .06, .075, .10. These are assumption-indexed
sensitivity values, **not estimated budgets**. Alternatively, claim 045 part 2
needs eta_cal for the entire calibration-vector law versus an iid score law
and rho_eval for the future score kernel given the full reference record.
Neither independent-looking windows nor observed calibration histograms
establish these conditions. No real-data budget is set to zero here.

For a realized cutoff, its iid conditional-risk binomial formula uses
r_cal=n_cal−k_cal (49 at n_cal=999 and 5%); it is not an ordinary binomial
confidence interval for dependent real-data evaluation flags. All evaluation
rows share a reference, and many share prices and market shocks. Descriptive
or dependence-adjusted regression uncertainty does not prove test calibration.
These are individual-window bounds, not familywise or false-discovery control
for 10,000 tests, three levels or several algorithms. No sequential/anytime
claim follows from the fitted LR or these ranks.

At 6.4 seconds per window, 999 reference fits add about 15 minutes on seven
workers before overhead, within the PM budget. The existing holdout supplies
calibration-transport diagnostics; do not add a second reference fit program
or tune a period-specific cutoff after reading item 25 results. Preserve the
pilot's reported/reproduced distinction and ordinary review; its promising
matched-law behavior motivates this evaluation but cannot certify real data.
