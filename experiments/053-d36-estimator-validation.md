---
id: "053"
title: "D36 item 26b: do the elasticity estimators recover known local-volatility bubbles? Real data without the own-stock state, and a cross-scale return–volatility test"
status: reproduced
direction: D36
claims: ["055"]
code: experiments/053/
---
## Question

The human's request via the PM (note `2026-10-09-d36-item26b.md`).
- **The doubt:** the human questions the reading that local volatility "fails across scales", and suspects
  estimator artefacts.
- **The suspected artefacts:**
  - experiment 052's (a2) and (b) control the stock's own smooth volatility state, which can absorb slow
    level–variance co-movement;
  - experiment 049's daily estimators pool run-up and crash phases into one global power law.
- **Three questions:**
  1. **Validation:** on simulated local-volatility bubbles with realistic stochastic volatility, a diurnal clock and
     5-minute sampling, what β do the exact estimators of 052 and 049 recover against the truth?
  2. **Real data without the own state:** controlling only the market's (SPY's) variance and the diurnal clock, what
     do the real 5-minute data give, on whole records and on run-up segments, run-ups against calm controls?
  3. **Cross-scale move test:** what is the sign of the correlation between returns and same-interval changes in
     deseasonalized volatility at 5-minute, hourly and daily scales?
     - A stochastic-volatility strict-local-martingale mechanism with positive return–volatility correlation
       [sin1995complications] (AX-05; citation corrected by Deviation 3) predicts a positive sign at every scale. A purely intraday order-flow effect predicts it intraday
       only.
     - mathb states the condition for reading this. This experiment only measures.

**Job:** (1) verifies estimator behaviour under known truth; (2) and (3) are descriptive diagnostics, not tests.

**Budget:** D36's second experiment, which leaves one for item 28.

## Design

**β is the variance exponent throughout** (variance ∝ price^β; 052's and 049's convention; β_053 = 2 β_D36).

**(1) Simulation** (seed `SeedSequence([20261053, cell, path])`; 20 paths per cell).
- **Grid:** two years of 504 sessions × 78 five-minute bars. The first year is the prior year (for 052's clock) and
  the second the record.
- **Dynamics:** log-Euler steps of log S with variance per step v_t c_j (S/S₀)^β Δ and drift −½·variance plus μΔ.
  - **Diurnal clock:** c_j = 1 + 1.5((j − 38.5)/38.5)², normalized to mean 1.
  - **Overnight:** a Gaussian move with 20% of a day's variance at the current level. It is not scored, but enters
    the level.
- **Stochastic volatility:** log v follows an Ornstein–Uhlenbeck process with long-run volatility 0.40 per year,
  half-life 20 sessions and stationary s.d. of log v of 0.5. Its shocks have correlation ρ with the price shocks.
- **Cells** (μ in per-year units):

  | cell | β | ρ | μ |
  |---|---|---|---|
  | L2 (local leverage) | −2 | 0 | 0 |
  | Z0 | 0 | 0 | 0 |
  | ZL (SV leverage) | 0 | −0.7 | 0 |
  | P1 | 1 | 0 | 0 |
  | P2 | 2 | 0 | 0 |
  | P1U (run-up) | 1 | 0 | +0.8 |
  | P2U (run-up) | 2 | 0 | +0.8 |

  β = 1 and 2 are CEV p = 1.5 and 2.
- **Market path:** a separate Z0 path stands in for SPY, used by 052's (a2) and 049's market control.
- **Estimators, unchanged code:**
  - 052's (a1), (a2) and (b) (`experiments/052/run.py`), with SIP sessions replaced by the simulated ones;
  - 049's (a) monthly realized-variance elasticity and (b2) local-lognormal fitted β on the record's daily closes
    (`experiments/049/run.py`), using the whole record.
- **Reported per cell and estimator:** the median, quartiles and the share of recovered β above 0, against the truth.

**(2) Real data without the own-stock state** (052's 112 records and positive run-up segments, onset to peak by
042's rule).
- **(a2′) Across days:** OLS of log q_d on x_{d,0} and log q_d of SPY, with no own-state term, and Newey–West
  standard errors (10 lags).
- **(b′) Oracle:** r ~ N(0, σ² s_j (q_d^SPY)^γ exp(β x)), with σ² profiled and (β, γ) fitted by bounded L-BFGS-B
  (β ∈ [−20, 20] against [−20, 0]; γ ∈ [−3, 3]).
  - **Reported:** β, the log-LR, bound hits and convergence.
  - **Scope:** SPY's same-day variance is a descriptive covariate, not an available forecast.
- **Clocks:** 052's (the prior year, or in-record where labelled).
- **Groups:** E5, E9, 033-B, controls (SPY/DIA and members), and run-up segments of at least 20 sessions.

**(3) Cross-scale move test** (052's records and run-up segments).
- **5 minutes:** corr(r_t, Δ log σ̂_t), with σ̂_t the root mean square of the last 12 deseasonalized returns
  including r_t. It measures whether an up-move raises local volatility more than a down-move of the same size.
- **Hourly:** within-session hours of 12 bars. corr(hour return, Δ log hourly deseasonalized realized volatility)
  between consecutive hours of the same session.
- **Daily:** corr(intraday open-to-close return, Δ log daily deseasonalized realized volatility) between
  consecutive sessions.
- **Reported:** per record and group, the median correlation and the share above 0, positives against controls, with
  the 20 simulated cells as a reference for the signs at each scale.

**Computation.** A single process, minutes. Outputs: `results.json` and `summary.csv`.

**Scope.**
- **Simulation:** one SV specification and one clock. Overnight moves are Gaussian.
- **Real data:** as in 052 (sub-penny 5-minute closes, design-used episodes).
- **Cross-scale correlations:** descriptive. Mechanical overlap at 5 minutes (r_t enters σ̂_t) is shared by every
  group and by the simulation.

## Deviations

**Deviation 1 (2026-10-09, after a crashed first run and before any result was read): simulation failures.**
- **The crash:** the first full run stopped with an overflow in cell L2. Under β = −2, a falling price raises variance
  and the log price diverges downward.
- **The gap in the design:** it had no rule for such paths, and the code capped log S at 30, which silently distorts
  paths.
- **The rule now:** a path whose |log S| exceeds 5 (a price factor of about 150) at any step is stopped and retained
  as a simulation failure. Its estimators are absent, and the failures are counted per cell. The cap is removed.
- **Unread:** the real-data part had printed per-record lines before the crash. They were not read, and the rerun
  recomputes them identically.

**Deviation 2 (2026-10-09, after the Results; per mathb's note `2026-10-09-d36-sin-reading.md` and FINDINGS "D36
item 26b: the Sin sign condition is model-specific"): reading of part 3 corrected.** No new run. The Question's
framing (from the PM's note) that "a stochastic-volatility strict-local-martingale mechanism [sin1995complications] (AX-05; citation corrected by Deviation 3) predicts a
positive sign at every scale" is superseded:
- **Model-specific:** Sin's condition (audited AX-05) is a model-specific condition on the instantaneous driver
  correlation, not on the measured finite-interval correlation of returns with estimated volatility changes.
- **No identification:** neither all-scale nor intraday-only positivity identifies a pricing bubble or order flow
  (claim 003).
- **Added to part 3:** the estimator definitions, the 5-minute overlap and smoothing, the absence of per-record
  uncertainty, and the design-used selection.
- **No universal cutoff:** none is imposed while the Andersen–Piterbarg audit is pending.

**Deviation 3 (2026-10-09, after the Results and the review; per mathb's note
`2026-10-09-exp053-reading-corrections.md`, `checks/d36-item26b-reading/README.md` and the Review): reading
corrections.** No new run or tuning. mathb's archive recount passes, and the reviewer reproduced the experiment.
Corrected in place:
- **The β = 0 claim:** "all estimators have a small positive bias at β = 0" is withdrawn. (a1)'s median here is
  −0.09 (10 of 20 positive), and on the reviewer's 100 paths every median is +0.00 to +0.14. 20-path medians have SE
  of about 0.2–0.4.
- **ZL:** −4.14 is the median, with all 20 paths negative, not every estimate.
- **E5 across days:** it was already +0.65 with the own state (+0.78 without), and only 2 of 4 records increased. No
  matched no-state simulation isolates the attenuation's cause, and (b′) also changes the SPY treatment.
- **The 131 (b′) fits:** none has an alternative-side bound hit, but 64 have null-side bound flags (null β not saved).
- **No power claims:** no rejection rule establishes power at any scale. P1U's 5-minute and hourly positive shares are
  16 of 20 and 17 of 20 despite small medians.
- **Records:** the simulation archive holds aggregates only, with no per-path records.
- **Failed paths:** L2's summaries cover its 17 successful paths of 20.
- **Sin:** the simulated OU log-variance model is not Sin's model, and a measured finite-scale correlation is not an
  instantaneous ρ. Claim 003 prevents mechanism or pricing identification.
- **Citation:** the unregistered "[Sin 1998]" is replaced by the audited [sin1995complications] (AX-05), including
  in the Question, and the all-scales implication is corrected as in Deviation 2.
- **Retained:** the descriptive daily association, the hindsight-segment and same-day-SPY limitations, and the
  reported status.

**Deviation 4 (2026-10-09; per math's notes `2026-10-09-d36-item26b-reading-corrections.md` and
`2026-10-09-d36-item26b-math-path.md`): further reading scope.** No rerun. The published primary numbers and recorded
failures are kept. Math's reading and check (`checks/d36-item26b-reading-math/`; mathb's is
`checks/d36-item26b-reading/`) agree with Deviation 3. Added:
- **Bound flags:** the 64 null-side bound flags split into 47 whole-record and 17 segment fits, with no
  alternative-side hits.
- **Simulation scope:** the recovery is of coefficients in a hybrid OU/log-Euler simulation, not a validation on
  certified continuous-time strict-local-martingale samples. No β = 0 positive-ρ cell was simulated, so the sign
  that correlated stochastic volatility alone would give is not measured here.
- **Power:** without a calibrated rejection rule or power calculation, small cross-scale magnitudes are not called
  a lack of power, and daily magnitudes are not called demonstrated power.
- **Attenuation:** the simulated no-state ablation was not run, so the attenuation is observed, not a universal
  causal halving.
- **Archive scope:** math's check rebuilds the real-data summaries and CSV, but the simulation's per-path fits are
  absent, so only their aggregate consistency is checked.

## Results

**Status: reported (2026-10-09).** `experiments/053/run.py` (Deviation 1), a single process, about 15 minutes.
Outputs: `results.json` and `summary.csv`.
- **Units:** β is the variance exponent (β_053 = 2 β_D36).
- **Simulation:** 20 paths per cell. Three L2 paths left exp(±5) and are retained as failures; no other cell
  failed.
- **Real data:** experiment 052's 112 records, and 19 run-up segments of at least 20 sessions.

**1. Estimator validation** (simulation; recovered β as median [quartiles], share > 0).

| cell (true β; ρ; μ) | 052 (a1) within-day | 052 (a2) across-day, own state | 052 (b) oracle, own state | 049 (a) daily RV | 049 (b2) daily fit |
|---|---|---|---|---|---|
| L2 (−2; 0; 0) | −2.52 [−3.15, −1.45] 0% | −1.24 6% | −1.03 18% | −1.40 12% | −1.84 6% |
| Z0 (0; 0; 0) | −0.09 [−0.45, 0.71] 50% | +0.43 65% | +0.37 55% | +0.50 60% | +0.32 60% |
| ZL (0; −0.7; 0) | **−4.14** [−4.71, −2.83] 0% | −1.07 20% | −0.38 30% | −0.68 40% | −1.03 15% |
| P1 (1; 0; 0) | +1.10 [0.22, 2.22] 80% | +1.02 80% | +0.73 75% | +0.70 75% | +0.64 70% |
| P2 (2; 0; 0) | +2.74 [1.86, 3.52] 90% | +1.08 80% | +1.02 80% | +1.39 80% | +2.01 85% |
| P1U (1; 0; 0.8) | +0.79 90% | +0.65 80% | +0.42 70% | +0.67 75% | +0.91 80% |
| P2U (2; 0; 0.8) | +1.89 95% | +1.36 85% | +0.79 90% | +1.65 90% | +1.78 90% |

- **The estimators are not broken: they recover the sign and roughly the size of a simulated local-volatility
  bubble.**
  - The simulation is a hybrid log-variance OU and log-Euler design, not certified continuous-time
    strict-local-martingale samples. No β = 0 cell with *positive* return–volatility correlation was simulated
    (Deviation 4).
  - **Daily (049):** recovers β = 2 almost exactly (b2: 2.01, run-up 1.78). Its pooled global fit is not the
    problem in this design.
- **Controlling the stock's own smooth state attenuates the slope** (052 (a2) and (b): β = 2 gives 1.0–1.4 here,
  and 0.8 under the oracle in a run-up).
  - On the reviewer's 100 paths at β = 2: (a2) +1.36 and (b) +0.83, i.e. two-thirds and two-fifths of the truth.
  - The human's suspicion holds for these two estimators.
- **20-path medians are imprecise** (standard error about 0.2–0.4; Deviation 3). The β = 0 "bias" first reported
  here (+0.3 to +0.5) is not supported:
  - here, (a1) is −0.09 with 10 of 20 positive;
  - on the reviewer's 100 Z0 paths every estimator's median is +0.00 to +0.14.
  - The β = 0 *spread* is wide, so a single record's sign is weak evidence. At β = 2, (a1)'s +2.74 is +1.95 on 100
    paths.
- **Within-day β (a1) confounds local volatility with return–volatility correlation.** With β = 0 and stochastic
  volatility correlated −0.7 with returns (ZL), its median is −4.14, with all 20 paths negative (the reviewer: −3.27,
  all negative).
  - 052's within-day contrast (calm names strongly negative, meme run-ups positive) is therefore equally consistent
    with differences in the sign of the return–volatility correlation. It is not specific to a level-dependent
    diffusion coefficient.

**2. Real data without the own-stock state** (controlling SPY's same-day variance and the diurnal clock).

| group | records | (a2′) across-day β (share > 0; t > 2) | (b′) oracle β (share > 0) | (b′) log-LR > log 20 |
|---|---|---|---|---|
| E5 | 4 | +0.78 (100%; 3) | +1.31 (100%) | 4 |
| E9 | 4 | −0.02 (50%; 2) | −0.02 (50%) | 2 |
| 033-B | 20 | −0.02 (50%; 7) | +0.24 (55%) | 10 |
| all positives | 28 | +0.16 (57%; 12) | +0.37 (61%) | 16 |
| run-up segments (onset to peak) | 19 | **+0.51 (84%)** | **+0.75 (89%)** | 15 |
| controls, all | 84 | −0.47 (38%; 16) | −0.75 (35%) | 21 |
| controls, SPY and DIA | 24 | −0.67 (21%) | −1.12 (25%) | 3 |

- **Without the own state, the across-day level association is positive in the E5 run-ups and on run-up segments,
  and negative in calm controls.**
  - **E5 was already positive before removal** (Deviation 3): 052's (a2) gave a median of +0.65, now +0.78, and only
    2 of 4 records increased individually.
  - **Not a matched comparison:** no no-state simulation isolates the attenuation's cause, and (b′) also changes the
    SPY treatment. The pattern is consistent with part 1's attenuation, not a matched demonstration of it.
- **Run-up segments** are positive in 84–89% of cases, and the oracle exceeds log 20 in 15 of 19.
  - But the segments are chosen with hindsight (onset to peak). The no-state estimators were not validated by
    simulation in this registration, so their behaviour at β = 0 is unknown.
- **The oracle exceeds log 20 in 25% of controls,** a reminder that it is an in-sample statistic, not a test.
- **The SPY covariate:** same-day SPY variance is descriptive, not an available forecast.
- **Fit status:** every (b′) fit converged, with no alternative-side bound hits. 64 of the 131 fits carry a null-side
  bound flag (the null's β at its bound): 47 whole-record and 17 run-up-segment fits. The null's β values were not
  saved (Deviations 3 and 4).

**3. Cross-scale move test** (median correlation of returns with same-interval changes in log deseasonalized
volatility; share > 0).

| | 5 minutes | hourly | daily |
|---|---|---|---|
| simulation, local volatility (P1, P2, P1U, P2U) | +0.002 to +0.009 | +0.004 to +0.025 | **+0.05 to +0.17** (75–100%) |
| simulation, SV leverage (ZL) | −0.003 | −0.010 | **−0.18** (0%) |
| simulation, no effect (Z0) | −0.002 | +0.005 | −0.004 |
| E5 | +0.036 (100%) | +0.084 (100%) | **+0.26** (100%) |
| E9 | −0.012 | −0.034 (0%) | −0.04 (0%) |
| 033-B | +0.001 | +0.016 (60%) | **+0.21** (75%) |
| all positives | +0.003 | +0.016 | +0.19 (68%) |
| run-up segments | −0.005 | −0.009 | +0.11 (74%) |
| controls | −0.019 (25%) | −0.053 (13%) | **−0.14** (21%) |
| controls, SPY and DIA | −0.043 (0%) | −0.123 (0%) | −0.17 (0%) |

- **The 5-minute and hourly medians are small in simulation** (below 0.03 under every local-volatility cell), yet P1U is
  positive in 16 of 20 paths at 5 minutes and 17 of 20 hourly. No rejection rule was registered, so this establishes
  no power at any scale (Deviation 3). The daily scale shows the clearest simulated contrast.
- **Daily scale:**
  - E5 and the class-B run-ups have a positive return–volatility correlation, in the range simulated local
    volatility produces;
  - the calm controls and E9 have a negative correlation, in the range of SV leverage;
  - E5 is also positive hourly and at 5 minutes.
- **Not confined to intraday scales** in these run-ups. Per Deviation 2, this does not by itself identify or exclude
  an order-flow mechanism.
- **Uncertainty (Deviation 2):** the table reports medians and shares above 0 across records, with no per-record
  standard errors or intervals.
  - The 5-minute measure overlaps by construction: r_t enters σ̂_t, and consecutive 12-bar windows share 11 bars.
  - The hourly and daily measures use non-overlapping intervals, but the daily correlation rests on 68–858
    session pairs per record.
  - Records are design-used (052) and hindsight-selected run-ups.

**Reading** (item 26b).
- **The local-volatility estimators are not artefact-broken.**
  - The daily estimator (049) and the within-day estimator recover a true β of 1–2.
  - Controlling the stock's own smooth volatility state attenuates the slope (052's (a2) and (b): to two-fifths or
    two-thirds of the truth in the reviewer's 100-path run).
  - Without that control, the across-day association is positive in the 2020–21 meme run-ups (already +0.65 with
    it) and on run-up segments, against negative in calm controls.
  - That fits the human's suspicion that the own-state control hid part of the association. No matched no-state
    simulation isolates the cause.
- **Within-day β is not specific:** in simulation, return–volatility correlation alone gives a large signed
  within-day β. 052's within-day contrast is evidence of a sign difference in the return–volatility relation between
  run-ups and calm names, not of local volatility in particular.
- **The sign difference is not intraday-only in these run-ups:** at the daily scale, where the measure moves in
  simulation, E5 and most class-B run-ups show a positive correlation between returns and estimated volatility
  changes (+0.19 to +0.26), and calm names a negative one (−0.14).
- **What this does not show (Deviation 2, mathb's FINDINGS entry "D36 item 26b: the Sin sign condition is
  model-specific"):**
  - **Not Sin's quantity:** the measured quantity is a finite-interval correlation of returns with *estimated*
    volatility changes. Sin's strictness condition (AX-05: positive driver correlation in its specified
    multiplicative-volatility, mean-reverting model, with nonzero vol-of-vol) concerns the *instantaneous* driver
    correlation, so the theorem does not predict a positive measured sign at every scale.
  - **Positivity identifies no mechanism:** all-scale positivity would not identify a pricing bubble (claim 003:
    the same price and volatility observations are compatible with true and strict pricing measures), and
    intraday-only positivity would not identify order flow.
  - **Pure CEV p > 1** is covered by AX-03, not by Sin's rule. A hybrid CEV-plus-SV truth needs separate
    justification.
  - **The pricing interpretation is open:** the measurement is consistent with a level-dependent diffusion, with
    positively correlated stochastic volatility, and with other mechanisms.
  - **The simulation is not Sin's model:** its OU log-variance model is not the model of AX-05, and a measured
    finite-scale correlation cannot be inserted as an instantaneous ρ (Deviation 3).
- **For item 27/28:**
  - **No own-state shrinkage:** the monitor should not let a fast own-volatility state absorb the level effect.
    Math's frozen pre-fit is consistent with that.
  - **β can't be read alone:** a fixed-β local-volatility alternative and a correlated-SV alternative predict the
    same within-day sign, so β alone does not identify the mechanism.
  - **Calibrate per record:** the wide β = 0 spread means single-record signs need calibration, not a sign test.
- **Scope:**
  - one SV specification and one clock in simulation;
  - no simulation validation of the no-state variants (registered for the real data only);
  - hindsight run-up segments and design-used episodes;
  - same-day SPY variance as a descriptive covariate;
  - sub-penny 5-minute closes.

## Review

Reviewer, 2026-10-09, against main at `b92089c7`, which contains the results commit `5b4f6161`.

**Method.** I wrote my own code from the Design, without reading `experiments/053/run.py`, `052/run.py` or `049/run.py`. It is committed as `checks/review/exp053/reproduce.py`, with its rerun command and seeds in its header, and runs in about 2 minutes on 2 workers.
- **(1) Simulation.** My own simulator follows the Design: 504 × 78 bars, the stated clock, overnight move, OU log-volatility with correlated shocks, and the |log S| > 5 failure rule. It runs 20 paths per cell on my own seeds, plus 100 further paths each for Z0 and P2.
  - **Estimators:** 052-style (a1), (a2) and (b), as in my experiment-052 reproduction, and 049-style (a) and (b2) on the daily closes.
  - **Two parameter choices** the Design leaves open: the OU stationary mean of log v is log 0.16, and the "months" are 21-session blocks.
- **(2) and (3) Real data.** (a2′), (b′) and the three cross-scale correlations, on experiment 052's 112 records (list from its `results.json`) and the run-up segments, with my experiment-052 data handling.

**Reproduced.**
- **(2) Real data without the own state, essentially exactly.**
  - **(a2′):** E5 +0.79 (100%; 3), E9 −0.02, 033-B −0.02 (7), all positives +0.16 (57%; 12), run-up segments +0.51 (84%), controls −0.47 (38%; 16) and SPY/DIA −0.67 (21%).
  - **(b′):** E5 +1.33 (4 above log 20), 033-B +0.24 (10), all positives +0.37 (61%; 16) and segments +0.75 (89%; 15 of 19). Every fit converged.
  - **The (b′) control rows differ only in scope.** I did not fit SPY's own record against its own variance as covariate, so my controls are 72 records, at −0.62 with 20 above log 20, against −0.75 and 21.
- **(3) The cross-scale correlations on real data.** E5 +0.047/+0.082/+0.275 against +0.036/+0.084/+0.26. 033-B daily +0.216 (75%) against +0.21 (75%). Controls −0.019/−0.053/−0.143 against −0.019/−0.053/−0.14. SPY/DIA −0.043/−0.124/−0.173 against −0.043/−0.123/−0.17.
- **(1) The simulation's qualitative findings.**
  - **Within-day β is not specific.** With β = 0 and leverage correlation −0.7 (ZL), (a1) is negative in every path: −3.27 here against −4.14.
  - **The daily estimator recovers local volatility.** 049 (b2) at β = 2 gives +1.87 on 100 paths (SE 0.17), against +2.01.
  - **The own-state control attenuates the slope.** At β = 2 on 100 paths, (a2) gives +1.36 and (b) +0.83.
  - **The daily cross-correlation has power.** It is positive under local volatility (P2, 100 paths: +0.065, 92% positive) and negative under SV leverage (ZL −0.19, 0% positive).
  - **L2 failures:** 2 here against 3.

**Two simulation figures don't survive more paths.** Both come from 20-path medians.
- **"All estimators have a small positive bias at β = 0 (+0.3 to +0.5)."** This is not supported. On 100 Z0 paths the medians are +0.00 (a1), +0.14 (a2), +0.07 (b), −0.01 (049 a) and +0.14 (049 b2), with bootstrap SEs of 0.08–0.19 and 49–57% positive. At n = 20 the median's SE is about 0.3–0.4, so the reported +0.3 to +0.5 is noise.
  - **What still stands:** a single record's sign is weak evidence, because the β = 0 spread is wide. The reason is the variance, not the bias.
- **The magnitudes at β = 2.** (a1)'s +2.74 is +1.95 (SE 0.21) on 100 paths, close to the truth. The own-state attenuation is about two-thirds of the truth for (a2) (+1.36) and two-fifths for (b) (+0.83): "about half" is a fair round figure for (b), less so for (a2).
- **None of this changes the readings,** which rest on signs and contrasts. I'd ask the analyst to drop the β = 0 bias sentence, or restate it as width, and to note that 20 paths per cell give medians with SE of about 0.2–0.4.

**The Deviation is honest.** Deviation 1 replaces a silent log-price cap at 30 with a retained-failure rule at |log S| > 5, after a crash and before any result was read. The diff shows the rule, the failure counts and summaries restricted to successful paths. The real-data lines printed before the crash were not used. `run.py` is unchanged from Deviation 1 to the results.

**The readings are fair, with the bias correction above.**
- **The estimators work.** The daily and within-day estimators recover a true local-volatility β.
- **The own state attenuates.** The own-state versions attenuate, and removing the own state turns the across-day association positive in E5 and on run-up segments, against negative in calm controls.
- **Within-day β is confounded** by the return–volatility correlation.
- **The daily-scale sign difference** (positive in E5 and the class-B run-ups, negative in controls) argues against a purely intraday order-flow mechanism, without telling local volatility from positively correlated stochastic volatility. The report says so.
- **The caveats are stated:** hindsight segments, and the no-state estimators' lack of simulation validation.

Verdict: reproduced
