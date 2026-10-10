---
id: "055"
title: "D37 item 30: simulation validation of the daily market-scale level statistic (coefficient recovery, matched and transported calibration, power and delay) against calibrated GSADF and 051's score"
status: reproduced
direction: D37
claims: ["045"]
code: experiments/055/
---
## Question

LAB_REQUEST.md eighth addendum, item 30, per the PM's gated note `2026-10-09-d37-validate-and-test.md` and mathb's
design `checks/d37-statistic-design/README.md` (FINDINGS "D37 statistic design").

**The statistic:** variance ∝ w · m_t^g · exp(β x), with m_t the lagged 20-session SPY squared-return scale,
normalized once on training, and β the **full** log-variance/log-price exponent. Only β differs between the two
sides. Is it fit for a real-data reading?
- **(1) Recovery:** does it recover a known β in its own discrete family, with the prefitted nuisance and with the
  true (oracle) nuisance?
- **(2) CEV and stochastic volatility:** what does it report on discretized CEV p = 1.5 and 2 diffusions with
  market-driven and with own stochastic volatility, and on their p = 1 leverage controls?
- **(3) Calibration:** does its strict-rank calibration hold when calibration and evaluation share a law (matched)?
  How does it transport to 050's nulls and stresses?
- **(4) Comparison:** what are its power and time-to-first-alarm against calibrated GSADF and 051's frozen score?

**Job:** verification in the statistic's own family (parts 1 and 3, matched) and performance outside it (parts 2 and
3, transported). Discretized SDE cases are not certified strict-local-martingale samples.

**Decision gates** (mathb's, predeclared and exploratory, not simultaneous tests):
- **Recovery,** in the exact in-model β = 1 and β = 2 cells, reported separately for the oracle and the fitted
  nuisance:
  - at least 90% finite coefficient estimates;
  - a positive-estimate share of at least 80% of all requested paths;
  - absolute median coefficient error at most 25% of the true value.
- **Calibration:**
  - in matched β = 0 and negative controls, failure if a Wilson 95% lower limit exceeds 0.05;
  - **uninformative** if scoring failures exceed 10% or the cutoff is at least 1 (a low rate alone is not a pass);
  - the same diagnostics on transported 050 controls are labelled transport performance.

## Design

**Common path layout.**
- **Length:** 20 market warm-up + 252 fitting + 252 scored daily sessions, with 252 sessions per year.
- **Seeds:** `SeedSequence([20261037, family_id, role, path_id])`, with role 0 calibration, 1 evaluation and
  2 resolution.
- **Paths:** 499 calibration and 500 evaluation paths per null cell, and 500 per alternative cell. All methods share
  the paths. Stock and market observations get exactly the real procedure's treatment.

**The statistic** (mathb's design verbatim; `checks/d37-statistic-design/model.py` kernel reused).
- **Prior fit:** (μ, w, g, ν) at β = 0 on the 252 prior returns.
  - **Domains:** μ ∈ [−0.1, 0.1], w ∈ [10⁻⁸, 0.25], g ∈ [0, 2], ν ∈ {6, 10}.
  - **Starts:** for each ν, three deterministic starts at g = 0, 1 and 2.
  - **Solver:** μ and g mapped linearly and log w linearly to [0, 1]; D35's L-BFGS-B settings.
  - **Acceptance:** a fresh raw finite objective with positive variances; the 10¹⁰⁰ penalty is never accepted.
  - **Selection:** the largest objective, with ties to the lower ν and then the lower start. Every attempt is
    archived. If all attempts fail, the path scores −1.
- **Batch score:** A_N = sup_{β≥0} ℓ − sup_{β≤0} ℓ at N = 252, transformed by D35's `score_fit`.
- **Daily monitor:**
  - full-exponent support {1/8, 1/4, 1/2, 1, 2, 4, 8, 16} with weights 1/8;
  - log D_n is the β ≤ 0 profile on the whole prefix;
  - each prefix is sent as a `PrefixLog` to mathb's unchanged `checks/d36-monitor-calibration/monitor.py` on the
    schedule 1…252.
- **Profiles:** D36's version-2.4 doubling and bisection search in full-exponent units (bisection to width 10⁻¹⁰,
  at most 200 steps and 400 evaluations including the final one).
  - **Statuses:** `boundary_zero`, `interior`, `unresolved_tail`, `unresolved_budget`, `stagnation`,
    `numerical_failure`, `infinite_profile` (ray witness, rescaled), and `flat`.
  - Every failure scores −1.
- **Coefficient diagnostic:** the all-real-β profile maximizer of ℓ_252, with its status.
- **Daily rolling-volatility proxy correlation** (descriptive): corr(R_t, ½Δ log V_t), with V_t the mean of the last
  20 squared stock returns. It needs at least 30 valid pairs.
- **Variants, each with its own frozen threshold** (no union):
  - **fitted:** the primary statistic;
  - **oracle:** the true nuisance; in-model cells only, where it is defined;
  - **g0:** the paired diagnostic, the same statistic with g fixed at 0 and (μ, w, ν) fitted.

**Families and cells** (family_id in brackets).
1. **In-model** (market log variance AR(1) with coefficient 0.95, innovation s.d. 0.15, mean log(0.04/252); Gaussian
   market returns with mean −½ variance; the market proxy built from those returns).
   - **Stock:** variance-one Student-t innovations, μ = 0, baseline A_t = 2.25 M_t (g = 1). β = 0 in training and
     β ∈ {−1, 0, 1, 2} in scoring, anchored at launch.
   - **Cells:** I6m1 [1], I60 [2], I61 [3], I62 [4] (ν = 6); I10m1 [5], I100 [6], I101 [7], I102 [8] (ν = 10);
     G0 [9] (g = 0, A = 0.09/252, ν = 6, β = 0); persistent P1 [10] and P2 [11] (ν = 6; β = 1 and 2 in training
     and scoring, generating anchor at the first training price).
   - **Oracle:** w = 2.25 M_ref (g = 1), or 0.09/252 (g = 0). For the persistent cells, w is rescaled at launch to
     the actual baseline there.
2. **CEV and stochastic volatility** (050's S3/S4 simulator: κ = 2, θ = 0.09, ξ = 0.5, v₀ = 0.09; 10 sub-steps per
   day; p = 1 before launch and the chosen p after it, with the level reference reset at launch).
   - **(a) Market-driven** [20 + 3i + q]: one variance factor drives both stock and market. The market's price driver
     is −0.7 times that factor's driver plus an independent component, with p = 1 throughout.
   - **(b) Own stochastic volatility** [40 + 3i + q]: independent stock and market variance factors, with the market
     driver pair correlated −0.7.
   - **Indices:** i indexes stock price/volatility-driver correlation ρ ∈ {−0.7, 0, +0.7}, and q indexes
     p ∈ {1, 1.5, 2}.
   - **Constant-volatility CEV** [60 + q], with variance 0.09 and p ∈ {1, 1.5, 2}, and the in-model market process
     attached.
   - **Structural exponent:** β = 2(p − 1) (1 and 2).
   - **Resolution check:** on 100 evaluation paths per cell, 10 against 50 sub-steps with coupled Brownian
     increments. Reported: per-path failures, terminal-log and log-RV differences, and coefficient and alarm
     sensitivity.
   - **Failures:** a path whose log price leaves ±5 is a retained failure (050/053 convention); there is no capping.
3. **050 null robustness** [70–79]: C1–C5, O1, O2 and S1–S3 with 050's exact parameters and transitions, extended to
   524 sessions, with the in-model market process from (1) attached. Their half-slope β values are reported doubled.

**Calibration.**
- **Matched:** each null cell is calibrated on its own 499 calibration paths at α = 1/20 (rank 475; cutoff
  max(0, q_cal); +∞ if failures push the rank beyond the sample).
- **Alternatives** use the null with identical volatility, correlation and market construction:
  - I61, I62, P1 and P2 → I60; I101 and I102 → I100;
  - CEV cells (a) and (b) with p > 1 → their p = 1 cell at the same ρ;
  - constant-volatility CEV p > 1 → its p = 1 cell.
- **Transported:** I60's cutoff (g = 1, ν = 6, β = 0) applied to every null and stress cell.
- **Separate thresholds:** the batch scores (endpoint) and the monitor path maxima are calibrated separately.

**Comparators, on the same paths and scored intervals.**
- **Calibrated GSADF (daily prefix map):**
  - **The statistic:** the backward SADF series on the 504 daily closes (prior 252 + scored 252), with r₀ by 021's
    rule at n = 504. The prefix GSADF at scored day n is the running maximum of that series through day n.
  - **Path score and calibration:** the score is the path maximum, calibrated on the same references, with strict
    exceedance and no zero floor. The first alarm is the first day above the cutoff.
- **051's frozen score:** experiment 050's fitter and `score_fit` on the 378-return window (the last 126 prior
  returns, the D37 252 scored returns), at its registered endpoint only, calibrated at α = 1/20 on the matched null.
  - **Subset tier, declared now for runtime:** the first 100 calibration and the first 100 evaluation paths of every
    cell (rank 96 at n = 100). The run would otherwise take more than 6 hours.

**Outputs.**
- **Per path:** fitted and oracle β estimates with status, the true structural β, the log-level range and its
  correlation with log M, and the batch and monitor scores for each variant.
  - Also: the first alarm or none, GSADF, 051 where computed, the proxy correlation, and failures and boundary hits.
- **Per cell:**
  - bias, RMSE and positive-sign rate (oracle and fitted);
  - size or power with Wilson 95% intervals, matched and transported;
  - delay distributions with non-crossers retained at the horizon;
  - failure, infinite and unresolved proportions, and every cutoff.
- **The gate table.**
- **Archives:** code and uv.lock hashes, seeds and runtime. Per-path outcomes go to `paths.json.gz` (committed if
  under 50 MB).

**Implementation checks before generation** (`experiments/055/check.py`):
- a future market return cannot change an earlier scale or score;
- full-exponent β equals 2 × D36's β, through the D36 profile on the same fixture;
- oracle and prefit inputs stay separate;
- the profile matches brute force on fixtures;
- mathb's `checks/d37-statistic-design/check.py` passes.

**Runtime.**
- **Estimate:** about 32,000 paths at about 1 s each, plus 051 on about 8,400 paths at about 6 s each, on 7 workers,
  for about 3–4 hours.
- **Ordering:** run after experiment 054's pool finishes, with no concurrent pooled job.
- **Smoke tier:** 2 paths per cell, for timing only.
- **Budget:** a projection over 8 hours is recorded under Deviations before the full run.

**Scope.**
- Simulation only.
- Discretized SDEs are not exact strict-local-martingale laws, and a Student-t log-return model is not a pricing law.
- Matched calibration is claim 045's exchangeable case for complete simulated paths; transported results measure
  misspecification.
- The gates are exploratory and per cell.

## Deviations

**Deviation 1 (2026-10-09, before the full run; no result read): an import fix and smoke timing.**
- **The import fix:** `run.py` and `check.py` now load `analysis.py` and `run.py` by explicit path, and pass the run
  module to the analysis. Importing `run` by name could resolve to experiment 050's `run.py`, because 050 puts its
  directory first on `sys.path`. The same latent bug crashed experiment 054's analysis step.
- **No change to the statistic, simulators, comparators or analysis rules.**
- **The smoke tier:** 149 paths, 117 s wall, mean 4.8 s per path, nominally 6.5 hours.
  - **The projection is biased upward:** every smoke path has an index below 100, so all of them ran 051's subset tier
    (about 4.6 s each). In the full run, 051 runs on about 6,400 of the 33,600 paths, and the rest take about 0.2 s
    each (single-process test).
  - **The realistic projection** is about 1.4 hours, within the 8-hour budget. Smoke scores were not read.

**Deviation 2 (2026-10-09, after the Results; per mathb's note `2026-10-09-exp055-failure-accounting.md` and
`checks/d37-item30-reading-mathb/`): failure accounting in the derived summaries.** No new fit or simulation; the raw
path archive is unchanged. `analysis.py` was corrected and rerun on the saved archive (`run.py analyze`), and
`results.json` and `summary.csv` were regenerated.
- **Coefficients:**
  - **The bug:** missing coefficients had taken the score getter's −1 default and counted as finite.
  - **Corrected finite counts:** fitted N_C3 489 / 500, N_C4 489 / 500, N_O1 394 / 500 (471 simulated), N_S3
    499 / 500.
  - **Corrected medians:** N_C3 −2.60, N_C4 −2.77, N_O1 −48.1, N_S3 −2.74. g0 is corrected likewise.
  - **Unchanged:** positive-share denominators stay the requested paths, and the 12 recovery gates are unaffected.
- **051 subset tier:**
  - **The bug:** failed early paths without an 051 score had been dropped.
  - **The fix:** they now keep the registered −1 at n = 100. C3 is 3/100, C4 9/100 and O1 9/100 (O1's cutoff is now
    0), against the reported 3/99, 9/98 and 4/83.
- **Oracle:** outputs are marked unavailable outside the in-model cells (the transported "0" entries are removed).
- **Design wording:** the Design's "+∞ if failures push the rank beyond the sample" is incorrect. Retained finite −1
  scores leave n and the rank unchanged; +∞ arises only for an insufficient sample count.
- **Resolution:** mathb's fixed coarse-cutoff diagnostic finds 4 fitted-monitor alarm flips in 2,100 paired paths, so
  the scope is "coefficients insensitive; alarms nearly so".
- **P1:** its fitted positive share is 396/500, a failed gate. Prior-fit contamination is plausible but not isolated.
  Its batch power (36.8%) is now included in the in-model range.
- **No guarantee from calibration:** calm references from the same universe do not establish claim 045's
  post-selection premises or real-data size control.

## Results

**Status: reported (2026-10-09).** 34,078 paths (calibration, evaluation and resolution) in 1.71 hours on 7 workers
(Deviation 1).
- **Outputs:** `results.json` and `summary.csv`.
- **Archives:** per-path outcomes `data/d37/exp055/paths.json.gz` and per-prefix monitor scores
  `data/d37/exp055/prefix_scores.npz`, with code and uv.lock hashes in the archive.
- **Units:** β is the full exponent (β = 2(p − 1); 050's half-slopes are shown doubled).
- **Not applicable:** the "oracle" variant exists only in the in-model cells. Its transported "0" rates elsewhere in
  `results.json` are not applicable, not flags.

**1. Recovery gates** (in-model β = 1 and β = 2; 500 requested paths each).

| cell | fitted: finite / positive share / \|median error\|/truth | oracle: finite / positive / error | gate |
|---|---|---|---|
| I61 (ν 6, β 1) | 500 / 0.886 / 0.004 | 500 / 0.906 / 0.012 | pass |
| I62 (ν 6, β 2) | 500 / 0.980 / 0.007 | 500 / 0.976 / 0.005 | pass |
| I101 (ν 10, β 1) | 500 / 0.878 / 0.020 | 500 / 0.918 / 0.022 | pass |
| I102 (ν 10, β 2) | 500 / 0.990 / 0.009 | 500 / 0.996 / 0.006 | pass |
| P1 (persistent β 1) | 500 / **0.792** / 0.060 | 500 / 0.902 / 0.030 | **fitted fails** (positive share < 0.80) |
| P2 (persistent β 2) | 500 / 0.882 / 0.016 | 500 / 0.978 / 0.011 | pass |

- **The statistic recovers a known β in its own family:** every estimate is finite, and the median error is at most
  6% of the truth.
- **The one failure is prefit contamination:** when β is already active in training (P1), the β = 0 prefit absorbs
  part of it and the positive share drops to 79.2% (396 of 500). The oracle passes in the same cell.
  - Prior-fit contamination is the plausible explanation; it is not independently isolated (Deviation 2).

**2. Matched calibration on null cells** (each calibrated on its own law at α = 1/20).
- **Overall:** across the 22 null cells, the fitted statistic's matched flag rate averages **4.85%** (batch) and
  **4.61%** (monitor).
- **Gate failures** (Wilson lower limit above 0.05), 4 of the per-cell checks:
  - I100 oracle monitor, 7.6%;
  - N_C3 fitted batch and g0 batch, both 8.8%;
  - N_O1 fitted monitor, 7.0%.
- **Uninformative:** N_O1 (β = −40 in D37 units) has 15% simulation failures and is flagged uninformative.
- **Realized cutoffs:** these are realized-cutoff rates from one calibration sample per cell. The gates are
  exploratory and not simultaneous.

**3. Power** (matched calibration; flag rate at α = 1/20, batch / monitor; GSADF path maximum; 051 on its 100-path
subset).

| cell | fitted | oracle | g0 (no market scale) | GSADF | 051 |
|---|---|---|---|---|---|
| I61 / I62 (ν 6) | 0.39 / 0.31; 0.66 / 0.60 | 0.52 / 0.32; 0.80 / 0.67 | 0.19 / 0.19; 0.41 / 0.39 | 0.07; 0.11 | 0.27; 0.52 |
| I101 / I102 (ν 10) | 0.39 / 0.29; 0.71 / 0.58 | 0.54 / 0.43; 0.85 / 0.74 | 0.14 / 0.13; 0.32 / 0.30 | 0.08; 0.14 | 0.06; 0.21 |
| P1 / P2 (persistent) | 0.37 / 0.31; 0.63 / 0.57 | 0.49 / 0.32; 0.78 / 0.63 | 0.22 / 0.22; 0.40 / 0.39 | 0.11; 0.14 | 0.28; 0.33 |
| CEV, constant volatility, p 1.5 / 2 | 0.41 / 0.31; 0.72 / 0.61 | n/a | 0.42 / 0.31; 0.74 / 0.63 | 0.06; 0.10 | 0.11; 0.31 |
| CEV with market-driven SV (a), ρ = 0, p 1.5 / 2 | 0.13 / 0.13; 0.23 / 0.23 | n/a | 0.07 / 0.06; 0.12 / 0.10 | 0.08; 0.11 | 0.29; 0.44 |
| (a), ρ = −0.7 | 0.22 / 0.17; 0.44 / 0.35 | n/a | 0.11 / 0.11; 0.19 / 0.13 | 0.02; 0.03 | 0.12; 0.23 |
| (a), ρ = +0.7 | 0.10 / 0.08; 0.22 / 0.20 | n/a | 0.09 / 0.08; 0.18 / 0.16 | 0.05; 0.09 | 0.12; 0.16 |
| CEV with own SV (b), ρ = 0, p 1.5 / 2 | 0.06 / 0.06; 0.10 / 0.10 | n/a | 0.05 / 0.05; 0.11 / 0.10 | 0.06; 0.10 | 0.08; 0.16 |
| (b), ρ = −0.7 | 0.11 / 0.12; 0.12 / 0.13 | n/a | 0.10 / 0.10; 0.13 / 0.12 | 0.05; 0.04 | 0.13; 0.12 |
| (b), ρ = +0.7 | 0.13 / 0.13; 0.20 / 0.19 | n/a | 0.12 / 0.13; 0.20 / 0.19 | 0.06; 0.08 | 0.10; 0.28 |

- **Delays:** the monitor's median first-alarm day among alarmed paths is 130–170 of 252 (195 in (b) at ρ = 0,
  p = 2). Calibrated GSADF's is 24–135, but it alarms far less often.
- **The market scale matters in the market-driven cells:** the g0 variant has about half the power in-model and
  under (a).
- **Own SV:** under own stochastic volatility (b), power at p = 2 is only 10–20%.

**4. Coefficient behaviour under stochastic volatility (structural β vs fitted β̂, median).**
- **Under own SV, β̂ tracks the return–volatility correlation even at p = 1** (structural β = 0):
  - (b) at ρ = +0.7 gives β̂ = 2.54 (76% positive), and at ρ = −0.7 gives −2.58;
  - under (a) at p = 1: ρ = +0.7 gives 1.00, and ρ = −0.7 gives −1.12.
  - The daily statistic therefore cannot separate a level-dependent diffusion from correlated stochastic
    volatility. This repeats 053's within-day finding at the daily scale.
- **Constant-volatility CEV:** β̂ is 1.02 at p = 1.5 and 1.89 at p = 2 (truth 1 and 2).

**5. Transported calibration** (I60's cutoff applied to every null; misspecification performance, not claim-045
failures). Fitted batch / monitor flag rates:
- **In-model:** the negative-β nulls give 0.4–1.0%, and G0 3.2% / 2.6%.
- **Market-driven SV at p = 1:** ρ = 0 gives 19% / 22%, ρ = +0.7 40% / 45%, and ρ = −0.7 2.4% / 3.4%.
- **Own SV at p = 1:** ρ = 0 gives 32% / 41%, ρ = +0.7 63% / 70%, and ρ = −0.7 11% / 14%.
- **050's laws:** C1 19% / 25%, C2 18% / 21%, C3 14% / 23%, C4 8% / 16%, O2 17% / 25%, S2 (regime) 33% / 44%,
  S3 (Heston) 8% / 11%; S1 (Merton) 3.8% / 3.4%, C5 7% / 7%.
- **The cutoff does not transport across volatility laws:** own-stock volatility clustering, positive SV correlation
  and regime switching all inflate flags several-fold when the reference law differs. Real-data references must
  therefore come from the target's own kind of history (item 31's calm-start reference). Even then, transport error
  is unknown.

**6. Comparators.**
- **Calibrated GSADF** has little power over these 252-session suffixes: 2–14% in every alternative cell.
- **051's frozen score** (100-path tier) reaches 21–52% in-model and up to 44% under (a).
  - Its matched null rates scatter widely (1–18%, mean 7.0% after Deviation 2's failure accounting).
  - This partly reflects the realized-cutoff noise of a 100-path calibration, but not all of the scatter is
    attributed to it.
  - Its rates are not comparable in precision to the 499-path cutoffs.

**7. Resolution** (10 against 50 sub-steps, 100 coupled paths per diffusion cell). There were no failures. Median
absolute differences: terminal log price 0.003–0.004, log RV 0.004–0.008, β̂ 0.02–0.07 (SV) and at most 0.003
(constant volatility).
- **Coefficients** are insensitive to the discretization at this level.
- **Alarms are not strictly invariant:** mathb's post-hoc diagnostic, at a fixed coarse cutoff, finds 4 fitted-monitor
  alarm flips in 2,100 paired paths (Deviation 2).

**Reading** (item 30; mathb's gates and D37's kill criterion).
- **Recovery:** the statistic recovers a known β in its own discrete family. 11 of 12 recovery gates pass, and the
  failing one (P1, fitted) is the predicted prefit contamination.
- **Matched calibration:** it holds near nominal (mean 4.6–4.9%), with 4 exploratory per-cell gate failures and one
  uninformative stress (O1).
- **In-model power:** it has real in-model and constant-volatility CEV power (37–72% batch; P1 36.8%), well above
  calibrated
  GSADF (7–14%).
- **Under realistic stochastic volatility it is weaker:** 6–44%, and only 10–20% at p = 2 with own SV.
- **Its β̂ responds to correlated stochastic volatility as strongly as to level dependence,** so a positive daily β is
  not specific to a local-volatility bubble. This is the same limit as 053, now at the daily scale.
- **Calibration transport is the decisive risk for real data.** A β = 0 reference cutoff applied to stocks with their
  own volatility clustering, positive leverage-sign correlation or regime switches flags 8–70%.
- **For D37's kill criterion and item 31:**
  - the validation does not show that the statistic "cannot recover a known β or keep calibration" in its family, so
    D37 proceeds;
  - item 31's empirical calibration on real calm-start references is essential;
  - the transported-law results warn that real-data flag rates may reflect volatility dynamics rather than level
    dependence.
  - The P1 failure and the SV non-specificity are stated, not hidden.
- **Scope:**
  - discretized SDEs, not certified strict-local-martingale laws;
  - matched calibration is claim 045's exchangeable case for complete simulated paths;
  - exploratory, non-simultaneous gates;
  - 051 only on its 100-path tier.

## Review

Reviewer, 2026-10-09, against main at `98290557`, which contains the results commit `0b1a3aa5`.

**Method.** I wrote my own code from the Design and mathb's design (`checks/d37-statistic-design/README.md`), without reading `experiments/055/*.py` or the design's `model.py` except the Deviation 1 diff. It is committed as `checks/review/exp055/reproduce.py`, with its rerun command and seed in its header, and runs in about 25 s on 2 workers.
- **(A) Every reported table,** recomputed from the committed per-path outcomes (`paths.json.gz`) with my own analysis code: recovery gates, strict-rank matched cutoffs and gates, power with the registered null mapping, GSADF without the zero floor, 051 on paths 0–99, transported I60 cutoffs, fitted-β medians, resolution pairs and O1's failures.
- **(B) Fresh paths** with my own simulators and my own statistic:
  - **the market scale:** the lagged 20-session squared-return scale, normalized by its training geometric mean;
  - **the prior fit:** (μ, w, g, ν) at β = 0 with three g starts per ν and D35's L-BFGS-B settings;
  - **the scores:** the batch half-line contrast and the all-real profile maximizer;
  - **the cells:** I60, I62, constant-volatility CEV at p = 1 and 2, and own-SV (b) at p = 1 with ρ = +0.7 and 0.
- **Not rerun:** the daily monitor (its scores enter (A) as stored path maxima), the oracle and g0 variants in (B), the delay distributions (stored only in the gitignored prefix archive), and the 050 null simulators.

**Reproduced.**
- **(A) Recovery gates, exactly.** Fitted finite / positive share / |median error| over truth:

  | Cell | Fitted | Oracle |
  |---|---|---|
  | I61 | 500 / 0.886 / 0.004 | 500 / 0.906 / 0.012 |
  | I62 | 500 / 0.980 / 0.007 | |
  | I101 | 500 / 0.878 / 0.020 | |
  | I102 | 500 / 0.990 / 0.009 | |
  | P1 | 500 / **0.792** / 0.060, fails | 500 / 0.902 / 0.030, passes |
  | P2 | 500 / 0.882 / 0.016 | |

- **(A) Matched calibration, exactly.**
  - **Means:** across the 22 null cells, the fitted mean flag rate is 4.85% (batch) and 4.61% (monitor).
  - **Gate failures:** the same four, I100 oracle monitor at 0.076, N_C3 fitted and g0 batch at 0.088, and N_O1 fitted monitor at 0.070.
  - **O1:** 77 simulation failures (15.4%) and 106 fitted scoring failures (21.2%), so it is correctly "uninformative".
- **(A) The power table, every cell exactly.** For example, I62 0.66/0.60 (fitted), 0.80/0.67 (oracle), 0.41/0.39 (g0), GSADF 0.11 and 051 0.52. CEV with own SV (b) at ρ = 0, p = 2 is 0.10/0.10.
- **(A) The coefficient medians.** Own SV (b) at p = 1 gives +2.54 at ρ = +0.7 and −2.58 at ρ = −0.7. Market-driven (a) gives +1.00 and −1.12. Constant-volatility CEV gives 1.02 and 1.89.
- **(A) Transport.** Every I60 rate in section 5 matches: for example SVb ρ = +0.7 at 62.6/69.8%, S2 at 32.8/44.4% and S1 at 3.8/3.4%.
- **(A) Resolution.** The SV medians of |10 − 50 sub-step| differences are 0.0035 (terminal log price), 0.006 (log RV) and 0.036 (β̂), and there are no failures.
- **(B) My own implementation agrees within Monte Carlo error.**
  - **I62,** with my own 300-path I60 cutoff: 64.3% [58.8, 69.5], against 66%; β̂ median +1.97, 98% positive.
  - **Constant-volatility CEV at p = 2:** 77.3% [72.3, 81.7], against 72%; β̂ +1.89.
  - **The own-SV non-specificity** reproduces on fresh paths. At structural β = 0 and ρ = +0.7, β̂ has median +2.58 (88% positive), against +2.54 (76%). At ρ = 0 it is +0.10, against −0.07. The fitted market exponent g is about 0, as expected with an independent market.
  - **The I60 null** flags 2.7% [1.4, 5.2] under my own cutoff.

**One wording point.** Section 7's "terminal log price 0.003–0.004, log RV 0.004–0.008" describes the SV cells. The constant-volatility pairs differ by about 0.0002, which is smaller still, so nothing changes.

**The Deviation is honest.** Deviation 1 changes only how `analysis.py` and `run.py` are loaded (by explicit path, with the run module passed in), as diffed, after the same `sys.path` collision as experiment 054. It corrects the smoke projection's upward bias with a stated reason. The code is unchanged from Deviation 1 to the results.

**The readings are fair.**
- **In its own family** the statistic recovers β, 11 of 12 gates passing. P1's failure is the predicted prefit contamination, and the oracle passes there.
- **Matched calibration** is near nominal, with the four exploratory per-cell gate failures stated.
- **In-model and constant-volatility CEV power** is far above calibrated GSADF over 252-session suffixes.
- **Power falls under stochastic volatility,** to 10–20% with own SV at p = 2.
- **β̂ is not specific:** it tracks the return–volatility correlation at structural β = 0, and I reproduced this on independent paths.
- **I60's cutoff does not transport** across volatility laws (8–70%), which correctly makes item 31's own-kind calm references essential, without removing transport risk.

Verdict: reproduced
