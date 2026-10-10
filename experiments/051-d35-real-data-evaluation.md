---
id: "051"
title: "D35 item 25: the repaired score on real data, calibrated on a fixed 1995–2010 calm reference, against v1 and calibrated GSADF, evaluated as item 16 did"
status: reproduced
direction: D35
claims: ["045", "055"]
code: experiments/051/
---
## Question

LAB_REQUEST.md sixth addendum, item 25, per the PM's gated note `2026-10-08-d35-item25-gated.md` and math's
recommendation (FINDINGS "D35 item 25 calibration reference"; contract `checks/d35-item25-reference/README.md`).

**The scores:** the repaired score, the common-fitter numerical LR of experiment 050 (revision-1 fitter, unchanged),
and two comparators on the same windows.

**The calibration:** all three are empirically calibrated by claim 045's strict rank rule on one fixed historical
reference of calm-start windows.

**The question:** on daily real data, compared with v1 (claim 055) and calibrated GSADF:
- (i) how often does each score flag across 039's unselected universe, by period, and on calm and other starts?
- (ii) does it carry predictive content for forward drawdowns and returns?
- (iii) how does it rank the consensus bubble episodes against mechanical controls?

**Job: performance on real data.**
- No real-data false-alarm guarantee is claimed. Claim 045 applies only under its stated law conditions, and no
  real-data exchangeability or TV budget is established.
- Rates on calm starts after 2010 are empirical rates, not certified size. The consensus ROC is optimistic.

D35's third and last experiment.

## Design

**Windows.**
- **Calendar:** the complete ^GSPC session calendar (039's pinned cache, adjusted daily closes).
- **Input:** each input is exactly 379 positive finite prices on 379 consecutive ^GSPC sessions. The first 126
  returns train the state and the last 252 are scored.
- **Inputs:** no forward fill, interpolation or compression.
- **Ends:** on the first ^GSPC session of a month.
- **Window ID:** (symbol, first session, last session).

**Evaluation sample** (the PM's default, ROADMAP D35).
- **Frame:** every 039 universe name and month-start end with a complete input, and with 039's forward coverage rule
  (at least 99% of the 126 forward sessions present). The frame is counted in the manifest.
- **Sample:** sorted by ID, then `numpy.random.default_rng(20261051).choice(frame, 10000, replace=False)`. No filtering
  by calmness, score, forward value or label.

**Consensus records.**
- **Rebuild:** experiment 021's 33 full-window positives and 103 mechanical negatives, each rebuilt to the 379 sessions
  ending at its original full-window endpoint. A changed lookback is flagged.
- **Unavailable:** a record without a complete 379-session ^GSPC-calendar history stays requested, labelled
  unavailable. At registration 3 positives are unavailable (one each in E6, E7 and E8).
- **No re-selection:** no endpoint, duration or to-peak re-selection.

**Calibration reference** (math's contract, verbatim).
- **Candidates:** complete inputs ending 1995-01-01 to 2010-12-31, judged calm on the first 127 prices only: stock
  annualized RMS volatility ≤ 0.30 and drawdown ≤ 0.15; ^GSPC on the same dates ≤ 0.20 and ≤ 0.10.
- **Exclusions:** the exact IDs of the evaluation sample and the consensus records are excluded.
- **Order and selection:** order by SHA-256 of `20261151|symbol|start|end`, with ties by ID. Retain greedily with no
  shared price date within a name, and stop at 999. If fewer survive, use all of them with the actual rank; never
  widen cutoffs or replace failed fits.
- **Overlap:** cross-name calendar overlap is allowed and reported.

**Manifest frozen before fitting.**
- `run.py manifest` writes `manifest.json`: frame count, sample IDs, consensus records, reference IDs and features,
  candidate and exclusion counts, same-name overlap check, end-year distribution, and cache SHA-256s. It reads
  training-period prices and metadata only, and runs no fitter.
- The manifest is committed before any score.

**Scores (experiment 050's conventions).**
- **The new score:** the revision-1 fitter (`experiments/050/fitter.py`), then `calibrate.score_fit`, with failures
  at −1.
- **v1:** `cev.score` logEd on the 379 prices.
- **GSADF:** r₀ = 38, on the 379 prices.
- **Failures:** v1 and GSADF nonfinite values go to −10³⁰⁰. Method-specific failures are reported, with no
  common-success denominators.

**Calibration.**
- **Cutoffs:** for each score separately, `calibrate.rank_cutoff` on the same reference IDs, at α = 1/20 (primary),
  1/100 (item 16's charter ROC level) and 1/10 (secondary). With 999 reference windows the ranks are 950, 990 and 900.
  Strict exceedance only.
- **Not used:** 040/045's interpolated, tie-inclusive cutoffs. No level is selected afterwards, and no cutoff is tuned
  per period.

**Time ordering.**
- **Holdout:** the primary temporal holdout is evaluation windows whose full input starts on or after 2011-01-01.
  Earlier windows and windows crossing the boundary are retrospective comparisons.
- **Retrospective consensus:** consensus records ending before 2011 are retrospective, never contemporaneous
  monitoring.

**Analyses** (item 16's, as in experiment 039).
1. **Flag rates:** each score at each level, on the full sample, the holdout and the retrospective rows.
   - Within each: all starts, calm starts (the identical training-only predicate) and other starts. Other starts
     measure transport.
   - By period (1995–99, 2003–07, 2009–19, 2023–26, by end year) and by end year.
2. **Forward regressions:** on the full unfiltered sample, with 039's outcomes (forward maximum drawdown and log return
   at 63 and 126 sessions from the last close).
   - **Regressors:** each score as a percentile rank within its end date (ranks among the sampled windows at that
     date), with an intercept. Each score alone, then a horse race of all three.
   - **Errors:** Driscoll–Kraay with end-month groups and ⌈1.5 × 18⌉ = 27 lags (primary); two-way clustered by end
     date and name (robustness); end-date fixed effects (secondary).
   - **Out of sample:** coefficients trained on rows whose whole outcome interval ends before 2011-01-01 (incomplete
     labels embargoed), frozen and evaluated on the holdout. Out-of-sample R² is measured against the training mean,
     with a block bootstrap over end months (18-month blocks, 1,000 resamples, seed 20261351).
3. **Consensus, labelled optimistic:**
   - ROC AUC per score, with a blocked bootstrap over 021's rows (1,000, seed 20261251);
   - positives' and negatives' flags at the reference cutoffs at each level, with unavailable records listed.
4. **Claim 045, assumption-indexed:** the pointwise bound min(1, α + ε_joint) at assumed budgets ε_joint ∈ {0, 0.01,
   0.025, 0.05}, i.e. 0.05, 0.06, 0.075 and 0.10 at 5%.
   - These are sensitivity values, not estimated budgets.
   - **Why the budgets cannot be estimated here:** no joint-exchangeability, TV or calibration-conditional premise is
     shown, and claim 045 part 3 rules out inferring validity on unselected targets from calm calibration.
   - **Shared calibration:** it licenses no binomial inference for dependent window flags, and no familywise,
     false-discovery or sequential guarantee.

**Runtime.**
- **Estimate:** about 11,100 windows at about 6.4 s per window on 7 workers, about 2.9 hours.
- **Smoke tier:** 14 windows, for timing only; scores not read.
- **Budget:** a smoke projection over 5 hours is recorded under Deviations before the full run.
- **Order:** the registration merges first, and then the run (the only pooled job).

**Scope and selection limitations.**
- **Selection:** current S&P 500 constituents (survivorship), and required forward coverage.
- **Data:** daily adjusted closes. The Student-t normalization source audit is still open.
- **Other limits:**
  - cross-name common shocks;
  - the historical reference against later evaluation;
  - ranks among sampled names, not the full universe.
- **The repaired score's limits:** the model is statistical, not a pricing-martingale test; the numerical LR is not an
  e-value; there is no sequential claim.

## Deviations

**Deviation 1 (2026-10-08, before any fit was read): manifest facts and smoke timing; no design change.**
- **Manifest** (`manifest.json`, eec5696f):
  - the frame has 152,677 windows;
  - 18,634 calm-start reference candidates, the same as math's independent feasibility count; 17,445 remain after
    exclusions;
  - 999 reference windows across 333 names, with 0 same-name overlaps;
  - 133 of 136 consensus records available. The 3 unavailable are positives in E6, E7 and E8, with incomplete
    ^GSPC-calendar histories.
- **Timing:** the smoke tier scored 14 windows with a median of 6.0 s per window; the full run projects to 2.6 hours,
  within budget. Smoke scores were not read.

**Deviation 2 (2026-10-08, before any output): a false start, restarted unchanged.** The first full run (started
22:19) failed within seconds with FileNotFoundError on `data/d24/yahoo_^GSPC.json`. The worktree's data symlink was
briefly removed while the workers started, an operator error. No window was scored and no output was written. No
stray process remained. The run was restarted with identical code and manifest.

**Deviation 3 (2026-10-08, during the run and before any result was read): an analysis entry point; one property
noted.**
- **The entry point:** `run.py analyze` reruns the analysis from `windows.json.gz` (0b760d04). It was tested on
  synthetic stand-in records, never real scores. Scoring and analysis code are unchanged, and the reported results come
  from the full run's own analysis.
- **The property, noted rather than changed:** the scores enter as percentile ranks within end date, so every date
  has the same mean rank. The end-date fixed-effects coefficients are therefore identical to the pooled ones by
  construction. The fixed-effects specification adds nothing here and is not tabulated separately.

**Deviation 4 (2026-10-09, after the Results; per math's note `2026-10-09-exp051-reading-corrections.md` and
`checks/d35-item25-reading/README.md`): reading corrections.** No new fit and no change to any registered output.
Math's independent recount agrees with all counts, cutoffs, AUCs and the 16 OLS, Driscoll–Kraay and out-of-sample
point estimates; it is not a reproduction or a bootstrap replay. Corrected in place:
- **Overstated wording:** "is calibrated", "does not detect anything" and "absent or reversed" become empirical
  calibration with no demonstrated useful drawdown prediction or episode separation for this fixed daily algorithm.
  Sequential certification remains unresolved.
- **Period bins:** they omit 2,255 rows (119 flags). Annual rates range 1.35–16.22% (2018: 55 of 339), so "near
  nominal everywhere" is removed.
- **The calm holdout's 7.53%** is one rate at one shared random cutoff: neither a TV-budget estimate or lower bound,
  nor a refutation of the marginal guarantee. Budgets are unsupplied, independently of the observed rate.
- **Denominators:** the AUC uses 30 available positives and 103 negatives, while the flag counts use 33 requested
  positives. The new score's AUC interval includes 0.5.
- **Regressions:** they test continuous ranks, not flags. The inherited `pct_rank` breaks ties in symbol order (6,550
  new-score zeros). The primary outputs are not reranked; math's average-rank sensitivity (drawdown t 0.81 and 0.95,
  126-session return t −1.39) is cited as a sensitivity.
- **Comparison wording:** v1 has a negative drawdown association (t about −3), so "only GSADF has predictive content"
  becomes "GSADF has the clear positive drawdown association and about 1% holdout gain". Nonsignificance proves no
  absence of signal.
- **Forward coverage:** one row has 125 of 126 forward sessions (FISV, missing session 94). That is allowed by the
  registered 99% coverage rule, and its return endpoints are unchanged. No correction.

## Results

**Status: reported (2026-10-09).** `experiments/051/run.py full`, with the manifest frozen at eec5696f, 2.51 hours on
7 workers.
- **Outputs:** `results.json`, `summary.csv`, `windows.json.gz` (per window) and `manifest.json`.
- **Windows:** 11,132 (999 reference, 10,000 sample, 133 consensus).
- **Fits:**
  - every window's fit completed, with no new-score failure;
  - 5 of 200,376 optimizations did not succeed (retained; another candidate covered each);
  - neither v1 nor GSADF had a method failure.
- **Labels:**
  - **Empirical rates:** all rates are empirical, not certified real-data size. Claim 045's premises are not
    established for these windows.
  - **Shared calibration:** all windows share one calibration, and flags are dependent across windows. No binomial
    intervals are given.

**Calibration** (999 calm 1995–2010 reference windows; ranks 950, 990 and 900; strict exceedance).
- **New score:** cutoffs 0.664 (5%), 0.861 (1%) and 0.486 (10%).
- **GSADF:** 3.005, 3.965 and 2.570.
- **v1:** cutoff 0 at both 5% and 1%. That is the tie at log e = 0 (the null-member numerator, experiment 049), so v1
  flags almost nothing at these levels.

**1. Flag rates on the 10,000-window universe sample** (5% / 1% / 10%).

| rows | n | new score | v1 | calibrated GSADF |
|---|---|---|---|---|
| all | 10,000 | 4.9 / 0.6 / 9.3% | 0.8 / 0.8 / 13.2% | 5.9 / 1.6 / 10.4% |
| holdout (input starts ≥ 2011), all starts | 5,033 | 5.0 / 0.6 / 10.0% | 0.7 / 0.7 / 13.0% | 5.8 / 1.7 / 9.8% |
| holdout, calm starts | 1,899 | **7.5** / 0.5 / 14.5% | 1.1 / 1.1 / 13.3% | 5.2 / 2.1 / 9.3% |
| holdout, other starts | 3,134 | 3.5 / 0.6 / 7.2% | 0.5 / 0.5 / 12.9% | 6.2 / 1.6 / 10.1% |
| retrospective (start < 2011), all | 4,967 | 4.7 / 0.7 / 8.6% | 0.9 / 0.9 / 13.3% | 5.9 / 1.5 / 11.0% |

- **By period, at 5%:**
  - the new score is 4.0–4.9% in the four labelled periods: 1995–99 4.8%, 2003–07 4.8%, 2009–19 4.9%, 2023–26 4.0%;
  - those bins omit 2,255 rows (119 new-score flags; 2000–02, 2008, 2020–22). By end year the new score's rate ranges
    from 1.35% to 16.22% (2018: 55 of 339; 2022: 31 of 405; 1999: 3 of 223), in `universe_by_end_year`;
  - GSADF is higher in 1995–99 (7.6%) than in the others (3.8–4.1%);
  - v1 is 0.5–1.6%.
- **Calm-start holdout:** the new score flags *calm* starts more often (7.5% in the holdout) than other starts (3.5%).
  Calm holdout windows are judged by the same training-only predicate as the reference, yet flag above 5%.
  - It is one rate at one shared, randomly realized cutoff. It is not an estimate or lower bound of a TV budget, nor a
    refutation of claim 045's marginal exchangeable guarantee (Deviation 4).
  - It is not a certified false-alarm rate.

**2. Forward regressions** (full sample; percentile ranks within end date; Driscoll–Kraay t, 27 lags; out-of-sample R²
on the holdout from frozen pre-2011 coefficients, with block-bootstrap SE).
- **What they test:** continuous ranks, not flags.
- **The rank convention (Deviation 4):** the inherited `pct_rank` gives tied values distinct ordinal ranks in input
  order (symbol order); the new score has 6,550 zeros.
- **Average-rank sensitivity:** math's independent check (`checks/d35-item25-reading/README.md`) gives new-score
  drawdown t 0.81 and 0.95, and 126-session return t −1.39. This is a sensitivity, not a replacement for the
  registered result.

| outcome | new score: coef (t_DK) | v1: coef (t_DK) | GSADF: coef (t_DK) | horse race OOS R² (SE) |
|---|---|---|---|---|
| max drawdown, 63 sessions | +0.002 (0.55) | −0.021 (−3.18) | **+0.026 (4.94)** | 1.00% (0.43) |
| max drawdown, 126 sessions | +0.005 (0.96) | −0.025 (−2.99) | **+0.036 (5.46)** | 1.16% (0.63) |
| log return, 63 sessions | −0.005 (−1.12) | +0.009 (1.28) | +0.009 (1.58) | −0.07% (0.10) |
| log return, 126 sessions | −0.017 (−1.81) | +0.010 (1.00) | +0.009 (0.86) | −0.13% (0.15) |

- **Single-score out-of-sample R²:**
  - new score: 0.01% and −0.03% for drawdowns;
  - GSADF: 1.07% (0.33) and 1.12% (0.44);
  - v1: 0.05% and 0.14%.
- **The new score shows no demonstrated drawdown prediction.** Its drawdown slopes are not significant and its
  out-of-sample R² is about 0. Its return slope at 126 sessions is negative and marginal (t_DK −1.81, two-way t
  −2.27; −1.39 under average ranks). Nonsignificance does not prove absence of signal.
- **v1's rank has a negative drawdown association** (t_DK about −3), with out-of-sample R² about 0.
- **GSADF's rank predicts larger forward drawdowns**, as in experiments 039 and 045, with out-of-sample R² about 1%.
  In the horse race it keeps its coefficient; the new score adds nothing.

**3. Consensus episodes (labelled optimistic).**
- **Coverage:** 133 of 136 records are scored. Unavailable: 000660.KS (E6), ^N225 (E7) and 000001.SS (E8), all
  positives with incomplete ^GSPC-calendar histories. All 133 inputs have a lookback different from the original
  episode window (fixed 379 sessions ending at the original endpoint).
- **AUC** (30 available positives and 103 negatives; blocked bootstrap 95% interval, by 021 row):
  - new score 0.34 (0.19–0.57);
  - v1 0.31 (0.11–0.45);
  - GSADF 0.48 (0.27–0.77).
- **Flags at the reference cutoffs** (positives of 33 requested / negatives of 103):

  | score | 5% | 1% | 10% |
  |---|---|---|---|
  | new score | 3 / 20 | 1 / 12 | 4 / 28 |
  | v1 | 0 / 2 | 0 / 2 | 5 / 14 |
  | GSADF | 6 / 6 | 5 / 0 | 6 / 12 |

- **Calm controls versus episodes:** the new score flags the calm mechanical controls more often than the bubble
  episodes, 20 of 103 negatives against 3 of 33 requested positives at 5%. This is consistent with 049's finding that
  the variance elasticity is about 0 in run-ups and positive in calm large caps.
  - Its AUC interval (0.19–0.57) includes 0.5, so the observed below-chance ranking does not prove a population
    reversal.
- **GSADF at 1% flags 5 positives and no negatives.**

**4. Claim 045, assumption-indexed.** At 5% the pointwise bound is 0.05, 0.06, 0.075 or 0.10 under assumed joint
budgets of 0, 0.01, 0.025 or 0.05.
- These are sensitivity values. The budgets are not supplied, and that holds independently of any observed rate.
- The 7.5% calm-holdout rate certifies no nonzero budget.

**Reading** (item 25).
- **The repaired score is empirically calibrated and it fires, but it shows no demonstrated useful drawdown prediction
  or episode separation** for this fixed daily algorithm (revised by Deviation 4).
  - **Firing rate:** it flags 4.9% of the sample at 5%, unlike v1 (0.8%). The rate varies by end year (1.35–16.22%).
  - **Prediction:** its drawdown slopes are not significant (t ≤ 0.96), with out-of-sample R² about 0.
  - **Consensus:** it flags 3 of 33 consensus positives against 20 of 103 controls at 5%. Its AUC is 0.34, with an
    interval that includes 0.5.
  - **What this does not show:** nonsignificance does not prove the level-elasticity signal absent or reversed. It is
    consistent with experiment 049's diagnosis.
  - **Still open:** sequential certification remains unresolved.
- **Calibration transport:** calm-start windows after 2010 flag at 7.5% at the shared 1995–2010 calm reference's cutoff,
  under the identical calm predicate. That is an empirical observation at one cutoff, not a budget estimate.
- **Calibrated GSADF has the clear positive drawdown association:** t about 5, and about 1% out-of-sample R² gain on
  the holdout. At 1% it flags 5 positives and no controls. This repeats experiments 039, 040 and 045.
  - v1's rank has a negative drawdown association (t about −3), without out-of-sample gain.
- **For D35's kill criterion** ("the repaired score fires on some real data with controlled false alarms and carries
  predictive content"):
  - it fires at about the nominal overall rate, with large year-to-year variation;
  - it shows no demonstrated drawdown prediction and no episode separation;
  - together with 049 and 050, this points to the targeted signal, not the construction, as the likely limit. That
    is a reading, not a proof;
  - the decision is math's and the PM's.
- **Scope:**
  - daily adjusted closes of current S&P 500 constituents (survivorship);
  - required forward coverage;
  - a fixed calm reference with no established exchangeability;
  - the Student-t normalization audit open;
  - ranks among sampled windows;
  - consensus lookbacks changed to the fixed length.

## Review

Reviewer, 2026-10-09, against main at `dcd12f10`, which contains the results commit `e0f61e36`.

**Method.** I wrote my own code from the Design, without reading `experiments/051/run.py` except the Deviation 3 diff. It is committed as `checks/review/exp051/reproduce.py`, with its rerun command in its header, and runs in under a minute on 2 workers. A full rescoring needs about 2.5 hours on 7 workers, so the reproduction has three parts.
- **(C) The frozen manifest,** rebuilt from the pinned caches with my own window, frame, sampling and reference rules.
- **(A) Every analysis,** recomputed from the stored per-window scores.
- **(B) A rescoring spot check** of 40 sampled and 6 consensus windows, using my own contract fitter (experiment-050 review), v1 (experiment-021 review) and GSADF.
- **Not recomputed:** the bootstrap SEs, the two-way clustered errors and the claim-045 sensitivity values, which are arithmetic.

**Reproduced.**
- **(C) The manifest, exactly.**
  - **Calendar:** 14,313 ^GSPC sessions.
  - **Frame:** 152,677 windows. This needed an end ≥ 1995-01-01 restriction (experiment 039's span) that the Design does not state; without it the frame is 194,548.
  - **Sample:** all 10,000 seeded IDs are identical.
  - **Reference:** 18,634 calm candidates and 17,445 after exclusions. All 999 hash-ordered greedy reference windows are identical in order, across 333 names, with identical calm features.
- **(A) Calibration, flag rates and consensus, exactly.**
  - **Cutoffs:** new score 0.664/0.861/0.486, GSADF 3.005/3.965/2.570, and v1 0/0.
  - **Flag rates:** every row of table 1, for example holdout calm starts at 7.5/0.5/14.5% for the new score and other starts at 3.5%. Every period rate: the new score at 4.8, 4.8, 4.9 and 4.0%, and GSADF at 7.6% in 1995–99.
  - **Consensus:** AUCs 0.34, 0.31 and 0.48. Flags 3/20, 1/12 and 4/28 (new), 0/2, 0/2 and 5/14 (v1), and 6/6, 5/0 and 6/12 (GSADF).
- **(A) Regressions and out-of-sample R².**
  - **v1 and GSADF:** they match. GSADF gives +0.025 (t 4.94) and +0.034 (5.47) on the drawdowns; v1 gives −0.020 (−3.18) and −0.024 (−2.99).
  - **Out-of-sample R²:** GSADF 1.04% and 1.11%; horse race 1.00%, 1.16%, −0.08% and −0.15%. The new score is about 0.
  - **The new score's slopes** match only under one rank convention; see below.
- **(B) Rescoring.**
  - **v1** within 6.5×10⁻⁴ and **GSADF** within 2.6×10⁻⁵.
  - **The new score:** median gap difference 3×10⁻⁹. One window has a 0.30 gap difference, a different local optimum. The new score's 5% flag agrees on all 46 windows.

**One analysis convention changes a reported t statistic.** 65.5% of sampled windows score exactly 0 on the new score (no positive gap), so its within-end-date percentile rank depends on how ties are broken (`checks/review/exp051/rank_ties.py`).
- **The published slopes** (+0.002, t 0.55; +0.005, 0.96; −0.017, −1.81) are reproduced exactly only by **ordinal** ranks. These order tied windows by their position in the sample, which is arbitrary.
- **With average ranks for ties,** which is experiment 039's convention and the one I matched there, the slopes are +0.004 (0.82), +0.006 (0.95) and −0.017 (−1.39).
- **What it changes.** The drawdown reading is unchanged: the new score has no detectable drawdown content. The "negative and marginal" 126-session return slope weakens from t −1.81 to −1.39. I'd ask the analyst to state the tie convention, report average-tie ranks as primary, and drop the marginal return-slope sentence or qualify it as convention-dependent. v1's ties are fewer, and its slopes barely move.

**The Deviations are honest.**
- **Order.** The registration (22:16:34) and frozen manifest (22:16:53) were committed before any fit, and I reproduced the manifest exactly.
- **Deviation 1** records manifest facts and smoke timing only.
- **Deviation 2** is a false start that wrote no output, restarted unchanged.
- **Deviation 3** adds the `analyze` entry point (diffed), and notes the end-date fixed-effects identity, which is correct: within-date percentile ranks have the same mean on every date.
- **The code.** `run.py` is unchanged from Deviation 3 to the results.
- **One unstated frame restriction.** The Design's frame does not state the 1995 lower bound on ends. It is implied by "039 universe", and the manifest was frozen with it.

**The readings are fair, subject to the tie-convention point.**
- **Calibration.** The repaired score flags near its nominal rate by period.
- **No signal.** It has no drawdown content, and ranks the consensus bubbles below the calm controls (3 of 33 against 20 of 103 at 5%).
- **Transport.** The calm-start holdout's 7.5% is an empirical transport gap from the 1995–2010 reference.
- **GSADF** is again the only score with drawdown content, with out-of-sample R² about 1%.
- **The labels** stay honest: empirical rates, dependent flags and assumption-indexed claim-045 values.

Verdict: reproduced
