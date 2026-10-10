---
id: "049"
title: "D35 diagnosis (item 23): volatility-level elasticity, an in-sample oracle check, and a decomposition of v1's log score on data already on disk"
status: reproduced
direction: D35
claims: ["055", "054"]
code: experiments/049/
---
## Question

LAB_REQUEST.md sixth addendum, item 23, following the PM's note `2026-10-08-sixth-addendum-stop-and-diagnose.md`.
The lab's likelihood score almost never fires on real data: experiment 039, v1 fires on 0.1–0.2% of 416,380 windows
with an AUC of 0.16. This experiment asks why, on data already on disk:
- **(a) Is there a level signal?** Is the variance's elasticity to the price level above zero in run-ups, and below
  zero (the leverage effect) generally?
- **(b) Absent signal or bad construction?** In sample, does the best bubble alternative beat the null's profile? If
  not even in sample, the signal is absent. If in sample but not as v1 is built, the construction is the problem.
- **(c) Where does v1's log score go?** Split it into scale misfit, level dependence, drift, and null enlargement.

**Job:** diagnosis only. No test is claimed. The oracle uses the evaluation data and has no calibration.

**v1's construction** (`checks/d13-drift-total/total.py`, `checks/d14-cev-domain/total.py`):
- **Numerator:** the zero-drift CEV transition of the catalogue pair (p, κ), with p ∈ {0.5, 0.75, 1, 1.25, 1.5, 2} and
  κ ∈ {0.2, 0.3, 0.45}, chosen by training likelihood on the first ⌊(n−1)/2⌋ returns and evaluated on the rest.
- **Denominator:** the larger of the catalogue's p ≤ 1 evaluation maximum and the Gaussian log-return profile with free
  drift and free volatility on the evaluation half.

No diagnostic below has been computed when this Design is committed.

## Design

**Records** (data on disk; daily adjusted closes; times i/252; prices normalized by the first close).
- **Consensus records:** experiment 021's full-window positives (33) and mechanical negatives (103), via
  `experiments/021/negatives.py`.
- **Unselected sample:** a seeded random sample of 3,000 of experiment 039's L = 24 name-windows
  (`SeedSequence(20261049)`), via 039's `build_windows`, from `data/d24/`.
- **Run-up subset, defined before any diagnostic:** sampled 039 windows whose whole-window log return is in the top
  10% of that start date's windows (from 039's universe at that start).

**(a) Elasticity.**
- **Per record:** an ordinary least-squares regression of log monthly realized variance (the sum of squared daily log
  returns within each calendar month, months with at least 15 returns) on the log price at the month's start, with
  log ^GSPC monthly realized variance as a time control.
- **The slope β** is the variance's elasticity to the level: β = 2(p − 1) under CEV, and β < 0 is the leverage
  effect.
- **Reported:** β's distribution (median, quartiles, share above 0) for positives, negatives, the unselected sample
  and run-ups; and a pooled within-record regression per group with standard errors clustered by record.

**(b) In-sample oracle** (diagnostic only; evaluation half as in v1). Two comparisons:
- **(b1) v1's own comparison, with v1's rigidity removed on the alternative side:** the best zero-drift CEV with
  p ∈ {1.25, 1.5, 2, 3} and κ optimized continuously (log κ ∈ [log 0.02, log 5], bounded scalar search), against v1's
  denominator profile (Gaussian, free drift and volatility; and CEV p ≤ 1 with free κ).
  - **Reported:** the log ratio's distribution and the share above 0 and above log 20.
- **(b2) The repaired structure's in-sample likelihood ratio:** local-lognormal returns
  R_j ~ N(μΔ − v_j/2, v_j), with v_j = σ²(S_(j−1)/S₀)^β Δ.
  - Free μ, σ and β (the alternative, β > 0), against the same with β ≤ 0 (the null, which allows leverage), both
    fitted on the evaluation half.
  - **Reported:** the log-likelihood difference and the fitted β.

**(c) Decomposition of v1's raw log score** on the evaluation half, as an exact telescoping sum. With
ℓ(·) the evaluation log-likelihood:

    log raw = [ℓ(p_fit, κ_fit) − ℓ(p_fit, κ*_eval)]          scale misfit (≤ 0)
            + [ℓ(p_fit, κ*_eval) − ℓ(1, κ*_1)]                 level dependence (p_fit vs GBM, each at its best κ)
            + [ℓ(1, κ*_1) − ℓ_Gauss(μ̂, σ̂)]                    drift (zero-drift GBM vs free-drift Gaussian; ≤ 0)
            + [ℓ_Gauss(μ̂, σ̂) − D]                              null enlargement (D = v1's denominator; ≤ 0)

- **The terms:** κ*_eval is the evaluation-optimal κ at p_fit, and κ*_1 at p = 1.
- **Reported:** each term's median and share by group, and the share of records where each term is the largest
  negative contribution.

**Computation.**
- **Likelihoods:** floating-point CEV log kernels (`experiments/022/cev.py`, the same density as the v1 adapter),
  checked against the adapter's exact values on 20 records (reported maximum |Δ|). Gaussian profiles in closed form.
- **Optimization:** scipy bounded, with `minimize` for (b2).
- **Execution:** a single process, minutes. It does not run alongside a worker pool (046's run uses it).

**Outputs and routing.**
- Files: `results.json` (per-record values and group summaries) and `summary.csv`.
- **(b) goes to math as soon as it exists,** per the PM's note. The repair design does not wait for (a) or (c).

**Scope.**
- Descriptive. Realized variance is a noisy proxy.
- The oracle uses evaluation data, so it is not a test.
- Consensus labels; survivorship as in experiment 039.

## Deviations

**Deviation 1 (2026-10-08, with the run code and before any diagnostic): the implementation check.**
- **The check:** the floating-point v1 pieces in `experiments/049/run.py` agree with the exact adapter
  (`checks/d13-drift-total/total.py`) on 20 records (the first and last 10), with maximum |Δ log e| = 5.9 × 10⁻¹⁰.
- **Implementation notes:**
  - the Gaussian profile is the closed-form maximum likelihood with free mean and variance of the log returns, in
    price coordinates;
  - (b2) uses L-BFGS-B from three starting values of β, with bounds β ∈ [−20, 20] (alternative) or [−20, 0] (null);
  - the run-up subset ranks all 144,793 L = 24 windows within each start date before sampling.

**Deviation 2 (2026-10-08, before any output was written): a summary-stage bug.** The first full run computed every
record and then crashed while tabulating, on a Python scoping error in the "largest negative term" line. Nothing was
written. The fix (0be2284) uses the fixed term names and caches per-record diagnostics (`data/d35/diag049.json`) before
summarizing. The diagnostics are otherwise unchanged and were recomputed in full.

**Deviation 3 (2026-10-08, after the Results; requested by math's note `2026-10-08-d35-shared-model-input.md`): the
oracle's optimizer detail, and one correction.** `experiments/049/oracle_detail.py` recomputes 23(b) on the same
records with the same likelihood functions. It reproduces every per-record b1 and b2 value exactly. It also records
each fit's convergence status, its bound hits and the signed log-likelihoods (`oracle_detail.json.gz` since Deviation 4).
- **Families and domains:**
  - **b1 alternative:** zero-drift CEV transitions, p ∈ {1.25, 1.5, 2, 3}, κ ∈ [0.02, 5].
  - **b1 null:** the larger of the zero-drift CEV with p ∈ {0.5, 0.75, 1} and κ ∈ [0.02, 5], and the Gaussian
    log-return profile with free mean and variance (closed form, unbounded).
  - **b2:** local-lognormal, with β ∈ [−20, 20] for the alternative and [−20, 0] for the null, μ ∈ [−5, 5] and
    log σ ∈ [−8, 3]. Fitted by L-BFGS-B from β starts −2, 0 and 2.
- **Optimizer status:**
  - every one of the 3,136 records converged on both sides of b2, and no b1 fit failed;
  - every value is a feasible optimizer value on the bounded domain. **No global optimum is certified.**
- **Bound hits:**
  - **b1:** the best alternative and best null CEV fits never end at a κ bound. Some non-maximizing catalogue members
    do, in 11 positives, 0 negatives and 59 universe windows, so the reported b1 maximum is not certified over κ.
  - **b2 drift bound:** μ ends at its bound of 5 in 3 positives (GME, AMC, KOSS in episode E5). Their likelihoods
    are bounded-domain values.
  - **b2 variance collapse:** β ends at −20 on both sides in 4 records (2 negatives, 2 universe windows). This is the
    collapse direction math's note identifies, so these profiles are **unresolved**, and the supremum may be
    infinite. They stay in the counts. Their saved gaps are near zero, not exactly zero (Deviation 5).
- **The b2 log-LR (qualified by Deviations 4 and 5):** nested exact optima would give nonnegative gaps, since the
  alternative's domain contains the null's. But 624 saved local-fit gaps are slightly negative, all above
  −1.25 × 10⁻⁸.
- **Correction to (b)'s table:** the b2 "share > 0" column counted optimizer noise of order 10⁻¹² as positive. With a
  10⁻⁶ threshold it is 30% (positives), 34% (negatives), 26% (universe) and 37% (run-ups), not 70/76/68/72%. It
  equals the share with fitted β > 0. The column is corrected in place. The log 20 shares and every median are
  unchanged.
- **The labels stay as before:**
  - the b1 and b2 values are oracle, in-sample fitted likelihood ratios;
  - they are diagnostic, not e-values;
  - one finite-family fit not separating does not show that no bubble signal exists.

**Deviation 4 (2026-10-08, after the Results and the review; per math's note `2026-10-08-exp049-oracle-scope.md`):
reading scope and optimizer archive.** Math recounted the 3,136 records with `checks/d35-oracle-reading/check.py`.
The Results numbers are unchanged; the reading of (b) and (c) is corrected in place:
- **b2's domains:** b2 fits β ∈ [−20, 20] against [−20, 0], with μ ∈ [−5, 5] and log σ ∈ [−8, 3], not
  "β > 0 against β ≤ 0". At global optima it is the positive-β improvement clipped at zero.
- **The fitted β** is the full-model variance exponent, twice the exponent of the proposed repair. No
  unrestricted-null claim follows.
- **b2's counts:**
  - strictly above 0: 23 / 78 / 2,053 / 215 (positives, negatives, universe, run-ups);
  - above the diagnostic tolerance 10⁻⁶: 10 / 35 / 779 / 110;
  - above log 20: 4 / 12 / 225 / 42.
  - Every apparent gain at fitted β ≤ 0 is below 10⁻⁶: a numerical near-tie, not a substantive gain. This is not an
    error certificate or a changed testing rule.
- **v1's numerator** is a null-catalogue member (p_fit ≤ 1) in 15/33, 88/103, 2,287/3,000 and 192/297 records. The
  denominator contains that member, forcing raw evidence ≤ 1. Not every fitted numerator is a bubble alternative, and
  not all silence is attributable to scale mismatch.
- **(c)'s scale term** is a retrospective scale-fit penalty. It does not separate a training/evaluation shift from grid
  coarseness, and re-fitting on evaluation data is not a valid repaired numerator.
  - The earlier "removes 90–99% of the deficit" is replaced by the ratio of medians, 88–99%.
- **b1 also frees κ on the null side,** so it changes the null's catalogue scales too.
- **The optimizer archive is extended:** `experiments/049/oracle_detail.py` now keeps, per record:
  - every b1 candidate's fit (κ, log-likelihood, success, bound hit) and every b2 start (θ, log-likelihood, status);
  - the v1 numerator's p_fit;
  - math's checks: strict > 0 counts, the maximum apparent gain at fitted β ≤ 0, and the count of alternatives
    below the null's feasible point.
  - Failures are retained. There are no error bounds: the evaluation is floating point, without a certified error.
    The archive moves to `oracle_detail.json.gz` (1.4 MB; the uncompressed file would be 9.3 MB).
  - **The rerun's counts match math's recount exactly.** Strictly negative b2 differences (8 / 15 / 601 / 67) are all
    above −1.3 × 10⁻⁸: alternative fits a hair below the null's feasible point, which is optimizer tolerance. The
    largest apparent gain at fitted β ≤ 0 is 6.1 × 10⁻⁷.
- **Labels:** these are diagnostic oracle fitted likelihood ratios, not e-values. No simulated size or calibration
  follows from an in-sample log 20 comparison.

**Deviation 5 (2026-10-08, per math's note `2026-10-08-exp049-detail-labels.md`): two archive labels qualified.** No
fit or run. Math's extended `checks/d35-oracle-reading/check.py` matches the compressed detail to all 3,136 original
rows: 21,952 CEV candidates and 18,816 b2 start slots, all successful. The log 20 counts stay 4 / 12 / 225 / 42.
- **The legacy key `share_gt0` under `b2`** in `oracle_detail.py` and `oracle_detail.json.gz` means the share above
  10⁻⁹ (counts 12 / 51 / 1,081 / 126 for positives, negatives, universe, run-ups).
  - It is not the strict > 0 count (23 / 78 / 2,053 / 215, field `strict_gt0`), nor the 10⁻⁶ count (10 / 35 / 779 /
    110, field `gt_1e-6`).
  - The artifact is preserved unchanged; a comment in `oracle_detail.py` now documents the threshold. Under `b1`,
    `share_gt0` is the strict > 0 share.
- **The four joint β = −20 boundary records** (Deviation 3) have saved gaps 1.3074 × 10⁻¹², 0, 1.8190 × 10⁻¹² and
  −2.2737 × 10⁻¹³, not four exact zeros.
  - A bound hit does not prove the unrestricted profile diverges for these records. They are unresolved, not shown
    infinite.
- **Sign of the saved gaps:** 624 saved b2 gaps are negative (8 positives, 15 controls, 601 universe windows), all above
  −1.25 × 10⁻⁸. Nested exact optima would be nonnegative. Deviation 3's unqualified "never negative" line is
  corrected in place to agree with Deviation 4.

## Results

**Status: reported (2026-10-08).** `experiments/049/run.py` (0be2284), a single process. Outputs: `results.json`
(per-record values and group summaries) and `summary.csv`.
- **Records:** 33 consensus positives, 103 negatives, 3,000 sampled universe windows (297 of them run-ups).
- **Decomposition check:** the four terms sum to v1's log score to within 9 × 10⁻¹³ in every record.

**(c) Where v1's log score goes** (medians in nats; the term most often the largest negative):

| group | v1 | scale misfit | level dependence | drift | null enlargement | scale misfit largest |
|---|---|---|---|---|---|---|
| positives | −229.6 | −228.2 | −1.47 | −0.32 | 0.00 | 82% |
| negatives | −18.1 | −17.6 | +0.33 | −0.50 | 0.00 | 83% |
| universe | −12.1 | −10.6 | +0.27 | −0.28 | 0.00 | 79% |
| universe run-ups | −18.4 | −16.7 | 0.00 | −1.06 | 0.00 | 76% |

- **The largest term is a retrospective scale-fit penalty.** It is the gap between the training-chosen κ (from
  {0.2, 0.3, 0.45}) and the evaluation-optimal κ at the same p. In the median it is 88–99% of v1's score (Deviation 4).
  - This term does not separate a volatility shift between halves from the coarseness of the three-point grid.
  - Re-fitting κ on evaluation data is a diagnostic, not a valid repaired numerator.
- **v1's numerator is often a null member** (Deviation 4). The training fit chose p ≤ 1 in 15 of 33 positives, 88 of
  103 negatives, 2,287 of 3,000 universe windows and 192 of 297 run-ups. The denominator includes that member, so v1's
  raw evidence is at most 1 in those records, whatever the scale. The fitted numerator is not always a bubble
  alternative.
- The level-dependence term is near zero and of either sign. Drift costs about half a nat (one nat in run-ups).

**(b) In-sample oracle** (diagnostic only, on the evaluation half; share above 0 / above log 20; b2's share above 0
corrected by Deviation 3; optimizer detail in `oracle_detail.json.gz`).

| group | b1: best free-κ zero-drift CEV vs v1's null with free κ, median | b1 share > 0 / > log 20 | b2: local-lognormal β ∈ [−20, 20] vs β ∈ [−20, 0], log-LR median | b2 share > 10⁻⁶ / > log 20 | b2 fitted variance exponent β, median (share > 0) |
|---|---|---|---|---|---|
| positives | −38.0 | 18% / 9.1% | 0.00 | 30% / 12.1% | −1.65 (30%) |
| negatives | −1.47 | 22% / 4.9% | 0.00 | 34% / 11.7% | −1.29 (34%) |
| universe | −2.79 | 14% / 4.1% | 0.00 | 26% / 7.5% | −1.56 (26%) |
| universe run-ups | −3.01 | 22% / 7.7% | 0.00 | 37% / 14.1% | −0.63 (37%) |

- **Even in sample,** with κ freed on both sides (b1 changes the null's catalogue scales too), a zero-drift CEV
  alternative beats the null in only 14–22% of records, and by more than log 20 in 4–9%.
  - On the positives it is much worse in the median (−38): a CEV with p > 1 predicts relative volatility rising with
    the price, which their large rises do not show.
- **b2's in-sample likelihood ratio** fits the full range β ∈ [−20, 20] against β ∈ [−20, 0], with μ ∈ [−5, 5] and
  log σ ∈ [−8, 3]. At global optima it equals the positive-β improvement clipped at zero. It exceeds log 20 in
  7.5–14% of records (counts 4, 12, 225 and 42), **with no separation between positives (12.1%) and calm negatives
  (11.7%)**.
  - **Near-ties:** apparent gains at fitted β ≤ 0 are all below 10⁻⁶ and are numerical near-ties, not gains.
  - **No unrestricted-null claim follows:** both sides are bounded, and 4 records are unresolved collapse profiles
    (Deviation 3).
  - **The fitted β is the variance exponent,** twice the exponent of the proposed D35 repair's volatility function.
    It is negative in the median in every group: variance falls as the price rises.
  - Run-ups have the least negative β (−0.63), and the highest share above log 20 (14%), but this is not an
    explosive-level signature.

**(a) Realized-variance elasticity** (monthly log RV on log month-start price, with log market RV as the time
control).

| group | median β (share > 0) | pooled within-record β (record-clustered SE) |
|---|---|---|
| positives | +0.10 (64%) | +0.02 (0.08) |
| negatives | +0.35 (72%) | +0.59 (0.10) |
| universe | −0.40 (36%) | −0.27 (0.03) |
| universe run-ups | −0.08 (47%) | +0.05 (0.04) |

- **Unselected universe:** variance falls with the level, the leverage effect (pooled −0.27, t ≈ −10).
- **Run-ups and consensus positives:** the elasticity is about zero, not above zero.
- **Calm negatives:** it is positive (+0.59). They are mechanically selected calm large caps over six-year windows;
  that this exceeds the positives is itself evidence against a level-elasticity signature of bubbles in daily data.

**Reading** (the item-23 question).
- **Two features of the construction keep v1 silent** (revised by Deviation 4).
  - **Null-member numerators:** in 46–76% of records the training fit chooses a null-catalogue member (p ≤ 1). The
    denominator contains it, so raw evidence cannot exceed 1.
  - **Retrospective scale-fit penalty:** the training-chosen volatility from a three-point grid, with zero drift, is
    scored against a null that re-fits drift and volatility on the evaluation data. This is the largest negative term
    in 76–83% of records, and −228 nats in the median on the consensus bubbles.
  - **What the decomposition cannot separate:** a volatility shift between halves from grid coarseness. Not all of the
    silence is attributable to scale mismatch.
- **These finite-family oracles do not show a strong level signal.**
  - In sample, with drift, scale and elasticity free on both sides, the full β range beats β ≤ 0 by more than log 20
    in only 7.5–14% of windows, and as often on calm controls as on consensus bubbles.
  - A finite-family oracle's failure does not prove that every bubble signal is absent.
  - The fitted and realized-variance elasticities are negative or near zero, not positive, in run-ups.
- **Implication for item 24's repair:** a shared nuisance model on both sides removes the asymmetric scale fit. That
  alone does not guarantee the score fires more often or separates bubbles from calm controls. In these daily data, the
  level-elasticity signal the oracles target is weak and not specific to the positives. Out-of-sample evaluation
  (item 25) decides.
- **No calibration follows:** an in-sample log 20 comparison implies no simulated size or calibration.
- **Scope:**
  - descriptive, on daily adjusted closes;
  - the oracle uses evaluation data, so it is not a test;
  - realized variance is a noisy proxy;
  - consensus labels, survivorship as in experiment 039, 3,000 sampled windows.

## Review

Reviewer, 2026-10-08, against main at `826c78f1`, which contains the results commit `63f8a39a`.

**Method.** I wrote my own code from the Design, without reading `experiments/049/run.py` except the Deviation 2 diff. It is committed as `checks/review/exp049/reproduce.py`, with its rerun command in its header. It runs on 2 workers in under a minute.
- **The records.**
  - **Experiment 021's positives and negatives:** my experiment-021 loader on `data/d6`.
  - **The 3,000 sampled universe windows:** their keys are taken from `results.json` and their start and end dates from experiment 039's `windows.csv.gz`, rebuilt from `data/d24` adjusted closes.
  - **The run-up flag:** recomputed from all 144,793 L = 24 windows, as the top 10% of whole-window log return within each start date.
- **The computations, all my own:**
  - v1, using my experiment-021 implementation;
  - the four-term decomposition, with κ* by bounded search over log κ ∈ [log 0.02, log 5];
  - (b1) and (b2) as registered and as described in Deviation 1, with μ profiled in closed form in (b2);
  - (a) with my own monthly realized-variance code, month-start price taken as the month's first close in the record, and a pooled within-record slope with record-clustered errors.

**Reproduced.**
- **Exact or near-exact matches.**
  - **Run-up flags:** mine agree with the published flags on all 3,000 sampled windows.
  - **v1:** matches on all 3,136 records to 7×10⁻¹², and every fitted (p, κ) is identical.
  - **The decomposition:** its four terms sum to v1 within 9×10⁻¹³, and each term matches within 6×10⁻⁷.
- **The decomposition table matches exactly.** Medians of scale misfit, level, drift and null enlargement: −228.15, −1.47, −0.32, 0 (positives); −17.61, +0.33, −0.50, 0 (negatives); −10.62, +0.27, −0.28, 0 (universe); −16.66, 0.00, −1.06, 0 (run-ups). Scale misfit is the largest negative term in 82%, 83%, 79% and 76% of records.
- **(b1) matches.** Medians −37.99, −1.47, −2.79 and −3.01. Shares above log 20: 9.1%, 4.9%, 4.1% and 7.7%. Shares above zero: 18%, 22%, 13% (published 14%) and 22%.
- **(b2) matches.**
  - **Shares above log 20:** 12.1%, 11.7%, 7.5% and 14.1%.
  - **Fitted-β medians:** −1.65, −1.29, −1.56 and −0.63.
  - **Shares with fitted β > 0:** 33% (published 30%, one record), 34%, 26% and 37%.
- **(a) matches on the pooled slopes, with small differences in the medians.**
  - **Pooled within-record slopes:** +0.01 (0.08), +0.58 (0.10), −0.28 (0.03) and +0.05 (0.04), against +0.02, +0.59, −0.27 and +0.05.
  - **Per-record medians:** +0.06 (67% above zero), +0.25 (71%), −0.39 (36%) and −0.08 (48%), against +0.10, +0.35, −0.40 and −0.08. The small differences come from the month-start-price convention, which the Design leaves open. No reading changes.

**One reporting correction.** The (b2) column "share > 0" (70%, 76%, 68% and 72%) counts optimizer noise.
- **Why.** Per Deviation 1 the alternative fits β ∈ [−20, 20] and the null β ∈ [−20, 0], so the log-LR is ≥ 0 and is exactly zero whenever the unconstrained β̂ ≤ 0. In `results.json` the positive values below 10⁻⁶ are of order 10⁻⁹.
- **The meaningful shares.** The shares above 10⁻⁶ are 30%, 34%, 26% and 37%, equal to the shares with fitted β > 0.
- **The reading is unaffected:** it uses the shares above log 20 and the fitted β. I'd ask the analyst to relabel the column or replace it with the share above 10⁻⁶.
- **A related wording point.** The Design's "the alternative, β > 0" was implemented as unconstrained β. This is the usual nested likelihood ratio, and the two give the same LR whenever β̂ > 0.

**The Deviations are honest.**
- **Order.** The Design was registered at 17:23, and the code with Deviation 1's implementation check at 17:26, before any diagnostic.
- **Deviation 2** (17:29). The diff changes only the "largest negative term" line, which now uses the fixed term names, and adds a per-record cache. The first run crashed before that cache code existed, so the rerun recomputed every record, as stated.
- **The results** came at 17:32, and `run.py` is unchanged from Deviation 2 to the results.

**The readings are fair.**
- **Scale misfit is the reason v1 almost never fires.** v1 is driven almost entirely by it. Measured as the ratio of medians, re-fitting κ on the evaluation half removes 88–99% of the deficit; the report's "90–99%" is marginally generous at 88% for the universe.
- **There is no strong level signal even in sample.** With the scale free, CEV beats v1's null by more than log 20 in only 4–9% of records. The full local-lognormal LR exceeds log 20 as often on calm negatives (11.7%) as on positives (12.1%). The fitted and realized-variance elasticities are negative or near zero in run-ups.
- **The implication for item 24 is correctly drawn.** A common volatility model on both sides repairs the construction, but daily level elasticity should not be expected to separate bubbles from calm controls.
- **The scope is stated:** in-sample oracle, noisy realized-variance proxy, consensus labels and survivorship.

Verdict: reproduced
