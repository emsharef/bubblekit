---
id: "019"
title: "D5: size, power and coverage of claim 052's calibrated catalogue test by sampling frequency and horizon"
status: reproduced
direction: D5
claims: [52]
code: experiments/019/
---
## Question

Job: **measure** (PM note `2026-10-06-exp-d5-claim052.md`).
- **Inside the assumptions:** the models claim 052 supports, with P = Q and the truth in the declared catalogue.
- **Outside the assumptions:** stress cells, labelled as such.

Claim 052 gives, for one name observed on a fixed grid, a split-likelihood confidence set C over a declared finite
catalogue of global power laws σ(x) = κx^p, p ∈ {1, 2}. Rejecting the martingale null (p = 1) when C excludes every
p = 1 candidate has finite-sample size at most α. Equivalently, the e-value E exceeds 1/α.

How do its power, size and coverage change with sampling frequency and horizon? How does it compare with the four
competitors on the same paths? The reviewer saw 1–7% power with monthly data over two years.

**Scope.**
- Power is pointwise, at the catalogue alternatives. Claim 052 part 3 rules out power one on any fixed finite grid.
- In the stress cells the catalogue does not contain the truth, so claim 052 makes no promise there.
- The competitors test their own hypotheses. GSADF tests an explosive root.

## Design

**Catalogue Θ (fixed here).** mathb made no recommendation, so these are my choices.
- Ordered, which also gives the tie order: (p, κ) = (1, 0.15), (1, 0.20), (1, 0.30), (1, 0.45), (2, 0.15),
  (2, 0.20), (2, 0.30), (2, 0.45).
- κ is per √(trading year), and s = 1. So σ(1)/1 = κ is the local volatility at the start for both powers.
- The null catalogue is the four p = 1 entries.
- **Split:** k = ⌊N/2⌋ training increments.
- **α = 0.05,** with 0.10 as a secondary.
- **Bands:** R = 1 and r = e^{0.15}, as in experiment 016, using claim 052 (3) for b₁ and b₂.

**Likelihoods.** These are claim 052 (1).
- p = 1: the lognormal kernel f₁.
- p = 2: f₂ in the stable form log x − 3 log y − ½ log(2πv) − (1/y − 1/x)²/(2v) + log(−expm1(−2/(xyv))).
- They are evaluated in float64, vectorized.
- **Selector:** the training-likelihood argmax over Θ, with ties to the earlier entry.
- **Ratios:** T(ϑ) = g_ϑ̂(V|U)/g_ϑ(V|U).
- **Outputs:** C = {T ≤ 1/α}; E = min over the p = 1 entries of T; z = min(1, 1/E).
- **Check of the implementation, before the run:** 40 random (Δ, x, y, κ, p) values are compared against mathb's
  mpmath `checks/d3-price-likelihood/kernels.py` `log_transition`, to a relative tolerance of 1e−9.

**Models.** S_0 = 1, and time is in trading years (252 days of 78 five-minute bars).
- **In catalogue (P = Q),** all eight catalogue members, simulated exactly at the sampled times:
  - GBM (p = 1): S = exp(κW − κ²t/2);
  - p = 2: S = 1/|1 + κB| with B a 3-d Brownian motion, the reciprocal BES(3) law of AX-54.
- **Stress (outside the assumptions):**
  - CEV p = 1.5, σ = 0.3x^{1.5}, exact via experiment 015's BESQ transform;
  - GBM κ = 0.30 with a physical drift μ = 0.10 a year (P ≠ Q);
  - Sin's model with a·γ < 0 and with a·γ > 0, γ = (0.3, 0), log-Euler at 5-minute steps (as in experiment 015).

**Sampling** (the headline grid).
- Frequencies: monthly (21 trading days), weekly (5 days), daily and 5-minute (78 a day).
- Horizons: T ∈ {1, 2, 5} years.
- **Common random numbers:** each path is generated once on the 5-minute grid of its horizon and subsampled.

**Paths and seeds.**
- 1,000 paths per (model, T), in batches of 100.
- Seeds: `SeedSequence(20261019)`, spawned per (model, T) and per batch.

**Reported per (model, T, frequency).** Each comes with a binomial SE.
- The rejection rate of "C ∩ Θ₀ = ∅" (equivalently E > 1/α), at α = 0.05 and 0.10. This is size for the p = 1
  truths and power for the p = 2 truths.
- The band-rule rejection U₂ < L₁.
- Coverage P(ϑ* ∈ C) for the in-catalogue truths.
- The e-values: the sample mean of E at nulls, which claim 051 bounds by 1, with its SE; and the median of log E at
  all truths.
- The fraction of paths with p̂ = 2 in training.

**Competitors on the same paths** (rule 20; experiment 015's implementations and tunings, imported unchanged).
- **Models:** the core cells (GBM κ = 0.30 and p = 2 κ = 0.30) and all stress cells.
- **Monthly, weekly and daily data over the full horizon:**
  - SADF and GSADF, with finite-sample critical values from 2,000 null simulations at each sample size
    (`SeedSequence(20261020)`);
  - JKP Methods 2 and 1;
  - the panel t and J tests on S − S_0, which is experiment 015's Deviation 1 reading, with the price-level reading as
    a secondary. Panels are 20 paths, so the 1,000 paths make 50 panels.
- **5-minute data:** the competitors see the last 21 days, as in experiment 015, while claim 052 uses the full
  5-minute path. This asymmetry is stated beside every such row.
- **OPY:** 5-minute data, T = 1 only, the last 84 days, the first 200 paths.

**Outputs.**
- `experiments/019/results.json` and `summary.csv`.
- Regenerate with `uv run python experiments/019/run.py`, run inside `.worktrees/analyst` on cores − 3 workers.

## Deviations

1. **mathb's run specification is adopted before any result** (`2026-10-06-claim052-run-spec.md`; the PM's note says
   to take mathb's specification).
   - **Timing.** It arrived after this Design was committed and while the first launch was running. That launch was
     stopped before it printed or wrote any result, and nothing from it was used.
   - **Catalogue.** It is replaced by mathb's six ordered candidates: (1, 0.2), (1, 0.3), (1, 0.45), (2, 0.2),
     (2, 0.3), (2, 0.45). This drops κ = 0.15.
     - The reviewer used this catalogue before, and its low monthly power is already known. So it is not chosen blind
       to all results, and it is not optimized.
     - The supported cells are these six models.
   - **Band rule (secondary).** It uses R = e^{−0.15} and r = e^{0.15}.
   - **Coverage reports.** These are now true-parameter noncoverage and joint noncoverage of both blocks.
   - **Stress cells.**
     - The physical drift becomes μ = 0.05: dS = 0.05 S dt + 0.3 S dW under P, with the zero-drift p = 1 pricing law.
     - Off-catalogue cells (p, κ) = (1, 0.35) and (2, 0.35) are added and preregistered here. They expose the
       exact-catalogue assumption.
     - The CEV 1.5 and Sin cells are unchanged. All of these stay outside the likelihood assumptions.
   - **Grids.** Strides of 21·78, 5·78, 78 and 1 on the same 5-minute path keep time 0 and the terminal point.
     - A shortened final interval uses its actual elapsed time: weekly, since 252 is not divisible by 5.
     - Time stays in years and κ is annual; there is no rescaling to [0, 1].
     - The 5-minute grid covers the full horizon for claim 052. The competitors' 5-minute window stays the last
       21 days, as already stated.
   - **Decisions.** Log E = min over the p = 1 scores. Rejection is log E > −log α, and equality does not reject.
     Decisions are made in log space and never exponentiated. Mean e-values are reported with mathb's caution that
     rare large values can dominate them.
   - **Numerical checks, preregistered here:**
     - every path's scores are recomputed with mathb's `checks/d3-price-likelihood/fast.py` (`batch_split_scores`),
       and the maximum |Δ log T| and any decision mismatch are reported;
     - the first five paths of every (model, T, frequency) cell are recomputed at high precision with
       `checks/d3-price-likelihood/kernels.py` (`split_scores`, mpmath), with mismatches reported.
   - **Policy for ambiguous decisions.** A decision is flagged as ambiguous if |log E + log α| < 10⁻⁶, or if the
     training argmax margin is below 10⁻⁶. Ambiguous counts are reported. Where a high-precision value exists, it
     decides; otherwise the float64 decision stands and is flagged.
   - **Failures.** Nonpositive prices or nonfinite scores are counted and reported, never floored or dropped.

## Results

**Claim 052's null-exclusion rule: rejection rate at α = 0.05** (1,000 paths per cell; SE ≤ 0.016). Rows above the rule are in-catalogue under P = Q; rows below are outside the assumptions.

| model | T | monthly | weekly | daily | 5-minute |
|---|---|---|---|---|---|
| GBM κ = 0.20 (null) | 1 | 0.000 | 0.000 | 0.000 | 0.000 |
| GBM κ = 0.20 (null) | 2 | 0.000 | 0.000 | 0.000 | 0.000 |
| GBM κ = 0.20 (null) | 5 | 0.001 | 0.001 | 0.000 | 0.000 |
| GBM κ = 0.30 (null) | 1 | 0.000 | 0.000 | 0.001 | 0.000 |
| GBM κ = 0.30 (null) | 2 | 0.000 | 0.000 | 0.000 | 0.000 |
| GBM κ = 0.30 (null) | 5 | 0.001 | 0.000 | 0.000 | 0.000 |
| GBM κ = 0.45 (null) | 1 | 0.000 | 0.000 | 0.000 | 0.000 |
| GBM κ = 0.45 (null) | 2 | 0.000 | 0.000 | 0.000 | 0.000 |
| GBM κ = 0.45 (null) | 5 | 0.001 | 0.000 | 0.000 | 0.000 |
| p = 2, κ = 0.20 | 1 | 0.000 | 0.015 | 0.242 | 0.993 |
| p = 2, κ = 0.20 | 2 | 0.004 | 0.146 | 0.596 | 1.000 |
| p = 2, κ = 0.20 | 5 | 0.209 | 0.628 | 0.958 | 1.000 |
| p = 2, κ = 0.30 | 1 | 0.001 | 0.007 | 0.298 | 1.000 |
| p = 2, κ = 0.30 | 2 | 0.005 | 0.079 | 0.696 | 1.000 |
| p = 2, κ = 0.30 | 5 | 0.143 | 0.603 | 0.979 | 1.000 |
| p = 2, κ = 0.45 | 1 | 0.026 | 0.104 | 0.457 | 1.000 |
| p = 2, κ = 0.45 | 2 | 0.062 | 0.235 | 0.780 | 1.000 |
| p = 2, κ = 0.45 | 5 | 0.176 | 0.659 | 0.974 | 1.000 |
| *outside the assumptions* | | | | | |
| GBM κ = 0.35, off-catalogue (pricing null) | 1 | 0.000 | 0.000 | 0.037 | 0.281 |
| GBM κ = 0.35, off-catalogue (pricing null) | 2 | 0.000 | 0.002 | 0.066 | 0.142 |
| GBM κ = 0.35, off-catalogue (pricing null) | 5 | 0.000 | 0.006 | 0.010 | 0.009 |
| p = 2, κ = 0.35, off-catalogue (strict) | 1 | 0.002 | 0.014 | 0.101 | 0.192 |
| p = 2, κ = 0.35, off-catalogue (strict) | 2 | 0.014 | 0.076 | 0.216 | 0.309 |
| p = 2, κ = 0.35, off-catalogue (strict) | 5 | 0.106 | 0.322 | 0.507 | 0.582 |
| CEV p = 1.5 (strict; outside) | 1 | 0.000 | 0.000 | 0.034 | 0.183 |
| CEV p = 1.5 (strict; outside) | 2 | 0.000 | 0.010 | 0.096 | 0.200 |
| CEV p = 1.5 (strict; outside) | 5 | 0.006 | 0.060 | 0.098 | 0.151 |
| GBM κ = 0.30, μ = 0.05 under P (pricing null; outside) | 1 | 0.000 | 0.000 | 0.002 | 0.000 |
| GBM κ = 0.30, μ = 0.05 under P (pricing null; outside) | 2 | 0.000 | 0.000 | 0.000 | 0.000 |
| GBM κ = 0.30, μ = 0.05 under P (pricing null; outside) | 5 | 0.000 | 0.000 | 0.000 | 0.000 |
| Sin a·γ < 0 (martingale; outside) | 1 | 0.000 | 0.001 | 0.003 | 0.006 |
| Sin a·γ < 0 (martingale; outside) | 2 | 0.000 | 0.002 | 0.004 | 0.004 |
| Sin a·γ < 0 (martingale; outside) | 5 | 0.000 | 0.000 | 0.000 | 0.000 |
| Sin a·γ > 0 (strict; outside) | 1 | 0.023 | 0.106 | 0.331 | 0.425 |
| Sin a·γ > 0 (strict; outside) | 2 | 0.037 | 0.221 | 0.350 | 0.391 |
| Sin a·γ > 0 (strict; outside) | 5 | 0.113 | 0.261 | 0.288 | 0.304 |

Size and coverage on the in-catalogue cells: the largest null rejection rate is 0.001 at α = 0.05 and 0.003 at α = 0.10. The largest true-parameter noncoverage is 0.003 (α = 0.05) and 0.010 (α = 0.10); the largest joint (both-block) noncoverage is 0.003 at α = 0.05.

**Competitors on the same paths** (5% rejection; JKP Method 2 and OPY: bubble rate, no level). GSADF, JKP and the panel test use the full horizon at monthly, weekly and daily sampling and the **last 21 days** at 5-minute sampling; claim 052 uses the full 5-minute path. Panel: S − S_0, 50 panels of 20. OPY: T = 1, last 84 days, 200 paths.

| model | T | GSADF m / w / d / 5-min | JKP M2 m / w / d / 5-min | panel t m / w / d / 5-min | OPY |
|---|---|---|---|---|---|
| GBM κ = 0.30 (null) | 1 | 0.05 / 0.07 / 0.09 / 0.04 | 0.00 / 1.00 / 1.00 / 0.61 | 0.78 / 0.08 / 0.06 / 0.00 | 0.44 |
| GBM κ = 0.30 (null) | 2 | 0.07 / 0.09 / 0.11 / 0.04 | 1.00 / 1.00 / 0.89 / 0.62 | 0.18 / 0.04 / 0.04 / 0.02 | — |
| GBM κ = 0.30 (null) | 5 | 0.11 / 0.14 / 0.18 / 0.05 | 1.00 / 1.00 / 0.96 / 0.61 | 0.00 / 0.00 / 0.00 / 0.02 | — |
| p = 2, κ = 0.30 | 1 | 0.07 / 0.10 / 0.12 / 0.06 | 0.00 / 1.00 / 1.00 / 0.71 | 0.56 / 0.08 / 0.02 / 0.02 | 0.38 |
| p = 2, κ = 0.30 | 2 | 0.08 / 0.14 / 0.21 / 0.06 | 1.00 / 1.00 / 0.96 / 0.72 | 0.22 / 0.06 / 0.06 / 0.00 | — |
| p = 2, κ = 0.30 | 5 | 0.16 / 0.25 / 0.35 / 0.06 | 1.00 / 1.00 / 0.99 / 0.72 | 0.00 / 0.00 / 0.00 / 0.00 | — |
| GBM κ = 0.35, off-catalogue (pricing null) | 1 | 0.05 / 0.08 / 0.11 / 0.05 | 0.00 / 1.00 / 1.00 / 0.63 | 0.76 / 0.04 / 0.04 / 0.00 | 0.46 |
| GBM κ = 0.35, off-catalogue (pricing null) | 2 | 0.07 / 0.09 / 0.12 / 0.05 | 1.00 / 1.00 / 0.86 / 0.63 | 0.10 / 0.00 / 0.00 / 0.00 | — |
| GBM κ = 0.35, off-catalogue (pricing null) | 5 | 0.12 / 0.16 / 0.21 / 0.05 | 1.00 / 1.00 / 0.96 / 0.62 | 0.02 / 0.02 / 0.02 / 0.00 | — |
| p = 2, κ = 0.35, off-catalogue (strict) | 1 | 0.06 / 0.13 / 0.16 / 0.06 | 0.00 / 1.00 / 1.00 / 0.73 | 0.40 / 0.04 / 0.00 / 0.00 | 0.48 |
| p = 2, κ = 0.35, off-catalogue (strict) | 2 | 0.09 / 0.16 / 0.23 / 0.07 | 1.00 / 1.00 / 0.98 / 0.71 | 0.08 / 0.00 / 0.00 / 0.02 | — |
| p = 2, κ = 0.35, off-catalogue (strict) | 5 | 0.16 / 0.27 / 0.38 / 0.05 | 1.00 / 1.00 / 1.00 / 0.69 | 0.06 / 0.04 / 0.02 / 0.02 | — |
| CEV p = 1.5 (strict; outside) | 1 | 0.05 / 0.09 / 0.10 / 0.05 | 0.00 / 1.00 / 1.00 / 0.66 | 0.80 / 0.04 / 0.00 / 0.00 | 0.48 |
| CEV p = 1.5 (strict; outside) | 2 | 0.11 / 0.12 / 0.16 / 0.06 | 1.00 / 1.00 / 0.89 / 0.68 | 0.18 / 0.08 / 0.08 / 0.00 | — |
| CEV p = 1.5 (strict; outside) | 5 | 0.14 / 0.19 / 0.27 / 0.05 | 1.00 / 1.00 / 0.88 / 0.64 | 0.06 / 0.04 / 0.02 / 0.00 | — |
| GBM κ = 0.30, μ = 0.05 under P (pricing null; outside) | 1 | 0.06 / 0.07 / 0.09 / 0.05 | 0.00 / 1.00 / 1.00 / 0.61 | 0.80 / 0.10 / 0.08 / 0.00 | 0.45 |
| GBM κ = 0.30, μ = 0.05 under P (pricing null; outside) | 2 | 0.07 / 0.09 / 0.11 / 0.04 | 1.00 / 1.00 / 0.87 / 0.62 | 0.28 / 0.14 / 0.08 / 0.00 | — |
| GBM κ = 0.30, μ = 0.05 under P (pricing null; outside) | 5 | 0.15 / 0.19 / 0.24 / 0.04 | 1.00 / 1.00 / 0.97 / 0.61 | 0.16 / 0.12 / 0.16 / 0.00 | — |
| Sin a·γ < 0 (martingale; outside) | 1 | 0.06 / 0.10 / 0.19 / 0.06 | 0.00 / 1.00 / 1.00 / 0.27 | 0.54 / 0.02 / 0.00 / 0.02 | 0.20 |
| Sin a·γ < 0 (martingale; outside) | 2 | 0.09 / 0.16 / 0.25 / 0.06 | 1.00 / 1.00 / 0.98 / 0.30 | 0.06 / 0.00 / 0.00 / 0.02 | — |
| Sin a·γ < 0 (martingale; outside) | 5 | 0.15 / 0.28 / 0.49 / 0.09 | 1.00 / 1.00 / 0.98 / 0.27 | 0.02 / 0.02 / 0.02 / 0.02 | — |
| Sin a·γ > 0 (strict; outside) | 1 | 0.08 / 0.18 / 0.29 / 0.11 | 0.00 / 1.00 / 1.00 / 0.77 | 0.22 / 0.04 / 0.00 / 0.00 | 0.29 |
| Sin a·γ > 0 (strict; outside) | 2 | 0.10 / 0.25 / 0.42 / 0.10 | 1.00 / 1.00 / 0.96 / 0.78 | 0.06 / 0.00 / 0.00 / 0.02 | — |
| Sin a·γ > 0 (strict; outside) | 5 | 0.23 / 0.45 / 0.74 / 0.09 | 1.00 / 1.00 / 0.98 / 0.78 | 0.02 / 0.00 / 0.00 / 0.02 | — |

**Numerical checks** (Deviation 1's preregistered policy).
- **Against mathb's `fast.py`, on every path of every cell:** zero selection mismatches and zero decision mismatches
  at both α.
- **Absolute differences in log T:** at most 2·10⁻⁸ in every model except Sin's. In the Sin stress cells the
  simulated prices approach zero (one path reached about 10⁻⁶⁶), the p = 2 log-likelihoods become astronomically
  large, and the absolute float64 differences reach 10¹⁴¹. They are rounding at that scale and do not change any
  selection or decision.
- **High precision (mpmath `kernels.split_scores`), on 720 paths** (the first five of every cell): zero selection
  mismatches, and a largest |Δ log T| of 5.4·10⁻⁷.
- **Policy outcomes:** zero ambiguous decisions, zero training margins below 10⁻⁶, and zero failures (nonpositive or
  nonfinite prices or scores).
- **Shutdown noise.** The run's log ends with `BrokenPipeError` tracebacks from pool workers at interpreter shutdown.
  These come after the main process printed "done" and wrote `results.json`, and they affect no result.

**e-values** (claim 051's E, a null catalogue minimum; `results.json`). At the in-catalogue nulls, the sample mean
of E (capped at e⁵⁰) is 0.62–0.87 for monthly sampling and 1.00 at 5 minutes. At 5 minutes the training fit picks the
true p = 1 candidate, and E = 1 exactly. A sample mean near one does not certify E[E] ≤ 1 (mathb's caution).

For p = 2, κ = 0.30, the median log E grows with information:
- −0.31, 0.00, 1.47 and 183 at T = 1 (monthly, weekly, daily, 5-minute);
- 0.31, 4.4, 25 and 1,976 at T = 5.

**Readings.** These are pointwise, at these catalogue alternatives.
1. **Inside its assumptions, claim 052's test is calibrated and conservative.**
   - The largest null rejection rate over the three GBM nulls, all horizons and all frequencies is 0.001 at α = 0.05.
   - Noncoverage of the true parameter is at most 0.003. This is the finite-sample guarantee at work, well inside α.
2. **Its power is set by sampling frequency far more than by horizon.**
   - **Monthly data:** almost powerless. Rejection is 0.000–0.026 at T = 1 and 0.004–0.062 at T = 2, which matches
     the reviewer's 1–7%. It reaches only 0.14–0.21 at T = 5.
   - **Weekly data:** 0.01–0.10 (T = 1) up to 0.60–0.66 (T = 5).
   - **Daily data:** 0.24–0.46 (T = 1) up to 0.96–0.98 (T = 5).
   - **5-minute data over the horizon:** 0.99–1.00 everywhere.
   - The band rule tracks the null-exclusion rule closely. It is a little lower at monthly and weekly sampling, where
     coordinate extrema lose information.
3. **Off the catalogue it loses calibration, at high frequency.**
   - The off-grid pricing null, GBM κ = 0.35, gets false alarms of 0.281 (T = 1) and 0.142 (T = 2) with 5-minute data,
     and 0.04–0.07 daily.
   - This is the failure claim 023 predicts. As sampling increases, an off-grid volatility becomes almost perfectly
     distinguishable from every null-grid member.
   - At T = 5 the false alarms fall back to about 0.01. Why is not established here.
   - **The catalogue must contain the truth for the guarantee to hold,** and a fine catalogue is costly. Math's grid
     budget puts the requirement at hundreds to thousands of points.
4. **Other misspecifications behave differently.**
   - **Physical drift (μ = 0.05)** leaves the test quiet: ≤ 0.002.
   - **Sin's martingale model** gives ≤ 0.006, so these stresses do not produce false alarms here.
   - **Strict models outside the catalogue are detected, but less than the catalogue alternatives:** CEV 1.5 at
     0.03–0.20 at daily and 5-minute sampling, Sin's strict model at 0.29–0.43, and the off-grid p = 2 at 0.10–0.58.
5. **Against the competitors on the same paths.**
   - **GSADF:** its rates on the true martingales rise with horizon (GBM κ = 0.30: 0.11 monthly and 0.18 daily at
     T = 5; Sin's martingale model: 0.49 daily at T = 5). Its rates on p = 2 (0.16–0.35 at T = 5) barely exceed those.
   - **JKP Method 2** says "bubble" on 86–100% of paths at monthly, weekly and daily sampling (0% at 1-year monthly,
     where it fails). At the 5-minute month it says so on 61–78%, nulls included, and 27–30% under Sin's martingale
     model.
   - **The panel t on S − S_0** has no power.
   - **OPY** dates births on 0.20–0.48 of paths whatever the truth.
   - So claim 052's test is the only procedure here that holds size on the nulls and has high power on the catalogue
     alternatives. Its edge rests on the exact-catalogue premise and on high-frequency data.
   - **The 5-minute comparison is asymmetric:** claim 052 sees the full 5-minute path, the competitors the last month.

Regenerate:
- Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
  experiments/019/run.py`, inside `.worktrees/analyst`, on cores − 3 workers.
  - The reported run predates the human's thread-limit instruction and ran without the prefix. That changes timing,
    not results.
- Seeds: `SeedSequence(20261019)` for the paths and `SeedSequence(20261020)` for the GSADF critical values.
- Environment: `uv.lock` at the reporting commit.
- About 1 hour.

## Review

Reviewer, 2026-10-06, against main at `c862071`, which contains the reporting commit `75f5b13`.

**Method.** I wrote my own code from the Design and Deviation 1, without reading `experiments/019/*.py`. It is committed as `checks/review/exp019/reproduce.py`, with its rerun commands and seed (`SeedSequence(1919)`) in its header; its method and outputs are below.
- **The design followed.** mathb's six-candidate catalogue; the split k = ⌊N/2⌋; strides of 21·78, 5·78, 78 and 1 on a 5-minute grid, keeping 0 and T, with a short last weekly interval at its actual length; the training-argmax selector with ties to the earlier entry; and log-space decisions with log E > log 20.
- **My own exact paths.** GBM, the reciprocal BES3 (p = 2), CEV 1.5 via a 4-d Bessel process, and the drift cell. 1,000 paths per in-catalogue and off-catalogue cell and 500 per CEV and drift cell, with my own seeds.
- **Not rerun:** the Sin cells and the competitor table. Those use experiment 015's implementations, which I reproduced in that review.

**Headline numbers reproduced** (mine, then theirs; rejection at α = 0.05).
- **Size and coverage in the catalogue.**
  - The largest null rejection over the three GBM nulls, three horizons and four frequencies is 0.002, against 0.001.
  - The largest true-parameter non-coverage is 0.004, against 0.003.
  - No nonfinite score or nonpositive price occurred.
- **Power for p = 2, by frequency** (monthly / weekly / daily / 5-minute):

  | Cell | Mine | Theirs |
  |---|---|---|
  | κ = 0.20, T = 1 | 0.000 / 0.014 / 0.221 / 0.993 | 0.000 / 0.015 / 0.242 / 0.993 |
  | κ = 0.30, T = 2 | 0.007 / 0.097 / 0.661 / 1.000 | 0.005 / 0.079 / 0.696 / 1.000 |
  | κ = 0.45, T = 5 | 0.187 / 0.675 / 0.959 / 1.000 | 0.176 / 0.659 / 0.974 / 1.000 |

  Every other cell agrees within about 2 SE.
- **The off-catalogue pricing null, GBM κ = 0.35:**
  - 5-minute: 0.251, 0.132, 0.014 at T = 1, 2, 5, against 0.281, 0.142, 0.009;
  - daily: 0.051, 0.049, 0.007, against 0.037, 0.066, 0.010.
- **The other stress cells.**
  - Off-catalogue p = 2, κ = 0.35: 5-minute 0.150, 0.306, 0.601, against 0.192, 0.309, 0.582.
  - CEV 1.5: 5-minute 0.174, 0.214, 0.176, against 0.183, 0.200, 0.151.
  - Drift μ = 0.05: ≤ 0.004, against ≤ 0.002.

**Reading 3's open question has a partial explanation.** Experiment 019 says it is not established why the off-grid false alarms fall back at T = 5. One fact explains part of it: a rejection requires the training fit to select a p = 2 candidate. If a null candidate is selected, its own ratio is one, so E ≤ 1.
- **Selection.** For GBM κ = 0.35 at 5-minute sampling, the selected-p = 2 fraction falls from 0.57 to 0.44 to 0.16 at T = 1, 2, 5.
- **Rejection given that selection** also falls: about 0.44, 0.30, 0.09.
- **So the decline has two parts.** Over longer horizons the price leaves the region where a p = 2 coefficient mimics volatility 0.35. And the misfit null candidates are then the better training fit.
- **Mean e-values at 5 minutes.** At the in-catalogue nulls the 5-minute training fit never selects p = 2 (fraction 0.00 in every cell), which is why the mean E there is exactly 1.

**The Deviations are honest.**
- **Order.** mathb's specification note was committed at 17:53:30 (`9c0f64c`), after the Design was registered (`7fa381f`, 17:47). Deviation 1 (`eca9aca`, 17:59) and the runner (`d1af758`, 18:02) came before the report (19:09), which fits the stated one-hour run.
- **The first launch.** The stopped first launch is disclosed, along with the fact that it produced no result.
- **Knowledge of the catalogue.** The catalogue choice is disclosed as not blind to my earlier claim-052 review, and it is not optimized.
- **The numerical-check policy** was preregistered, and its outcomes, including Sin's large-magnitude rounding, are reported.

**One point the readings should carry more strongly.** The high-power regime, 5-minute data with power 0.99–1.00, is also where the off-grid null's false alarms are worst (0.25–0.28 at T = 1). So the test's edge over the competitors is real only if the catalogue contains the truth at that resolution. Claim 023 shows TV budgets cannot fix that at high frequency, and claim 055's continuous Gaussian null fixes it for the GBM part only, at a large cost in power. Separately, claim 024 adds a rounding concern specific to 5-minute data. Reading 5's "its edge rests on the exact-catalogue premise and on high-frequency data" is accurate. The two requirements pull against each other.

**Scope.** As stated: pointwise power at the catalogue alternatives, and stress cells outside the guarantee. My reproduction confirms the calibrated in-catalogue behaviour and the frequency-driven power, which is the main D5 finding for the lab's test so far.

Verdict: reproduced
