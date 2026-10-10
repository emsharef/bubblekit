---
id: "022"
title: "D5/D14: claim 054's CEV-grid test and claim 055's drift-robust score, in and out of catalogue, by sampling frequency"
status: reproduced
direction: D5
claims: [54, 55, 23, 24]
code: experiments/022/
---
## Question

Job: **measure**, both inside and outside each score's assumptions (PM note `2026-10-06-d5-cev-grid-stage.md`). It
folds in math's four D14 notes: robustness measurements, grid budget, CEV domain adapter and rounding scope. Each truth's
**pricing status** (true or strict martingale under its pricing law) and its **physical observation law** are labelled
separately. Raw scores are not e-values off-model, and sample score means do not prove null moments.

Claim 054 extends the calibrated catalogue test to absorbed CEV powers p > 0, where p ≤ 1 is the null. Claim 055 adds
a drift-robust score, valid when the actual null conditional law is in the catalogue null or is any constant-drift
Gaussian (geometric Brownian) law. Claim 023 bounds size under misspecification by α + E ε, given a conditional-TV
envelope ε, and allows clipped scores.

On realistic sampling grids:
- What are these scores' false-alarm rates and power, both on the catalogue and off it (omitted exponents and scales,
  physical drift, stochastic volatility, jumps, rounding)?
- How do the observed rates compare with claim 023's analytic bounds where the parameters are known?
- How does e-BH behave on all-null and mixed panels?

Experiment 019's claim-052 benchmark is kept unchanged. Its six-candidate test is run on the same paths as a column.

## Design

**Catalogue Θ** (fixed here; mathb gave no CEV-grid recommendation; the family size was coordinated with math's grid
budget, see below).
- p ∈ {0.5, 0.75, 1.0, 1.25, 1.5, 2.0} × κ ∈ {0.20, 0.30, 0.45}, which is 18 candidates. The order is p ascending, then
  κ ascending, and it is also the tie order.
- The null is p ≤ 1 (9 candidates).
- S_0 = 1, so κ is the local volatility at the start. Time is in years (252 days × 78 five-minute bars).
- The κ grid is equal-log: log(0.3/0.2) = log(0.45/0.3).
- Split k = ⌊N/2⌋, with training on the first k increments only. α = 0.05 (0.10 secondary). R = e^{−0.15},
  r = e^{0.15}, as in 019.

**Scores, all on the same price vectors:**
- **S1, claim 054 raw null exclusion:** E = Ĝ/G₀ (0 if Ĝ = 0). Reject at E > 1/α.
- **S2, claim 054 band rule:** U₂ < L₁ from the projected block bands (claim 054 part 2).
- **S3, claim 055 drift-robust score:** E^drift = Ĝ/max(G₀, D_G), with D_G the closed-form Gaussian supremum (claim
  055 (3)), and 0 if Ĝ = 0 or D = ∞. Reject at E^drift > 1/α.
- **S4, claim 023 clipped score:** min(E, c)/(1 + c ε), with cap c = 50 preregistered (> 40, math's requirement at
  α = 0.05 for ε ≤ 0.025).
  - ε = `grid_budget(n_eval, τ_eval, 0.20, 0.45, 0, 2)` (`checks/d14-grid-budget/budget.py`): the uniform envelope for
    GBM nulls with volatility in [0.2, 0.45] and zero drift, against this 3-point κ grid.
  - It is valid only for that declared class. Elsewhere it is labelled outside.
- **S5, the claim-052 benchmark:** experiment 019's six-candidate p ∈ {1, 2} test, unchanged.
- **Domain handling** follows math's reviewed contract (`checks/d14-cev-domain/total.py`):
  - impossible arrays (zero training likelihoods, zero selected evaluation density, resurrection after absorption)
    get the claim's total-score values;
  - negative or nonfinite observations and numerical failures get zero evidence with a status record;
  - nothing is dropped, and e-BH keeps the original panel size;
  - configuration errors stop the run.
  - Size and power are never conditioned on successful evaluation or on survival.

**Kernels.**
- **p ≠ 1:** AX-56's absorbed CEV densities on μ_CEV (Lebesgue on (0, ∞) plus an atom at 0), computed through the
  Bessel transform Y = S^{2(1−p)}/(κ²(1−p)²):
  - log-density via `scipy.special.ive` in log space;
  - for p < 1, the absorption atom a_p = Q(ν′, Y/(2Δ)) with ν′ = 1/(2(1 − p)), the regularized upper gamma.
- **p = 1:** the lognormal kernel. The trapped extension at zero is as in claim 054.
- **Numerical checks, preregistered:**
  - normalization and atom mass by quadrature at 20 fixed (p, κ, Δ, x);
  - every path's scores against mathb's high-precision prototype, `checks/d13-support-input/cev.py` (or `total.py`), on
    the first five paths of every (model, T, frequency) cell;
  - the ambiguity policy is 019's (|log E + log α| < 10⁻⁶, or a training margin < 10⁻⁶), with high precision deciding;
  - mismatch and failure counts are reported.

**Truths** (1,000 paths per (model, T); S_0 = 1).

| truth | simulation | pricing status | physical law | relation to the assumptions |
|---|---|---|---|---|
| CEV p ∈ {0.5, 0.75, 1.0, 1.25, 1.5, 2.0}, κ = 0.30 | exact (below) | true (p ≤ 1) / strict (p > 1) | = pricing (P = Q) | in catalogue |
| CEV p = 1.75, κ = 0.30 | exact | strict | P = Q | omitted exponent |
| GBM κ = 0.35 | exact | true | P = Q | omitted scale; S3 and S4 in class |
| CEV p = 1.5, κ = 0.35 | exact | strict | P = Q | omitted scale |
| GBM κ = 0.30, μ = 0.05 under P | exact | true (zero-drift pricing law) | drifted GBM | S3 in class; S1, S2, S4 outside |
| Sin a·γ < 0, a·γ > 0 (015) | log-Euler, 5-minute | true / strict | = pricing | stochastic volatility, outside |
| Merton jumps: GBM κ = 0.30 plus jumps, intensity 5 a year, log size N(−0.02, 0.05²), compensated | exact on the grid | true | = pricing | jumps, outside |
| GBM κ = 0.30 and CEV p = 1.5 κ = 0.30, observed rounded to h = 10⁻⁴ (one cent on $100) | exact, then rounded | true / strict | rounded observation | claim 024: outside the exact-observation guarantee |

- **Exact CEV simulation:**
  - **p > 1:** the BESQ(δ), δ = (2p − 1)/(p − 1), noncentral-χ² transition.
  - **p < 1:** absorbed, through this exact Gamma–Poisson representation of the transition. With λ = Y/(2Δ) and
    ν′ = 1/(2(1 − p)), draw G ~ Gamma(ν′). If G > λ the path is absorbed (Y = 0). Otherwise draw K ~ Poisson(λ − G)
    and set Y = 2Δ·Gamma(K + 1).
  - This representation reproduces the absorbed BESQ(δ < 2) series term by term, which I checked algebraically. A
    pre-run test compares it with the kernel by quadrature.
- **Seeds:** `SeedSequence(20261023)`, spawned per (model, T) and per batch of 100.

**Sampling.** As in experiment 019: monthly (21 days), weekly (5), daily and 5-minute over the full horizon,
T ∈ {1, 2, 5}. Paths are generated once on the 5-minute grid and subsampled, keeping time 0 and the terminal point.

**Reported per (truth, T, frequency, score).** Each comes with a binomial SE.
- The rejection rate at α = 0.05 and 0.10.
- True-parameter and joint noncoverage, for in-catalogue truths.
- The ineligible or zero-evidence count, with status.
- Absorbed paths.
- The median log score.
- The mean score, with mathb's caution that it does not certify validity.

**Claim 023's analytic bounds beside the observed rates,** from `loss_bound` and `tv_budget`, with the evaluation
count and horizon of each cell. They are not predicted rejection rates.
- **GBM κ = 0.35:** radius log(0.35/0.30), with (smin, smax) = (0.30, 0.35) and zero drift. This gives the size bound
  α + ε for S1.
- **Drifted GBM:** radius 0 and drift bound 0.05 (smin = smax = 0.30).
- **S4:** the grid ε above, and the resulting clipped power cost.

**e-BH** (Wang–Ramdas base procedure, q = 0.10, original panel size m = 20, scores S1, S3 and S4), on panels of 20
paths from one (T, frequency). 50 panels each:
- all-null in catalogue: GBM κ = 0.30;
- all-null off catalogue: GBM κ = 0.35, and drifted GBM;
- mixed: 10 GBM κ = 0.30 with 10 CEV p = 1.5 κ = 0.30, and 10 GBM κ = 0.35 with 10 CEV p = 1.75.

Reported: FDR (the mean false-discovery proportion) and power (the mean share of alternatives discovered).

**Cost and runs.**
- Large grids (math's 184 to 1,609 points) are not run; their cost is reported analytically.
- Runs are inside `.worktrees/analyst` with `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
  VECLIB_MAXIMUM_THREADS=1`, on cores − 3 workers.

**Outputs.** `experiments/022/results.json` and `summary.csv`.

## Deviations

1. **A scope statement added before any run** (math's `2026-10-06-d14-support-application.md`; proposed claim 025 is
   not yet reviewed). No method or number changes. This experiment makes no calibration claim for a mixed-support
   robustness comparison of claim 054's score:
   - S4 uses claim 023's envelope only for the declared Gaussian GBM-null class.
   - Every off-catalogue S1/S2 rate is a measurement outside the assumptions.
   - Surviving float64 scores are not certified. Claim 025's sufficient condition, an implemented score bounded above
     by the exact score, is not established here, so the preregistered high-precision checks are numerical evidence
     only.
2. **The high-precision check scope is reduced, before any run, for cost.**
   - **Why.** mathb's mpmath kernel (`checks/d13-cev-input/kernels.py`) costs about 0.2 ms per transition. So a
     5-minute path of up to 98,280 transitions × 18 candidates takes about 6 minutes, and checking the first five
     paths of every 5-minute cell would take about 1.8 hours on 7 workers.
   - **Kept as registered:** the first five paths of every monthly, weekly and daily cell are checked through
     `checks/d14-cev-domain/total.py` (`score_total_path`), comparing selected fits and log E.
   - **5-minute cells:** the first path at T = 1, plus a kernel-level comparison of about 2,000 transitions per cell
     (111 random transitions × 18 candidates) against `log_transition`.
   - **Already checked before the run:**
     - the float64 kernel matches `log_transition` to a relative 4·10⁻¹⁰ on 60 random inputs;
     - it normalizes, atom included, to 10⁻¹⁰ in six cases;
     - the Gamma–Poisson sampler matches the kernel's absorption probability and quartiles within Monte Carlo error
       (400,000 draws).

3. **A post-run numerical cross-check of S3, added after launch and before any result** (mathb's
   `2026-10-06-claim055-total-adapter.md`).
   - S3's `log_e` is recomputed with `checks/d13-drift-total/total.py` (`score_total_path`) on the first five paths of
     every monthly, weekly and daily cell. Each path is regenerated from its seed.
   - Reported: the agreement, and the counts of `gaussian_sup_unbounded` valid boundaries and of failures.
   - The run, its scores and its decisions are unchanged. This is numerical evidence only, and neither implementation
     is certified.

4. **A post-hoc numerical-failure sensitivity, added after seeing the results.**
   - **The failures.** The registered run recorded `numerical_failure` on 282 path-frequency records: 33 for CEV
     p = 0.5 at T = 5, and 249 across Sin's models (Sin's martingale model 12, 31 and 121 at T = 1, 2 and 5; Sin's
     strict model 1, 10 and 74). The cause is `scipy.special.ive(ν, z)` returning NaN for very large
     arguments, z of order 10⁹ (for example ν = 0.5, z = 1.08·10⁹). This hits the p ≥ 1.5 candidates at low prices on
     the 5-minute grid. The exact value is finite: mathb's mpmath kernel gives −71,399 for one such transition.
   - **What the registered run did.** As the contract requires, these records were kept as zero evidence, so as
     nonrejections, and no path was dropped.
   - **The sensitivity.** `experiments/022/failures_sensitivity.py` regenerates the affected cells and recomputes only
     those records. It replaces scipy's NaN by the exact four-term large-argument series of e^{−z}I_ν(z), which
     matches mpmath to machine precision at z of 2·10⁷ to 3·10⁹.
   - **Reporting.** Its outcome is reported beside the registered numbers, and the registered numbers stand.

## Results

**Rejection rates at α = 0.05** (1,000 paths per cell; binomial SE ≤ 0.016). Each entry is S1 / S3 / S5 for monthly, weekly, daily, 5-minute: S1 = claim 054 raw null exclusion, S3 = claim 055 drift-robust score, S5 = experiment 019's claim-052 test. The band rule S2 tracks S1 slightly lower, and the clipped score S4 never rejects in any cell (see below); both are in `results.json`.

| truth (pricing; relation) | T | monthly | weekly | daily | 5-minute |
|---|---|---|---|---|---|
| CEV p = 0.5 (true; in) | 1 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| CEV p = 0.5 (true; in) | 2 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| CEV p = 0.5 (true; in) | 5 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| CEV p = 0.75 (true; in) | 1 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| CEV p = 0.75 (true; in) | 2 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| CEV p = 0.75 (true; in) | 5 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| GBM κ = 0.30 (true; in) | 1 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| GBM κ = 0.30 (true; in) | 2 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| GBM κ = 0.30 (true; in) | 5 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| CEV p = 1.25 (strict; in) | 1 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.83 / 0.39 / 0.00 |
| CEV p = 1.25 (strict; in) | 2 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.06 / 0.00 / 0.00 | 0.98 / 0.88 / 0.00 |
| CEV p = 1.25 (strict; in) | 5 | 0.00 / 0.00 / 0.00 | 0.05 / 0.00 / 0.01 | 0.49 / 0.07 / 0.00 | 1.00 / 1.00 / 0.00 |
| CEV p = 1.5 (strict; in) | 1 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.03 / 0.00 / 0.05 | 0.98 / 0.86 / 0.22 |
| CEV p = 1.5 (strict; in) | 2 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.01 | 0.25 / 0.03 / 0.09 | 1.00 / 0.99 / 0.19 |
| CEV p = 1.5 (strict; in) | 5 | 0.01 / 0.00 / 0.01 | 0.19 / 0.05 / 0.07 | 0.76 / 0.43 / 0.12 | 1.00 / 1.00 / 0.16 |
| CEV p = 2 (strict; in) | 1 | 0.00 / 0.00 / 0.00 | 0.01 / 0.00 / 0.01 | 0.17 / 0.03 / 0.29 | 1.00 / 0.99 / 1.00 |
| CEV p = 2 (strict; in) | 2 | 0.01 / 0.00 / 0.01 | 0.09 / 0.02 / 0.10 | 0.59 / 0.30 / 0.68 | 1.00 / 1.00 / 1.00 |
| CEV p = 2 (strict; in) | 5 | 0.12 / 0.04 / 0.14 | 0.58 / 0.28 / 0.64 | 0.95 / 0.82 / 0.97 | 1.00 / 1.00 / 1.00 |
| CEV p = 1.75 (strict; omitted exponent) | 1 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.10 / 0.00 / 0.16 | 0.85 / 0.57 / 0.92 |
| CEV p = 1.75 (strict; omitted exponent) | 2 | 0.00 / 0.00 / 0.00 | 0.03 / 0.00 / 0.05 | 0.39 / 0.08 / 0.41 | 0.79 / 0.58 / 0.85 |
| CEV p = 1.75 (strict; omitted exponent) | 5 | 0.04 / 0.01 / 0.05 | 0.30 / 0.12 / 0.29 | 0.67 / 0.40 / 0.64 | 0.75 / 0.58 / 0.73 |
| GBM κ = 0.35 (true; omitted scale) | 1 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.01 / 0.00 / 0.05 | 0.24 / 0.00 / 0.27 |
| GBM κ = 0.35 (true; omitted scale) | 2 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.03 / 0.00 / 0.05 | 0.18 / 0.00 / 0.13 |
| GBM κ = 0.35 (true; omitted scale) | 5 | 0.00 / 0.00 / 0.00 | 0.01 / 0.00 / 0.00 | 0.09 / 0.00 / 0.01 | 0.16 / 0.00 / 0.01 |
| CEV p = 1.5, κ = 0.35 (strict; omitted scale) | 1 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.03 / 0.00 / 0.06 | 0.26 / 0.02 / 0.25 |
| CEV p = 1.5, κ = 0.35 (strict; omitted scale) | 2 | 0.00 / 0.00 / 0.00 | 0.01 / 0.00 / 0.01 | 0.09 / 0.02 / 0.11 | 0.26 / 0.08 / 0.20 |
| CEV p = 1.5, κ = 0.35 (strict; omitted scale) | 5 | 0.03 / 0.01 / 0.02 | 0.12 / 0.02 / 0.09 | 0.30 / 0.09 / 0.17 | 0.41 / 0.23 / 0.18 |
| GBM κ = 0.30, μ = 0.05 (true; drift) | 1 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| GBM κ = 0.30, μ = 0.05 (true; drift) | 2 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| GBM κ = 0.30, μ = 0.05 (true; drift) | 5 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| Sin a·γ < 0 (true; SV) | 1 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.01 / 0.00 / 0.00 |
| Sin a·γ < 0 (true; SV) | 2 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.01 / 0.00 / 0.00 |
| Sin a·γ < 0 (true; SV) | 5 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| Sin a·γ > 0 (strict; SV) | 1 | 0.01 / 0.00 / 0.01 | 0.11 / 0.00 / 0.11 | 0.31 / 0.07 / 0.31 | 0.42 / 0.19 / 0.42 |
| Sin a·γ > 0 (strict; SV) | 2 | 0.03 / 0.00 / 0.03 | 0.22 / 0.04 / 0.23 | 0.38 / 0.16 / 0.37 | 0.42 / 0.22 / 0.41 |
| Sin a·γ > 0 (strict; SV) | 5 | 0.12 / 0.03 / 0.12 | 0.27 / 0.14 / 0.26 | 0.30 / 0.20 / 0.28 | 0.31 / 0.20 / 0.29 |
| Merton jumps (true; jumps) | 1 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.01 / 0.00 / 0.01 | 0.08 / 0.02 / 0.03 |
| Merton jumps (true; jumps) | 2 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.01 / 0.00 / 0.01 | 0.09 / 0.03 / 0.01 |
| Merton jumps (true; jumps) | 5 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.02 / 0.00 / 0.00 | 0.05 / 0.01 / 0.00 |
| GBM κ = 0.30, rounded to 10⁻⁴ (true) | 1 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| GBM κ = 0.30, rounded to 10⁻⁴ (true) | 2 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| GBM κ = 0.30, rounded to 10⁻⁴ (true) | 5 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 |
| CEV p = 1.5, rounded to 10⁻⁴ (strict) | 1 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.03 / 0.00 / 0.05 | 0.98 / 0.86 / 0.21 |
| CEV p = 1.5, rounded to 10⁻⁴ (strict) | 2 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.01 | 0.25 / 0.03 / 0.09 | 1.00 / 0.99 / 0.18 |
| CEV p = 1.5, rounded to 10⁻⁴ (strict) | 5 | 0.01 / 0.00 / 0.01 | 0.19 / 0.05 / 0.07 | 0.76 / 0.43 / 0.12 | 1.00 / 1.00 / 0.16 |

**Claim 023's analytic envelopes ε** (from `checks/d14-grid-budget/budget.py`, evaluation block of each cell). Entries: GBM κ = 0.35 against the nearest grid point / drifted GBM against κ = 0.30 / the uniform grid envelope used by S4. The size bound is α + ε; it is not a predicted rejection rate.

| T | monthly | weekly | daily | 5-minute |
|---|---|---|---|---|
| 1 | 0.26 / 0.06 / 0.34 | 0.51 / 0.06 / 0.64 | 0.88 / 0.06 / 0.96 | 1.00 / 0.06 / 1.00 |
| 2 | 0.36 / 0.08 / 0.47 | 0.67 / 0.08 / 0.80 | 0.97 / 0.08 / 1.00 | 1.00 / 0.08 / 1.00 |
| 5 | 0.55 / 0.13 / 0.68 | 0.88 / 0.13 / 0.96 | 1.00 / 0.13 / 1.00 | 1.00 / 0.13 / 1.00 |

**e-BH at q = 0.10 (m = 20, 50 panels): mean FDP; for mixed panels also power.** Entries S1 / S3 (S4 makes no discoveries anywhere).

| panel | T | daily | 5-minute |
|---|---|---|---|
| all null, GBM κ = 0.30 | 1 | FDP 0.00 / 0.00 | FDP 0.00 / 0.00 |
| all null, GBM κ = 0.30 | 2 | FDP 0.00 / 0.00 | FDP 0.00 / 0.00 |
| all null, GBM κ = 0.30 | 5 | FDP 0.00 / 0.00 | FDP 0.00 / 0.00 |
| all null, GBM κ = 0.35 (off-grid) | 1 | FDP 0.02 / 0.00 | FDP 1.00 / 0.00 |
| all null, GBM κ = 0.35 (off-grid) | 2 | FDP 0.16 / 0.00 | FDP 1.00 / 0.00 |
| all null, GBM κ = 0.35 (off-grid) | 5 | FDP 0.66 / 0.00 | FDP 0.98 / 0.00 |
| all null, drifted GBM | 1 | FDP 0.00 / 0.00 | FDP 0.02 / 0.00 |
| all null, drifted GBM | 2 | FDP 0.00 / 0.00 | FDP 0.00 / 0.00 |
| all null, drifted GBM | 5 | FDP 0.00 / 0.00 | FDP 0.00 / 0.00 |
| 10 GBM 0.30 + 10 CEV 1.5 | 1 | FDP 0.00 / 0.00; power 0.00 / 0.00 | FDP 0.00 / 0.00; power 0.97 / 0.84 |
| 10 GBM 0.30 + 10 CEV 1.5 | 2 | FDP 0.00 / 0.00; power 0.12 / 0.00 | FDP 0.00 / 0.00; power 1.00 / 0.99 |
| 10 GBM 0.30 + 10 CEV 1.5 | 5 | FDP 0.00 / 0.00; power 0.77 / 0.37 | FDP 0.00 / 0.00; power 1.00 / 1.00 |
| 10 GBM 0.35 + 10 CEV 1.75 | 1 | FDP 0.02 / 0.00; power 0.01 / 0.00 | FDP 0.20 / 0.00; power 0.86 / 0.55 |
| 10 GBM 0.35 + 10 CEV 1.75 | 2 | FDP 0.03 / 0.00; power 0.30 / 0.02 | FDP 0.19 / 0.00; power 0.77 / 0.57 |
| 10 GBM 0.35 + 10 CEV 1.75 | 5 | FDP 0.11 / 0.00; power 0.66 / 0.37 | FDP 0.20 / 0.00; power 0.73 / 0.58 |

**Numerical checks.**
- **High precision.** The `total.py` path checks cover 690 paths: the first five of every monthly, weekly and daily
  cell, and the first path of each 5-minute cell at T = 1. They give zero fit mismatches, with log E agreeing within
  8.8·10⁻⁸.
- **Kernel level.** On 5-minute transitions, the kernel agrees with `log_transition` to a relative 2.4·10⁻⁸.
- **S3 against mathb's claim-055 adapter** (Deviation 3, `crosscheck_s3.json`): 675 paths agree to 4.2·10⁻¹⁰, with zero
  decision mismatches and every status "ok".
- **Decision policy.** Zero ambiguous decisions, and one training margin below 10⁻⁶.
- **Absorption.** CEV p = 0.5 at T = 5 has 9 paths absorbed at zero by T, and they stay in every denominator.
- **S5 failures.** S5 (claim 052) fails on 36 records: nonpositive prices, which are outside its domain, counted as
  nonrejections.
- **Numerical failures** in S1–S4: see Deviation 4 and the sensitivity below.

**Deviation 4's sensitivity** (`failures_sensitivity.json`).
- All 282 failed records are recomputed with the exact large-argument Bessel series. None still fails.
- None of them would reject under S1 or S3, at α = 0.05 or 0.10.
- So the registered zero-evidence handling changed no decision, and every reported rate stands.

**Readings.** These are pointwise, at κ = 0.30 truths unless noted.
1. **In catalogue, claim 054's test is calibrated and has frequency-driven power across CEV powers.**
   - On the null powers p = 0.5, 0.75 and 1, the largest S1 rate is 0.001.
   - True-parameter noncoverage is at most 0.004 at α = 0.05 (0.012 at α = 0.10).
   - **Power at 5 minutes:** 0.83–1.00 at p = 1.25, and 0.98–1.00 at p = 1.5 and 2.
   - **Power on daily data:** p = 1.5 rises from 0.03 (T = 1) to 0.76 (T = 5); p = 2 from 0.17 to 0.95.
   - **Monthly data** stays near zero except p = 2 at T = 5 (0.12).
2. **The CEV grid matters where the claim-052 benchmark's catalogue lacks the truth.** On p = 1.5, experiment 019's
   p ∈ {1, 2} test (S5) reaches only 0.16–0.22 at 5 minutes, against S1's 0.98–1.00. On p = 2, which is in both
   catalogues, the two are similar.
3. **Off the catalogue, S1 loses calibration at high frequency; S3 restores it for Gaussian nulls.**
   - The off-grid GBM κ = 0.35 is a pricing null. S1 rejects it at 0.24 / 0.18 / 0.16 at 5 minutes (T = 1 / 2 / 5),
     and S3 at 0.00 everywhere. GBM is in S3's declared class.
   - **On all-null κ = 0.35 panels,** e-BH with S1 makes a false discovery in essentially every 5-minute panel (mean
     FDP 0.98–1.00). With S3 it makes none.
   - **Drifted GBM:** zero under every score.
   - **Merton jumps** (outside every class): S1 reaches 0.05–0.09 at 5 minutes, S3 0.01–0.03.
   - **Sin's martingale model:** at most 0.01 under any score.
4. **S3's robustness costs power.**
   - p = 1.5 daily at T = 5: S1 0.76, S3 0.43. p = 1.25 daily at T = 5: S1 0.49, S3 0.07.
   - At 5 minutes both reach about 1 on the in-catalogue alternatives.
   - On the mixed panels at 5 minutes, S3 keeps FDP at 0 with power 0.84–1.00 (in catalogue) and 0.55–0.58 (off
     catalogue). S1's off-catalogue mixed panels have FDP of about 0.19.
5. **The clipped score S4 never rejects and makes no e-BH discovery.**
   - The grid envelope for a 3-point κ grid is 0.34–0.68 monthly and about 1 from daily up. So
     min(E, 50)/(1 + 50ε) ≤ 2.8, far below 1/α = 20.
   - This is the power cost math's grid budget predicted. Making S4 usable needs a far finer grid (hundreds to
     thousands of points), which was not run.
6. **Claim 023's analytic envelopes** (the table above) are vacuous at daily and 5-minute sampling for the off-grid
   scale (0.88–1.00). The observed S1 false alarms (0.00–0.24) are within α + ε everywhere. For drift the envelope is
   small (0.06–0.13), and the observed false alarms are zero.
7. **Off-catalogue strict truths are detected, at reduced power.**
   - The omitted exponent p = 1.75 reaches S1 0.75–0.85 at 5 minutes (S3 0.57–0.58). It is lower at T = 5 than at
     T = 1.
   - The omitted scale CEV 1.5 with κ = 0.35 reaches 0.26–0.41.
   - Sin's strict model reaches 0.31–0.42.
8. **Rounding to a 10⁻⁴ tick** (outside claim 024's exact-observation guarantee) changes no rate at this tick size.
   Coarser ticks were not run.

Regenerate:
- Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
  experiments/022/run.py`, then `crosscheck_s3.py` and `failures_sensitivity.py`, inside `.worktrees/analyst`, on
  cores − 3 workers.
- The main run takes about 35 minutes.
- Seeds: `SeedSequence(20261023)`.
- Environment: `uv.lock` at the reporting commit.

## Review

Reviewer, 2026-10-06, against main at `856391c`, which contains the reporting commit `9c6e257`.

**Method.** I wrote my own code from the Design, without reading `experiments/022/*.py`. It is committed as `checks/review/exp022/reproduce.py`, with its rerun command and seed (`SeedSequence(2222)`) in its header.
- **The design followed.** The 18-candidate catalogue in its registered order; split k = ⌊N/2⌋; daily and 5-minute grids keeping 0 and T; S1 = claim 054's null exclusion; S3 = claim 055's score with the closed-form Gaussian supremum; rejection at log E > log 20.
- **My own kernels.** AX-55 lognormal, and AX-56 absorbed CEV in log space with the zero atom. Where scipy's `ive` returns NaN or 0 at huge argument, I use my own large-z expansion, which differs from the analyst's four-term series.
- **My own exact paths.** GBM; CEV p ∈ {1.25, 1.5, 2} as Bessel transforms of integer dimension 6, 4 and 3; p = ½ by BESQ(0) Poisson–gamma steps with exact absorption.
- **Sample.** 500 paths for the T = 1 cells (daily and 5-minute) and 1,000 for daily T = 5.
- **Not rerun:** p = 0.75, p = 1.75, the κ = 0.35 CEV, Sin, Merton, rounding, the 5-minute T = 2 and 5 cells, the e-BH panels and the monthly and weekly columns.

**Headline numbers reproduced** (mine, then theirs; S1 / S3).
- **Nulls in the catalogue** (GBM κ = 0.30; CEV p = ½): 0.000 / 0.000 in every cell, against 0.00 / 0.00. CEV p = ½ at T = 5 absorbed 10 of 1,000 paths, against their 9; the absorbed paths stay in the denominator.
- **p = 1.25:** 5-minute T = 1 gives 0.828 / 0.386, against 0.83 / 0.39. Daily T = 5 gives 0.508 / 0.060, against 0.49 / 0.07.
- **p = 1.5:**
  - 5-minute T = 1: 0.984 / 0.896, against 0.98 / 0.86. The S3 gap is about 2 SE.
  - Daily T = 5: 0.748 / 0.442, against 0.76 / 0.43. Daily T = 1: 0.020 / 0.000, against 0.03 / 0.00.
- **p = 2:** daily T = 1 gives 0.178 / 0.034, against 0.17 / 0.03; daily T = 5 gives 0.958 / 0.819, against 0.95 / 0.82; 5-minute T = 1 gives 1.000 / 0.992, against 1.00 / 0.99.
- **The off-grid pricing null, GBM κ = 0.35:**
  - 5-minute T = 1: 0.198 / 0.000, against 0.24 / 0.00. That is about 1.9 SE on S1.
  - Daily T = 5: 0.071 / 0.001, against 0.09 / 0.00.
  - So S3's removal of the off-grid false alarms reproduces.
- **Drifted GBM** (μ = 0.05): ≤ 0.002 / 0.000, against 0.00 / 0.00.
- **S4 (Reading 5)** follows arithmetically. With the reported envelopes ε ≥ 0.34, min(E, 50)/(1 + 50ε) ≤ 50/18 < 2.8, far below 20, so it can never reject.
- **Numerics.** None of my computed kernels was NaN after my large-argument handling. That is consistent with Deviation 4's diagnosis: scipy's `ive` NaN at z of order 10⁹ is a library limitation, not a property of the score.

**The Deviations are honest.**
- **Deviation 1** (scope, `dfda8ac`, 19:14:18) precedes the code commit (`2ff7ed8`, 19:22).
- **Deviation 2** (reduced high-precision scope, for cost) is recorded in that code commit, before the run.
- **Deviation 3** (the S3 cross-check, `c8e725b`) was added after launch but before any result, and is disclosed as such.
- **Deviation 4** (the Bessel-failure sensitivity) is labelled post hoc. Its 282 failed records were kept as zero evidence in the registered numbers, which stand, and the recomputation changes no decision.
- **Timing.** The code-to-results interval (19:22 to 19:59) fits the stated 35-minute run.

**The readings are fair.** Two emphases:
1. **The best result so far, and its condition.** Reading 3 is the most important D5/D14 result to date. On these paths claim 055's S3 eliminates the off-grid-scale false alarms and the e-BH false discoveries, which S1 makes in essentially every 5-minute all-null panel, while keeping 5-minute power of 0.39–0.99 on the in-catalogue alternatives. That holds only when the null's conditional law really is Gaussian (or in the catalogue). The Merton and Sin rows (S3 at 0.01–0.03 and ≤ 0.01) are measurements outside that class, not guarantees, as labelled. My claim-026 review shows that jumps break S3's raw e-moment even where its false-alarm rate stays small.
2. **The power cost at daily sampling.** Reading 4 is reproduced: p = 1.25 daily at T = 5 falls from about 0.5 to about 0.06 under S3. My claim-057 review shows that a declared scale interval recovers much of that cost.

Verdict: reproduced
