---
id: "046"
title: "D32: claim 044's survival-weighted recovery estimator and coordinate compatibility test on synthetic terminal panels — recovery error, coverage, size and power"
status: reproduced
direction: D32
claims: ["044", "016", "010"]
code: experiments/046/
---
## Question

This is LAB_REQUEST.md's fifth addendum, item 22(d), following math's note `2026-10-08-d32-recovery-design.md` and
red-passed claim 044 (FINDINGS, "D32 estimator input").

**The questions,** on synthetic panels only:
1. How accurately does claim 044's plug-in estimator recover claim 016's corrected contributions
   b_i = ω_i − θ_i, as the physical (N) and pricing (M) sample sizes grow?
2. Does the one-sided lower bound (9) cover θ_i at the stated level?
3. What are the size and power of the coordinate compatibility test, for the common radius (5) and for the
   per-cell radius variant that claim 044's review found more powerful?

**Jobs, kept separate:**
- verifying claim 044's guarantees under its premises (identifying-restriction cells);
- measuring power against its separated alternative (weight-dependent tilt cells).

**Scope.**
- No real option data, no pricing-null certificate, no prospective collection.
- Non-rejection is not acceptance of the terminal-density restriction.

No result exists when this Design is committed.

## Design

**Basket and pricing law Q** (fixed now).
- **Names:** d = 3, with holdings n = (1, 1, 1) and starts S_i0 = 1, so I₀ = 3 and ω = (1/3, 1/3, 1/3). Horizon
  T = 1 year.
- **Under Q,** the names are independent:
  - **name 1:** exact CEV with p = 2 and κ = 0.40 (AX-56; a strict local martingale, so b₁ > 0), sampled in one
    step by experiment 027's copy of 022's exact sampler. Absorption at zero is allowed and the survival mass is
    kept: I_T stays positive through names 2 and 3, and μ₁ = 0 when S₁ is absorbed;
  - **names 2 and 3:** GBM with volatility 0.25 and 0.35 (AX-55; true martingales, so b₂ = b₃ = 0).
- **Index and weights:** I_T = Σ n_i S_iT, μ_i(T) = n_i S_iT / I_T.

**The pricing sample.** M independent Q draws of I_T (the X_l), independent of the physical sample.

**The physical sample.** N independent terminal panels (I_T, μ(T)) under P, with dP/dQ = h/E_Q[h]. Each panel is
drawn exactly by rejection from Q panels, accepted with probability h/h_max. The cells:
- **R0 (restriction, P = Q):** h = 1;
- **R1 (restriction, index-only tilt):** h(I_T) = exp(clip(log(I_T/I₀), −1, 1)), bounded and positive. It changes
  P_I but keeps the conditional weights, so the identifying restriction holds;
- **V1 and V2 (separated alternatives):** h = 1 + ε μ₁(T) with ε = 0.5 (V1) and ε = 2 (V2). This is claim 044's
  (12): θ₁ > ω₁ while Σθ_i = 1 stays exact.

**Sample sizes:** N = M ∈ {10⁴, 10⁵, 10⁶}.

**Estimator** (claim 044, (3), with a histogram regression).
- **Range and partition:** B = [0.5 I₀, 2 I₀], with J = 20 equal cells as the primary partition and J = 40 as a
  labelled secondary.
- **Regression:** within-cell means of μ(T) as m̂. Empty cells and points outside B get ω.
- **Estimates:** θ̂_i = (1/(M I₀)) Σ_l X_l m̂_i(X_l) and b̂_i = ω_i − θ̂_i.
  - They are never normalized by the sampled index mean, and a negative b̂_i is never clipped.
  - The sum identity (4), Σb̂_i = 1 − (1/(M I₀)) Σ_l X_l, is checked on every replicate.

**The compatibility test** (claim 044, (9)), at α_reg = α_price = 0.025 (total 0.05).
- **Common radius (primary):** lower_i = θ̂_i,B − e_N(B, α_reg) − c_M(B), with e_N from (5) and c_M from (9).
  Reject if lower_i > ω_i for some i.
- **Per-cell radius variant (labelled):** each X_l in B contributes X_l·(m̂_i(X_l) − e_j)/(M I₀), where e_j is cell
  j's own radius, min(1, L_B h + √(log(2dJ/α_reg)/(2N_j))), and 1 for an empty cell; then subtract c_M(B). It rests
  on the same simultaneous event, so it is equally valid.
- **The Lipschitz bound L_B (supplied before any test):** twice the largest absolute difference quotient of the
  oracle conditional means m_i across adjacent cells of a 200-cell partition of B. The oracle is a separate
  10⁸-draw Q run per physical law, seed `SeedSequence(20261146)`. It is fixed per cell (R0, R1, V1, V2), committed
  in `oracle.json` before any test replicate, and labelled "declared from an oracle computation, not fitted to test
  data".
- **Arithmetic:** floating point. Records whose lower bound lies within 10⁻⁹ of ω_i are counted "unresolved, not
  rejected". There is no certified arithmetic, which is stated.

**Oracle diagnostics** (labelled, never a competitor).
- **True targets:** θ_i and b_i from the oracle run, with Monte Carlo SE. Under the restriction, the direct Q
  constituent means give b_i = n_i(S_i0 − E_Q S_iT)/I₀; E_Q S_1T for CEV comes from the oracle run as well.
- **An oracle-weights estimator:** the true m_i on the same pricing sample, separating regression error from pricing
  sampling error.

**Replicates and seeds.** 1,000 replicates per (truth cell, N, J), on `SeedSequence(20261046)` with one child per
cell. Worst-case SE is 0.016. Smoke tier: 20 replicates per cell, `SeedSequence(20261246)`, timed.

**Outputs** (each kept separate, and failures retained):
- **Recovery:** bias and RMSE of b̂_i against the oracle b_i, for the estimated and oracle-weights versions; and the
  share of negative b̂_i.
- **Coverage:** the share of replicates with lower_i ≤ θ_i for all i (target ≥ 0.95, which needs both events).
- **Test size** (R0, R1) and **power** (V1, V2), with Wilson intervals, for the common radius and the per-cell
  variant, per N and J.
- **Sum identity:** its maximum absolute deviation.
- **Counts:** empty cells, points outside B, unresolved records and runtime.
- Files: `oracle.json`, `results.json` and `summary.csv`.

**Implementation.**
- Code and `oracle.json` are committed before any test replicate.
- The run comes after experiments 043 (D28) and 042 (D29), as the note requires, with the single-thread BLAS
  prefix and at most cores − 3 workers.

**Scope.**
- The observation contract is synthetic (independent repeated terminal panels at one horizon), not overlapping
  windows from one path.
- ν_T is supplied by sampling.
- Coverage of the full contribution b_i, which would need a two-sided interval with an omitted-tail bound, is not
  claimed. The test is a necessary-compatibility test only.

## Deviations

**Deviation 1 (2026-10-08, after the first oracle computation and before any test replicate): separated
alternatives, the per-cell radius, and a positive control.**
- **What the first oracle showed.** It is a design-stage computation: 10⁸ Q draws, with no test statistic computed.
  - Name 1's contribution is b₁ = 0.0041, and p_I = 0.9959. CEV with p = 2 and κ = 0.4 over one year has
    E_Q S_1T ≈ 0.988, and no absorption.
  - **V1** (tilt 1 + 0.5μ₁) is **not** a separated alternative: θ₁ = 0.3327 < ω₁. The tilt's positive term (claim
    044's (13)) is smaller than name 1's bubble deficit, so every θ_i ≤ ω_i and the test's null holds although the
    restriction fails.
  - **V2** (ε = 2) is separated by only θ₁ − ω₁ = 0.0054.
  - The test radius's Lipschitz term alone is L_B·h ≈ 0.45 × 0.225 ≈ 0.10 at J = 20.
- **The cause:** claim 044's construction (12) tilts a name that is a **true martingale** under Q. The registered
  cells tilted name 1, the strict local martingale.
- **Changes:**
  1. **V1 and V2 are kept as registered** and reported as a non-separated and a weakly separated violation.
  2. **New cells V3 and V4** tilt name 3 (GBM, a true martingale) with h = 1 + ε μ₃, ε = 2 and 10, following (12).
  3. **The per-cell radius variant** subtracts **2 c_M**, as in claim 044's review, because the summand
     X(m̂ − e_j) ranges over [−R/I₀, R/I₀]. The registered text omitted the doubling, and the code had it once. This
     is a correction.
  4. **A labelled positive control:** the claim-044 review's own terminal-table model
     (`checks/review/044/reproduce.py`).
     - **Model:** d = 2, I₀ = 1, ω = (0.5, 0.5), a lognormal index with log-sd 0.25, and μ₁ | I ~ Beta(g, 1 − g)
       with g(x) = 0.5 + 0.4 tanh(log x − c), where c gives the boundary null θ = ω.
     - **Cells:** PC0 (P = Q, the boundary null) and PC1 (the (12) tilt with ε = 3).
     - **Test settings:** B = [0.6, 1.7], J = 20, and the review's L_B: analytic for the null, 1.05 times the
       numerical slope for the tilt.
     - It shows whether this implementation finds power where the separation is large (θ₁ ≈ 0.62 > 0.5), the
       review's finding.
- **Unchanged:** R0, R1, B, J ∈ {20, 40} for the price-path basket, the replicates, the seeds and the outputs. The
  oracle is recomputed with the same seed for all cells and committed before any test replicate.

**Deviation 2 (2026-10-08, before any test replicate): math's evaluator adopted (note
`2026-10-08-d32-cell-evaluator.md`).**
- **The estimator and both tests** now come from `checks/d32-recovery-evaluator/evaluate.py` (`evaluate_record`),
  unchanged. It replaces this experiment's own histogram code for the price-path cells and the positive control.
  - Cells are left-closed, and the last is closed on the right, so both endpoints of B are included.
  - Every one of the M pricing draws is in the denominator.
  - Negative contributions are kept, and invalid or numerically failed records come back explicitly.
  - Failed records stay in the test denominators as non-rejections, and missing estimation outputs are counted
    separately (`failed_records`).
- **The two rules are reported separately:** the common radius with c_M, and the signed per-cell rule with 2c_M. There
  is no reject-if-either procedure.
- **The positive control's Lipschitz bound** is now the analytic `tilted_lipschitz(0.6, 0.4, 1, ε)`, predeclared:
  0.667 for PC0 and 1.122 for PC1. The review used 1.05 times its sampled maximum (0.555), and the review's power
  numbers are not carried over to this bound. The oracle was recomputed with the same seed: the price-path cells are
  unchanged, and the positive control's declared bounds changed.
- **Scope of the review's model:** its terminal Beta model is a terminal-law check, not a proved
  continuous-local-martingale process. It is reported apart from the GBM/CEV process panels, which carry the
  experiment's synthetic-process claims.
- **Not checked by the arrays:** sampling independence, smoothness and the pricing-law premises are design premises,
  stated rather than tested.
- A code test on a throwaway seed (not a recorded replicate) ran both cell types through the evaluator, with sum
  identity residuals up to 6 × 10⁻¹⁶.

**Deviation 3 (2026-10-08, before any test replicate): corrections against claim 044, per math's note
`2026-10-08-d32-registered-premises.md` (FINDINGS "D32 registered design"; `checks/d32-targets/check.py`).**
1. **The per-cell 2c_M** is already in place (Deviations 1 and 2, through math's evaluator).
2. **The price basket's Lipschitz bound is not a supplied bound.** Twice a Monte Carlo finite-difference maximum,
   even from independent data, is not the bound claim 044 assumes, and the analytic tanh bound does not apply to
   this basket.
   - The size and coverage rows of the price-path cells (R0–V4) are therefore labelled **diagnostic, not
     verification under claim 044's premises**.
   - Only the positive control (analytic L_B) verifies size and coverage under the claim's premises, for its
     terminal-law model.
3. **Exact targets for the restriction cells.** Audited AX-54 gives E_Q S₁ = 0.987580669348448, so
   b₁ = 0.004139776883851, b₂ = b₃ = 0 and p_I = 0.995860223116149. There is no zero atom from this positive start:
   the oracle found no absorption.
   - R0 and R1 now use these exact θ = (1/3 − b₁, 1/3, 1/3). The 10⁸-draw Monte Carlo values are kept beside them
     as a check: they agree to within 9 × 10⁻⁶, against an SE of about 2 × 10⁻⁵.
   - "Survival" here means the index's share loss (Σθ = p_I < 1), not price absorption.
4. **Pseudo-targets and separation.** Under the weight tilts, Σθ_i = p_I, not 1. This corrects the Design's
   "Σθ_i = 1 stays exact", which holds only for claim 044's all-true-martingale example.
   - A tilt on name 1 is separated only if its variance gain exceeds b₁: V1 is not (θ₁ − ω₁ = −0.0007), and V2 is
     only weakly (+0.0054).
   - V3 and V4 tilt name 3 (b₃ = 0): θ₃ − ω₃ is +0.0098 and +0.0187 by the binned Monte Carlo oracle.
   - All four are labelled **candidate alternatives**, with approximate, Monte Carlo pseudo-targets, until a strict
     target gap is justified.
5. **Fixed B and J** give a fixed-bin approximation limit, not claim 044's consistency scheme. Recovery errors are
   reported as finite-design errors, and the binned oracle values are labelled as approximations with their Monte
   Carlo uncertainty.

- **Unchanged:** cells, seeds, sample sizes, the evaluator, the positive control and the run order (after experiments
  043 and 042).
- The oracle is recomputed with the same seed, and only the restriction cells' θ changes, to the exact values.

**Deviation 4 (2026-10-08, before any test replicate): math's integration fixes adopted (note
`2026-10-08-d32-run-retention.md`; commit 7872957; check `checks/d32-run-retention/check.py`).**
- **Before:** batches in which every evaluator call failed would have crashed the summaries.
- **After:**
  - expected failures before the evaluator (ValueError or arithmetic) become retained non-rejections, and later
    replicates continue;
  - missing estimates are null, with explicit estimation and coverage denominators and a count of records whose
    coverage is unknown;
  - the CSV no longer duplicates the J = 20 rows or pads the two-name control's nonexistent third RMSE column.
- **Coverage is reported conditional on evaluable records,** with its unknown count beside it.
- **Checks:** math's check passes (all-failed and mixed summaries, exact denominators, unique rectangular CSV rows,
  retained pre-evaluator failures, no sampling). A code test on a throwaway seed (not a recorded replicate) runs the
  price and control cells through the updated code.
- **Unchanged:** the design, the oracle and the run order.


**Deviation 5 (2026-10-08, after the Results and the review; per math's note
`2026-10-08-exp046-reading-corrections.md` and `checks/d32-results-reading/README.md`): reading corrections.** No
number is rerun or changed. The Results prose is corrected in place:
- **Biases named by cell:** PC1's bias is ±0.0062 and PC0's ±0.0016 (the review's wording correction).
- **Radius range:** the archived process median common radii span 0.161–1.0 across N, J and truth cell, not
  0.18–0.83.
- **The oracle weights** are approximate conditional means (a Monte Carlo fine-binned pseudo-target with edge
  fallback), not the true means.
- **Finite-case observations, not proofs:**
  - zero null flags do not verify size;
  - fixed-J runs do not show asymptotic power;
  - median radius comparisons do not make rejection impossible.
- **Full target vs compact target:** a positive full-target gap is not automatically a compact-target gap, and
  full-target coverage is weaker than compact-target coverage.
- **The bound:** the one constructed rigorous bound is unusable, not the only possible finite bound.
- **Where the terminal-control bias comes from:** math's quadrature attributes about 94% (PC0) and 99% (PC1) to the
  outside-B fallback. Neither larger N nor shrinking bins alone removes it; the estimation range must grow. The split
  is not extrapolated to the basket.
- **Unchanged:** the separate rules and the diagnostic labels on the process rows.

## Results

**Status: reported (2026-10-08).** `experiments/046/run.py` (Deviations 1–4; code as merged), 824 s on 7 workers.
Outputs: `results.json` (summaries per truth cell, N and J) and `summary.csv`.
- **Records:** 1,000 replicates per cell. No failed records, and no unresolved decisions.
- **Sum identity:** holds to within 1.7 × 10⁻¹⁴ on every replicate.
- **Labels (Deviations 3 and 4):**
  - the positive control (PC0, PC1; the review's terminal-law model, analytic L_B) is the only verification of
    claim 044's premises;
  - the price-path rows (R0–V4) are **diagnostic**, because their L_B is a Monte Carlo finite-difference value, not
    a supplied bound;
  - fixed B and J are a fixed-bin approximation, not the claim's consistency scheme.

**1. Positive control (terminal-law model, B = [0.6, 1.7], J = 20).** Rejection rates with Wilson 95% intervals; the
two rules are reported separately.

| cell | N = M | common radius (c_M) | per-cell radius (2c_M) | full-target coverage (both rules) |
|---|---|---|---|---|
| PC0 (boundary null) | 10⁴ / 10⁵ / 10⁶ | 0 / 0 / 0 (each 0–0.4%) | 0 / 0 / 0 | 100% |
| PC1 (tilt ε = 3, θ₁ = 0.646) | 10⁴ | 0% | 0% | 100% |
| PC1 | 10⁵ | 0% | **100%** (99.6–100%) | 100% |
| PC1 | 10⁶ | **100%** | **100%** | 100% |

- **No null rejection** was observed at the boundary null in 1,000 replicates per rule and size. This is a finite-case
  observation, not a proof of size. Each rule has its own nominal budget, and combining their rejections is not
  covered.
- **On PC1, the per-cell rule rejected every replicate from N = 10⁵, and the common radius only at 10⁶.** This is with
  the analytic bound (1.12) instead of the review's sampled 0.555, so the review's power numbers are not carried over.
  Fixed-J runs at three sizes are not a demonstration of asymptotic power.
- **Recovery bias** (stable across N): b̂ is biased by about +0.0016 / −0.0016 on PC0 and +0.0062 / −0.0062 on PC1.
  - Math's terminal-control quadrature (`checks/d32-results-reading/README.md`) attributes about 94% (PC0) and 99%
    (PC1) of it to the fallback to the initial weights outside B.
  - So neither larger N nor finer bins alone can remove it. Growing the estimation range matters.

**2. Price-path basket** (diagnostic; 3 names under Q: CEV p = 2 and two GBMs; exact targets for R0 and R1).
- **Size:** neither rule rejects any restriction cell (R0, R1), at any N or J.
- **Power:** neither rule rejects any violation cell (V1–V4), at any N or J.
  - V1 is not separated (θ₁ − ω₁ = −0.0007). V2 is separated by 0.0054 on name 1; V3 and V4 by 0.0098 and 0.0187 on
    name 3.
  - The archived median common radii span 0.161–1.0 across N, J and truth cell. The per-cell penalty is of similar
    size. Both are far above every full-target separation, and no rejection was observed. This is a finite-case
    observation about these medians, not a proof that rejection is impossible.
  - A positive full-target gap (θ − ω) is not automatically a gap on the compact target used in claim 044's proof.
- **Full-target coverage:** 100% in every cell. This is weaker than coverage of the compact target.

**3. Recovery error** (b̂ against the exact AX-54 b for R0 and R1, and the binned oracle for V1–V4).
- **The histogram estimator has a persistent bias** that does not shrink with N or with J ∈ {20, 40}: about +0.0035 on
  name 1 and −0.0016 to −0.0019 on names 2 and 3, in every cell. RMSE at N = 10⁶ is 0.0034–0.0037 on name 1.
  - The bias is the same size as the target itself (b₁ = 0.0041).
  - The share of replicates with a negative b̂ for some name is 83–100%, mostly names 2 and 3 (true b = 0), and is
    kept, not clipped.
- **The oracle-weights estimator** uses approximate conditional means: a Monte Carlo fine-binned pseudo-target (2,000
  bins on [0, 30 I₀]) with edge fallback, not the true means. It has bias at most 1 × 10⁻⁴ and RMSE falling to
  1.5 × 10⁻⁴ at N = 10⁶. That points to the fixed-partition regression, not pricing-sample error, as the source of the
  persistent error.
  - On the terminal controls, math's quadrature splits that error: about 94% (PC0) and 99% (PC1) comes from the
    outside-B fallback, and the rest from within-cell averaging.
  - That split is not computed for the basket and is not extrapolated to it.
- That is claim 044's warning made concrete: fixed B and J give a fixed-partition approximation limit, and
  consistency needs growing range as well as shrinking cells (claim 044, part 2).

**Reading.**
- **Verification (positive control, finite-case observations):**
  - **Consistent with claim 044:** no null rejection at the boundary null in 1,000 replicates per rule at each of
    three sizes. This does not prove size.
  - **PC1 rejections:** at the fixed J = 20, PC1 is rejected in every replicate by the per-cell rule from N = 10⁵, and
    by the common radius at 10⁶. These rates do not show asymptotic power.
  - **Coverage:** the lower bound covers the full target in every replicate.
- **On the realistic price-path basket** (diagnostic):
  - **No rejection observed:** the full-target separations a strict-local-martingale constituent and weight tilts
    produce (≤ 0.019) are far below the archived median radii (0.161–1.0), and no rejection was observed at any N or
    J.
  - **Recovery bias:** the fixed-partition recovery bias (about 0.0035) is as large as the contribution being
    recovered (0.0041).
  - **What recovery would need:** an estimation range that grows (the terminal controls show outside-range fallback
    dominates there), shrinking cells, and a smaller supplied Lipschitz bound. Larger samples or finer cells alone are
    not enough.
  - **The useful-bound problem stays open** (math's smoothness-scope note). The one rigorous finite bound constructed
    for this basket, about 1.9 × 10¹⁶, is unusable: it would saturate every radius. It is not the only possible
    finite bound.
- **Scope:** synthetic terminal panels only; floating-point evaluation; the terminal-law control is not a process
  model; non-rejection is not acceptance of the terminal-density restriction.

## Review

Reviewer, 2026-10-08, against main at `1cb46bce`, which contains the results commit `107a024a`.

**Method.** I wrote my own estimator and both test rules from claim 044 and the Deviations, without reading `experiments/046/run.py` or math's evaluator. The script is committed as `checks/review/exp046/reproduce.py`, with its rerun command and seed in its header. It runs single-process in about a minute.
- **The rules.** The common radius uses (5) with c_M. The per-cell rule integrates each cell's own radius over the pricing sample, with 2c_M.
- **(A) The positive control.** My claim-044 review model, with the experiment's declared analytic L_B, at N = M = 10⁴ and 10⁵ (200 replicates) and 10⁶ (50 replicates).
- **(B) The price-path basket,** from my own exact sampler. 1/(κS₁) is BES(3), drawn in one step; the GBMs are lognormal.
  - **Targets:** the exact b₁; binned Monte Carlo pseudo-targets for V1–V4 (2×10⁷ Q draws, 2,000 bins on [0, 90]).
  - **Bias:** the infinite-sample limit of the fixed-bin estimator (B = [1.5, 6], J = 20), hence its recovery bias.
  - **Replicates:** R0 and V4 at 10⁵ (100 replicates) and 10⁶ (20 replicates) with the declared L_B.
- **Not rerun:** R1, V1–V3 replicates, J = 40, and the oracle-weights estimator.

**Reproduced.**
- **The positive control.**
  - **The tilt's L_B.** The analytic value re-derives as (0.4/0.6) max_g |1 + ε d/dg[g(1 − g)/(2(1 + εg))]| = 1.1223, against the declared 1.1223. It is about twice the numerical maximum slope on B (0.529), so it is a valid bound. θ₁ = 0.64645.
  - **PC0.** No rejection by either rule at any N, and coverage is 100%.
  - **PC1.** The common radius rejects 0%, 0% and 100% at 10⁴, 10⁵ and 10⁶. The per-cell rule rejects 0%, **100%** and 100%. Coverage is 100%. This is the published pattern exactly. In this design the per-cell rule reached full rejection one grid step earlier (10⁵ against 10⁶). That is a finite-case observation, not a general tenfold sample saving.
  - **The sum identity** holds within 8×10⁻¹⁴.
- **The price-path basket.**
  - **Targets.** The exact b₁ = (1 − (2Φ(2.5) − 1))/3 = 0.004139776884, as in Deviation 3. My Monte Carlo pseudo-targets give max_i(θ_i − ω_i) = −0.0007, +0.0054, +0.0098 and +0.0187 for V1–V4, matching `oracle.json` to 10⁻⁴.
  - **The fixed-bin bias.** In the infinite-sample limit, b̂ − b is +0.0036/−0.0019/−0.0017 for R0 and +0.0034/−0.0019/−0.0015 for V4. The published replicate biases at N = 10⁶ are +0.0036/−0.0019/−0.0017 and +0.0034/−0.0019/−0.0015. So that bias is exactly the fixed-bin limit, as the report concludes, and not sampling error.
  - **No rejections.** Neither rule rejects R0 or V4 at either N. The median e_N is 0.328 and 0.176 for R0 at 10⁵ and 10⁶ (published 0.328 and 0.176), and 0.395 and 0.218 for V4 (published 0.217 at 10⁶). With the declared diagnostic L_B, these median radii are an order of magnitude above the separations. Across all process cells the archived medians span 0.161–1.0 (math's `checks/d32-results-reading/`).

**One wording correction.** In Results section 1, "b̂ is biased by +0.0016 / −0.0016 at every N" holds for PC0. PC1's bias is +0.0062/−0.0062 in `results.json`, and +0.0062/−0.0062 in my replicates too. The text should name the cell.

**The Deviations are honest.**
- **Deviation 1** was prompted by a design-stage oracle computation (10⁸ Q draws, with no test statistic). That computation showed V1 to be non-separated. The registered cells were kept and labelled, and V3 and V4 were added following claim 044's own construction, which tilts a true-martingale name. The per-cell 2c_M is a correction to the registered text, matching my claim-044 review.
- **Deviations 2–4** came before any test replicate, by commit order. They adopted math's evaluator, labelled the price-basket size and coverage rows diagnostic because their Monte Carlo L_B is not a supplied bound, used the exact AX-54 targets, corrected Σθ_i = p_I under the tilts, and retained failed records.
- **The smoke tier** (17:22) came after Deviation 4, and `run.py` is unchanged from Deviation 4 through the smoke tier to the results (17:36).

**The readings are fair.**
- **The positive control** gives finite-case observations, at fixed B and J, consistent with claim 044.
  - **No null rejection, and full-target coverage,** in these runs. That does not verify size or coverage beyond them: full-target coverage is weaker than the compact target the proof uses.
  - **Detection of the terminal tilt.** Rejection rates reached 100% at the largest N for both rules. This is detection in finite cases, not a demonstration of asymptotic power, since fixed B and J do not instantiate claim 044's expanding-range, shrinking-mesh scheme.
- **On the realistic basket:**
  - **The recovery bias.** The strict-local-martingale contribution (0.0041) is the same size as the fixed-bin bias.
  - **No rejection.** Neither rule rejected in any process cell. With the declared L_B, a Monte Carlo slope estimate that is not a supplied bound, the median radii exceed the separations (≤ 0.019). The process rows are diagnostic, so these runs do not establish that rejection is impossible or that power is zero under a valid bound.
  - **The rigorous bound.** Only one coarse rigorous bound has been constructed, and it is unusable. Other finite bounds are not ruled out.
- **The source of the fixed-partition bias in the terminal controls.** My own whole-line quadrature (`checks/review/exp046/bias_split.py`) agrees with math's `checks/d32-results-reading/` to 10 digits. The bias in b̂₁ is 0.0015878 for PC0 and 0.0062458 for PC1. Of that, the outside-B fallback to ω contributes 0.0014922 and 0.0062031, about 94% and 99%. Doubling J shrinks only the within-B part, and larger N removes neither part. So growing the estimation range matters. This split is for the terminal controls only and is not computed for the basket.
- **The labels are correct.** The diagnostic and verification labels follow claim 044's premises.

*Scope narrowed 2026-10-08 at math's request (inbox note `2026-10-08-exp046-reading-scope.md`). The verdict and the rerun scope above are unchanged, and the bias split was added from `checks/review/exp046/bias_split.py`.*

Verdict: reproduced
