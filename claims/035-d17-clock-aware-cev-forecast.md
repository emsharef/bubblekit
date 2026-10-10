---
id: "035"
title: "D17: training-selected CEV clock forecasts for exact and rounded prices"
status: formalized
depends_on: ["033", "034", "054", "053"]
axioms_used: [AX-53, AX-55, AX-56, AX-58]
formal: lean/Standalone/D17ClockForecast.lean
direction: D17
---
## Statement

**Conditional on AX-56's CEV kernel facts and the relevant existing null
contract; FDR remains conditional on AX-53.** The mechanism is selecting
a normalized forecast from training, or mixing normalized forecasts,
while leaving the dominating null likelihood unchanged. AX-58
([wasserman2019universal]) already permits this. The application here
supplies a CEV forecast with declared variance-clock increments in
place of an always-calendar-time forecast. Normalization does not
require the actual alternative law to equal the forecast.

Fix a nonempty training block of k increments and an evaluation block
of n≥1 increments. Declare before observation an ordered nonempty
finite forecast catalogue Ξ. A member ξ comprises p_ξ>1, κ_ξ>0 and
a full vector of positive deterministic increments
v_(ξ,1),...,v_(ξ,k+n). These are *forecast* clock increments and need
not be members of the null clock catalogue. The null family remains
exactly the one in claim 033 or 034, as specified below. Forecast
choice cannot remove null clocks or change their coverage premises.

Let K_(p,κ)(v,x,y) be claim 054/AX-56's mixed CEV kernel at elapsed
time v, relative to μ_CEV. For p>1 and x>0 its atom at y=0 is zero,
its positive density f_p is strictly positive and finite, and its
total mass is one. At x=0 use the trapped extension. Substitution of
positive v into this existing kernel defines a forecast; no stochastic
time-change theorem or new diffusion law is claimed.

1. **Exact-price forecast.** In claim 033's observation domain, use
   the known start y_0>0 and exact training values y_1,...,y_k. Define

       L_ξ^ex(U)=Π_(j=1)^k K_(pξ,κξ)(v_(ξ,j),y_(j−1),y_j),
       ξ_hat^ex(U)=first maximizer of L_ξ^ex(U) over Ξ,
       q_CEV^ex(V|U)=Π_(j=k+1)^(k+n)
                     K_(pξ,κξ)(v_(ξ,j),y_(j−1),y_j),   (1)

   with ξ=ξ_hat^ex(U). All-zero likelihood ties, including impossible
   training histories, use the same first-index rule. Then q_CEV^ex
   is a finite nonnegative measurable density normalized for every U.
   Its clock and parameters are chosen using training alone.

   Let q_base^ex be claim 033's original Ĝ and keep its denominator
   D_i^clock unchanged, including the finite CEV null maximum. For a
   measurable training-only weight 0<λ(U)<1 set

       q_mix^ex=λ q_base^ex+(1−λ)q_CEV^ex.              (2)

   The scores q_CEV^ex/D_i^clock and q_mix^ex/D_i^clock, using zero
   if their numerator is zero or the denominator is infinite, are
   finite on every nonnegative array. Under claim 033's actual null
   contract they have conditional and unconditional mean at most one.

2. **Rounded-label forecast.** In claim 034's domain keep its fixed
   monetary cells C_z, tick δ_tick and entire observed training prefix
   z_0,...,z_k. Use the positive representative

       r_δ(z)=δ_tick z for z≥1,   r_δ(0)=δ_tick/4,
       P_(ξ,j)(z,z')=∫_(C_z') K_(pξ,κξ)(v_(ξ,j),r_δ(z),y) μ_CEV(dy).
                                                               (3)

   For every ξ,j,z these row masses are positive, at most one, and
   sum to one over z'≥0. Select the first maximizer of
   L_ξ^cell(U)=Π_(j=1)^k P_(ξ,j)(z_(j−1),z_j), and define

       q_CEV^cell(Z|U)=Π_(j=k+1)^(k+n) P_(ξ_hat,j)(z_(j−1),z_j). (4)

   This is a normalized, positive measurable forecast on all future
   label vectors for every training prefix. It is a *forecast on
   labels*, not the joint likelihood of a continuously evolving latent
   CEV price conditional on its rounded history. Only the forecast
   restarts at a representative. The null denominator continues to
   cover the actual latent endpoint posterior throughout each cell.

   For any baseline normalized q_base^cell, including claim 034's
   Gaussian example, use the training-only blend (2) with superscript
   cell and keep D_clock^{h,ℓ} from 034 unchanged. Both its pure CEV
   and blended scores satisfy every moment, strict-size, lower-score
   and original-m panel conclusion of 034, with its finite measurable
   evaluation-selected refinement levels and its **compact Gaussian
   null** only. Neither CEV nulls nor unrestricted parameters are added
   to 034 by changing its numerator.

3. **Mixture protection, boundary and interpretation.** In either
   observation domain the blended score equals

       E_mix=λ E_base+(1−λ)E_CEV ≥ λ E_base.            (5)

   On any path with E_base>0, its loss in log score relative to that
   baseline with the same denominator is at most −log λ. This is a
   pointwise protection, not a power gain or a guarantee to preserve
   baseline rejections at the same level. There is no general ordering
   between the pure CEV and baseline scores. The weight or selected
   ξ cannot be chosen to maximize the completed evaluation score.

   Under the respective null contracts, strict per-name testing at
   1/α has size ≤α, and claim 053's base e-BH under AX-53 has FDR
   ≤q_FDR|N₀|/m under arbitrary dependence, with original-m zero masks.
   Exact-price training absorption followed by zeros gives both
   scores one. At first exact evaluation absorption, the pure p>1
   forecast score is zero and the blended score is λ E_base≤1.
   With one exact evaluation increment neither can flag: positive
   paths have the infinite profile denominator, and boundary cases
   are at most one. On an all-zero rounded suffix from a zero quote,
   the denominator is one and both label scores are at most one.

## Proof

**Exact normalization and support.** Apply the existing AX-56 kernel
normalization at each strictly positive v_(ξ,j), including its trapped
extension. Successive nonnegative integration over the evaluation
coordinates gives total mass one for each fixed ξ from every last
training price. The products are finite and jointly measurable by
claim 054's kernel facts. Finite first-index maximization is measurable,
including its all-zero tie case. Partitioning training space by the
selected index proves the normalization and measurability of (1) for
every training value. A convex combination with training-only weights
preserves these properties.

For score finiteness, support must be checked because the numerator
has changed. If the last training price is positive, q_CEV^ex can be
positive only when all evaluation prices are positive: p>1 has no
zero atom. On that set every fixed Gaussian null density in 033 is
positive, so D_i^clock>0. If the last training price is zero, the new
forecast is positive only on the all-zero suffix, where the denominator
is one. For the baseline numerator the retained support fact is already
proved in 033. Thus either numerator being positive forces a positive
denominator. At infinity the scores are defined as zero, otherwise
ordinary division is finite. Measurability follows from the explicit
denominator in 033 and these cases.

The unchanged denominator still dominates every component, hence every
actual conditional mixture, in 033's null contract. The new numerator
is normalized for every U, so AX-58 gives the stated moments. This is
an application of the existing dominated-likelihood result, not a
claim that the actual evaluation law is CEV.

**Label normalization.** The cells form a countable partition of the
nonnegative state space. AX-56 therefore gives Σ_z' P_(ξ,j)(z,z')=1.
Each representative is positive and every monetary cell contains a
nonempty positive interval. Positivity of f_p yields strictly positive
row masses even for z'=0, despite the zero atom being absent. Their
sum one bounds each by one. Measurability on the countable label spaces
is immediate. Summing the product (4) successively over the last label,
then each preceding label, gives one. Although the representative
depends on the preceding evaluation label, each such forecast row
still has mass one; ξ is fixed given training. Finite first maximization
and training-only convex blending preserve normalization.

Claim 034's denominator is positive on every label vector and dominates
the actual rounded conditional mass under its declared null law. Apply
its normalized-forecast result to (4) or the blend. This proves part 2,
including its adaptive computation and lower-score conclusions. No
likelihood evaluated at a representative enters the denominator, and
no assertion about a rounded latent CEV posterior is needed.

**Mixtures and boundaries.** At a finite positive common denominator,
linearity gives (5). At an infinite exact denominator all three scores
are zero, so the same identity holds. At a zero exact denominator all
numerators are zero by the support argument, again giving the identity.
The log bound follows by monotonicity of log wherever E_base>0.
Training-only weights also give the null conditional moment directly
from the two component moments. Finiteness and the null moments verify
AX-53's hypotheses exactly as in claims 033–034 and 053; measurable
nonnegative lower scores preserve these moments.

For exact absorption the kernel products give the stated zero/one
values. Claim 033 gives the corresponding denominator and baseline
values and its single-increment infinite profile. For rounded zeros,
034 gives denominator one and each normalized forecast assigns mass
at most one to the all-zero label path. These prove the boundary claims.

**Why evaluation maximization is excluded.** On a finite sample space
of 21 outcomes let the actual null be uniform, and let 21 normalized
forecasts each concentrate on one outcome. Taking the largest forecast
after observing the outcome gives score 21 at every outcome, hence
size one at α=.05. A fixed uniform mixture instead gives score one
everywhere. Normalization is preserved by the permitted training-only
selection and mixing, not by a post-evaluation pointwise maximum.

## Checks

`checks/035/check.py` checks `checks/d17-clock-forecast/forecast.py`.
The fixed diagnostics verify CEV mass and full
cell partitions with explicit unbounded tails, independent price/radius
quadratures, variance-clock scaling, zero-quote re-emergence,
training-only selection under changed evaluation suffixes, both clock
selection branches and ties, impossible exact training histories,
mixture protection and the exact finite evaluation-max counterexample.
The implementation and fixed paths are diagnostics, not certified
scores, diffusion simulations or power measurements.

## Not shown

- The exact and label forecast normalization, score validity under
  033/034's unchanged null contracts, blend bounds, boundary cases,
  evaluation-maximum counterexample and panel result are formalized
  in `lean/Standalone/D17ClockForecast.lean`, proved by `statement_holds`
  in `lean/Novel/D17ClockForecastProof.lean`. The remarks about no general
  ordering of pure and baseline scores, and the forecast not being the
  latent CEV likelihood, remain interpretive. CEV forecast normalization
  uses AX-56; its Lean instance is vacuous on a base
  without Brownian motion, as disclosed in the ledger. Exact-price
  baseline/kernel support also inherits AX-55/56 through 033/054.
  AX-58 is proved; FDR remains conditional on AX-53's degenerate instance.
- No identification or empirical coverage of a clock, volatility range,
  physical drift, noise model or pricing-null label. The forecast uses
  zero-drift CEV kernels, not an estimated physical CEV drift law. It
  does not expand the observation/null contracts of 033 or 034.
- No assertion that representative label restarts give the true rounded
  CEV likelihood, recover the latent endpoint filter, or handle arbitrary
  observation noise. Such a forecast may be inefficient. Its validity
  follows from normalization under the separate declared null contract.
- No power gain over a Gaussian forecast or calendar-time CEV forecast,
  real-feed validation, frequency preference, or repeated-date guarantee.
  The last claim supplies a possible bubble-shaped forecast, not a
  demonstration that D17 yields a useful intraday detector.
- No outward numerator/denominator certificate. Cell probabilities are
  integrals, not midpoint densities times cell widths; the arbitrary-
  precision quadrature must not be advertised as a lower bound. A
  conservative implementation needs a lower normalized-forecast value
  and an upper null bound with both numerical errors accounted for.

## Prior art

AX-58 already permits arbitrary normalized training-selected forecasts
and composite null upper likelihoods [wasserman2019universal], Section 6.
The CEV kernel and its normalization are the registered, source-audited
AX-56 [makarov2009exact], as used in claim 054. Claim 031 supplies the
representative-label forecasting construction; 033–034 provide the
two-clock nulls. Claim 063 already uses a whole-path independence blend.
The general rules are reused, not presented as new mixture or inference
theorems. The application checks clock substitution in the positive CEV
kernel, exact support on boundary arrays, and label-row normalization
before using those rules. The preceding D17 findings, the reviews of
033/034, the existing kernel implementation and the source-audited
ledger entry were read; no time-change theory is reconstructed.

## Review

Reviewer, 2026-10-07, on branch `math/d17-clock-forecast-inputs` at `266adfb`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/035/` and `checks/d17-clock-forecast/`.
- **Inputs.** AX-53, AX-55, AX-56 and AX-58 are audited, and AX-58 is proved. Claims 033, 034, 053 and 054, the dependencies, are approved. [makarov2009exact] is registered.
- **Script.** My check is committed as `checks/review/035/reproduce.py`, with its rerun command and seed in its header. It runs on 2 worker processes and is not a CI `check.py`.

**Part 1 (the exact-price forecast): correct.**
- **Normalization.** Each fixed ξ is a product of AX-56 kernels at positive elapsed times. Each kernel has mass one from every state, with the trapped extension at zero. Selecting the first maximizer on training only partitions training space, so (1) is normalized for every U, and so is a blend with training-only weight.
- **The new support check is needed and right.** For p > 1 the kernel has no zero atom, so a positive forecast from a positive endpoint forces positive evaluation prices. There claim 033's Gaussian denominator is positive. From a zero endpoint, the forecast lives on the all-zero suffix, where the denominator is one. Hence no x/0, and the infinite-denominator convention gives zero.

**Part 2 (the rounded-label forecast): correct.**
- **The rows.** They are cell masses of a mass-one kernel from a positive representative, so they sum to one. They are positive because f_p > 0 on every positive interval, including C₀.
- **The product.** Summing it over labels from the last backward gives one, even though the representative depends on the previous label.
- **The denominator.** Claim 034's denominator is unchanged, so its validity conclusion transfers. The claim rightly keeps 034's compact Gaussian null only.

**Part 3 (mixtures and boundaries): correct.**
- **The mixture.** (5) is linearity at a common denominator. The log-loss bound −log λ follows where E_base > 0.
- **The boundaries.**
  - First exact evaluation absorption gives zero p > 1 forecast mass.
  - With one evaluation increment, claim 033's denominator is infinite on positive paths.
  - All-zero rounded suffixes have D = 1.
- **The counterexample** in `claims/refuted/d17-evaluation-forecast-maximum.txt` is correct: 21 point forecasts against a uniform null give max score 21 > 20 with certainty.

**Checks** (evidence, not proof).
- **(a) Kernel mass.** The p > 1 kernel at clock increments v ∈ {1/252, 3/365, 1/4} integrates to one to 2×10⁻⁸ over 36 cases.
- **(b) Label rows.** On 24 cent-tick rows (including from label 0 at δ/4 and very peaked p = 2 rows), the cell masses plus the explicit upper tail sum to one to 6×10⁻¹³. The zero-label mass from label 1 at v = 1/4 is 1.6×10⁻²⁶ > 0. Shorter v underflows numerically, which is the claim's own warning about computed quadratures.
- **(c) Power on the weekend design of my claim-033 review.**
  - **The setup.** Weekday closes for two years with calendar gaps. The denominator is claim 033's with clocks {Δ, trading} plus claim 055's calendar CEV null maximum, unchanged. The forecast catalogue is p ∈ {1.25, 1.5, 2} × κ ∈ {0.2, 0.3, 0.45} × {calendar, trading} clock. There are 2,000 paths per truth.
  - **The result.** P(E > 20) = power at α = 0.05; the null row gives mean E instead.

  | Truth | Baseline Ĝ (calendar) | Clock-aware CEV forecast | Blend λ = 1/2 |
  |---|---|---|---|
  | Trading-clock GBM null: mean E | 0.005 | 0.16 | 0.08 |
  | Trading-time CEV p = 1.5, κ = 0.45 | 0.006 | **0.145** | 0.108 |
  | Trading-time CEV p = 2, κ = 0.30 | 0.027 | **0.294** | 0.246 |

  - **Reading.** No null path exceeded 10. The clock-aware forecast recovers much of the power my claim-033 review found lost: 0.55% → 14.5% for p = 1.5. At α = 0.10 it reaches 19.7%, against claim 055's 6.2% on the same design without the trading-clock null.
  - **This is optimistic for the forecast.** The alternative's clock is exactly a catalogue clock, and the design is mine.
- **The author's check.** I ran `checks/035/check.py` afterwards. It passes the CEV mass and partition integrals, clock scaling, zero rows, training-only ties, mixture protection and the counterexample.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **Validity comes entirely from the unchanged null contracts of 033 and 034.** A clock or forecast choice cannot add coverage.
2. **No power claim is made.** My (c) suggests that when the bubble clock matches a declared forecast clock, the remaining loss in claim 033 is in the numerator, not the denominator. Whether real intraday or weekend clocks match is an empirical question.
3. **Not covered:** rounded-latent CEV likelihoods, noise, outward certificates and repeated testing dates, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red re-derived normalization of training-selected CEV clock forecasts and rounded label row products, the positive-support/zero-suffix boundary cases, unchanged 033/034 denominators under AX-58, the blend bound and the evaluation-maximum counterexample; committed review script; scope honest


Reuse claim 054's kernel normalization, positivity and first-selection
lemmas, claim 031's countable-row normalization construction, and the
AX-58 applications in 033–034. The clock substitution supplies positive
elapsed times only. The new exact support check matters because the
numerator differs from 033's original Ĝ. Prove mixture identities by
finite algebra. Do not assume normalization of computed quadratures
or encode a representative forecast as the latent observation law.

Formalizer B, 2026-10-07, in two stages (`formb/d17-clock-aware-cev-forecast`, merged, and `formb/d17-clock-forecast-cells`). **Status: formalized.**
- **Files.** The statement is in `lean/Standalone/D17ClockForecast.lean` (`statement := exact ∧ labels ∧ cells ∧ evalMax ∧ panel`). The proof is `lean/Novel/D17ClockForecastProof.lean` (`statement_holds`), with:
  - `D17ClockForecastExact.lean`: parts 1 and 3 on claim 033's design;
  - `D17ClockForecastLabels.lean`: the row masses (3) and the label forecast (4);
  - `D17ClockForecastCells.lean`: parts 2 and 3 on claim 034's design.

  There is no `sorry`, and the axiom audit is clean.
- **Inputs.** AX-55 and AX-56 supply claim 054's kernel `Kc` on a base carrying a Brownian motion. AX-58 is proved. AX-53 is used for FDR only. Claim 033's and 034's denominators are reused unchanged, and their validity is proved for any normalized numerator: claim 033's `clock_valid` (refactored in stage 1) and claim 034's `validity`.
- **Encoding.** The catalogue Ξ is `Fin r`, ordered by index, with powers, scales and training and evaluation clock increments. `selEx` and `selCell` are first maximizers (`firstMax`) of the training likelihoods, so ties and all-zero likelihoods use the first index. `Pcell` is (3), with claim 031's representative `mrep` and cells.
- **Part 1** (`exact`).
  - (1) and (2) are measurable, nonnegative and of mass one at every training record.
  - The scores use claim 033's `Edrift` convention and denominator. They are measurable and finite. Under claim 033's mixture premise they have conditional and unconditional mean ≤ 1, size ≤ α, and the reciprocal-p bound.
  - The new support check: for p > 1 the forecast is positive only where claim 033's denominator is.
- **Part 2.**
  - `labels`: every row of (3) has positive masses, at most one, summing to one. So (4) and any training-only blend with a normalized baseline are positive normalized forecasts on all evaluation label vectors.
  - `cells`: both label scores satisfy all of claim 034's conclusions under its null contract and compact Gaussian null, with `D_clock^(h,ℓ)` unchanged. These are the domination, finiteness, the moments, strict size and lower scores, at finite evaluation-selected levels h and ℓ.
- **Part 3.**
  - (5), its floor λ E_base ≤ E_mix and the log protection log λ ≤ log(E_mix/E_base), in both domains, the label one at every pair of levels.
  - The exact boundary cases: trapped training with a zero suffix gives one; first evaluation absorption gives E_CEV = 0 and E_mix = λ E_base ≤ 1; with one increment both are at most one.
  - On an all-zero rounded suffix from a zero quote, D_clock = 1 and both label scores are at most one.
  - `evalMax`: maximizing over 21 point-mass forecasts after seeing the outcome gives score 21 everywhere, while their fixed uniform mixture gives 1.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53, with masks at the original m.
- **Not formalized.** The interpretive remarks only: no general ordering of the pure and baseline scores, and the forecast is not the latent CEV likelihood.
