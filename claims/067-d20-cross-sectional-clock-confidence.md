---
id: "067"
title: "D20: cross-sectional clock confidence and safe per-name scores"
status: formalized
depends_on: ["026", "033", "053", "054", "058"]
axioms_used: [AX-53, AX-55, AX-56, AX-58]
formal: lean/Standalone/D20ClockConfidence.lean
direction: D20
---
## Statement

**Conditional on the finite common-clock observation law below.** FDR is
conditional on AX-53; CEV forecast and retained-null kernels inherit
AX-55/56. The mechanism without model nouns is likelihood-confidence
inversion on an auxiliary sample, conditional likelihood domination on
the tested sample, and the bounded failure-event correction. These are
AX-58 ([wasserman2019universal]) and claims 058/026. The contribution is
an explicit cross-sectional construction and its conditioning check,
not a new confidence or multiple-testing theorem.

Fix m tested names, a fixed actual-null subset N₀, and one test date.
For each name i fix n≥1 positive calendar increments Δ, a nonempty
finite clock catalogue 𝒱_i containing Δ, and r_i≥1 reference names
not including i. All clocks have positive increments. Fix 0<δ_i<1
and 1≤c_i<∞ before data. Designs, reference membership and catalogues
are fixed before data; missing records do not reduce m.

A_i is the complete pre-evaluation training information used by name i,
including its own and reference training records and endpoints. W_-i
is the panel of reference evaluation prices on the same n increments.
For the reference calculation their starting prices are positive,
A_i-measurable, and their evaluation space is (0,∞)^(r_i n).
The tested suffix V_i is nonnegative, with the mixed reference measure
μ_CEV^n and the boundary conventions of claims 054/033. All records,
latent variables and parameter maps below are standard Borel/measurable.
Different tested names may share references and training observations.

### Actual null contract

For every i∈N₀, given A_i supply a latent component Z_i of either type:

* **Common-clock Gaussian type.** Z_i specifies a clock v∈𝒱_i,
  finite drifts b_i,b_(i,a), and positive scales w_i,w_(i,a),
  a=1,…,r_i. Conditional on (A_i,Z_i), the reference suffixes are
  mutually independent with densities g_(v,b_(i,a),w_(i,a)) of
  claim 033. The tested suffix is independent of the whole W_-i
  conditional on (A_i,Z_i), with density g_(v,b_i,w_i).
  Equivalently, its positive-endpoint returns are independent
  Normal(b_iΔ_j−w_i v_j/2,w_i v_j), and the references have the same
  form with their own constant drift and scale. A zero tested endpoint
  has the trapped extension. The joint conditional distribution of
  Z_i given A_i is otherwise arbitrary and need not be estimated.
* **Retained CEV type.** Conditional on (A_i,Z_i,W_-i), the tested
  suffix has one of claim 054's retained finite null densities, at its
  actual training endpoint. Reference observations may have any law
  on this component. Mixtures of retained components are obtained by
  mixing Z_i; the component choice is measurable.

Both are premises about the actual conditional laws after *all* the
stated conditioning. They are not consequences of marginal Gaussianity
or leave-one-out fitting. The first type permits random common clock
shapes but excludes residual shared return shocks after conditioning
on Z_i. Constant multiplicative clock differences can be absorbed into
the name scales. Name-specific changes of relative clock shape, clocks
outside 𝒱_i, and arbitrary alternative reference names are not covered.
No restriction is imposed on a tested alternative except the inputs
needed to compute a finite score. If it serves as a reference for an
actual null, that null's reference-law premise still applies.

### Auxiliary likelihood and clock set

Declare a finite positive reference forecast q_i^ref(A_i,W_-i),
normalized in W_-i against positive-price Lebesgue measure for every
A_i. It must be constructed without any reference evaluation data or
the tested evaluation suffix. One explicit choice is a finite mixture
of products of claim 033's Gaussian densities, with clocks, finite
drifts, positive scales and nonnegative weights summing to one chosen
from A_i alone. It is a joint forecast, not a product of scores asserted
valid under unspecified dependence.

On positive reference arrays define

    D_(i,v)^ref = ∏_(a=1)^r_i D_(a,v)(W_a | A_i),
    T_(i,v)^ref = q_i^ref/D_(i,v)^ref, with q/∞ := 0,
    C_i(W_-i,A_i) = {Δ} ∪ {v∈𝒱_i : T_(i,v)^ref ≤ 1/δ_i}.    (1)

Each D_(a,v) is exactly claim 033's supremum over that reference name's
constant b∈ℝ,w>0, including its price Jacobian. It is strictly positive
and possibly infinite. If reference inputs are not positive finite
arrays, set C_i=𝒱_i. Thus C_i is always nonempty; no record is removed.
Retaining equality in (1) makes exclusion the strict event T>1/δ_i.
The calendar clock is retained regardless of its auxiliary evidence.

The set is computed from contemporaneous peers; it is not a point
estimate treated as known, and it does not assert conditional coverage
given the observed peer panel.

### Tested score

For each (A_i,W_-i), select a finite nonnegative normalized suffix
forecast q_i(A_i,W_-i,·) without using V_i. A selection from claim 054's
finite CEV candidate densities by a measurable first-maximizer rule is
one choice; peer evaluation data may inform that choice because they
are in the conditioning record. Keep the maximum G_(i,0) of the
retained finite CEV nulls, and require the existing support condition
q_i>0 ⇒ G_(i,0)>0 on every nonnegative array. The chosen catalogue and
selection must satisfy this, as in claim 054. Define

    D_i^sel = max(G_(i,0), max_(v∈C_i) D_(i,v)),
    E_i^sel = q_i/D_i^sel if q_i>0 and 0<D_i^sel<∞,
              0 otherwise,
    E_i^safe = min(E_i^sel,c_i)/[1+(c_i−1)δ_i].               (2)

Use claim 033's trapped/zero extensions for D_(i,v). On invalid tested
records output zero. Forecast definitions at valid but impossible
training records retain claim 054's normalized completion. No division
of the observed returns or reconstruction of a new price path is used.

1. **Clock coverage.** On every Gaussian component, almost surely in
   (A_i,Z_i),

       P(v∉C_i | A_i,Z_i) ≤ δ_i.                            (3)

   This probability is over the reference suffixes. There is no union
   penalty in |𝒱_i|: (3) concerns the one true component clock. If
   δ_i is decreased, C_i can only grow. Clocks proportional by a
   positive constant have identical D^ref and identical retention
   tests, apart from the unconditional retention of Δ.

2. **Safe conditional moments and original-family FDR.** The scores
   in (2) are measurable and finite on every declared input. For each
   actual null,

       E[E_i^safe | A_i] ≤ 1,
       P(E_i^sel>1/α_i | A_i)
           ≤ α_i+(1−α_i)δ_i,        0<α_i<1.               (4)

   The same bounds hold unconditionally. If δ_i<α_i, the raw-score
   threshold (1−δ_i)/(α_i−δ_i) has size at most α_i. Base e-BH on
   all m safe scores gives FDR≤q_FDR|N₀|/m under AX-53, with arbitrary
   dependence between the resulting scores. Measurable zero masks and
   finite certified lower implementations preserve this, with m
   unchanged. No FDR guarantee conditional on separate observed peer
   panels or a retained set is claimed.

   Conditional on (A_i,Z_i,W_-i) with the Gaussian clock retained, the
   raw target moment is at most one. After an incorrect clock exclusion
   there is no such raw bound. In particular (4) is not a claim of
   conditional calibration given (A_i,W_-i).

3. **Cost, comparisons and boundaries.** With the same q_i and G_(i,0),
   let E_i^all be the score retaining all 𝒱_i. Pointwise,

       E_i^sel ≥ E_i^all,
       E_i^safe ≥ min(E_i^all,c_i)/[1+(c_i−1)δ_i].          (5)

   This is not a guarantee that the safe score exceeds the uncorrected
   full-catalogue score. The safe score's ceiling is
   c_i/[1+(c_i−1)δ_i]. Strict rejection at 1/α_i is possible only if
   δ_i<α_i and c_i>(1−δ_i)/(α_i−δ_i). The same ceiling applies to
   an e-BH rank threshold with α_i=q_FDR k/m. If n=1, every reference
   profile is infinite on positive arrays and no clock is excluded;
   every positive tested path also has infinite Gaussian profile and
   score zero. With a claim-054 CEV-candidate forecast selection, zero
   endpoints and first absorption retain the 054/033 raw scores ≤1,
   hence cannot yield a safe score above one. The first-absorption
   assertion is not made for an arbitrary normalized forecast.

   Profile evaluation costs O(r_i n |𝒱_i|) operations for the reference
   panel and O(n|C_i|) for the tested name, plus forecast construction
   and evaluation. This uses scalar profiles, not an r_i×r_i covariance
   optimization. All possible two-state switch paths over n increments
   can require 2^n catalogue entries; no polynomial-cost coverage of
   unrestricted switches is claimed. A smaller catalogue must be a
   correct restriction on the actual common clock, not an uncorrected
   grid approximation.

## Proof

**Likelihood-confidence hypotheses.** Fix (A_i,Z_i) on a Gaussian
component. Its reference density is the product of the specified
Gaussian price densities. For each fixed v, positivity and measurability
of D_(a,v), including the infinite singular case, are claim 033. Products
of finitely many strictly positive extended values are defined and
measurable; independent parameter coordinates also make this product
the joint supremum, though only domination is needed. The actual
reference density at the component's true v is bounded pointwise by
D_(i,v)^ref. q_i^ref is normalized at this fixed A_i and remains the
same function after fixing Z_i. Apply AX-58 to this reference experiment.
It gives conditional mean T_(i,v)^ref≤1; Markov and (1) give (3).
This is claim 058's likelihood-confidence mechanism with the finite
clock as the index and nuisance drifts/scales profiled. No estimated
posterior or simultaneous rejection bound is used. Scale invariance
and the monotonicity in δ_i follow from claim 033 and (1).

**Target hypotheses under the augmented conditioning.** On a Gaussian
component, conditional independence leaves the target law equal to
g_(v,b_i,w_i) even after W_-i is observed. If v∈C_i, (2) dominates
that law pointwise. At each fixed (A_i,Z_i,W_-i), q_i is normalized;
its dependence on peers does not involve the remaining integration
variable V_i. AX-58 therefore gives the covered-record raw moment
and strict size at most α_i. On a retained CEV component, G_(i,0)
dominates the actual target component for every peer observation, so
the same conclusion holds without a clock event or any reference-law
premise on that component. The support condition, finite q_i, and the
zero-at-infinity convention give finite raw scores on alternatives
as well. Finite set membership and finite maxima give measurability.

**Failure-event correction.** Keep a Gaussian component fixed. Its
failure event {v∉C_i} is measurable in W_-i and has conditional
probability p≤δ_i by (3). On its complement, the conditional expected
clipped target score is ≤1. On it, the score is ≤c_i. Thus the exact
covered/failed-record calculation of claims 026/058 gives an upper
mean (1−p)+c_i p≤1+(c_i−1)δ_i. Similarly the raw rejection probability
is at most α_i(1−p)+p≤α_i+(1−α_i)δ_i. This checks the required
conditioning rather than assuming that the *latent* coverage event is
measurable in (A_i,W_-i). Integrate over Z_i given A_i. The retained
CEV components have raw moment ≤1 everywhere and obey the same bounds.
Division proves (4). Threshold rearrangement is the existing 058
correction. Integrating over A_i and applying AX-53 gives the stated
FDR bound. It does not require the A_i or reference sets to be disjoint.

**Comparisons and boundaries.** C_i⊆𝒱_i and contains Δ, so the selected
denominator is no larger than the full one and still contains every
retained CEV null. Taking ratios, with the identical zero/infinity
conventions and support condition, proves (5); monotonicity of min(·,c_i)
preserves it. Solving the ceiling inequality gives the necessary cap
condition. The n=1 singularity is exactly claim 033's. For its original
CEV-candidate forecast choices, the trapped/absorption comparison is
unchanged because G_(i,0) is retained and the Gaussian terms have the
same zero/trapped extensions. Its O(n) profile per name and clock gives
the displayed cost.

**Nonzero actual model.** Take constant training records with positive
endpoints, two predeclared positive clocks including Δ, and an
independent Bernoulli selection of their common shape. Conditional on
that shape draw independent Gaussian increments with positive variance
for all reference and tested names, with any fixed finite drifts and
positive constant scales. Exponentiate cumulative returns. This
satisfies the Gaussian contract and has genuinely random, positive
prices for each clock. It may be built with one shared designated
reference pool for several tested names. This finite observation model
does not construct a pricing measure, justify a market reference pool,
or model experiment 025's shared return shock.

## Checks

`checks/067/clock.py` is an arbitrary-precision diagnostic implementation
of the reference profile products, Gaussian-mixture reference forecast,
clock selection and positive-path safe score. `checks/067/check.py`
checks original-density domination at fixed parameter values, Gaussian
forecast normalization by quadrature, nontrivial clock exclusions,
nested confidence sets, scale invariance, the one-increment boundary,
and selected/full denominator comparisons. A finite exact-rational
analogue separately checks coverage and the cap correction after a
latent clock mixture, and exhibits a raw moment above one despite valid
auxiliary coverage. It is a conditioning diagnostic, not a Gaussian
counterexample or a simulation of size/power. No Monte Carlo, experiment
or empirical estimate is introduced.

## Not shown

- No shared return shocks conditional on the clock, arbitrary correlated
  reference innovations, leverage, stochastic-volatility conditional
  Gaussianity, name-specific clock switches, jumps or contamination
  guarantee. The reference product is not valid merely because each
  reference marginal has the right Gaussian law. A full covariance
  relaxation would be a different test and would inherit claim 062's
  cost. Unknown loadings or alternative reference names are not repaired
  by excluding only the tested name.
- No finite-data identification of a continuous arbitrary clock, a
  correct finite catalogue learned from the same evaluation panel, or
  cost-free plug-in estimator. The catalogue is a substantive model
  restriction. The peers estimate a confidence *set* within it; clipping
  pays for mistaken exclusions. Claims about conditional coverage after
  observing that set would be stronger and are not proved.
- No useful power, improvement over v1/e-BH, or repair of experiment
  025's name-specific regime failure. Small per-rank e-BH thresholds
  require correspondingly small δ_i, making exclusion harder. Many
  profiled reference parameters may also make the clock set large.
  This first D20 claim does not meet the practical comparison goal.
- No rounding/noise likelihood, numerical upper-bound certificate,
  continuous-time time-change theorem, bubble classification of an
  adjusted price series, or repeated-date guarantee. Actual pricing
  nulls must separately satisfy one of the stated physical-law types.
- The auxiliary clock selection and latent-event application are
  formalized in `lean/Standalone/D20ClockConfidence.lean`, proved by
  `statement_holds` in `lean/Novel/D20ClockConfidenceProof.lean`.
  The operation counts, the 2^n catalogue-size remark and output zero
  on invalid tested records remain commentary; formal tested records
  are nonnegative arrays. The formal nonzero model uses the calendar
  clock only, rather than the proof's random choice between two clocks.
  AX-58 is proved; AX-55/56's current Lean instances are vacuous and
  AX-53's is degenerate. Diagnostic precision does not certify set membership:
  falsely excluding a clock due to numerical error can break (3).
  A certified implementation must use a lower reference forecast and
  upper reference profile products for exclusions, and a lower target
  forecast and upper selected target denominator for reported scores,
  with certified comparisons or conservative retention at uncertainty.

## Prior art

Read the D20 input/literature findings, claims 033, 058, 026, 053/054,
the registered text of [wasserman2019universal] and its AX-58 entry,
and the disjoint-window and evaluation-selection refutations. Its
Section 6 already supplies conditional-likelihood inference, and 058
already supplies likelihood-confidence inversion and the cap penalty.
The introductory cross-fitting discussion in [chernozhukov2017double]
uses orthogonal moments; none is asserted here and none of that theory
is imported. The existing 033 profile and Mathlib Gaussian primitives
supply the computational route. There is no new stochastic-analysis
source or upstream ledger input. What is checked here is the particular
reference product, random retained clocks, latent conditional-independence
contract, retained CEV components, and safe original-m discovery list.

## Review

Reviewer, 2026-10-07, on branch `mathb/d20-clock-confidence` at `5990847`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/067/`.
- **Inputs.** AX-53, AX-55, AX-56 and AX-58 are audited, and AX-58 is proved. Claims 026, 033, 053, 054 and 058, the dependencies, are formalized. [chernozhukov2017double] is registered.
- **Script.** My check is committed as `checks/review/067/reproduce.py`, with its rerun command and seed in its header. It runs on 2 worker processes and is not a CI `check.py`.

**Part 1 (clock coverage (3)): correct.**
- **Domination.** On a Gaussian component the references are independent given (A, Z), so the true reference density is a product of claim-033 densities at the true clock. It is dominated by D^ref_v, the product of the per-name suprema.
- **The confidence step.** q^ref is A-measurable and normalized, so AX-58 gives E[T_v | A, Z] ≤ 1, and Markov gives P(T_v > 1/δ) ≤ δ. The index is the single true clock, so no union over 𝒱 is paid.
- **Monotonicity and scale.** Monotonicity in δ is immediate, and scale invariance comes from claim 033.

**Part 2 (the safe score (4)): correct.** Fix a Gaussian component and the reference panel W.
- **The covered event.** The target is independent of W given (A, Z). The selected denominator contains the true clock, and q is normalized given (A, W). So the raw conditional mean is at most one, and P(E > 1/α | A, Z, W) ≤ α.
- **The failure event.** It is measurable in W and has probability p ≤ δ, and there the clipped score is at most c.
- **The bounds.** Hence E[min(E, c) | A, Z] ≤ (1 − p) + cp ≤ 1 + (c − 1)δ, and P(E > 1/α | A, Z) ≤ α(1 − p) + p ≤ α + (1 − α)δ.
- **The raw threshold.** For t = (1 − δ)/(α − δ), the bound (1 − p)/t + p increases in p and equals α at p = δ.
- **CEV components and FDR.** Retained CEV components are dominated by G₀ whatever the peers. Integrating over Z and A and applying AX-53 gives the original-m FDR bound.

**Part 3 (comparisons, ceiling and boundaries): correct.**
- **The ordering.** C ⊆ 𝒱 contains Δ, so (5) holds.
- **The ceiling.** c/(1 + (c − 1)δ) > 1/α iff c(α − δ) > 1 − δ.
- **The boundaries.** At n = 1 every profile is infinite (claim 033), so nothing is excluded and every positive tested path scores zero.

**Checks** (evidence, not proof).
- **The design.** The weekend design of my claim-033 and claim-035 reviews, with the clock catalogue {calendar, w1, w2, w6}. Here w_ω gives a weekend gap ω trading days of variance, and calendar time is proportional to w3. The true common clock is w1 (trading time).
  - **The references.** GBM names on that clock with their own drift and scale.
  - **q^ref.** An equal-weight mixture over clocks of Gaussian products, at each reference's training variance.
  - **The tested name.** It uses claim 035's clock-aware CEV forecast and claim 055's calendar CEV nulls.
- **(a) Coverage.** With r = 2 references and δ = 0.2, over 2,000 panels: the true clock is excluded 0.05% of the time (≤ 0.2), mean T at the true clock is 0.043 (≤ 1), and mean |C| is 2.27.
- **(b) Power and safety** with r = 20, δ = 0.01, c = 100, α = 0.05 and 2,000 panels per truth. The peers always reduce C to {calendar, w1}.

  | Tested truth | E_all > 20 | raw E_sel > 20 | raw E_sel > 24.75 | E_safe > 20 |
  |---|---|---|---|---|
  | GBM null on the true clock | 0 | 0 | 0 | 0 (mean E_safe 0.078) |
  | CEV p = 1.5, κ = 0.45, trading time | 0.149 | 0.152 | 0.144 | **0.123** |

  - **Reading.** In this design the excluded clocks hardly constrained the tested CEV path anyway, so selection gains 0.3 points, while the safe correction costs about 3. **The safe score is lower than the uncorrected full-catalogue score.** This matches the claim's own "no useful power" disclosure. A gain needs wrong clocks that would otherwise absorb bubble evidence.
- **The author's check.** I ran `checks/067/check.py` afterwards. It passes profile domination and normalization, nontrivial selection, nested sets and the boundaries. Its finite analogue shows a raw mean of 1.89 despite valid coverage, so the cap correction is necessary.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The contract is strong.** References must be conditionally independent Gaussians on the *same* clock as the tested null, with no residual common shock. That is exactly what a market factor would violate, and it does not address experiment 025's name-specific switches. Both are stated.
2. **The catalogue is a model restriction.** Peers choose a confidence set within it and do not learn a clock.
3. **The practical value is not shown,** as my (b) illustrates.

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red re-derived the clock confidence set via AX-58 and Markov without a union, the safe capped score on covered and failure events, the raw-threshold and ceiling conditions, CEV domination and original-m FDR; committed review script; strong contract and no-gain result stated


Reuse claim 033's Gaussian profile and scaling, AX-58, claim 054's
support conventions and claim 026/058's bounded failure-event algebra.
Use a finite clock type and a finite reference product. The new proof
obligations are its conditional-law domination, measurable retention,
and the two-stage conditioning on (A_i,Z_i,W_-i) before averaging over
the latent clock. Do not replace conditional independence by a marginal
law or encode the coverage inequality as an unproved assumption. The
fixed-training positive Gaussian construction above supplies a nonzero
observation model; no stochastic calculus or new pricing theorem is needed.

Formalizer B, 2026-10-07, on `formb/d20-cross-sectional-clock-confidence`. **Status: formalized.**
- **Files.** The statement is in `lean/Standalone/D20ClockConfidence.lean` (`statement := sets ∧ scores ∧ model ∧ panel`). The proof is `lean/Novel/D20ClockConfidenceProof.lean` (`statement_holds`), with:
  - `D20ClockConfidenceSet.lean`: the clock set (1) and measurable retention;
  - `D20ClockConfidenceCover.lean`: (3);
  - `D20ClockConfidenceStage.lean`: the two-stage conditioning;
  - `D20ClockConfidenceScore.lean`: the safe-score algebra;
  - `D20ClockConfidenceModel.lean`: the nonzero model.

  There is no `sorry`, and the axiom audit is clean.
- **Inputs.** As in claim 033. AX-55 and AX-56 supply claim 054's kernels on a base carrying a Brownian motion. AX-58 is proved and applied through its pointwise step. AX-53 is used for FDR only. Claim 033's profile `Dv` (its supremum identity and scaling) and its boundary cases, claim 055's normalization and claim 054's design are reused. Nothing new is cited.
- **Encoding.** One tested name on claim 033's design (claim 054's name, retained CEV nulls, `Edrift` convention), with r ≥ 1 references.
  - A = (U, ξ): the tested training record and any other training information ξ ∈ 𝒳. The references' starts `sref(A)` are positive and A-measurable.
  - `Dref` is ∏_a D_(a,v)(W_a), `Tref` is q^ref/D^ref with q/∞ = 0, and `Csel` is (1), equal to 𝒱 off positive reference inputs.
  - q^ref is any measurable nonnegative function of (A, W) with mass at most one over positive reference arrays, on which μ_CEV is Lebesgue measure. The tested forecast q(A, W, ·) is any measurable nonnegative forecast of mass one, positive only where G₀ > 0.
  - D^sel is claim 033's `Dclock` over C: max(G₀, D_G, max_(v ∈ C) D_v). This equals (2)'s max(G₀, max_(v ∈ C) D_v), because D_G = D_Δ and Δ ∈ C. E^sel uses claim 054's convention, which agrees with (2) under the support condition. E^safe = min(E^sel, c)/(1 + (c − 1)δ).
  - **The contract.** The latent Z is a retained CEV null, or a clock v ∈ 𝒱 with tested (b, w) and reference (b_a, w_a). Two premises encode it.
    - The tested suffix's conditional law given ((A, Z), W) is the component's density: the retained null's at the training endpoint, or g_(v,b,w). So on Gaussian components it is independent of W given (A, Z).
    - For a Gaussian component, the references' conditional law given (A, Z) has the product density ∏_a g_(v,b_a,w_a)(W_a), i.e. they are mutually independent with those densities. Nothing is imposed on the references for CEV components.

    The law of Z given A is arbitrary and is never estimated.
- **Part 1.**
  - Δ ∈ C ⊆ 𝒱, and C grows as δ decreases. Proportional clocks have identical D^ref and T^ref (claim 033's scaling).
  - (3), for a.e. (A, Z) on each Gaussian component. Each reference density is at most its profile, which is positive on positive arrays. So T_v · density ≤ q^ref, the mean of T_v is ≤ 1, and Markov's inequality applies. There is no union over 𝒱.
- **Part 2.**
  - Measurability: retention of each fixed clock is a measurable event in (A, W). The scores are finite.
  - The raw moment given ((A, Z), W) is ≤ 1 when the Gaussian clock is retained (or the component is a CEV null).
  - (4) given A almost surely and unconditionally: E[E^safe] ≤ 1 and P(E^sel > 1/α) ≤ α + (1 − α)δ.
  - The raw threshold (1 − δ)/(α − δ) has size ≤ α when δ < α. Lower measurable scores keep the mean.
  - The proof disintegrates over ((A, Z), W) and then (A, Z) (`lintegral_two_stage`, `cond_bound`). On the covered event the clipped mean is ≤ 1 and the rejection probability ≤ α; on the failure event (probability ≤ δ) they are ≤ c and ≤ 1. The latent component is then integrated out.
- **Part 3.**
  - (5): E^sel ≥ E^all and the safe comparison; the ceiling c/(1 + (c − 1)δ); strict rejection at 1/α (in particular at any e-BH rank threshold) needs δ < α and c > (1 − δ)/(α − δ).
  - n = 1: on positive reference inputs no clock is excluded, and positive tested paths score zero.
  - With claim 054's CEV-candidate forecast, a zero endpoint with zero suffix and first absorption keep raw scores ≤ 1 (claim 033's boundary cases with C as the catalogue), so the safe score is ≤ 1.
- **`model`.** The proof's nonzero model, so the contract is not vacuous. Reference and tested prices are positive Gaussian on the calendar clock, with any finite drifts and positive scales, a fixed training record with a positive endpoint, and positive reference starts. They satisfy both premises, with all prices positive almost surely. The model uses the calendar clock only, rather than the proof's random choice between two clocks.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53 with masks at the original m, applied to the safe scores, and e-BH never selects a score ≤ 1.
- **Not formalized.** These are commentary only:
  - the operation counts;
  - the remark that all two-state switch paths may need 2^n catalogue entries;
  - output zero on invalid tested records (the formal records are always nonnegative arrays).
