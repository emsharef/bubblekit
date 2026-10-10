---
id: "034"
title: "D17: rounded-price calibration over compact calendar-drift and variance-clock families"
status: formalized
depends_on: ["030", "031", "033", "053"]
axioms_used: [AX-53, AX-58]
formal: lean/Standalone/D17ClockCells.lean
direction: D17
---
## Statement

**Conditional on the declared rounding map, parameter coverage and actual
conditional Gaussian law below; FDR is conditional on AX-53.** The
mechanism is a finite partition bound for a conditional likelihood,
followed by AX-58 ([wasserman2019universal]). Claims 030–031 already
supply that recursion and inference step. The new application bounds
its transition terms uniformly over continuous parameter boxes while
retaining claim 033's separate calendar and variance clocks. This is
not a discretized latent model or an exact rounded likelihood profile.

Fix a finite panel of m names and its pricing-null subset N₀, with
arbitrary dependence across names. For each name fix a finite training
prefix U of monetary labels and n≥1 evaluation increments with
calendar durations Δ_j>0. Observe latent nonnegative prices only
through claim 031's quantizer Q_δ, at a declared tick δ_tick>0:

    C_0=[0,δ_tick/2),
    C_z=[δ_tick(z−1/2),δ_tick(z+1/2)), z≥1.

Let z_0 be the last training label and Z=(z_1,...,z_n) the future labels.
Before observing data, declare a finite nonempty set 𝒱 of positive
variance-increment vectors v and the closed rectangle

    ℬ=[b_-,b_+]×[w_-,w_+],
    −∞<b_-≤b_+<∞,   0<w_-≤w_+<∞,   w=κ².             (1)

At each actual null, supply an actual conditional distribution of
(X_0,v,b,w) given the **whole rounded training prefix** U, supported
on C_(z_0)×𝒱×ℬ. Given U,X_0,v,b,w, if X_0>0, the future log returns
are independent Normal(bΔ_j−wv_j/2,wv_j). If X_0=0 the future latent
path stays zero. Observed future labels are exactly Q_δ applied to
that path. The posterior may otherwise be arbitrary. No law restriction
is imposed on other names. Pricing-null membership and these coverage
premises are supplied, not inferred from a fit.

**Uniform transition bound.** For a parameter subbox B⊆ℬ with
endpoints (b_L,b_H,w_L,w_H), source S=[a,d_S), target T=[c,d_T),
0≤a<d_S<∞, 0≤c<d_T<∞, and one pair Δ,v>0, define

    M_-=log a+b_LΔ−w_Hv/2,   M_+=log d_S+b_HΔ−w_Lv/2,
    s_-=sqrt(w_Lv),         s_+=sqrt(w_Hv),             (2)

where M_-=-∞ if a=0. The bound W_clock(B;S,T;Δ,v) is:

- If a=c=0, one.
- If c=0<a, let t=log d_T−M_-; use Φ(t/s_-) when t≥0 and
  Φ(t/s_+) when t<0.
- If c>0, write L=log c, R=log d_T and
  m*=clip_[M_-,M_+]((L+R)/2), using min(M_+,(L+R)/2) at M_-=-∞.
  If L≤m*≤R, use s*=s_-. Otherwise reflect the two residual endpoints
  L−m*, R−m* if needed to obtain 0<ℓ<r and set

      s*=clip_[s_-,s_+] sqrt((r²−ℓ²)/(2 log(r/ℓ))).     (3)

  In both subcases set W_clock=Φ((R−m*)/s*)−Φ((L−m*)/s*).

1. **Transition domination.** W_clock is in (0,1] and bounds the
   actual one-step target probability from every x∈S and every
   (b,w)∈B, including the trapped state. On positive source states
   it maximizes over the *independent containing mean/scale rectangle*
   (2). Generally it is only an upper bound for the coupled model.
   For a singleton B it equals claim 031's exact interval supremum,
   using local scale sqrt(wv/Δ) and calendar drift b.

2. **Finite covers and refinement.** Let ℘_h be the dyadic parameter
   cover obtained by bisecting both coordinates of ℬ h times, h≥0.
   Degenerate sides are permitted; repeated identical boxes may be
   kept or removed. The union always equals ℬ. Independently split
   every observed cell C_(z_j) into 2^ℓ equal price-width half-open
   subcells J_(j,a)^ℓ, with ℓ≥0. For each B∈℘_h and v∈𝒱 set

       U_(n,a)^{B,v,ℓ}=1,
       T_(j,a)^{B,v,ℓ}=Σ_d W_clock(B;J_(j,a)^ℓ,J_(j+1,d)^ℓ;Δ_(j+1),v_(j+1))
                                      U_(j+1,d)^{B,v,ℓ},
       U_(j,a)^{B,v,0}=min(1,T_(j,a)^{B,v,0}),
       U_(j,a)^{B,v,ℓ}=min(1,T_(j,a)^{B,v,ℓ},U_(j,floor(a/2))^{B,v,ℓ−1})
                                                    when ℓ≥1,
       B_clock^{B,v,ℓ}=max_a U_(0,a)^{B,v,ℓ},
       D_clock^{h,ℓ}=max_(B∈℘_h,v∈𝒱) B_clock^{B,v,ℓ}. (4)

   The parent state bound is computed for the same parameter box B.
   All these quantities are strictly positive and at most one. For
   every actual null, almost surely in U and at every label vector Z,

       P(Z|U) ≤ D_clock^{h,ℓ}(U,Z).                    (5)

   Increasing either h or ℓ weakly decreases D_clock. The same is
   true for any succession of covering child subboxes in place of
   uniform parameter bisection, with the same state grids.

3. **Calibrated finite score.** Fix any nonnegative measurable forecast
   q_clock(Z|U), normalized over all future label vectors for every U.
   Its forecasting rule is selected using training alone. For finite
   measurable nonnegative integer choices h(U,Z), ℓ(U,Z), put

       E_clock^cell(U,Z)=q_clock(Z|U)/D_clock^{h(U,Z),ℓ(U,Z)}(U,Z). (6)

   This is a finite measurable nonnegative score on every input
   array. At each actual null its conditional and unconditional means
   are at most one; the strict rule E_clock^cell>1/α has size ≤α
   for 0<α<1. AX-53 gives claim 053's base e-BH FDR bound
   q_FDR|N₀|/m, including measurable zero masks with original m.
   Measurable nonnegative implemented lower scores retain the moment.
   The parameter domain, clocks and normalized forecast stay fixed
   during evaluation-dependent computation. This permits refinement,
   not selection of a smaller fitted null family.

   One normalized example is the product of Gaussian cell probabilities
   from representative δ_tick z at positive previous labels and
   δ_tick/4 at label zero, using b_f∈ℝ, w_f>0 and positive forecast
   increments v_f,j chosen measurably from U. Its row means are
   b_fΔ_j−w_f v_f,j/2 and variances w_f v_f,j. The representative
   is used only for forecasting; the denominator covers the full cell.

4. **Boundary and limits of the comparison.** On an all-zero future
   label path from z_0=0, D_clock=1 at every finite refinement and
   E_clock^cell≤1. For one clock v=Δ and a singleton box, (4) equals
   claim 031's bound for that Gaussian parameter. A finite set of
   singleton boxes similarly recovers its catalogue maximum. Refining
   the fixed family improves the score with the same q_clock, but no
   ordering with claim 033's exact-price score is asserted. Direct
   computation costs O(n 4^h 4^ℓ |𝒱|) exact operations, including
   the geometric sum over coarser state levels; this is not a runtime
   or floating-point-certification guarantee.

## Proof

**Scalar calculation.** For x>0, the log-price mean log x+bΔ−wv/2
and positive standard deviation sqrt(wv) lie in (2). Fix s>0.
As in claim 029/031, the derivative of normal interval mass in its mean
is positive below the interval midpoint and negative above. Hence its
maximizer over the containing mean interval is m*, independent of s.
Taking the closure at an excluded source upper endpoint does not alter
the supremum, by continuity. An unbounded lower mean interval likewise
has the displayed finite optimum.

If the target log interval straddles m*, both endpoint contributions
make its probability nonincreasing in s, so s_- maximizes it. Otherwise
reflection reduces to the interval [ℓ,r] with 0<ℓ<r. The derivative
in s of Φ(r/s)−Φ(ℓ/s) has the sign of

    ℓ exp(−ℓ²/(2s²))−r exp(−r²/(2s²)).

The ratio of the first term to the second is
(ℓ/r) exp((r²−ℓ²)/(2s²)), strictly decreasing from infinity to
ℓ/r<1. The unique zero is (3) before clipping; the sign is positive
below and negative above. This proves (3) for every scale interval,
including singletons. If c=0<a, the probability Φ((log d_T−m)/s)
decreases in m; at M_- its scale monotonicity gives the stated case.
If a=c=0, the admitted trapped source gives probability one. If a=0<c,
trapping contributes zero and does not change the positive-state
supremum. Normal interval/tail probabilities are positive here and
bounded by one, proving part 1. At a singleton box the only freedom
is the source state, exactly the calculation in 031 with the local
Gaussian variance and calendar drift specified above.

**Finite-path bound.** Fix one component (x,v,b,w) of the actual
conditional law, and a box B containing (b,w). At each fixed level,
the future label-path probability from a source subcell equals a sum
over target subcells of integrals of the remaining-path probability
against the actual Gaussian transition. The conditional independent
increments supply this Markov factorization at fixed parameters and
endpoint; no conditional independence given labels alone is assumed.
Every transition mass is bounded by W_clock, uniformly over its source
and parameters in B. The terminal suffix probability is one. Apply
030/031's backward finite-partition bound using these transition
inequalities: each suffix is bounded by the T term, by one, and by
the valid inherited parent bound on the larger source subcell.
Their minimum is therefore a bound. Inducting over levels and suffix
length proves domination for every source state, including zero.
Maximizing over initial subcells, then covering boxes/clocks, bounds
each component's label mass. Integrating the supplied actual posterior
of endpoint and parameters proves (5). The label space is countable,
so an almost-sure conditional-law version can be chosen simultaneously
for all label vectors and all integer refinement levels.

Every W is positive and finite; finite sums, maxima and minima in
(4) consequently stay in (0,1]. The inherited state bound implies
B_clock^{B,v,ℓ+1}≤B_clock^{B,v,ℓ}, as in 030. For a parameter
child B'⊆B, its containing mean/scale rectangle is a subset of the
parent's at every fixed pair of source/target subcells. Thus its exact
rectangle supremum W is no greater. Double induction on state level
and suffix length in (4) yields U^{B',v,ℓ}≤U^{B,v,ℓ}: terminal
values agree, all nonnegative sum terms decrease, and the inherited
parent-state term decreases by the induction hypothesis. Every child
has a parent, and children cover the unchanged domain. Taking maxima
proves parameter refinement monotonicity and part 2.

**Inference application.** The finite-prefix/future-label spaces are
countable; (4) defines measurable positive denominators everywhere.
The countable family of all integer levels satisfies (5) simultaneously,
so a measurable finite choice depending on the evaluation labels still
dominates the actual conditional mass. Normalization of q_clock,
counting measure as the common reference, measurability and domination
are exactly AX-58's hypotheses. Apply AX-58, then AX-53 to the finite
scores, with original family size m as in 053. Lower nonnegative scores
preserve the null moment, so masks and lower implementations follow.

For the example forecast, each representative is positive, each row
is the cell partition of a normalized lognormal law, and hence the row
masses sum to one. Successive nonnegative summation normalizes the
product over future labels, even though the representative changes
with the previous label. The parameters and clock are fixed given U.
This is 031's normalized forecasting construction with time-dependent
declared mean and variance; it asserts no fit to a bubble alternative.

**Boundary and cost.** From an exactly trapped zero, every all-zero
future label path has probability one. The uniform state bound therefore
must be at least one on the zero-containing initial subcell, while
(4) caps it by one. All maxima are consequently one. A normalized
forecast assigns at most one to that path. Singleton reduction is part
1 applied at every transition of the identical recursion. There are
at most 4^h parameter boxes and 4^ℓ source-target subcell pairs per
step; summing over earlier state levels changes this by a constant
factor. This proves the operation count and completes the claim.

## Checks

`checks/d17-clock-cells/check.py` supplies the fixed transition,
interior-scale optimum, independent two-step integration, singleton
reduction, clock scaling and state/parameter refinement checks.
`checks/034/check.py` additionally checks covered conditional mixtures
using tail-accounted one-step moment bounds, evaluation-selected finite
refinements, full-clock maxima, all-zero boundaries, forecast
normalization and invalid inputs. These are deterministic diagnostics,
not simulations, proofs of the claim or outward certificates.

## Not shown

- The transition bounds, covers and refinements, score validity at
  data-selected finite levels, boundary cases and panel result are
  formalized in `lean/Standalone/D17ClockCells.lean`, proved by
  `statement_holds` in `lean/Novel/D17ClockCellsProof.lean`. The
  operation count and the remark asserting no ordering with claim 033
  remain commentary. The formalization proves the containing rectangle's
  maximum and its bound for the coupled model, not non-attainment in
  that model. AX-58 and the recursion results are proved; FDR remains
  conditional on AX-53's degenerate instance. No CEV-kernel or new
  stochastic upstream input is used in this Gaussian rounded-law claim.
- No coverage outside (1), empirical clock declaration, positive scale
  floor justification, confidence guarantee for a fitted rectangle,
  or upper bound on the omitted unrestricted parameter tails. This is
  strictly narrower parameter coverage than 033, not its complete
  rounded-price implementation. It also does not retain 033's CEV nulls.
- No noise, jumps, arbitrary stochastic volatility, default from a
  positive Gaussian state, missing-data law, or pricing-measure
  construction. Unequal overnight gaps are covered only under the
  stated law with their supplied positive Δ_j and v_j.
- No convergence to the exact rounded maximum likelihood, rate for
  refinement, useful power, or preference between five-minute and
  hourly sampling. The example forecast is Gaussian, not a validated
  clock-aware bubble forecast. Repeated-date testing is not covered.
- No outward numerical certificate. The existing arbitrary-precision
  prototype is diagnostic; rounding errors, normal tails and unstable
  near-equality cases still require certified arithmetic before its
  computed score can be asserted to be a conservative implementation.

## Prior art

[wasserman2019universal], Section 6, already gives the upper-likelihood
and conditional-likelihood inference method (AX-58); [wang2020false]
supplies AX-53. Claims 029–031 provide Gaussian interval maxima and
the finite-partition recursion. Claim 033 supplies the two-clock
conditional model. The preceding D17 input finding and its checks,
these claims/proofs, the AX-58 source text and the refuted
disjoint-window coverage target were checked before proposing. The
application work is the uniform mean/scale rectangle bound and its
combination with parameter-cover refinement for monetary observations.
No general inference or stochastic time-change theorem is re-proved.

## Review

Reviewer, 2026-10-07, on branch `math/d17-compact-clock-cells` at `b3d3c9a`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/034/` and `checks/d17-clock-cells/`.
- **Inputs.** AX-53 and AX-58 are audited, and AX-58 is proved. Claims 030, 031, 033 and 053, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/034/reproduce.py`, with its rerun command and seed in its header. It is single-process and is not a CI `check.py`.

**Part 1 (the transition bound): correct.**
- **The mean/scale rectangle.** From x ∈ [a, d_S) and (b, w) ∈ B, the log-price mean log x + bΔ − wv/2 lies in [M₋, M₊] and the standard deviation √(wv) in [s₋, s₊]. Taking the two ranges independently gives an outer rectangle, so the bound holds for the coupled model.
- **The mean.** At fixed s, interval mass is unimodal in the mean about the log-midpoint, so its maximizer is the clipped midpoint m* for every s. The joint supremum is therefore sup over s of f(m*, s).
- **The scale, when the interval straddles m*.** The mass decreases in s, so s₋ is optimal.
- **The scale, otherwise.** After reflection, d/ds[Φ(r/s) − Φ(ℓ/s)] has the sign of ℓe^{−ℓ²/2s²} − re^{−r²/2s²}. That sign is positive then negative, with its root at s² = (r² − ℓ²)/(2 log(r/ℓ)), so clipping gives (3).
- **The zero target from a positive source.** Φ((log d_T − m)/s) decreases in m. In s it decreases when t ≥ 0 and increases when t < 0, which gives the stated case split.
- **Trapped sources.** The zero state is handled correctly in both cases. A singleton box reduces to claim 031 with local variance wv and mean bΔ − wv/2.

**Part 2 (finite covers and refinement): correct.** This is claim 030/031's induction with transition upper bounds that hold uniformly over the box.
- **Parameter refinement.** A child box's rectangle sits inside its parent's, so each W, and by double induction each U, decreases.
- **Domination.** It holds for each (x₀, v, b, w) component through a box containing (b, w), and then by integration over the arbitrary posterior.

**Part 3 (the score): correct.** Counting measure on a countable label space lets an evaluation-dependent finite (h, ℓ) keep domination, so AX-58 and AX-53 apply directly.

**Part 4 (the boundary): correct.** All-zero paths from a zero label give D = 1.

**Checks** (evidence, not proof).
- **(a) The transition bound against brute force.** Fifty-eight random cases, with boxes, nonproportional clocks, coarse ticks and zero cells:
  - W_clock equals the grid supremum over the independent rectangle to a relative 10⁻⁶;
  - no grid point of the coupled (x, b, w) box exceeds it;
  - the coupled supremum is typically 0.975 of W_clock (median), so the rectangle relaxation costs little per step.
- **(b) Reduction and monotonicity.** A singleton box with v = Δ reproduces claim 031's product to 10⁻¹³. On 20 paths the bound is monotone in both h and ℓ.
- **(c) Domination by Monte Carlo.** Over 400,000 two-step draws, with the endpoint uniform in the cell, (b, w) uniform in a box and the clock drawn from a two-clock set: 16 frequent label paths, no violations, and D above the frequency by a median factor of e^{2.7}.
- **(d) The cost of a compact box.**
  - **Setup.** A cent tick, a $5 GBM null with κ = 0.3, 60 daily steps and 8 paths. The numerator is claim 031's forecast at the true parameters.
  - **Result.** Median log E is −0.67 with the singleton true box (claim 031). With the box b ∈ [−0.1, 0.2], κ ∈ [0.15, 0.45] at state level 2, it is −22.8, −19.2, −11.3 and −5.4 at h = 0–3.
  - **Reading.** Parameter refinement removes most of the box's cost, but not all of it at h = 3, and it is still falling. Its O(4^h) cost per step makes deeper refinement expensive.
- **The author's checks.** I ran both afterwards. `checks/d17-clock-cells/check.py` passes 648 transition bounds, the rectangle maxima, refinement and the 031 reduction. `checks/034/check.py` passes the conditional mixtures with forecast tails, adaptive levels, trapping and invalid inputs.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **It is a rounded-price analogue of claim 033, but over a compact box only.** Coverage outside ℬ, including the scale floor w₋ > 0, is a premise, and the claim correctly states that it does not retain claim 033's CEV nulls or its unrestricted parameters.
2. **No power is shown.** My (d) measures evidence cost on null paths only. The claim rightly asserts no ordering with claim 033's exact-price score, whose power my claim-033 review found low on a weekend design.
3. **Not covered:** noise (D18, claim 064), jumps and outward certification, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red re-derived the clipped-midpoint mean and closed-form scale maxima over the box rectangle, zero-target cases, monotone parameter/state refinement with domination over any posterior, and AX-58 with evaluation-chosen covers; committed review script; scope honest


Reuse 030/031's deterministic interval and suffix-bound lemmas with
transition upper bounds. Prove the scale derivative/root and rectangle
inclusion directly as finite scalar analysis; these are not assumptions.
Keep parameter refinement separate from state refinement, with both
covering the same declared family. Apply the proved AX-58 result to
counting measure and AX-53 only for the panel conclusion. Preserve
the entire zero cell and the actual conditional endpoint posterior.

Formalizer, 2026-10-07, on `form/d17-compact-clock-cells`. **Status: formalized.** The statement is `lean/Standalone/D17ClockCells.lean`, with
`statement := transition ∧ covers ∧ validity ∧ boundary ∧ panel`.
It is proved in `lean/Novel/D17ClockCellsProof.lean` (`statement_holds`), from `D17ClockCells{Scale,Trans,Rec,Cover,Valid}`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** FDR is conditional on AX-53 through claim 026's `panel`. AX-58's step is proved directly with counting measure, as in claim 031. Claim 031's observation model (`mlabels`, `walkM`, `stepP`, subcells, `Wm`, `Ub`) and forecast, and claim 029's `cellP_le_clip` and `unimodal_real`, are reused. Nothing else is cited.
- **Encoding.** One name, with claim 031's tick δ > 0, labels and cells.
  - A box is `Box ⟨b_L, b_H, w_L, w_H⟩`. `Valid` asks b_L ≤ b_H and 0 < w_L ≤ w_H.
  - (2) is `meanLo`, `meanHi`, `sdLo` and `sdHi`. `Wclock` is part 1's bound, with the clipped midpoint `mstarC` (unbounded below at a = 0) and the scale `sstarC` of (3), including the reflection.
  - (4) is `Uc`/`Bc` over claim 031's subcells. `Dcov` is the maximum over any finite set of boxes and the clocks. `pbox ℬ h i k` is the dyadic subbox and `Dclock` the maximum over ℘_h.
  - The contract uses random variables. The endpoint X₀, clock V and parameters (b, w) have an arbitrary joint law given the whole rounded training record U, supported a.s. on C_(z₀) × 𝒱 × ℬ. Given (U, X₀, V, b, w) with X₀ > 0, the returns are independent Normal(bΔ_j − w v_j/2, w v_j). Z = mlabels(X₀, R), zero from X₀ = 0.
- **Part 1 (`transition`).** For a valid box, Δ, v > 0 and 0 ≤ a < d_S, 0 ≤ c < d_T:
  - W_clock ∈ (0, 1].
  - It bounds the one-step target probability from every x ∈ [a, d_S), trapped state included, and every (b, w) ∈ B.
  - On positive sources it is the maximum of the Gaussian mass over the rectangle (2), attained there.
  - A singleton box gives claim 031's `Wm` with drift bΔ − wv/2 and scale √(wv).
  - The scale optimum (3) is proved by the derivative sign in log-scale (`scale_le`): it is positive below √((r² − l²)/(2 log(r/l))) and negative above.
- **Part 2 (`covers`).**
  - Every B_clock is in (0, 1].
  - It weakly decreases with the state level and with a valid child box, by double induction through the rectangle inclusion.
  - Any refining cover of valid boxes lowers the maximum.
  - The dyadic subboxes are valid, lie in ℬ for in-range indices, and cover ℬ. D_clock is in (0, 1] and weakly decreases in h and in ℓ.
- **Parts 2–3 (`validity`), for any numerator q ≥ 0 normalized over label vectors at every training record**, at data-selected levels (h, ℓ)(U, Z):
  - (5) holds for a.e. U, simultaneously for every Z, h and ℓ.
  - E_clock^cell is finite. Its conditional and unconditional means are ≤ 1, its size is ≤ α for 0 < α < 1, and every lower measurable score keeps the mean.
  - This generic form is the one formalizerb asked for, for claim 035.
- **Part 3's example forecast and part 4 (`boundary`).**
  - Claim 031's Gaussian cell product with row means b_f Δ_j − w_f v_j/2 and standard deviations √(w_f v_j) is normalized with positive masses.
  - On the all-zero future path from z₀ = 0, D_clock = 1 at every (h, ℓ), and q/D_clock ≤ 1.
  - With one clock v = Δ, the singleton box (b, κ²) gives claim 031's recursion for θ = (b, κ).
  - A finite set of singleton boxes recovers claim 031's catalogue maximum.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53, with arbitrary dependence, lower scores and measurable zero masks at the original m.
- **Not formalized.** These are commentary only:
  - the operation count O(n 4^h 4^ℓ |𝒱|);
  - the remark that no ordering with claim 033's score is asserted;
  - the remark that W_clock is only an upper bound for the coupled model. The formal statement proves the bound and the rectangle maximum, not non-attainment.
