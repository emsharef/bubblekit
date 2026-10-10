---
id: "066"
title: "D18: a compact clock and noise-sign score with a training-selected CEV forecast"
status: formalized
depends_on: ["034", "035", "053", "054", "065"]
axioms_used: [AX-53, AX-56, AX-58]
formal: lean/Standalone/D18ClockNoise.lean
direction: D18
---
## Statement

**Conditional on the actual joint law and coverage specified below, AX-56
for CEV forecast normalization, and AX-53 for FDR.** This combines claim
034's uniform transition bound with claim 065's sign recursion and claim
035's training-only clock selection. AX-58 supplies inference. No new
scalar maximum, filtering theorem or stochastic time-change theorem is
asserted. This is a mathematical score specification, not a certified
implementation or a validated model of an intraday feed.

Fix m names, a supplied pricing-null subset N₀, levels 0<α_i<1 and
0<q_FDR<1. For each name, before observing data declare a tick δ_tick>0,
finite radius a_noise≥0, k≥1 training and n≥1 evaluation increments,
positive evaluation calendar durations Δ_j, a finite nonempty null clock
catalogue 𝒱 of positive vectors v=(v_1,…,v_n), and the compact rectangle

    ℬ=[b_-,b_+]×[w_-,w_+],
    −∞<b_-≤b_+<∞,  0<w_-≤w_+<∞.                     (1)

Also declare 0≤ρ_noise<1 and finite β_noise. Observations are the labels
of Y_j=max(0,X_j+a_noise H_j), H_j∈{−1,+1}, under the monetary quantizer
of 034/065. U=(z_0,…,z_k) is the entire noisy training prefix, ending in
z_k; Z=(z_(k+1),…,z_(k+n)) is evaluation. In denominator recursions only,
write the last training label as z_0 and renumber evaluation labels 1,…,n.

For i∈N₀, the actual conditional distribution of (v,b,w,X_0,H_0) given
U is arbitrary on 𝒱×ℬ and compatible endpoint/sign pairs
X_0∈I_(z_0,H_0)^noise from claim 065 (2). Conditional on those variables,
the actual future law is the product of

    P_(v,b,w,j)(x,dy) A_(h,t)(x,y),                 (2)

where P is the price kernel with independent log returns of mean
bΔ_(j+1)−wv_(j+1)/2 and variance wv_(j+1), trapped at zero, and A is
exactly claim 065 (1) with the declared ρ_noise, β_noise. Thus drift uses
calendar time and variance uses v. The conditioning is on the **whole
noisy prefix** and the joint latent endpoint/sign/parameter state. Neither
an unconditional Gaussian law nor a fitted clock or box supplies this
premise. There is no law restriction on names outside N₀.

**Denominator.** Let ℘_h be claim 034's dyadic cover of ℬ at parameter
depth h, allowing degenerate sides. For each B∈℘_h and v∈𝒱, compute two
recursions at price-state level ℓ, K=2^ℓ:

- State mode: use claim 065's sign-specific cells I_(z_j,t)^noise,
  omit empty cells, and split each nonempty cell into K equal price
  subcells. In (4) of 065 replace every Gaussian W by

      W_clock(B;S,T;Δ_(j+1),v_(j+1)),               (3)

  exactly as defined by (2)–(3) of 034. Keep its Abar_(h,t)(S,T),
  sums over next signs/subcells, cap at one, and same-sign parent bound
  from price-state level ℓ−1 for the same B and v. Call the initial
  sign/subcell maximum B_(B,v)^(state,ℓ).
- Support mode: use claim 064's expanded intervals
  I_z^a=[max(0,l_z−a_noise),r_z+a_noise), with K equal subcells. Use
  claim 034's scalar backward recursion with (3) on these intervals,
  cap at one and inherited price-state parent. There is no sign weight.
  Call its initial maximum B_(B,v)^(support,ℓ).

Set

    D_clocknoise^(r,h,ℓ)=max_(B∈℘_h,v∈𝒱) B_(B,v)^(r,ℓ),
                   r∈{state,support},
    D_clocknoise^(h,ℓ)=min(D_clocknoise^(state,h,ℓ),
                           D_clocknoise^(support,h,ℓ)).          (4)

This support recursion uses the **expanded** cells and the same clock/box
transition bound. It is not 034's ordinary-cell denominator or 065's
original finite constant-Gaussian catalogue denominator.

1. **Domination and refinement.** On every input label array the bounds
   in (4) lie in (0,1]. Under (2), for almost every actual null U and
   simultaneously every Z,h,ℓ,

       P(Z|U) ≤ D_clocknoise^(h,ℓ)(U,Z).             (5)

   Each of the two maxima and their minimum decreases weakly when h
   or ℓ increases. Any finite succession of covering rectangular child
   subdivisions gives the same conclusion in place of uniform h. A finite
   partition selected measurably from (U,Z) is permitted if it still covers
   the entire original ℬ and retains every original null clock. Choosing
   a fitted smaller null family is not permitted. On countable label
   spaces these selection rules are measurable whenever defined everywhere.

2. **A clocked CEV numerator on noisy labels.** Declare before observation
   a finite ordered nonempty forecast catalogue Ξ. A member ξ consists of
   p_ξ>1, κ_ξ>0, 0≤ρ_(forecast,ξ)<1, and positive full forecast-clock
   increments v_(ξ,1),…,v_(ξ,k+n). Forecast clocks need not belong to 𝒱.
   Keep the same tick and radius for this forecast construction.

   Let r_(z,h)^forecast be the positive midpoint of the nonempty
   I_(z,h)^noise. Let K_(p,κ) be the normalized p>1 CEV kernel from
   054/AX-56, relative to μ_CEV. For feasible source pairs define

       A_(ξ,h,t)^forecast=ρ_(forecast,ξ)1_(h=t)+(1−ρ_(forecast,ξ))/2,
       K_(ξ,j)^forecast((z,h),(z',t))=
           A_(ξ,h,t)^forecast ∫_(I_(z',t)^noise)
             K_(pξ,κξ)(v_(ξ,j),r_(z,h)^forecast,y) μ_CEV(dy).    (6)

   Empty target intervals have mass zero. The initial sign vector is
   uniform on the feasible signs of z_0. Define L_ξ(U) by summing the
   product of the first k transitions in (6) over all training sign paths.
   Let π_(ξ,k)^forecast(U) be the corresponding conditional final sign
   vector. Select the first maximizer ξ_hat(U) of L_ξ(U). The evaluation
   forecast q_CEV^clocknoise(Z|U) sums the product of the remaining n
   transitions against π_(ξ_hat,k)^forecast(U), over all evaluation signs.

   Every L_ξ(U)>0 and the conditional sign vector is defined for every
   label prefix. The selected evaluation forecast is finite, positive,
   measurable and normalized on ℕ^n for every U. It is the conditional
   law of this **discrete forecasting construction**, not the noisy
   likelihood of a continuously evolving CEV diffusion. Only its numerator
   restarts at representatives. Its forecast sign persistence is not a
   fitted replacement for ρ_noise or β_noise in the actual null (2).

   For any nonnegative normalized measurable baseline q_base(Z|U),
   including 034's Gaussian label forecast, and any training-only
   0<λ(U)<1, define

       q_mix^clocknoise=λ q_base+(1−λ)q_CEV^clocknoise.             (7)

3. **The combined score.** For q equal to either forecast above, or any
   other normalized training-selected label forecast, and finite measurable
   h(U,Z),ℓ(U,Z), put

       E_clocknoise=q(Z|U)/D_clocknoise^(h(U,Z),ℓ(U,Z))(U,Z).     (8)

   It is finite and nonnegative on every label array. Under (2) its
   conditional and unconditional null means are at most one and the rule
   E_clocknoise≥1/α_i has size ≤α_i. AX-53/053 gives base e-BH
   FDR≤q_FDR|N₀|/m under arbitrary dependence across names. Measurable
   nonnegative lower implementations and zero masks retain these guarantees,
   with the original panel size m. Numerical approximations below are not
   claimed to be such lower scores.

   With the same denominator, E_mix=λ E_base+(1−λ)E_CEV≥λ E_base.
   Refining the cover or state cells increases each exact score for fixed q;
   it changes neither the fitted forecast nor null coverage. No power gain
   follows from either ordering.

4. **Reductions, zero boundary and cost.** At a_noise=0, (4) equals
   claim 034's denominator for every β_noise. Forecast (6) reduces to
   claim 035's rounded CEV forecast, with the same ordered catalogue
   projected onto (p,κ,full clock); duplicate entries may be retained.
   With a singleton box, a single calendar clock v=Δ, and the same
   Gaussian parameter, (4) equals claim 065's combined denominator.

   At a_noise=δ_tick, β_noise=0 and an all-zero path including the
   last training label, (4) is [(1+ρ_noise)/2]^n at every h,ℓ,
   independently of the clock catalogue and parameter rectangle. Hence
   the wrong-sign-reset counterexample of 065 remains possible; adding
   clock coverage does not correct a false noise law.

   The denominator costs O(nH²4^h4^ℓ|𝒱|) exact operations, H=2.
   For N covering leaf boxes substitute N for 4^h. Forecast selection
   uses O(|Ξ|kH²) cell-integral evaluations, followed by O(nH²) for
   evaluation. These count exact operations, not runtime or numerical
   certification. Neither useful power nor feasible deep refinement is
   asserted.

## Proof

**Existing scalar bound, new composition.** Fix an actual component
(v,b,w,x_0,h_0) and any covering box B containing (b,w). For positive
x∈S, the log-price mean and standard deviation of (2) lie in 034's
containing rectangle (2), so that claim bounds the target probability
by (3). Its statement permits arbitrary finite nonnegative source/target
intervals, including every sign-specific or expanded subcell used here.
The zero transition is the same trapped state. Thus no new scalar
calculation is necessary. Claim 065 (3) bounds A on each source/target
pair; this bound is independent of b,w and the clock.

The exact joint suffix probability obeys 065 (8) with the new P.
On each target subcell, its integral is bounded by (3) times Abar times
the next suffix bound. Sum over target signs and subcells, then take
the minimum with one and the valid same-sign parent. The backward and
state-level inductions in 065 therefore apply word for word at fixed
B,v. They bound the suffix uniformly over all (b,w) in B. Taking the
initial maximum covers the exact endpoint and sign without factorizing
their posterior. Maximize over covering boxes and full clock vectors
and integrate the actual joint posterior to obtain the state-mode bound.

For support mode, |Y−X|≤a_noise gives the expanded-cell event containment
from 064. Summing the sign factors in (2) backward gives one for every
fixed latent price path; hence forgetting signs leaves precisely the
Gaussian product with mean bΔ−wv/2 and variance wv. Applying the same
partition induction on expanded cells with no Abar yields the support
bound, at fixed B,v and then for the joint posterior. The two bounds
dominate the same actual observation mass, proving (5) for their minimum.
The label space and uniform-depth choices are countable, so the
conditional statement holds simultaneously after one null set is removed.

All nonempty sign cells have positive-length positive interiors; the
negative-sign cell is always nonempty. Claim 034 gives W_clock>0,
and 065 gives Abar>0. The terminal suffix bounds are one. Finite
nonnegative sums with a positive negative-sign term, caps, parent minima
and initial maxima consequently remain strictly positive and at most one.
The same argument applies to expanded cells. Explicit formulas and finite
operations are measurable, proving the remaining assertions of part 1.

**Refinement and coverage.** State children inherit their parent bounds
for the same B,v and sign, giving state monotonicity. If B'⊆B, 034's
containing mean/scale rectangle on any fixed pair S,T shrinks, hence
W_clock(B';S,T)≤W_clock(B;S,T). Abar and all state grids are unchanged.
Induction on state level and backward time therefore compares all child
U values with their parent-box counterparts, exactly as in 034. The
covering maxima decrease because every child has a parent, while
coverage is preserved. This applies separately to state and support
modes and hence to their minimum. For any finite adaptive covering
partition, the same componentwise bound holds path by path: every
admitted (b,w) still belongs to a retained box. On the countable
observation domain, the selected denominator remains measurable. No
probability of choosing the cover has to be paid; omitting a parameter
or null clock would instead change the hypothesis being bounded.

**Forecast normalization and fitting.** For each fixed next sign t,
the intervals I_(z',t)^noise partition [0,∞). Each nonempty source
representative is positive. AX-56 evaluated at the positive forecast
increment has mass one on positive prices. Summing (6) over z' and t
therefore gives Σ_t A_(ξ,h,t)^forecast=1 on every feasible source pair.
Iterated nonnegative summation normalizes every finite label/sign path
law in this construction. The all-negative sign path is feasible for
every label record; its initial weight, transitions and CEV interval
masses are strictly positive. Thus every training likelihood and every
evaluation mass is positive. Conditional final sign weights exist on
every training prefix, place no mass on infeasible signs, and sum to one.

The forecast initialized by those weights is normalized for every U.
Finite first-index maximization is training-measurable; partition training
space by its selected index, as in 035. This proves normalization and
measurability of the selected forecast. Summing out training and evaluation
signs also identifies it as joint forecast label mass divided by the
training label mass for that selected member. Updating weights as evaluation
labels arrive computes this fixed forecast; it does not reselect its model.
Training-only convex blending with a normalized baseline preserves these
properties. No stochastic time-change theorem is used: the existing
normalized kernel is simply evaluated at positive declared arguments.

**Inference.** Every finite selected denominator in (8) dominates the
actual conditional label mass by (5), and is positive everywhere. Any
normalized label mass is at most one pointwise, so the score is finite.
Apply AX-58 on counting measure to this denominator and the supplied
normalized q, then AX-53 through 053 with original m. This gives all
moment, size, lower-score and FDR statements. The CEV version is
conditional on AX-56; the denominator and validity for a supplied normalized
q require no CEV assumption. Division by the same positive denominator
gives the blend identity. Denominator monotonicity proves the refinement
ordering without any comparison of rejection rates.

**Reductions and boundary.** At zero radius, expanded and sign-specific
cells all become the ordinary cells of 034, with identical partitions.
For a fixed source/target subcell, Σ_t Abar_(h,t)≥1. The induction in
065 shows that each raw sign suffix bound is at least the scalar bound
using the same W_clock, B and v. The support recursion is exactly 034's.
Taking maxima and then their minimum therefore gives exactly 034, also
after parameter refinement. Source representatives and CEV target intervals
in (6) are then sign-independent. Summing the stochastic sign chain leaves
035's scalar row product for training and evaluation, so its fitting and
forecast reduce as stated.

For a singleton box with v=Δ, 034's W_clock is 031's exact transition
supremum with drift b and scale sqrt(w). Both recursions consequently
are exactly those in 065. For the all-zero boundary at a_noise=δ_tick
and β=0, only the negative sign is feasible. Its transition weight is
r=(1+ρ_noise)/2, and W_clock=1 between zero-containing intervals.
At level zero the raw bound is r^n. The exact trapped endpoint attains
that probability for every parameter/clock, preventing refinement below
it. Support is one by the same trapped endpoint. Thus the combined
bound is r^n at all levels and covers. The existing reset counterexample
follows unchanged. Counting sign pairs, price-subcell pairs and covering
boxes gives part 4's denominator cost; the geometric sum over coarser
state levels changes only a constant. Forward sign summation gives the
forecast operation counts.

The actual-law premises are nonempty: start at a positive price, choose
a fixed allowed clock/parameter, generate independent Gaussian increments
and independent uniforms to choose signs by (2). A training block produced
by the same independent-input construction gives the required future law
when its endpoint/sign and parameters are supplied. This is a genuine
positive model instance, not evidence that a real feed satisfies (2).

## Checks

`checks/066/combined.py` composes the existing scalar bound and sign
weights, covering the parameter box and full null clock vectors, with
the adapted support comparison. It fits the noisy-label CEV forecast on
training, carries its sign weights to evaluation, and computes a fixed
baseline blend. The denominator uses mpmath and the numerator SciPy tails;
neither is outward-certified.

`checks/066/check.py` checks an independent two-step continuous
clock/parameter/endpoint/sign mixture, both refinement axes, exact reductions
to 034 and 065, clock scaling, trapped boundaries, full-clock maxima,
both forecast selection branches, ties, unchanged selection after changing
evaluation, joint/training forecast factorization, the blend identity and
an adaptive one-step null moment with an explicit forecast tail. These
are deterministic checks; no simulated or market performance is reported.

## Not shown

- No calibration when the actual future conditional law is outside (2),
  the clock catalogue or compact box. Training estimation does not certify
  those coverage premises or the known two-point noise radius and logistic
  transition. A variance estimate is not an almost-sure error bound.
- No general endogenous noise, time-varying spread, missing trades, jumps,
  SV null, pricing-measure identification, repeated-date error control or
  exact noisy CEV alternative likelihood. Forecast selection cannot repair
  an omitted null clock or a misspecified sign law.
- No useful power or near-noiseless evidence guarantee. Finite parameter
  boxes permit different transition maxima to use different parameters;
  the containing mean/scale rectangle loses coupling; finite state cells
  lose endpoint consistency; separate price and sign maxima lose their
  coupling. Refinement tightens the bound but no convergence rate or
  feasible-cost recovery result is proved. Narrowing the declared box
  changes null coverage rather than merely reducing computational slack.
- The composition is formalized in `lean/Standalone/D18ClockNoise.lean`
  and `lean/Novel/D18ClockNoiseProof.lean`, conditional on the stated actual
  joint law. CEV forecast normalization uses AX-56 with AX-55 through
  claim 054's kernel; their current Lean instances are vacuous. FDR uses
  AX-53, whose instance is degenerate. Validity for a supplied normalized
  numerator uses no CEV input. Operation counts, the model-existence
  remark and the counterexample-transfer remark remain informal; the
  forecast's joint/training likelihood ratio identity is not stated
  separately in Lean.
- No numerical certificate exists. Numerical underflow/failure must not
  be silently normalized away; the prototype raises on unresolved CEV
  tails. Even a nonfailed floating-point score is not asserted to be a
  certified lower score.

## Prior art

The mechanism is the existing likelihood-bound rule AX-58 from
[wasserman2019universal], applied after checking the observation domain,
actual joint conditional law and forecast normalization. The scalar
rectangle maximum and finite-cover comparison are claim 034; the
sign-specific bound and support minimum are 065; training-only CEV clock
selection is 035, based on AX-56 [makarov2009exact]. The prior-art and
model distinctions in 065 still apply: [diebold2010correlation] and
[jacod2013statistical] motivate noise dependence but do not supply (2).
No new source theorem or ledger input is imported. Read those claim
files, the D18 composition/looseness findings and the refuted training-
coverage and evaluation-forecast-maximum targets before this proposal.

The contribution is the explicit combined observation-space construction
and its compatibility checks. The reported experiment-027 failure of
034's coarse rounded bound motivates refinement, not a claim that this
composition restores power. Experiment 028 is a separate registered
performance study; none of its outcomes is a premise here.

## Review

Reviewer, 2026-10-07, on branch `mathb/d18-clock-noise` at `77e83a7`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/066/`.
- **Inputs.** AX-53, AX-56 and AX-58 are audited, and AX-58 is proved. Claims 034, 035, 053, 054 and 065, the dependencies, are approved or formalized. Cited keys are registered.
- **Script.** My check is committed as `checks/review/066/reproduce.py`, with its rerun command and seed in its header. It is single-process and is not a CI `check.py`.

**Part 1 (domination and refinement): correct as a composition.**
- **The transition bound.** Claim 034's W_clock bounds the Gaussian target probability for arbitrary nonnegative source and target intervals, uniformly over a box and from the trapped state. So it can replace claim 031's W in claim 065's sign recursion and in claim 064's expanded-cell recursion.
- **The sign weight.** Abar bounds A independently of (b, w, v), because A depends only on (h, x, y).
- **The support mode.** Summing the sign factors backward leaves the latent clock-Gaussian law, and |Y − X| ≤ a, so the containment holds and the minimum (4) is valid.
- **Refinement.** Child boxes shrink W_clock's rectangle while Abar and the grids are unchanged, so both modes decrease, and so does their minimum.
- **Adaptive covers.** They are valid only if they still cover ℬ and every null clock, as stated.

**Part 2 (the forecast): correct.**
- **The rows.** For each next sign the sign-specific intervals partition [0, ∞), and the forecast sign weights sum to one over t. So each row of (6) sums to one, and the label/sign chain is a normalized hidden-Markov forecast.
- **Positivity.** The all-negative sign path is always feasible, so L_ξ > 0 and the forward filter π is defined.
- **Selection and the blend.** Selection is a first maximizer on training, and the blend (7) uses a training-only λ, so normalization is kept as in claim 035.
- **Zero radius.** The midpoint representatives are δz and δ/4, which are claim 035's.

**Part 3 (the score): correct.** AX-58 applies on counting measure, and the blend identity follows from the common denominator.

**Part 4 (reductions and boundary): correct.**
- **Zero radius.** Claim 065's Σ_t Abar ≥ 1 argument gives claim 034's denominator.
- **A singleton box with v = Δ.** This gives claim 065's combined denominator.
- **The all-zero boundary.** At a = δ it is [(1 + ρ)/2]ⁿ, independent of the box and clocks.

**Checks** (evidence, not proof).
- **(a) Domination by Monte Carlo** of the full law (2).
  - **Setup.** A coarse tick, a = 0.4 tick, ρ = 0.6, β = ±5, (b, w) uniform in a box, the clock drawn from two nonproportional clocks, the endpoint and sign uniform on a random feasible cell, and 400,000 draws.
  - **Result.** At h = 1, ℓ = 2: 21 and 19 frequent two-step label paths, no violations, and D above the frequency by a median factor of e^{3.0}.
- **(b) Reductions.** At a = 0 the result equals my claim-034 box recursion exactly. With a singleton box and v = Δ it equals my claim-065 min(state, support) to 4×10⁻¹⁴.
- **(c) The forecast.** Rows of (6) over (z′, t), with tails, sum to one to 2×10⁻¹⁴ over 36 rows. The two-step forecast from a uniform initial sign, with the filter carried, has total mass 1.0000000000.
- **(d) The evidence cost of the box on top of noise.**
  - **Setup.** A cent tick, a = half a tick, signs with ρ = 0.5 and β = 0, a $5 GBM null with κ = 0.3, 40 days and 6 paths. The numerator is claim 031's forecast at the true law.
  - **Result.** Median log E is −0.43 for claim 065 at the true parameters (a singleton box). With the box b ∈ [−0.1, 0.2], κ ∈ [0.15, 0.45] it is −16.3, −13.4 and −8.9 at h = 0, 1, 2.
  - **Reading.** The two-point noise is nearly free, as in my claim-065 review. The compact box costs as much as in my claim-034 review, about 9 nats at h = 2 over 40 days, and refinement is expensive. This is consistent with experiment 027's near-zero power for claim 034's coarse bound and with this claim's "Not shown".
- **The author's check.** I ran `checks/066/check.py` afterwards. It passes the mixture integral, both refinements, the 034 and 065 reductions, the trapped boundary, training-only selection with sign carry-over, the blend and the tail-accounted moment.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The claim adds no coverage beyond its constituents.** Validity needs the declared clocks, the box, the two-point radius and the logistic sign law to hold given the noisy prefix.
2. **The forecast is a discrete restart construction, not a noisy CEV likelihood.** It is honestly labelled as such.
3. **Power is the open question.** With claim 035's clock-aware forecast, power will be limited mainly by the box slack shown in (d). That needs a narrower declared box, which changes coverage, or deep refinement at O(4^h) cost. Experiment 028 is the right place to measure it.

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red verified the composition (034's box transition bound inside 065's sign recursion and 064's support minimum), monotone refinement, the normalized sign-chain forecast with training-only selection and blend, the reductions and the trapped boundary; committed review script; box-slack limit stated

Formalizer, 2026-10-07, on `form/d18-clock-noise-score` (promoted from `provisional/form-d18-clock-noise-score`). **Status: formalized.** The statement is `lean/Standalone/D18ClockNoise.lean`, with
`statement := covers ∧ validity ∧ forecast ∧ scores ∧ reductions ∧ panel`.
It is proved in `lean/Novel/D18ClockNoiseProof.lean` (`statement_holds`), from `D18ClockNoise{Support,Forecast,State,Main,Valid}`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** FDR is conditional on AX-53 through claim 026's `panel`. The forecast's normalization uses AX-56 (with AX-55, as claim 035's `labels`), through claim 054's kernel `Kc`. AX-58's step is proved directly with counting measure. The denominator and the validity for a supplied normalized numerator use no CEV input. Reused results:
  - claim 034's `Wclock` and its part 1;
  - claim 065's sign intervals, `Abar`, `jointLawG` and the generic `UsW` with its suffix bound `Qg_le_UsW`;
  - claim 064's expanded cells;
  - claim 035's `qCell`;
  - claim 031's walk machinery.
- **Encoding.** One name, with claim 031's tick δ > 0, labels and cells, and radius a ≥ 0.
  - **State mode:** claim 065's `UsW` with the per-step bound `Wclock B` and step data (Δ_j, v_j).
  - **Support mode:** `Usup`, claim 034's recursion with `Wclock` on claim 064's expanded subcells.
  - (4) is `Dcn = min(DstC, DsupC)` over any finite set of boxes and the clock catalogue. `pcover ℬ h` is ℘_h.
  - **The contract (2).** The clock, the parameters (b, w), the endpoint and the initial sign have an arbitrary joint law given the whole noisy prefix U. It is supported a.s. on 𝒱 × ℬ × compatible endpoint/sign pairs. Given these, the evaluation returns and signs follow claim 065's joint law with means bΔ_j − w v_j/2 and standard deviations √(w v_j).
- **Part 1 (`covers`, `validity`).**
  - Both bounds and their minimum are in (0, 1] for every finite set of valid boxes.
  - They decrease weakly with the state level and with any refining set of child boxes, so the scores increase. The dyadic covers cover ℬ and refine each other.
  - (5) holds for a.e. U, simultaneously for every Z, h and ℓ on ℘_h.
  - (5) also holds for any cover of ℬ by valid boxes and any level selected from (U, Z) (`Cs`, `Lv`), with the original clocks kept.
- **Part 2 (`forecast`).**
  - Every training likelihood L_ξ(U) is positive. The final sign vector is a probability vector, zero on infeasible signs of the last training label.
  - The selected forecast (6) is positive and normalized on ℕ^n for every U, and so is the training-only blend (7) with any normalized baseline.
  - At a = 0 it is claim 035's `qCell` for the catalogue projected onto (p, κ, full clock). The midpoints are claim 031's representatives, and the sign chain sums out.
  - The forecast is defined through the final sign vector, as in the claim. The identity q = (joint label mass)/(training label mass) from the proof is not stated separately.
- **Part 3 (`validity`, `scores`).**
  - For any normalized numerator, E_clocknoise is finite. Its conditional and unconditional means are ≤ 1, P(E ≥ 1/α) ≤ α for 0 < α < 1, and every lower measurable score keeps the mean.
  - With the same denominator, E_mix = λ E_base + (1 − λ) E_CEV ≥ λ E_base.
- **Part 4 (`reductions`).**
  - At a = 0, (4) on ℘_h is claim 034's `Dclock`, for every β.
  - A singleton box (b, κ²) with v = Δ gives claim 065's `Djoint` for Γ = {(b, κ)}.
  - At a = δ, β = 0, the all-zero path from a zero quote gives ((1 + ρ)/2)^n at every level, for every nonempty finite set of valid boxes and every clock catalogue.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53, with arbitrary dependence, lower scores and measurable zero masks at the original m.
- **Not formalized.** These are commentary only:
  - the operation counts;
  - the remark that the counterexample of claim 065 "remains possible", which follows from the boundary value;
  - the proof's model-existence remark.
