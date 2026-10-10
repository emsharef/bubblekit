---
id: "065"
title: "D18: calibrated label scores with persistent and return-dependent noise signs"
status: formalized
depends_on: ["030", "031", "053", "064"]
axioms_used: [AX-53, AX-58]
formal: lean/Standalone/D18SignNoise.lean
direction: D18
---
## Statement

**Conditional on the actual joint transition law (1) given noisy training.**
The general mechanism is AX-58 applied to a dominating conditional likelihood.
Claims 030–031 and 064 supply the finite-partition bound. The application
here retains a finite noise sign inside that bound. It is neither a new
filtering theorem nor a likelihood for a substituted finite price grid.

Fix a panel of m names and a supplied pricing-null set N₀, with per-name
levels 0<α_i<1 and 0<q_FDR<1. For each name fix a tick δ_tick>0, finite
radius a_noise≥0, n≥1 evaluation gaps Δ_j>0, a finite nonempty catalogue
Γ_i of θ=(b_θ,κ_θ) with b_θ finite and κ_θ>0, and constants
0≤ρ_noise<1 and finite β_noise. All declarations are fixed before evaluation.
U_i is the entire noisy training prefix of nonnegative integer labels, ending
in z_0; V_i=(z_1,…,z_n) are the evaluation labels. Observations are

    Y_j=max(0,X_j+a_noise H_j),  H_j∈{−1,+1},
    z_j=floor(Y_j/δ_tick+1/2),  X_j≥0.

Use claim 031's ordinary monetary cells C_z^δ=[l_z,r_z), with
C_0^δ=[0,δ_tick/2). Let P_(θ,j)(x,dy) be its Gaussian price transition:
for x>0, log(X_(j+1)/x) is Normal((b_θ−κ_θ²/2)Δ_(j+1),
κ_θ²Δ_(j+1)); at x=0 it is the point mass at zero.

For every i∈N₀ supply the actual conditional distribution
ν_i^state(u;dθ,dx_0,dh_0) of the constant θ, exact endpoint and initial
sign. Conditional on these variables, the actual future joint path law
is the product of the transitions

    P_(θ,j)(x,dy) A_(h,t)(x,y),                        (1)
    A_(h,+)(x,y)=ρ_noise 1_(h=+1)+(1−ρ_noise) L(x,y),
    A_(h,−)(x,y)=1−A_(h,+)(x,y),
    L(x,y)=logistic(β_noise log(y/x)),  x,y>0,
           1/2,                       x=0 or y=0.

Here logistic(v)=1/(1+exp(−v)). This specifies the law **after conditioning
on the entire noisy prefix**, not merely its unconditional marginals.
The joint posterior is arbitrary on the compatible support: θ∈Γ_i,
h_0∈{−1,+1}, x_0∈I_(z_0,h_0)^noise, where

    I_(z,t)^noise=[max(0,l_z−t a_noise),r_z−t a_noise), z>0,
    I_(0,t)^noise=[0,δ_tick/2−t a_noise).               (2)

An interval whose upper endpoint does not exceed its lower endpoint is
empty and omitted. The negative-sign interval is nonempty for every label.
No representative replaces the initial posterior or a subsequent latent
state in (1).

At level ℓ≥0 partition every nonempty I_(z_j,h)^noise into K=2^ℓ equal
price-width half-open subintervals J_(j,h,d)^(state,ℓ), d=0,…,K−1.
For source S=[a,b) and target T=[c,d), use claim 031's exact Gaussian
probability supremum W_(θ,Δ)^δ(S,T), including its trapped-zero convention.
The following explicit upper bound on A is used. Set

    r_−=log(c/b) if c>0, and −∞ otherwise,
    r_+=log(d/a) if a>0, and +∞ otherwise.

For β_noise=0 set L_−=L_+=1/2. Otherwise take the smaller and larger of
logistic(β_noise r_−) and logistic(β_noise r_+); if a=0 or c=0, enlarge
that interval to include 1/2. Logistic at infinite arguments means its
limit. Define

    Abar_(h,+)(S,T)=ρ_noise 1_(h=+1)+(1−ρ_noise)L_+,
    Abar_(h,−)(S,T)=1−[ρ_noise 1_(h=+1)+(1−ρ_noise)L_−].              (3)

These are upper bounds, not asserted exact joint-transition probabilities.
The separate maxima of P and A need not occur at the same pair (x,y).

For each θ, compute backward on feasible sign/subcell pairs:

    U_(θ,n,h,d)^(state,ℓ)=1,
    T_(θ,j,h,d)^(state,ℓ)=Σ_(t,e feasible at j+1)
       W_(θ,Δ_(j+1))^δ(J_(j,h,d)^(state,ℓ),J_(j+1,t,e)^(state,ℓ))
       Abar_(h,t)(J_(j,h,d)^(state,ℓ),J_(j+1,t,e)^(state,ℓ))
       U_(θ,j+1,t,e)^(state,ℓ),
    U_(θ,j,h,d)^(state,0)=min(1,T_(θ,j,h,d)^(state,0)),
    U_(θ,j,h,d)^(state,ℓ)=min(1,T_(θ,j,h,d)^(state,ℓ),
                            U_(θ,j,h,floor(d/2))^(state,ℓ−1)), ℓ>0,
    B_(i,θ)^(state,ℓ)=max_(h,d feasible at 0) U_(θ,0,h,d)^(state,ℓ),
    D_i^(state,ℓ)=max_(θ∈Γ_i) B_(i,θ)^(state,ℓ).                   (4)

The parent is always for the **same** sign. Let D_i^(a,ℓ) be claim 064's
support denominator at the same radius, catalogue and level, and set

    D_i^(joint,ℓ)=min(D_i^(state,ℓ),D_i^(a,ℓ)).                    (5)

1. **Domination and calibration.** For each label array, every ℓ and almost
   every actual null training prefix,

       P(V_i=v | U_i=u) ≤ D_i^(joint,ℓ)(u,v),
       0 < D_i^(joint,ℓ) ≤ D_i^(state,ℓ) ≤ 1.                    (6)

   Given any jointly measurable training-selected nonnegative label
   forecast q_i^δ(v|u) normalized over all v∈ℕ^n for each u, and any
   finite measurable L_i(U_i,V_i)∈ℕ, define

       E_i^(joint,L_i)=q_i^δ(V_i|U_i)/D_i^(joint,L_i)(U_i,V_i).   (7)

   It is finite and nonnegative on every label array, with
   E[E_i^(joint,L_i)|U_i]≤1 and P(E_i^(joint,L_i)≥1/α_i)≤α_i for
   i∈N₀. Claim 053/AX-53 gives FDR≤q_FDR |N₀|/m under arbitrary panel
   dependence, retaining the original m. These guarantees also hold for
   measurable nonnegative implemented scores bounded above by (7), including
   zero masks. The numerical prototype is not asserted to satisfy that bound.

2. **Refinement and reductions.** D_i^(state,ℓ) and D_i^(joint,ℓ) decrease
   weakly with ℓ. The combined score is at least claim 064's support score
   for the same q and level. No ordering with its uniform score is asserted:
   the observation laws differ. If β_noise=0, A is the constant matrix
   with probability (1+ρ_noise)/2 of staying in the same sign. If also
   ρ_noise=0, the future signs are independent fair signs.

   At a_noise=0, (5) equals claim 031's denominator for **every** β_noise.
   The raw state bound in (4) need not cancel its relaxation for nonzero
   β_noise; the minimum in (5) ensures this reduction. With H=2 signs,
   computation through level L costs O(nH² K² |Γ_i|), K=2^L.

3. **Nonzero models and a wrong-contract obstruction.** The premises admit
   positive Gaussian latent prices and dependent observation signs, including
   β_noise≠0. A concrete normalized numerator is claim 031's Gaussian
   label forecast, as in claim 064; it is not a power assertion.

   At a_noise=δ_tick, β_noise=0 and on z_0=…=z_n=0, (4) and (5) are
   [(1+ρ_noise)/2]^n at every level. The actual probability from X_0=0,
   H_0=−1 equals that value. Resetting the sign to an independent fair
   sign at each observation is invalid under persistence. In particular,
   ρ_noise=.9, n=5 and a forecast concentrated on the all-zero suffix
   give the false independent-model score 32>20 with actual probability
   .95^5=.7737809375 at nominal level .05. Under the correct denominator
   the same event's score is .95^(−5), which is below 20.

## Proof

**Observation map and transition.** For positive labels the clamp is
irrelevant since l_z>0: l_z≤x+t a_noise<r_z, intersected with x≥0,
gives (2). For label zero the condition is x+t a_noise<δ_tick/2, with
no extra lower restriction beyond x≥0. Thus (2) includes clamped zeros,
excludes the right boundary, and at a_noise=δ_tick/2 the positive sign
cannot emit label zero. For each fixed sign its feasible intervals over
all labels partition [0,∞). Each nonempty interval has a positive-length
positive part; the negative-sign interval is always nonempty.

For finite β_noise and positive x,y, L is strictly between zero and one;
at zero it is 1/2. Hence for ρ_noise<1 every A entry is strictly positive,
and every row sums to one. Multiplying P by these entries and summing
over the next sign gives a probability transition. The product law in
(1) is a specified finite-grid model, not an imported diffusion theorem.
For positive x∈S and y∈T, log(y/x) is between r_− and r_+ in (3).
Monotonicity of logistic, with endpoint order reversed for negative β,
bounds L between L_− and L_+. The extra 1/2 covers every pair with a
zero coordinate. Substitution in (1) proves 0<A≤Abar≤1 on S×T.

**Suffix bounds.** Let F_(θ,j)^state(x,h) be the probability of the fixed
remaining labels z_(j+1),…,z_n under (1), starting at (x,h). It lies in
[0,1], terminates at one, and satisfies the exact recursion

    F_(θ,j)^state(x,h)=Σ_t ∫_(I_(z_(j+1),t)^noise)
        A_(h,t)(x,y) F_(θ,j+1)^state(y,t) P_(θ,j)(x,dy).           (8)

This is the finite product law (1), with signs summed. On a target
subcell, induction bounds the suffix by U and the sign probability by
Abar. The remaining integral of one is the Gaussian probability of that
subcell, bounded uniformly over the source by W. Summing gives T in
(4). One also bounds the suffix, as does its already established parent
bound on the same sign's parent interval. The minimum therefore remains
an upper bound. Backward induction in j inside induction in ℓ proves
the bound for every exact feasible source (including zero) at every level.
This is claim 030's partition argument applied to (8); overlaps between
different signs' price intervals cause no double counting error, since
the signs label disjoint states of the joint process.

Taking the initial sign/subcell maximum covers every exact endpoint pair.
Taking the catalogue maximum covers every θ. Integrating over the actual
joint posterior ν_i^state proves domination by D_i^(state,ℓ). The
posterior is never factorized into independent endpoint and sign laws.

**Support comparison.** For every x≥0 and sign, clamping gives
|max(0,x+a_noise h)−x|≤a_noise. Summing the product of the A factors
over all future signs gives one for each fixed latent price path: sum the
last sign first and continue backward. Thus the marginal latent law
conditional on (u,θ,x_0,h_0) is precisely the Gaussian product, independent
of h_0. Forgetting h_0 preserves the same law given (u,θ,x_0). This checks
claim 064's support contract, with the marginal posterior of (θ,x_0).
Its D_i^(a,ℓ) also dominates the actual label mass. Their minimum proves
the first inequality in (6).

**Positivity and measurability.** For any feasible source subcell, a
positive exact point has a Gaussian transition assigning positive mass
to the positive part of every nonempty target subcell. Consequently W>0.
An actual A value at a positive pair is positive, so its upper bound
Abar is positive. At each step there is a nonempty negative-sign target.
Backward induction makes every feasible U strictly positive; the minimum
with a strictly positive parent retains positivity. Initial maxima are
over nonempty finite sets. Claim 064's support bound is also strictly
positive. All bounds are at most one, proving the remaining assertions
of (6). Interval formulas, Gaussian probabilities, logistic, finite sums
and extrema are measurable; the label space is countable. Each normalized
q_i^δ(v|u)≤1, so (7) is finite. A finite observation-selected level retains
pointwise domination at each (u,v). Apply AX-58 with counting measure on
ℕ^n and then claim 053/AX-53, with its original-panel masking rule. No
universal-inference or FDR theorem is re-proved here.

**Refinement, zero noise and cost.** Every child U is at most its own
parent. Taking maxima at time zero and over θ proves monotonicity of
the raw bound. Claim 064's support bound is monotone too; their minimum
is monotone. Equation (5) proves the score comparison to that support
score. Constant β=0 gives L=1/2 and the stated sign transition matrix.

At zero radius both sign intervals and their partitions coincide with
claim 031's ordinary cells. For any fixed source/target pair, the sum
Σ_t Abar_(h,t) is at least one, since it bounds a stochastic row.
Induct backward and through levels to compare each raw U for each sign
with claim 031's common scalar U: if all next-sign suffix bounds are
at least that scalar bound, the sum defining T is also at least the
scalar T. Its cap and parent are at least the scalar cap and parent,
so their minima preserve that ordering. At the terminal time both are
one. The raw maximum therefore is at least the ordinary denominator.
Claim 064's support denominator equals that ordinary denominator at
zero radius. Taking the minimum gives the claimed exact reduction,
even when the separate A upper bounds lose row normalization.
For β=0 their row sums equal one, giving equality already for the raw
recursion. The sum of squared dyadic subcell counts through L is O(K²);
each level sums over H² sign pairs, n steps and |Γ_i| parameters. The
additional support computation is of no larger order.

**Instances and failure.** Starting from x>0, take independent normal
log increments with the stated means/variances, and independent uniforms
on (0,1); after each latent step choose the positive sign when its uniform
is below A_(h,+)(x,y). This constructs a genuine positive model of (1),
also with nonzero β and ρ. Generate a finite training block by the same
rule. Future independent random inputs ensure the required conditional
law after its noisy prefix and endpoint/sign are supplied. This verifies
consistency of the model, not applicability to market observations.
Claim 031's Gaussian representative forecast normalizes on ordinary
labels and supplies a concrete q without assuming representative restarts
for this null.

For a_noise=δ_tick and label zero only sign − is feasible; its interval
is [0,3δ_tick/2). At β=0 the surviving transition weight is
r=(1+ρ_noise)/2. Level zero has W=1 on that repeated interval, so (4)
is r^n. The exact start x=0 stays trapped and emits successive zero
labels precisely when the signs remain negative, with probability r^n.
No refinement can increase the level-zero bound or go below that exact
probability. Thus (4) equals r^n at every level. The support bound is one
by claim 064, proving the same for (5). The independent-model denominator
uses r=1/2 instead. With a point-mass all-zero forecast its erroneous
score is 2^5 on that event and zero otherwise. The actual event probability
is .95^5, establishing the false-alarm counterexample. It does not refute
calibration under the correctly specified independent-sign law.

## Checks

`checks/065/state.py` evaluates (2)–(5) with mpmath, a finite Gaussian
catalogue and the Gaussian forecast instance. `checks/065/check.py` compares
six two-step joint endpoint/sign/parameter mixtures to independent Gaussian
quadrature, including trapped components and both signs of β. It checks
refinement, the support minimum, return-dependent zero-noise reduction,
half-tick empty states, the exact persistence counterexample, unit scaling,
and an observation-selected one-step refinement with an explicit forecast
tail in the moment bound. Invalid contracts are rejected. The preceding
`checks/d18-markov-inputs/check.py` checks the scalar A bounds and four
fixed-state two-step integrals. These are deterministic diagnostics, not
simulated size/power or outward enclosures.

## Not shown

- No evidence that the declared finite catalogue, radius, logistic noise
  law or noisy-prefix conditional Gaussian law holds for a real feed.
  A noise standard deviation is not an almost-sure radius. Estimating
  ρ_noise, β_noise or the null catalogue from training does not by itself
  provide conditional coverage of the actual later law.
- No arbitrary endogenous-noise law, noise feedback into latent volatility,
  variable spread, missing trade state, Gaussian/unbounded noise, or
  uniform observation kernel is covered by (1). The sign is not reset
  independently after an observation. The noise model is a declaration,
  not a consequence of its marginal moments or autocorrelation.
- No jump or SV null, unrestricted drift/variance profile, inferred pricing
  measure, useful power, superiority, or repeated-date guarantee. Gaussian
  latent-law rejection is a pricing-null claim only for the supplied N₀
  whose actual conditional laws satisfy the premises.
- No exact noisy CEV alternative likelihood. The separate normalized
  numerator input in `checks/d18-noisy-forecast` may be a candidate q,
  but restarts its own forecast at representatives and has no power result.
- No general convergence rate, equality to the exact likelihood after finite
  refinement, or ordering of different noise declarations. The raw bound
  may retain a large relaxation; (5) supplies only the stated support cap.
- Parts 1–3 and the panel conclusion are formalized in
  `lean/Standalone/D18SignNoise.lean` and `lean/Novel/D18SignNoiseProof.lean`,
  conditional on the stated actual joint law; FDR remains conditional on
  AX-53. The operation count, the remark that the raw bound need not cancel
  its relaxation, and the construction of a training block by the same
  rule remain informal. The formal nonzero model uses a fixed training
  record, as the contract permits.
- No certified evaluator yet. Finite precision is not asserted to give a
  lower score; D14's certified ordinary-cell code does not certify the
  weights, state sums or this observation contract.

## Prior art

The librarian's finite-state D18 sweep is in FINDINGS. Read that sweep,
the existing D18 input findings, claims 030–031/064, the refuted conditional
coverage and post-filtering targets, and the registered primary texts.
[wasserman2019universal], the sieve discussion and Section 6's upper-bound
discussion, already covers hidden-model testing when a dominating null
likelihood can be supplied; AX-58 is proved in
`lean/Novel/SplitLikelihoodDominatedProof.lean`. The partition argument
is the existing claim 030 application, not new general likelihood theory.

[diebold2010correlation], Section 2.1, (3)–(5), gives observed **log**
transaction price as the market maker's pre-trade expected efficient price
plus a half-spread times trade direction; direction can also be zero for
no trade. Its efficient-price notions, information updates and resulting
noise correlations are not the monetary Gaussian/logistic product law (1).
[jacod2013statistical], abstract and introduction, reports positive noise
autocorrelation in its empirical sample and develops moment estimators.
Neither supplies the exact transition (1), an almost-sure error radius,
or a conditional coverage certificate. These citations motivate retaining
state and return dependence; none of their statistical results is imported
as a premise. No new ledger input is used. The actual product law is our
explicit model assumption, exercised by the nonzero construction above.

The contribution is the application of the existing upper-likelihood
method to sign-specific cells and a declared joint return-dependent
transition, with the arbitrary joint training posterior, empty states,
zero-noise reduction and wrong-contract counterexample made explicit.

## Review

Reviewer, 2026-10-07, on branch `mathb/d18-finite-state-noise` at `a70cce2`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/065/` and `checks/d18-markov-inputs/`.
- **Inputs.** AX-53 and AX-58 are audited, and AX-58 is proved. Claims 030, 031, 053 and 064, the dependencies, are approved or formalized. [diebold2010correlation] and [jacod2013statistical] are registered.
- **Script.** My check is committed as `checks/review/065/reproduce.py`, with its rerun command and seed in its header. It is single-process and is not a CI `check.py`.

**The observation map (2): correct.**
- **Labels z > 0.** Clamping is irrelevant because l_z > 0, so l_z ≤ x + ta < r_z gives [max(0, l_z − ta), r_z − ta).
- **Label 0.** x + ta < δ/2, clamped values included.
- **Partition and empty states.** For each fixed sign these intervals partition [0, ∞). The negative-sign interval is never empty, and the positive-sign zero interval is empty once a ≥ δ/2.

**The weights (1) and (3): correct.** Each row of A sums to one. For x ∈ [a, b) and y ∈ [c, d), log(y/x) lies in (log(c/b), log(d/a)). Logistic is monotone, so taking the min and max of the endpoint values handles either sign of β, and adding 1/2 covers the pairs with a zero coordinate. The two parts of Abar bound A_+ above and 1 − A_+ above respectively.

**The recursion (4) and domination (6): correct.**
- **The recursion.** It is claim 030's partition argument on the exact sign-augmented suffix (8), with W bounding the price transition uniformly over the source subcell and Abar the sign weight. The parent bound is for the same sign. Signs are disjoint states, so overlapping price intervals do not double count.
- **The support comparison.** Signs never feed back into X, and summing the sign factors backward gives one. So the latent law given (u, θ, x₀) is the Gaussian product, with |Y − X| ≤ a under clamping. Claim 064's support contract therefore holds, and the minimum (5) is valid.

**The zero-radius reduction: correct.** At a = 0 the sign intervals coincide with claim 031's cells, and Σ_t Abar ≥ 1. So by induction the raw bound is at least claim 031's, and the minimum with 064's support bound (which equals 031's there) gives equality for every β.

**The counterexample: correct.** At a = δ and label 0 only sign − is feasible, on the interval [0, 3δ/2), with W = 1 and A(−, −) = (1 + ρ)/2. So the bound is 0.95⁵ at ρ = 0.9, equal to the exact probability from X₀ = 0, H₀ = −1, while independent fair signs give 2⁻⁵.

**Checks** (evidence, not proof).
- **(a) The weight bounds.** Over 800 subcell, sign, ρ and β cases (β ∈ {−8, −1, 0, 2, 12}, zero endpoints included), no brute-force A exceeds Abar.
- **(b) Domination by Monte Carlo.**
  - **Setup.** The joint price/sign process (1) with a coarse tick, a = 0.4 tick, ρ = 0.6 and β = ±5, the endpoint uniform on a random sign's feasible interval, and 400,000 draws.
  - **Result.** 20 and 19 frequent two-step label paths, no violations. The joint bound is below 064's support bound by a median factor of e^{1.6} and e^{2.0}.
- **(c) The counterexample.** D_state = 0.7737809375 at levels 0–3, exactly 0.95⁵. The simulated all-zero probability is 0.7735.
- **(d) The zero radius.** At β = 3 on 15 paths, D_joint equals claim 031's bound exactly, and D_state is never below it.
- **(e) The evidence cost of noise.**
  - **Setup.** A cent tick, a = half a tick, a $5 GBM null with κ = 0.3, 60 days, and signs from (1) with ρ = 0.5, β = 0. The numerator is claim 031's forecast.
  - **Result.** Median log E at levels 0–3:

    | Denominator | Level 0 | Level 1 | Level 2 | Level 3 |
    |---|---|---|---|---|
    | Support (claim 064) | −46.9 | −44.3 | −43.0 | −42.3 |
    | Joint (5) | −2.8 | −1.4 | −0.7 | **−0.4** |

  - **Reading.** The joint score is essentially the no-noise level of my claim-064 review (−0.36), so it removes the n log 2 support cost.
- **The author's checks.** I ran both afterwards. `checks/065/check.py` passes the six two-step posterior mixtures, the support minimum, the zero-noise reduction, empty signs and the counterexample. `checks/d18-markov-inputs/check.py` passes the transition suprema and joint integrals.

**Gaps.** None.

**Scope; "Not shown" is honest.** One point deserves emphasis.
1. **(e)'s near-free result comes from a strong declaration.** The error is exactly ±a, a two-point law like a bid–ask bounce. Given the sign, each label pins X to an unexpanded interval of width δ. A bounded but continuous error, claim 064's support contract, still costs about n log 2. So the gain is purchased by the model, and the counterexample shows that a misdeclared sign law breaks size.
2. **The declarations are empirical premises.** Whether a real feed's errors are two-point with a known radius, and follow the logistic transition, is not shown, as stated. Estimating ρ or β from training does not give conditional coverage.
3. **Not covered:** jump or stochastic-volatility nulls, power and certification, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red re-derived the sign-specific observation intervals, the monotone logistic weight bounds, the sign-augmented recursion with support minimum and its domination, the zero-radius reduction and the persistence counterexample; committed review script; strong-declaration scope stated

Formalizer B, 2026-10-07, on `formb/d18-finite-state-noise`. **Status: formalized.** The statement is `lean/Standalone/D18SignNoise.lean`, with
`statement := part1 ∧ part2 ∧ part3 ∧ panel`.
It is proved in `lean/Novel/D18SignNoiseProof.lean` (`statement_holds`), from `D18SignNoise{Sign,Rec,Law,Valid}`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** FDR is conditional on AX-53 through claim 026's `panel`. AX-58's step is proved directly with counting measure, through claim 064's `conclusions`. Claim 031's interval supremum `Wm` and forecast, and claim 064's support denominator and suffix bound, are reused. Nothing else is cited.
- **Encoding.** One name, with claim 031's tick δ > 0, labels and cells, and radius a ≥ 0.
  - A sign is a `Bool` (`true` is +1). `obs δ a x t = mlabel δ (max 0 (x + t·a))` is the observation.
  - `ilo`/`ihi` are (2)'s sign intervals, `Feas` says one is nonempty, and `isub` are its 2^ℓ equal-width subcells.
  - `Lsig`, `Asig` are (1)'s L and A. `lgMinus`/`lgPlus` are the logistic at r₋, r₊, with its limits at infinite arguments. `Lminus`/`Lplus` and `Abar` are (3).
  - (4) is `UsW δ a ρ β W`, stated for any per-step bound `W`; claim 065 takes claim 031's `Wm` with the Gaussian step moments. `Dstate` is the maximum over the catalogue and the feasible initial sign/subcell pairs. `Djoint` is (5), the minimum with claim 064's `Dn … Msupp`.
  - `jointLaw ρ β Δ θ x₀ h₀` is (1)'s law of the evaluation log returns and signs. It is the Gaussian product law of the returns times counting measure on sign paths, with density ∏_j A(h_(j−1), h_j, x_(j−1), x_j) along the latent path. `jointLawG` is the same for general Gaussian step moments.
  - The contract is random variables (U, Θ, X₀, H₀, R, H). Θ ∈ Γ and X₀ ∈ I_(z₀,H₀) almost surely, and the joint posterior is otherwise arbitrary and never factorized. The conditional law of (R, H) given (U, Θ, X₀, H₀) is `jointLaw`. The labels are `obs` of the latent path and its signs.
- **Part 1.**
  - (1) is a probability law, and 0 < A ≤ Ā ≤ 1 on every pair of nonnegative intervals.
  - Under the contract, for a.e. u and every v and level: P(V = v | U = u) ≤ D^joint ≤ D^state ≤ 1, with D^joint > 0.
  - E = q/D^joint at a data-selected level L(u, v) is finite. It has conditional and unconditional mean ≤ 1 and size P(E ≥ 1/α) ≤ α (and with >) for 0 < α < 1, and every lower measurable score keeps the mean.
  - **State bound.** The label path's probability under (1) is an integral over the returns of a finite sum over sign paths (`Qg`), with the exact first-step recursion (8). By claim 030's partition induction with the same sign's parent, `Qg ≤ U` on every feasible subcell, exact zero included (`Qg_le_UsW`). A label from sign t puts the next price in I_(z,t), so t is feasible. There A ≤ Ā, and `W` bounds the step uniformly over the source subcell.
  - **Support bound.** On V = v each latent price lies in claim 064's expanded interval. The returns' marginal law under (1) is the Gaussian product, because the sign paths' products of A sum to one. So claim 064's `Qh_le_Bn` applies.
  - Both bounds go through one disintegration over (U, Θ, X₀, H₀) (`dom_joint`).
- **Part 2.**
  - D^state and D^joint decrease weakly with the level, and for the same numerator and level q/D^(a) ≤ q/D^joint.
  - At β = 0, A_(h,t) = (1 + ρ)/2 if t = h, and (1 − ρ)/2 otherwise. If also ρ = 0, (1) is the Gaussian product times (2^(−n) · counting measure): independent fair signs, independent of the returns.
  - At a = 0, D^joint equals claim 031's D^(δ,ℓ) for every β. Both sign intervals are claim 031's cells, each row of Ā sums to at least one, and so each sign's raw U is at least claim 031's U. Claim 064's support bound is claim 031's there.
- **Part 3.**
  - Nonzero models. For every β and ρ, any training record, parameter and positive endpoint in a sign interval is realized: the law (1) on its own sample space, with constant (U, Θ, X₀, H₀), satisfies the premises.
  - The concrete numerator is claim 031's Gaussian cell forecast, normalized with positive masses.
  - At a = δ and β = 0 on the all-zero labels, D^state = D^joint = r^n at every level and for every catalogue, with r = (1 + ρ)/2. From X₀ = 0, H₀ = −1, the all-zero labels have probability r^n under (1).
  - With ρ = 0 this denominator is (1/2)^n, the independent fair-sign one. With ρ = 0.9 and n = 5 the actual probability is 0.95^5. The arithmetic is formal: 1/(1/2)^5 = 32 > 20, 0.95^5 = 0.7737809375, and 0.95^(−5) < 20.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53, with arbitrary dependence, lower scores and measurable zero masks at the original m.
- **Not formalized.** These are commentary only:
  - the operation count O(n H² K² |Γ|);
  - the remark that the raw state bound need not cancel its relaxation for nonzero β;
  - the proof's construction of a training block by the same rule (the formal instance uses a fixed training record, which the contract permits).
