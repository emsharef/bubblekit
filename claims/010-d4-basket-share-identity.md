---
id: "010"
title: "D4: basket bubble additivity, finite-measure mixtures and killed weights"
status: formalized
depends_on: [006]
axioms_used: [AX-02, AX-03, AX-06, AX-09, AX-17]
formal: lean/Standalone/D4Basket.lean
direction: D4
---
## Statement

This is the corrected Theorem C. It is **conditional on AX-06 and AX-17**;
the concrete counterexample also uses AX-02, AX-03 and AX-09 through claim
006's diffusion family. All sources have passed audit; AX-17's source
audit passed at fc89855. The claim is formalized in
`lean/Standalone/D4Basket.lean` and `lean/Novel/D4BasketProof.lean` (`proof`).
Its AX-17 structure, `lean/Upstream/ShareProbability.lean`, was audited at
4a35c36 and has a genuine degenerate instance; this is not evidence for
the strict case. The formal counterexample assumes a supplied strict name.

**Model and versions.** Work at zero rates and dividends with finitely many
names i = 1,…,N, N ≥ 1, and fixed deterministic holdings n_i > 0. Each
S_i is a strictly positive continuous local martingale under one pricing
probability Q, with deterministic S_(i,0) = s_i > 0. Define

    I_t = Σ_i n_i S_(i,t),    I₀ = Σ_i n_i s_i,
    ω_i = n_i s_i/I₀,        β_i(t) = s_i − E_Q[S_(i,t)],
    β_I(t) = I₀ − E_Q[I_t].

For the share-probability part use the raw standard-system setting of
AX-17: F_t = F̃_(t+) and F∞ = σ(⋃_t F̃_t), without completion by all Q-null
events. The local-martingale assumptions above are on this right-continuous
filtration. Supply the normalized index X as a strictly positive continuous
local Q-martingale in that same source setting, with X_t = I_t/I₀ Q-almost
surely at each finite t. Its source lifetime is τ^I = τ^X of AX-17;
supply also that τ^I is an F-stopping time, as the Lean statement requires.
The index local-martingale property is an explicit premise here; finite-sum
closure is not imported as an unaudited stochastic lemma or claimed as a
new proof. No nonexplosive-only path space or usual completion is substituted
for AX-17's raw system. Exceptional explosion paths remain in that space.

All price coordinates have F_t-measurable versions. Ordinary ratios μ_i(t)
are defined as n_i S_(i,t)/I_t whenever all coordinates are finite positive,
and as zero otherwise. This bounded measurable convention agrees with
ordinary cap weights Q-almost surely at every finite time; their sum is one
there. AX-17 will also make the convention irrelevant on the share-survival
event, at each fixed time. No ordinary ratio is assigned a limiting value
on an explosion path by taking an undefined infinity divided by infinity.

**1. Additivity and finite-measure mixture.** For every finite t ≥ 0,

    β_I(t) = Σ_i n_i β_i(t),
    0 ≤ n_i β_i(t) ≤ β_I(t) < I₀.                            (1)

On F_t define terminal finite measures

    q_(i,t)(A) = E_Q[(S_(i,t)/s_i)1_A],
    q_(I,t)(A) = E_Q[(I_t/I₀)1_A].

They satisfy the exact measure identity

    q_(I,t) = Σ_i ω_i q_(i,t).                               (2)

Their total masses p_i(t) and p_I(t) lie in (0,1] and satisfy

    p_I(t) = Σ_i ω_i p_i(t),
    1−p_I(t) = β_I(t)/I₀.                                   (3)

Equation (2) concerns finite measures at a fixed time, not equality of
arbitrary full extensions of constituent share probabilities. If a name
has β_i(t)>0, its q_(i,t) is not a probability.

**2. Survival-adjusted hazards.** If, in addition, the p_i are absolutely
continuous on [0,T], set h_i(t)=−p_i′(t)/p_i(t) almost everywhere. Then
p_I is absolutely continuous, and its hazard satisfies

    h_I(t) = Σ_i [ω_i p_i(t)/p_I(t)] h_i(t)                  (4)

almost everywhere. The coefficients in brackets sum to one. In general
(4) is not the mixture with the constant initial weights ω_i. Absolute
continuity is an extra condition, not a consequence asserted here.

**3. Killed weights and bubble shares.** AX-17 supplies a share probability
Q̃_I satisfying, for each finite t and A ∈ F_t,

    Q̃_I(A∩{t<τ^I}) = E_Q[(I_t/I₀)1_A].                     (5)

Put μ_i†(t)=μ_i(t)1_{t<τ^I}. Each μ_i† is a bounded nonnegative
supermartingale under Q̃_I, with initial value ω_i almost surely. For
every finite t,

    Σ_i μ_i†(t) = 1_{t<τ^I}             Q̃_I-almost surely,
    E_(Q̃_I)[μ_i†(t)] = n_i E_Q[S_(i,t)]/I₀,
    ω_i − E_(Q̃_I)[μ_i†(t)] = n_i β_i(t)/I₀.                (6)

Consequently μ_i† is not a martingale on [0,T] exactly when β_i(T)>0.
Also Q̃_I(τ^I≤t)=β_I(t)/I₀. These conclusions are independent of how the
share measure is extended after its lifetime. They do not assert a
supermartingale property or an expected-loss formula for ordinary weights
continued after explosion.

**4. The ordinary-weight assertion is false.** Two identical strictly
bubbly names have ordinary weights 1/2. Their constant continuations have
zero expected loss under every probability, whereas (6) gives a positive
loss for their killed weights at a strict horizon. More generally, if all
ordinary weights are supermartingales under one probability and sum to one
at each time almost surely, all are martingales. Thus Theorem C(3) cannot
hold for ordinary weights while preserving that sum.
The Lean counterexample takes a name with E_Q[S_T]<s₀ as a premise;
it does not restate the existence of the CEV example through claim 006's
diffusion family.

## Proof

**Mechanism and general results.** Finite linearity of expectation and of
measures with densities gives (1)–(3). The share-survival identity transfers
set integrals of bounded weights back to constituent values under Q; the
usual characterization of conditional expectation by set integrals then
transfers the supermartingale inequality. These are applications of existing
integration results. AX-17 supplies the probability construction, not the
basket identities or killed-weight inequality. No exit-measure construction,
change-of-numéraire calculus or general conditional-expectation theorem is
re-proved here.

**Integrability and additivity.** AX-06 applies to each S_i: it is an
adapted nonnegative local martingale on a right-continuous filtration, with
integrable deterministic start. Thus S_(i,t) is integrable and
0 < E_Q[S_(i,t)] ≤ s_i. Strict positivity of the expectation follows from
strict positivity almost surely. Finite integral linearity gives
E_Q[I_t]=Σ_i n_i E_Q[S_(i,t)]. Subtract this from I₀ to obtain (1);
nonnegative summands give its lower bounds, and E_Q[I_t]>0 gives its
strict upper bound. At each t the defining nonnegative integrable densities
make the q's finite measures. Applying the same finite linearity on every
A ∈ F_t proves (2). Their masses and (3) follow by taking A=Ω.

If β_i(t)>0, q_(i,t)(Ω)=1−β_i(t)/s_i<1, so it cannot be a probability
restriction. In fact if s≤t and β_i(s)≠β_i(t), then q_(i,s) and the
restriction of q_(i,t) to F_s already disagree on Ω. A family with this
property cannot be the restrictions of a single probability on the
original sigma fields. This is why (2) does not license the charter's
unqualified global probability mixture.

**Hazards.** AX-06 makes every p_i nonincreasing. On the additional
absolute-continuity hypothesis, its derivative is nonpositive almost
everywhere. Since p_i(t)≥p_i(T)>0 on [0,T], division by p_i is legitimate.
Differentiate the finite sum (3) outside the union of its finitely many
exceptional sets and divide by p_I(t)>0. Replacing −p_i′ by p_i h_i gives
(4); (3) makes its coefficients sum to one. Only the finite-sum derivative
and the definition of hazard are used.

**Index survival input and measurable versions.** The supplied X has the
normalization, positivity, local-martingale property and raw standard-system
base required by AX-17. Apply that input to obtain Q̃_I and τ^I; substitute
X_t=I_t/I₀ in its right side to get (5). In particular
Q̃_I(t<τ^I)=p_I(t). The supplied stopping-time premise for τ^I makes the
survival indicator and μ_i†(t) F_t-measurable. We do not derive this premise
from AX-17's formal path conventions: values at the lifetime are
unconstrained, including a possible first level exceedance exactly there.

For fixed t the event on which one of the price coordinates is not finite
positive has Q-probability zero. Equation (5) shows that its intersection
with {t<τ^I} has Q̃_I-probability zero too. Thus on survival the bounded
ratios sum to one, Q̃_I-almost surely. After killing their sum is zero.
This proves the first assertion of (6). It also deals with all versions
chosen on the original null events without presuming Q̃_I≪Q on F_t.

**Weight transfer and conditional inequality.** Equality (5) is equality
of two finite measures on F_t. Integrating any bounded nonnegative
F_t-measurable function against these equal measures is valid. In particular,
for A ∈ F_t, cancellation under the original Q, where the prices are finite
positive, gives

    ∫_A μ_i†(t) dQ̃_I
       = E_Q[1_A μ_i(t) I_t/I₀]
       = (n_i/I₀) E_Q[1_A S_(i,t)].                         (7)

For 0≤s≤t and A∈F_s, AX-06's conditional inequality and (7) yield

    ∫_A μ_i†(t) dQ̃_I
       ≤ (n_i/I₀) E_Q[1_A S_(i,s)]
       = ∫_A μ_i†(s) dQ̃_I.

Since μ_i† is adapted and bounded in [0,1], this set-integral inequality
is precisely the supermartingale criterion. Setting A=Ω in (7) proves
its expectation identity; subtracting from ω_i proves the loss identity.
At time zero (5) has total mass one, and it also transfers the deterministic
initial ratios, giving μ_i†(0)=ω_i almost surely.

For completeness, the exact strictness assertion checks the conditional
loss rather than inferring it merely from the word "bubble". If β_i(T)>0,
(6) gives a strict decrease in expectation, excluding a martingale. If
β_i(T)=0, supermartingale expectations, nonincreasing between 0 and T,
are equal throughout. For each s≤t≤T the nonnegative conditional loss
μ_i†(s)−E[μ_i†(t)|F_s] then has mean zero, so is zero almost surely.
This is the martingale equality. Taking A=Ω in (5) and using (3) proves
the asserted lifetime probability. The argument used only (5), hence
works for every allowed extension giving that identity.

**Counterexample and sum obstruction.** Claim 006's supplied diffusion
family includes σ(x)=x². AX-09 gives weak existence, AX-02 excludes both
infinite exit (scale s(x)=x−1) and zero exit (∫₀¹ x^(−3)dx=∞), and AX-03
gives strictness on positive finite horizons from ∫₁∞ x^(−3)dx=1/2.
Use that positive diffusion S for both constituents with holdings one.
Then I=2S, ω_1=ω_2=1/2, and the normalized index is S itself. The ordinary
weights are 1/2 at every original price path; define their continuations
as the same constants wherever a share construction adds explosion paths.
They have zero deficit under every probability. Yet the contribution of
each name to the normalized bubble is (1−E_Q[S_T])/2>0. This disproves
the ordinary-weight equality, conditional on the cited diffusion inputs;
it does not require constructing a new share probability on a completed
Brownian space. If one uses a source-compatible raw share construction,
(6) gives the corrected killed-weight deficit.

Finally, for any finite family of supermartingale weights summing to one,
the nonnegative conditional losses at s≤t sum to
1−E[1|F_s]=0. Each loss must therefore vanish, so every weight is a
martingale. The contradiction is structural, not a numerical effect.

## Checks

No numerical experiment was run. The proportional-name counterexample is
algebraic given a supplied strictly positive strict local martingale; the
CEV specification above checks that such a diffusion is included in the
audited inputs. When N=1, (6) reduces to μ_1†=1_{t<τ^I} and the index
survival identity, while the ordinary weight is one. For constant positive
prices, p_i=1, no finite killing occurs under the share probability, and
all deficits are zero. These are convention checks, not independent proofs.

## Not shown

- The Lean proof and AX-17 structure exist, with a genuine degenerate
  AX-17 instance. The result remains conditional on AX-06 and AX-17.
  AX-06's current Lean interface uses everywhere continuous real paths;
  `Basket` accordingly assumes continuity, nonnegativity and the initial
  price on every path. Applying that interface to raw spaces retaining
  exceptional explosion paths still needs faithful treatment of almost-sure
  price versions; that reconciliation is not formalized here. The lifetime's
  stopping-time property and the counterexample's strict name are supplied
  premises, not existence results of this formalization.
- The normalized index local-martingale property is explicitly supplied;
  this claim does not formalize finite-sum closure of local martingales.
- No global mixture of arbitrary constituent share-probability extensions,
  and no ordinary-weight statement after the index lifetime.
- No absolute continuity of survival curves without the additional
  hypothesis in part 2, and no survival-adjusted weights replaced by ω_i.
- No signed holdings, rebalancing, dividends or zero-hitting constituents
  in the share construction. The expectation algebra alone has wider scope.
- No Theorem E recovery formula, option-pricing convention, estimator,
  identified set from observed options, or statistical superiority result.

## Prior art

[jarrow2007complete] Definition 3 writes a fundamental value as conditional
expected cash flows under one pricing measure. Part 1 is a corollary of
expectation linearity, not a new pricing principle. [kardaras2015strict]
Definition 2.5, Proposition 2.8, Remark 2.10 and Theorem 2.12 give the
single-numéraire survival measure and its raw-filtration restrictions;
AX-17 registers precisely that input. Its Section 7 concerns simultaneous
reciprocal local martingales, not the terminal basket mixture used here.

Read `board/FINDINGS.md`, `claims/refuted/d4-ordinary-weight-loss.txt` and
the registered source passages. Located Mathlib's `integral_finsetSum`,
`integral_smul`, with-density integration and the set-integral
characterization of submartingales (apply it to the negative weights).
Those existing results supply the deterministic integration steps.
The claim's content is the basket specialization with correct normalization,
survival convention and conditional inequality, plus the refutation of
ordinary-weight strict loss. No literature-wide novelty claim is made.

## Review

Reviewer, 2026-10-06, on branch `mathb/d4-basket-claim` at `42234e2`. I re-derived each part before reading the author's proof.
- **AX-17.** Its source audit passed at `fc89855`, which is on this branch; the body is byte-identical to the AX-16 pass at `5365734`. Its statement is exactly what (5) uses: the Kardaras–Kreher–Nikeghbali survival identity Q̃_X(A∩{t < τ^X}) = E_Q[X_t 1_A] on a raw standard system, with uniqueness only on F_{τ^X−} and no density on all of F_t.
- **Other inputs.** AX-06 is used on the right-continuous raw filtration F̃_{t+}, which is all its statement needs; no completion is required. AX-02, AX-03 and AX-09 enter only through claim 006's family, which is approved.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.** E I_t = Σ n_i E S_{i,t} by linearity, so β_I = Σ n_iβ_i. Nonnegative summands and E I_t > 0 give 0 ≤ n_iβ_i ≤ β_I < I₀. The density identity (I_t/I₀) = Σ ω_i (S_{i,t}/s_i) gives (2) on every A ∈ F_t, and A = Ω gives (3), including 1 − p_I = β_I/I₀. The observation that q_{i,s} and q_{i,t}|F_s already differ on Ω whenever β_i(s) ≠ β_i(t) is right. It is exactly why the charter's global mixture dQ̃_I = Σω_i dQ̃_i cannot hold as stated.

**Part 2: correct.** Differentiating p_I = Σ ω_i p_i and dividing by p_I > 0 gives (4) with weights ω_i p_i/p_I. Absolute continuity is correctly an added hypothesis.

**Part 3: correct.**
- **Survival indicator.** τ^I is a stopping time of the right-continuous filtration, so μ_i† is adapted.
- **Equal measures.** (5) is equality of the finite measures A ↦ Q̃_I(A∩{t < τ^I}) and A ↦ E_Q[X_t 1_A] on F_t. Integrating the bounded μ_i(t)1_A gives (7). On the Q-full event of finite positive prices, (I_t/I₀)·n_iS_{i,t}/I_t = n_iS_{i,t}/I₀, and the Q-null exceptional event is also Q̃_I-null on survival by (5).
- **Supermartingale.** AX-06's set-integral inequality E_Q[S_{i,t}1_A] ≤ E_Q[S_{i,s}1_A] for A ∈ F_s transfers through (7). For bounded adapted processes that is the supermartingale criterion.
- **The rest of (6).** The expectation and loss identities, Σμ_i† = 1_{t<τ^I}, and Q̃_I(τ^I ≤ t) = β_I/I₀ follow.
- **Strictness.** The "not a martingale iff β_i(T) > 0" step is argued correctly in both directions.

**Part 4: correct.** For supermartingale weights summing to one, the nonnegative conditional losses sum to zero, so every weight is a martingale. That is the structural obstruction to the charter's C(3). The proportional-name example (σ = x², I = 2S, constant weights 1/2, killed-weight loss (1 − E S_T)/2 > 0) is a valid concrete instance, conditional on the cited diffusion inputs as stated.

**Checks** (evidence, not proof). I took a two-name basket with closed-form survival curves: S₁ = 1/R with R a 3-d Bessel process (strict, p₁(t) = 2Φ(1/√t) − 1), S₂ geometric Brownian motion (p₂ = 1), and n = (1, 3), so ω = (1/4, 3/4).
- **(3).** 1 − p_I = β_I/I₀ holds to 1e-6 at t ∈ {0.25, 1, 4}.
- **(4).** The finite-difference index hazard equals the survival-weighted mixture: 0.1092, 0.0657 and 0.0130.
- **The charter's version is wrong.** The constant-ω mixture gives 0.1131, 0.0886 and 0.0287, with an error growing in t. So the survival weighting in (4) is needed numerically, not just formally.

**Gaps.** None.

**Two readings worth carrying into the paper.**
1. **The weights in (4) are expected killed weights given survival.** By (6), E_{Q̃_I}[μ_i†(t)] = ω_i p_i(t), and Q̃_I(t < τ^I) = p_I(t). So the hazard-mixing weights are E_{Q̃_I}[μ_i†(t) | t < τ^I]. This makes the corrected hazard statement the natural replacement for "the ω-mixture of hazard curves".
2. **The charter's mixture is true on survival events.** When AX-17 also applies to each S_i/s_i, (2) reads Q̃_I(A∩{t < τ^I}) = Σ ω_i Q̃_i(A∩{t < τ^i}) for A ∈ F_t. That is the charter's mixture restricted to survival events, the precise sense in which it holds. The claim's "no global mixture of arbitrary extensions" is the right boundary.

**Consequence for D4's Theorem E.** The charter's Theorem E is built on C(3)'s ordinary-weight statement: bubble share = μ_{i,0} − E_{Q̃_I}[E_P(μ_{i,T}|I_T)]. With ordinary weights the right side is zero in part 4's example, while the bubble share is positive. Any D4 Theorem E must be restated with killed weights μ_i†, or with an explicit survival conditioning, before it is proved. The claim does not address Theorem E and says so; this is a flag for mathb's next step, not a defect.

**Scope; "Not shown" is honest.** It excludes the Lean/AX-17 structure, the raw-space reconciliation with AX-06's current interface, finite-sum closure of local martingales (the index premise is supplied explicitly), signed holdings, rebalancing, dividends, zero-hitting names, and Theorem E. The prior-art paragraph cites [jarrow2007complete] and [kardaras2015strict] for exactly what they supply.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived additivity, the finite-measure mixture, survival-adjusted hazards, killed-weight supermartingale via AX-17 (null versions handled) and the sum-to-one obstruction; numeric hazard check; Theorem E restatement flagged


Separate (1)–(4)'s finite integral and derivative algebra from (5)'s cited
probability construction. The latter must enter through AX-17's survival
identity with an honest rule-6 instance, not through assumed killed-weight
or basket-mixture conclusions. A constant normalized index supplies the
registered degenerate model; it is not evidence for the strict case.

For (6) use equality of finite measures on F_t, density integration and
the conditional-expectation set-integral criterion. Preserve the original
Q-null versus share-survival-null distinction. Keep the raw standard system,
the source lifetime and the supplied local-martingale index premise visible.
The formal statement must not claim that the current everywhere-continuous
AX-06 interface already resolves the raw-space version issue described above.

Formalizer, 2026-10-06, on `form/d4-basket`. **Status: formalized.** The statement is `lean/Standalone/D4Basket.lean`; the proof is `lean/Novel/D4BasketProof.lean` (`proof`). The finite-sum and derivative algebra is its own module, `lean/Novel/D4BasketAlgebra.lean`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** AX-06 enters through claim 004's restatement `AX06`. AX-17 is restated as `AX17` (raw `StandardSystem`, `Fr.rightCont` without completion, ambient σ-algebra ⨆ Fr_t, concrete `lifetime`). It is derived from the audited `Upstream.ShareProbability` by `ax17_of_upstream`; that instance is DEGENERATE (one-point raw system).
- **Model (`Basket`).** N ≥ 1 names with nᵢ > 0 and sᵢ > 0, adapted to a right-continuous F and local Q-martingales. Strict positivity holds only Q-a.s. at each time. Continuity, nonnegativity and the start sᵢ are on every path, because AX-06's current Lean interface asks for that. As the claim's "Not shown" says, this does not reconcile that interface with almost-sure versions on the raw space.
- **Ratios.** nᵢSᵢ/I where every coordinate is positive, and 0 elsewhere. The sum of the killed weights is 1_{t<τ^I} only Q̃_I-a.s.: `killed_sum` shows the Q-null event of a nonpositive price is share-survival-null through (5), with no Q̃_I ≪ Q assumed.
- **Index.** X is supplied with AX-17's premises (`ShareIndex`) and X_t = I_t/I₀ Q-a.s. at each t. **Narrowing:** the lifetime is a supplied premise, `IsStoppingTime F (lifetime X)`, now explicit in the prose as well. The formal premises leave values at the lifetime unconstrained, including a possible first level exceedance exactly there, so the stopping-time property is not derived here. The auditor's 4a35c36 line on `lean/Upstream/ShareProbability.lean` recommends this explicit premise.
- **Parts 1–3 as stated.**
  - (1)–(3): additivity, the mixture on every A ∈ F_t, and the masses.
  - (4): the derivative and hazard identity at every r where all pᵢ are differentiable, which gives the a.e. statement, together with absolute continuity of p_I.
  - (5)–(6): for every probability Q̃ satisfying (5), and an existing one from AX-17. Supermartingale, bounds in [0,1], initial value ωᵢ a.s., sum, expectation, loss, "not a martingale on [0,T] iff βᵢ(T) > 0", and Q̃(τ^I ≤ t) = β_I(t)/I₀.
- **Proof route.** (5) becomes an equality of finite measures on F_t (`survival_trim`), and the claim's route follows: density integration (`transfer`), the weight transfer (7), and the set-integral supermartingale criterion.
- **Part 4.**
  - Two copies of a supplied strict name (∫S_T < s₀): ordinary ratios 1/2 Q-a.s., ωᵢ = 1/2, and killed loss (s₀ − E S_T)/(2s₀) > 0 for every share probability. The claim takes the existence of such a name from claim 006's family through AX-02, AX-03 and AX-09; the statement does not restate that existence.
  - The sum-to-one obstruction (`obstruction`): supermartingale weights summing to one a.s. at each time are martingales.
