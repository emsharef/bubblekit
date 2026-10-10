---
id: "016"
title: "D4: Theorem E with share survival and a terminal index-measurable density"
status: formalized
depends_on: [010]
axioms_used: [AX-06, AX-17]
formal: lean/Standalone/D4Recovery.lean
direction: D4
---
## Statement

This corrects Theorem E's ordinary-weight formula. It is conditional on
claim 010's common pricing model and share-survival input AX-17, whose source
audit is `fc89855`. The identifying restriction below is a terminal
Radon–Nikodym density measurable with respect to the terminal index. It is
not implied by observing index options or by calling a model one-factor.

**Setting and supplied observations.** Fix T>0. Use claim 010's finite positive
basket I=Σ_i n_i S_i, deterministic n_i>0 and starts s_i>0, I₀=Σ_i n_i s_i,
ω_i=n_i s_i/I₀, and β_i(T)=s_i−E_Q[S_(i,T)]. Keep its raw standard-system
filtration, positive continuous local-martingale constituents, supplied
normalized local-martingale index, and share probability Q̃_I with lifetime
τ^I. In particular, for A∈F_T,

    Q̃_I(A∩{T<τ^I}) = E_Q[(I_T/I₀)1_A].                 (1)

There is no replacement of this identity by a density for all of Q̃_I.
Let P be a physical probability equivalent to Q on F_T, and suppose its
population joint law of the terminal index and ordinary cap weights is
supplied. Denote the pricing index marginal by ν_T=Q∘I_T⁻¹, also supplied
as a full probability law on (0,∞) with finite first moment.

For the option interpretation, the declared observation operator is the
zero-rate European expectation operator: C_I⁰(K)=E_Q[(I_T−K)⁺] and
P_I(K)=E_Q[(K−I_T)⁺]. This claim takes ν_T as input. It does not extract ν_T
from a finite option panel, prove an option-surface inversion theorem, or
substitute market quotes for these expectations. Initial basket and price
panel information are population objects, not estimators from one path.

For conditional expectations, take finite measurable versions of I_T and
μ_i(T)=n_i S_(i,T)/I_T on the event of finite positive coordinates; set
I_T=1 and μ_i(T)=0 on its complement. This convention changes neither P-
nor Q-expectations and, by (1), affects no share-survival integral. Put
G_T=σ(I_T), as a sub-sigma-field of F_T. Supply Borel versions m_i:(0,∞)→[0,1]
with

    m_i(I_T)=E_P[μ_i(T)|G_T]     P-almost surely.          (2)

The physical population law fixes these functions P∘I_T⁻¹-almost everywhere.
Equivalence makes that enough for integration under ν_T. No regular
conditional probability on the entire raw path space is required.

**Identifying restriction.** At this fixed T, assume

    dQ/dP on F_T = Z_T = k_T(I_T)     P-almost surely,    (3)

for a Borel k_T:(0,∞)→(0,∞) with E_P[k_T(I_T)]=1.
There is no assertion of (3) for other maturities or for a density process
depending only on the current index at every time.

1. **Conditional invariance on survival.** Put

       p_I(T)=E_Q[I_T]/I₀ ∈ (0,1],
       R_T(A)=Q̃_I(A∩{T<τ^I})/p_I(T),   A∈F_T.          (4)

   For every bounded Borel function h of the terminal weight vector,

       E_Q[h(μ(T))|G_T]=E_P[h(μ(T))|G_T],
       E_(R_T)[h(μ(T))|G_T]=E_P[h(μ(T))|G_T].            (5)

   These are almost-sure equalities under the equivalent probabilities
   P,Q,R_T. Thus conditional weight laws agree under P, Q and the
   **survival-conditioned** share probability. No such equality is asserted
   for the unrestricted share probability Q̃_I.

2. **Corrected recovery formula.** Define the index survival subprobability

       η_T(B)=Q̃_I(T<τ^I, I_T∈B)
             =(1/I₀)∫_B x ν_T(dx),   B⊆(0,∞) Borel.    (6)

   For every constituent,

       n_i β_i(T)/I₀
         = ω_i − ∫ m_i(x) η_T(dx)
         = ω_i − (1/I₀)∫ x m_i(x) ν_T(dx)
         = ω_i − E_(Q̃_I)[1_{T<τ^I} m_i(I_T)].          (7)

   Equivalently the subtracted quantity is
   p_I(T) E_(R_T)[m_i(I_T)]. The survival factor cannot be dropped.
   The integrals are finite and independent of the choices of m_i on
   physical index-null sets or of share-measure extensions after τ^I.
   Therefore, among compatible models satisfying (3), the supplied physical
   joint law and ν_T determine each normalized bubble contribution uniquely.
   This is uniqueness conditional on model existence, not an existence theorem.

3. **Scope of the restriction and a necessary compatibility check.** For
   formula (7) alone, (3) may be replaced by the weaker mean restriction

       E_Q[μ_i(T)|G_T]=m_i(I_T),   for each i.             (8)

   Without (3) we do not claim (5) for every bounded h. Every compatible
   model must satisfy

       0 ≤ ∫ x m_i(x) ν_T(dx) ≤ n_i s_i,                 (9)
       Σ_i ∫ x m_i(x) ν_T(dx) = ∫ x ν_T(dx).             (10)

   Violation of (9) rules out the declared class, but these restrictions
   are not sufficient for a compatible local-martingale model. Equation
   (10) is automatic from the physical weights summing to one and marginal
   equivalence. Matching the sum of recovered contributions to the index
   defect is therefore not an independent overidentification test of (3).
   This claim does not show that (3) is testable from the supplied observations.

4. **The missing-survival formula fails even under (3).** In claim 010's
   two-proportional-name strict-price example, choose P=Q. Then k_T=1 and
   m_1=m_2=1/2. The charter's ordinary expression
   ω_i−E_(Q̃_I)[m_i(I_T)] is zero, using the constant continuation 1/2 on
   all paths. But the true contribution is (1−p_I(T))/2>0. Formula (7)
   returns that value. Simply replacing the physical inner variable by
   μ_i† does not fix the missing factor: P(T<τ^I)=1, so
   E_P[μ_i†(T)|G_T]=m_i(I_T) again. Survival must remain in the outer
   integration, or its mass must multiply the survival-conditioned mean.

## Proof

**Mechanism and existing result.** A density measurable with respect to a
conditioning sigma-field factors out of conditional expectations. Apply the
existing conditional-expectation pull-out and integral identities, followed
by claim 010's killed-weight identity. The underlying general mechanism is
standard change of probability, not a new recovery or conditional-expectation
theorem. Mathlib's `condExp_mul_of_stronglyMeasurable_left`,
`integral_condExp`, and `ae_eq_condExp_of_forall_setIntegral_eq` supply the
needed identities. No new stochastic input or general theory is reconstructed.

**Densities and conditional expectations.** Let D={T<τ^I}. Equation (1)
gives Q̃_I(D)=p_I(T)>0 by claim 010, so R_T is a probability on F_T.
Changing from Q to P in (1) gives

    dR_T/dP = I_T k_T(I_T)/(I₀ p_I(T)).                  (11)

Both (3) and (11) are strictly positive finite G_T-measurable densities,
integrable with mean one. Thus R_T, Q and P are equivalent on F_T; this
does not assert Q̃_I≪P on F_T. Measurable versions on the exceptional price
event have no effect by (1).

To apply the pull-out identity, put Y=h(μ(T)) and H=E_P[Y|G_T]. They are
bounded by the same deterministic bound. For either density D_T equal to
(3) or (11), the products D_T Y and D_T H are integrable. For A∈G_T,
the multiplier 1_A D_T is G_T-measurable. Pull-out followed by integration
of conditional expectation yields

    E_P[1_A D_T Y]=E_P[1_A D_T H].                       (12)

The density integration identity turns (12) into equality of the Y and H
set integrals under Q or R_T. H is G_T-measurable and bounded, so conditional
expectation uniqueness gives (5). This verifies exactly the integrability
and measurability hypotheses of the existing lemmas for the two densities.

**Recovery.** Set A={I_T∈B} in (1) and apply pushforward integration to
obtain (6); its mass is p_I(T), not one when the index is strict. Apply (5)
to coordinate functions on the weight cube (or their bounded extensions).
Claim 010 then gives

    n_i E_Q[S_(i,T)]/I₀
      = E_(Q̃_I)[μ_i(T)1_D]
      = p_I(T) E_(R_T)[μ_i(T)]
      = p_I(T) E_(R_T)[m_i(I_T)]
      = ∫ m_i(x) η_T(dx).

Subtract from ω_i and use (6) to obtain (7). The domination
0≤x m_i(x)≤x and the finite first moment of ν_T prove integrability.
Equivalence P∼Q implies ν_T∼P∘I_T⁻¹, hence also η_T≪P∘I_T⁻¹.
This proves version independence. Formula (6) proves independence of the
share extension after death. Each quantity on the right side of (7) is
fixed by the specified observation objects, proving conditional uniqueness.

**Weaker means and compatibility.** If only (8) holds, apply conditional
pull-out under Q with the nonnegative G_T-measurable multiplier I_T.
The products with μ_i and m_i are dominated by the integrable I_T, so

    n_i E_Q[S_(i,T)] = E_Q[I_T μ_i(T)]
                     = E_Q[I_T m_i(I_T)]
                     = ∫ x m_i(x) ν_T(dx).

Claim 010's nonnegative constituent defects prove (9) and (7).
Conditional-expectation linearity under P gives Σ_i m_i(I_T)=1 P-a.s.
Marginal equivalence transfers this equality to ν_T. Finite integration
then gives (10), independent of the unobserved full density (3).

**Counterexample.** Claim 010 supplies two copies of the same strictly
positive strict local martingale with equal holdings and starts. Its
ordinary weights are 1/2, its initial weights are 1/2, and
p_I(T)<1 at the strict horizon. Taking P=Q makes (3) hold with k_T≡1.
The unrestricted share expectation of the constant 1/2 is 1/2; its
survival-restricted expectation is p_I(T)/2. These give respectively
zero and (1−p_I(T))/2 after subtraction. AX-17 gives Q(D)=1 and P∼Q
gives P(D)=1, so killing only inside the physical conditional expectation
leaves that expectation unchanged. This completes part 4, conditional on
the strict-price example's cited inputs as disclosed in claim 010.

## Checks

`checks/016/check.py` uses exact rational terminal tables to verify density
normalization, conditional means under P,Q,R_T, all three integrals in (7),
and the missing-survival error. It also varies weight probabilities within
index-level cells while keeping the pricing index marginal fixed: this
breaks conditional invariance and shows why marginal data alone cannot
be substituted for (3). Those finite tables check measure algebra only;
they are not continuous local-martingale models or a dynamic
nonidentification counterexample. The strict-price counterexample in part 4
comes from claim 010, not from these tables. No simulation is used as proof.

## Not shown

No finite-option-panel recovery of ν_T, call-derivative identity, tail-free
estimation, kernel estimator or calibrated test. No proof that the full
kernel restriction is testable from constituent prices and index options,
and no converse from (9)–(10) to a pricing model. No recovery of P from
options, no ordinary conditional-law equality under Q̃_I after killing,
and no survival mass set to one in a strict-index model. A full population
joint law is supplied, not estimated consistently from one historical path.

No assertion covers signed holdings, zero-hitting constituents, dividends,
American options or an unspecified market pricing operator. The option
identified set from finitely many quotes and the cross-sectional dispersion
bound are separate D4 tasks.

The conditional Lean statement in `lean/Standalone/D4Recovery.lean` is
proved by `Novel.D4Recovery.proof` in `lean/Novel/D4RecoveryProof.lean`.
It assumes AX-06 and a supplied share probability satisfying (1); AX-17
provides that probability through claim 010, rather than through a new
share-measure construction here. Its model inherits claim 010's narrower
interface: continuity, nonnegativity and initial prices hold on every path,
and the index lifetime is supplied as a stopping time. Reconciling those
price premises with almost-sure versions on the raw space is not formalized.
The normalized index local-martingale property and the counterexample's
strict name remain supplied premises. No nondegenerate formal instance is
constructed here; the upstream AX-06/AX-17 instances remain degenerate.

## Prior art

Read claim 010 and its review, the refuted ordinary-weight claim, D4 findings,
AX-17 and its source audit, and the registered share-survival setup in
[kardaras2015strict] Theorem 2.12. That theorem supplies (1), not recovery
of constituent contributions. The standard conditional-expectation pull-out,
set-integral uniqueness and density/pushforward integration results already
exist in Mathlib; searched its ConditionalExpectation/PullOut, Basic and
RadonNikodym files before deriving this application. The project contribution
is the survival correction, exact terminal sigma-field restriction, and
separation of supplied marginal information from unproved option inversion.
There is no claim of novelty for change of probability. No additional
literature theorem is imported, and no general recovery theorem is reproved.

## Review

Reviewer, 2026-10-06, on branch `math/d4-killed-recovery` at `9d3098e`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/016/check.py`.
- **Inputs.** Claim 010, the dependency, is approved. AX-17's audit (`fc89855`) and AX-06 are as in my claim-010 review.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.** By (1) and (3), dR_T/dP = I_T·k_T(I_T)/(I₀p_I(T)). Like dQ/dP = k_T(I_T), this is a strictly positive, integrable, G_T-measurable density. For any such density D_T, the pull-out identity and set-integral uniqueness give E_{D·P}[Y | G_T] = E_P[Y | G_T] for bounded Y. That is (5) under Q and under R_T. P, Q and R_T are equivalent on F_T, and correctly no claim is made that Q̃_I ≪ P.

**Part 2: correct.**
- **The survival measure.** η_T(B) = Q̃_I(D, I_T ∈ B) = E_Q[(I_T/I₀)1{I_T ∈ B}] = (1/I₀)∫_B x ν_T(dx), the size-biased index law, with mass p_I(T).
- **The chain.** Claim 010's identity gives n_iE_Q[S_{i,T}]/I₀ = E_{Q̃_I}[μ_i 1_D] = p_I·E_R[μ_i] = p_I·E_R[m_i(I_T)] = ∫ m_i dη_T. Subtracting from ω_i gives (7).
- **Version independence.** It follows from ν_T ∼ P∘I_T⁻¹, and the integrability from 0 ≤ x·m_i(x) ≤ x. Uniqueness is correctly stated as conditional on a compatible model existing.

**Part 3: correct.** Under the weaker restriction (8), n_iE_Q[S_i] = E_Q[I_T μ_i] = E_Q[I_T m_i(I_T)] = ∫ x m_i dν_T by pull-out, which gives (7) and (9). Since Σm_i = 1 P-a.s. and the marginals are equivalent, (10) holds automatically. So (10) is not an overidentification test, as the claim says, and (3) is not shown testable.

**Part 4: correct.** With P = Q, k_T ≡ 1 and m_i = 1/2, the charter's expression gives 1/2 − 1/2 = 0, while the truth is (1 − p_I)/2. Killing only inside the physical conditional expectation changes nothing, since P(D) = Q(D) = 1.

**Checks** (evidence, not proof). I built 200 random finite terminal models in exact rational arithmetic: four index levels with three weight states each, a random physical P, and Q = k(I)·P. The survival measure is A ↦ E_Q[(I/I₀)1_A], with I₀ above every level so that p_I < 1, mimicking a strict index.
- **With an index-measurable density.** (5) holds under Q and R_T, and all three forms of (7) hold exactly, in all 200 models. Dropping the survival factor is wrong in all of them.
- **Off the class.** I tilted Q within index cells while keeping each cell's Q-mass, so ν_T is unchanged. Then (5) and (7) fail. This confirms that the index marginal cannot substitute for restriction (3).
- **Part 4's example,** with S = 1/R, R a 3-d Bessel process, T = 1 and p_I = E S₁ = 0.6827: the true contribution is 0.159, which (7) returns, against the charter formula's 0.
- **The author's check.** I ran `checks/016/check.py` afterwards. It passes: 7 index-measurable tilts, 14 recovery identities, the fixed-marginal non-factor tilt, and the missing-survival algebra.

**Gaps.** None.

**Scope, and what it means for D4.**
1. **This is the restated Theorem E my claim-010 review asked for.** It uses survival-weighted outer integration with η_T, the size-biased index law of mass p_I(T), or equivalently p_I times the survival-conditioned mean.
2. **The identifying restriction (3) is strong and, as stated, not shown testable.** It requires the whole terminal density dQ/dP on F_T to be a function of I_T alone. That is much more than "the pricing kernel is a function of the index", which the charter treated as natural. The claim correctly separates it from option observability.
3. **The observation objects are idealized.** They are the full pricing index marginal ν_T and the full physical joint law of (I_T, μ(T)), both supplied as population objects. Extracting ν_T from finitely many tick-limited quotes (experiment 014 shows far-wing calls sit at the one-cent floor) and estimating m_i from one historical path are the open D4 tasks, as "Not shown" says.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived conditional invariance via G_T-measurable densities, the survival-weighted recovery (7), the mean-restriction scope and the missing-survival counterexample; 200 exact models incl. off-class tilt; limits stated


Use claim 010's fixed-horizon killed-weight identity and existing Mathlib
conditional-expectation pull-out and density integration. Keep R_T a
probability conditioned on survival and η_T a subprobability. Neither can
be silently replaced by the full Q̃_I. The full F_T density assumption (3)
is distinct from specifying the marginal Radon–Nikodym derivative on G_T.
Formalize the fixed-time integration application, not a new construction
of AX-17 or option-implied marginals.

Formalizer, 2026-10-06, on `form/d4-recovery`. **Status: formalized.** The statement is `lean/Standalone/D4Recovery.lean`, proved in `lean/Novel/D4RecoveryProof.lean` (`proof`). There is no `sorry`, and the axiom audit is clean.
- **Setting** (`Model`). Claim 010's Lean model at horizon T, so it inherits that model's disclosed narrowings: AX-06's every-path price interface, and the lifetime supplied as a stopping time. Qs is any probability satisfying (1); AX-17 supplies one. P is equivalent to Q on F_T, stated with `trim`. T > 0 is not needed.
- **Versions.**
  - `indexV` is I_T on the event of positive coordinates and 1 elsewhere. The weights are claim 010's `ratio`. G_T = σ(`indexV`).
  - (2) is `WeightMean`: Borel mᵢ into [0,1] with mᵢ(I_T) = E_P[μᵢ | G_T] P-a.s. (3) is `IndexDensity`: dQ/dP = k(I_T) on F_T, an equality of trimmed measures.
  - ν_T = Q ∘ indexV⁻¹. R_T = p_I(T)⁻¹·Qs|_{T<τ}, a probability. η_T = (Qs|_{T<τ}) ∘ indexV⁻¹, a subprobability. Neither is replaced by the full Qs.
- **Part 1.** Under (3), R_T is a probability, and for every bounded Borel h of the weight vector, (5) holds under Q and under R_T.
  - The generic lemma `condExp_density` uses Mathlib's pull-out, `integral_condExp` and set-integral uniqueness.
  - R_T has the G_T-measurable density k(I_T)I_T/(I₀p_I(T)) (`R_density`), built from claim 010's `survival_trim` and transfer.
- **Part 2.**
  - η_T(B) = (1/I₀)∫_B x ν_T(dx) for Borel B.
  - Under (3), all forms of (7) hold: n_iβ_i(T)/I₀ = ω_i − ∫m_i dη_T, with ∫m_i dη_T = (1/I₀)∫x m_i(x) ν_T(dx) = E_Qs[1_{T<τ} m_i(I_T)] = p_I(T)E_{R_T}[m_i(I_T)].
  - Changing m on P∘I_T⁻¹-null sets does not change the integrals. The right side of (7) involves only (n, s, m, ν_T), which is the conditional-uniqueness content. No existence of a compatible model is asserted.
- **Part 3.** The mean restriction (8) alone gives (7) and (9) (`recovery`, by pull-out of I_T under Q). (10) holds from (2) alone, through Σμᵢ = 1 P-a.s. and ν_T ≪ P∘I_T⁻¹.
- **Part 4.**
  - In claim 010's two-name strict example with P = Q, k ≡ 1 and m ≡ 1/2 satisfy (2) and (3). The charter's expression is 0, while the truth and (7) give (1 − p_I(T))/2 > 0.
  - Given Q(τ^I = ∞) = 1 (AX-17's first conclusion), E_P[μᵢ†(T)|G_T] = E_P[μᵢ(T)|G_T] P-a.s. This is stated for the general model, not only the example.
