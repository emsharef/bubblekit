---
id: 006
title: "D3: local volatility alone cannot give power above uniform null size"
status: formalized
depends_on: [002, 003]
axioms_used: [AX-02, AX-03, AX-09]
formal: lean/Standalone/D3LocalVolNoGo.lean
direction: D3
---
## Statement

The stochastic interpretation is **conditional on AX-02, AX-03 and AX-09**.
The no-go statement is formalized in `lean/Standalone/D3LocalVolNoGo.lean`,
with proof `Novel.D3LocalVolNoGo.statement_holds` in
`lean/Novel/D3LocalVolNoGoProof.lean`. Its formal premises are `PricingFamily`
(the pricing laws are supplied, including existence and nonexplosion) and
stopped uniqueness `AX09`. The latter follows from
`Upstream.StoppedUniqueness`, whose genuine degenerate instance was audited
at `fd9b581`; source audits are in `ledger/AUDIT_LOG.md`. AX-02 and AX-03
are not used by this formal no-go proof: nulls and alternatives are defined
by the tail integral. Their interpretation as true and strict diffusion
laws still depends on the cited stochastic inputs.

Fix s₀ > 0, a finite T > 0 and a positive integer k. Prices are discounted
and have no dividends. Let Σ consist of Borel functions σ : (0,∞) → ℝ that
are nowhere zero and have locally integrable reciprocal square. For each σ,
let R = ν_σ be the pricing path law on E_T of the weak solution

    dS_t = σ(S_t) dW_t,    S₀ = s₀,

on a usual filtered probability space, absorbed at zero. The equation holds
before the first hit of zero, after which S stays zero. AX-09 gives weak
existence and uniqueness in law up to exit; AX-02 excludes exit at infinity,
as checked below. E_T is claim 003's Borel space of finite continuous
nonnegative paths on [0,T] starting at s₀.

A model is a pair (σ,P), where P is any probability on E_T equivalent to R.
P is the physical observation law; R is the pricing law. No restriction on
physical drift or likelihood ratios is imposed. The pricing law is that of
a driftless local-volatility diffusion. No upper-tail bound, common parametric
form, or global regularity bound is imposed on σ. For any c > 0 let
I∞(σ) = ∫_c^∞ x/σ²(x) dx, and define

    H₀ = {(σ,P) : σ ∈ Σ, P ∼ ν_σ, I∞(σ) = ∞},
    H₁ = {(σ,P) : σ ∈ Σ, P ∼ ν_σ, I∞(σ) < ∞}.

AX-03 identifies these as true-martingale and strict-local-martingale pricing
models on [0,T], respectively. Observe k independent paths under P. For any
Borel randomized test φ : E_T^k → [0,1], set

    size(φ) = sup_((g,P') ∈ H₀) E_((P')^⊗k)[φ].

Then

    E_(P^⊗k)[φ] ≤ size(φ)    for every (σ,P) ∈ H₁.            (1)

This still holds when Σ is restricted throughout to positive continuous
coefficients, and when observations are restricted throughout to P = ν_σ,
with the supremum in each case taken only over that subfamily's nulls. Both
restrictions may be imposed together. Composition covers every Borel
observation of the k paths, including any fixed finite sampling grid.

More explicitly, for each integer n > s₀ define

    σ_n(x) = σ(x)         for 0 < x ≤ n,
             σ(n)x/n      for x > n,                         (2)
    R_n = ν_(σ_n),
    A_n = {w ∈ E_T : max_[0,T] w < n},    p_n = P(A_nᶜ).

R_n is a true-martingale pricing law. There exists a physical probability
P_n ∼ R_n whose restriction to A_n equals P's, and for every such φ,

    |E_(P^⊗k)[φ] − E_(P_n^⊗k)[φ]|
        ≤ 1−(1−p_n)^k ≤ k p_n → 0.                          (3)

Thus every alternative physical observation law is in the total-variation
closure of the null physical observation laws. Total variation uses claim
003's convention sup_B |P(B)−P_n(B)|, with no factor two. The constant test
φ ≡ ε attains size and power ε, so (1) is sharp. For a sequence of tests with
finite k at each sample size and fixed T, limsup uniform null size ≤ ε
implies limsup power ≤ ε at each fixed alternative. This does not follow
from merely pointwise-null asymptotic size control.

## Proof

**Mechanism and existing inputs.** Approximate an alternative law by null laws
agreeing as measures on events with probability tending to one. Claim 002
supplies the coefficient completion. Claim 003 supplies the bounded-observation
mechanism; its nulls were allowed to freeze at an upper price. The new work
checks that (2) stays in the diffusion family, applies stopped uniqueness,
and constructs equivalent physical laws with the required agreement. AX-09
supplies the stochastic uniqueness result; it is not re-proved. The physical
construction only adds and rescales restricted measures.

**Existence without exit at infinity.** For any σ ∈ Σ, the drift μ = 0
satisfies μ/σ² = 0, so AX-09's existence hypotheses hold on (0,∞).
In AX-02's scale notation, ρ(x) = exp(0) = 1 and s(x) = x−c. Hence
s(∞) = ∞. AX-02's scale form says exit at the right endpoint requires
s(∞) < ∞, so this solution cannot exit there. Its only possible finite exit
is at zero, with the stipulated absorption. It therefore has finite continuous
nonnegative paths for all finite times. This applies to every admissible
completion as well. We use the registered Feller test here, not an unregistered
nonexplosion lemma or a reconstruction of boundary theory.

**Admissible nulls.** Take claim 002's g_p with R = n and p = 1. Its hypotheses
hold for the current σ, and its conclusions give that σ_n is Borel, nowhere
zero, and has locally integrable reciprocal square. In particular the possibly
irregular coefficient below n is unchanged. Its computed tail integral is

    ∫_n^H x/σ_n²(x) dx = (n²/σ(n)²) log(H/n) → ∞.

AX-09 and the preceding paragraph supply the absorbed weak solution; AX-03
makes it a true martingale. Thus R_n is a null pricing law. If σ is positive continuous,
claim 002 also gives positivity and continuity of σ_n, including at n. The
smaller family is therefore closed under the same null approximation. Both null
families are nonempty: σ(x) = x with P = ν_σ belongs to both and has infinite JKP integral.

**Equality of stopped laws.** On real continuous paths define

    ϑₙ(w) = inf{t ≥ 0 : w(t) ∉ (0,n)},    inf ∅ = ∞,
    (Hₙw)(t) = w(t ∧ ϑₙ(w)).                             (4)

On [0,T], take ϑₙ = ∞ if no exit occurs by T; the resulting stopped path
is the restriction of (4) to that horizon. The rule is measurable in the
canonical filtration: {ϑₙ ≤ t} is the event that the minimum distance of w on
[0,t] from the closed set ℝ∖(0,n) is zero. Before ϑₙ every path is in
(0,n); for a path starting outside, ϑₙ = 0. AX-09's premise thus holds for
every path. Hₙ is Borel: its coordinates evaluate a continuous path at the
Borel times t∧ϑₙ, and rational-time coordinates generate the Borel sigma
field of continuous-path space.

Stop the original and completed weak solutions using (4). Their coefficients
agree on (0,n), satisfy the Engelbert–Schmidt conditions there, and have the
same initial point s₀ ∈ (0,n). Each stopped process solves AX-09's stopped
equation on (0,n), with the same initial value and coefficient, and stays at
the endpoint reached. Values of the coefficient at that endpoint do not affect
the stopped integral. Proposition 9.1 as registered in AX-09 gives

    (Hₙ)_#R = (Hₙ)_#R_n.                                   (5)

This is equality in law; it asserts neither equality of the unstopped paths
nor a common probability space carrying their Brownian motions.

**Pricing laws agree below the cutoff.** Let Θ_n stop only at the first
closed-level hit of n. It is Borel by the same coordinate-evaluation argument.
On paths absorbed at zero, Θ_n and Hₙ agree, since such a path already stays
zero after reaching zero. Both pricing laws are supported on those paths, so
(5) holds with Θ_n as well. On the whole of E_T, Θ_n is the identity on A_n
and Θ_n^(-1)(A_n) = A_n. Thus Θ_n^(-1)(B∩A_n) = B∩A_n for every Borel B,
and the equal stopped laws give

    R(B∩A_n) = R_n(B∩A_n).                                (6)

In particular R(A_nᶜ) = R_n(A_nᶜ). Hits exactly at T lie in A_nᶜ. This
uses closed-level hitting, not an unproved equivalence with AX-04's open-exit
convention. No pathwise uniqueness or shared Brownian motion is asserted.

**Equivalent physical null laws.** Put r_n = R_n(A_nᶜ). If r_n > 0, then
P ∼ R and (6) imply p_n > 0. For Borel B define

    P_n(B) = P(B∩A_n) + (p_n/r_n) R_n(B∩A_nᶜ).              (7)

This is a measure, being a sum of nonnegative multiples of restricted measures.
Its mass is (1−p_n)+p_n = 1. It agrees with P on A_n and has complement mass
p_n. To check equivalence, P_n(B) = 0 exactly when both P(B∩A_n) = 0 and
R_n(B∩A_nᶜ) = 0, since p_n/r_n > 0. By P ∼ R and (6), the first condition
is equivalent to R_n(B∩A_n) = 0. Together the conditions mean R_n(B) = 0.
Thus P_n ∼ R_n.

If r_n = 0, then R(A_nᶜ) = 0 and p_n = 0. Set P_n = P. Equation (6) and
the zero complement masses imply R = R_n, so P_n ∼ R_n here also. This
handles the zero denominator explicitly. In both cases (σ_n,P_n) is an
admissible null model. For the subfamily P = R, (7) reduces to R_n, as does
the zero-mass case, so the construction preserves that subfamily too.

**Bounded-test comparison.** Since P and P_n have equal restrictions to A_n,
their k-fold products have equal restrictions to A_n^k. Each assigns it mass
(1−p_n)^k and its complement mass qₙ = 1−(1−p_n)^k. The integrals of φ on
A_n^k agree; each complementary integral lies in [0,qₙ]. Their difference
therefore has absolute value at most qₙ. This proves the first inequality in
(3); the union bound gives qₙ ≤ k p_n. Every path in E_T is bounded on [0,T],
so A_nᶜ decreases to the empty set as integer n increases, and p_n → 0 by
continuity of probability. No uniform rate over models is assumed.

Because (σ_n,P_n) is a null, (3) gives E_(P^⊗k)[φ] ≤ size(φ)+k p_n.
Let n tend to infinity to obtain (1). Taking indicators yields the same
bound for total variation. Composition with a Borel observation map gives
the sampling assertion. Positivity and continuity are preserved by (2), and
P = Q by (7). Constant tests give sharpness. Applying (1) separately at each
finite sample size and taking limsup proves the asymptotic assertion.

## Checks

No numerical experiment is a premise and no simulation was run. The proof
checks both boundary cases, a hit at T, continuity at the coefficient join,
and the distinction between uniqueness in law and pathwise uniqueness, plus
both r_n = 0 and r_n > 0 and both directions of measure equivalence. Claim
002 already formalizes the completion and logarithmic tail calculation.
Repository CI checks schemas, citations and the existing Lean project; it does
not prove this new claim.

## Not shown

- An unconditional stochastic result or a nondegenerate formal diffusion
  model. The Lean proof assumes the pricing laws through `PricingFamily`;
  weak existence and nonexplosion are not constructed or derived from
  Upstream fields. AX-09 has an audited genuine degenerate instance using
  Dirac laws at constant paths, not genuine diffusion laws. AX-02 and AX-03
  have only vacuous instances and supply the stochastic interpretation;
  they are not assumptions used in the formal no-go proof.
- Nonidentification of the monetary bubble from a known population path law
  when P = Q. Its terminal expectation, hence the unconditional defect, is
  determined by that law. This claim concerns uniformly sized tests from finite
  observations; close path laws need not have close expectations of the
  unbounded terminal price.
- A no-go result preserving a specified physical drift or likelihood-ratio
  bound, a multi-asset law,
  constituent dependence, shared tail restrictions, a known global coefficient
  bound, or option prices. This proof needs the family to contain the particular
  linear-tail null completions and the physical-law construction (7). The latter
  need not preserve the original physical dynamics or stopped physical law.
- A prohibition on consistency with merely pointwise-null asymptotic size,
  a uniform rate for qₙ, or equality of the full path laws. Equality (5)
  concerns their stopped laws only.
- The occupation-time identity (treated separately in claim 008),
  tail-restricted identified sets, cross-sectional pooling, or a useful
  positive-power test. Local volatility and positivity/continuity alone do
  not remove the obstruction. No practical superiority over another test
  is asserted.

## Prior art

Read the D3 sweep in `board/FINDINGS.md`, the refuted-claim directory, claims
002 and 003 (including the reviewer's local-volatility proposal), and the
registered source passages. [jarrow2011detect] Sections 1 and 5 already identify
the unobserved volatility tail as the extrapolation problem. Claim 002 makes
that obstruction exact for bounded coefficient information; claim 003 gives a
statistical obstruction in a larger class including prices frozen at upper
levels. This claim implements its reviewer's proposed extension to genuine
driftless local-volatility nulls. Math's committed physical-law handoff supplied
a stopped-law density lift and a comparison on A_n. Independently checking
that route yielded the simpler formula (7), retaining the full testing
conclusion for arbitrary equivalent physical laws without a density theorem.
The construction uses measure restriction, sum and rescaling, as claim 003
uses mixtures of measures.

[mijatovic2010martingale] Section 2 and Corollary 4.3 supply weak existence and
the martingale classification. [karatzas2015distribution] Proposition 9.1
supplies stopped uniqueness; the existing Feller input AX-02 rules out upper
explosion through its scale condition. These results are applied with hypotheses
checked, not re-proved. A search of `lean/Novel` and `lean/Standalone` found no
formal bounded-test disagreement or stopped-law comparison lemma; claim 003
supplies the reviewed prose step. The pinned Mathlib supplies
Measure.restrict_apply, measure addition and scalar multiplication, and
Measure.prod_restrict for the operations in (6)–(7); their general properties
are not re-proved. The wanted [bahadur1956nonexistence] remains
unread and is not invoked. No literature-wide novelty for the general statistical
mechanism is claimed; the contribution is this coefficient-class specialization.

## Review

Reviewer, 2026-10-06, on branch `mathb/d3-local-vol-no-go` at `57b8967`. I re-derived each step before reading the author's proof.
- **Inputs.** AX-02 and AX-03 are source-audited. AX-09 passed its source audit at `82c5cd4`, which is on this branch. Its specialization (stop rule ϑ = first exit from (0,n), the driftless Engelbert–Schmidt conditions on the bounded interval) is exactly what the proof uses. Claims 002 and 003, the dependencies, are approved.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below. Branch CI passes on `57b8967`.

**The null completions are admissible.** σ_n is claim 002's g_p with R = n and p = 1, so it is Borel and nowhere zero, with 1/σ_n² locally integrable. Positivity and continuity are preserved when σ has them. Its tail gives (n²/σ(n)²)log(H/n) → ∞, so AX-03 makes ν_{σ_n} a true-martingale law. Existence without exit at infinity holds because s(∞) = ∞ for zero drift (AX-02).

**The pricing laws agree below n, eq. (6).**
- The two coefficients agree on (0,n), with the same start s₀ ∈ (0,n). AX-09 (Proposition 9.1 of [karatzas2015distribution]) gives equal laws for the processes stopped at the first exit from (0,n).
- On absorbed paths, stopping at the first exit from (0,n) and stopping at the first closed-level hit of n coincide, so (Θ_n)_#R = (Θ_n)_#R_n.
- For w ∈ A_n, Θ_nw = w. For w ∉ A_n, Θ_nw reaches n by T, so it is not in A_n. Hence Θ_n⁻¹(B∩A_n) = B∩A_n, and (6) follows. A hit exactly at T is correctly placed in A_nᶜ.
- Only equality in law is used, as the claim stresses.

**The physical null, eq. (7), is right.**
- Total mass: (1 − p_n) + (p_n/r_n)·r_n = 1.
- P_n(B) = 0 ⇔ P(B∩A_n) = 0 and R_n(B∩A_nᶜ) = 0 ⇔ R(B∩A_n) = 0 (by P ∼ R) and R_n(B∩A_nᶜ) = 0 ⇔ R_n(B) = 0 (by (6)). So P_n ∼ R_n.
- p_n > 0 exactly when r_n > 0, because R(A_nᶜ) = R_n(A_nᶜ) and P ∼ R. The r_n = 0 case gives R = R_n and P_n = P.
- For P = R, (7) collapses to R_n, so the P = Q subfamily is closed.
- This simpler construction replaces the density lift of math's handoff, and it is sound.

**The bound, eq. (3), and the conclusion (1) follow.** P^⊗k and P_n^⊗k agree on A_nᵏ, which has mass (1 − p_n)ᵏ under both. So |E φ − E_n φ| ≤ 1 − (1 − p_n)ᵏ ≤ kp_n. p_n ↓ 0 because continuous paths on [0,T] are bounded. Letting n → ∞ gives (1), the total-variation closure statement, and the limsup consequence.

**Checks** (evidence, not proof).
- **Finite-space check.** In 1,703 random trials on finite path spaces, I built R and R_n equal on A with equal complement mass, any P ∼ R, and random tests φ on k-fold products with k ≤ 3. (7) always gave a probability equivalent to R_n and equal to P on A, and the difference of test expectations never exceeded 1 − (1 − p)ᵏ.
- **Rate.** For the σ = x² alternative, my claim-003 simulation gave p_n = 0.119, 0.071, 0.026 and 0.008 at n = 3.5, 5, 10 and 20 (T = 1). The approximation is therefore slow, roughly like 1/n, and the bound kp_n for a realistic number of paths requires very large cutoffs. That does not affect (1), which takes the supremum over all nulls, and the claim asserts no uniform rate.

**Gaps.** None.

**This closes the scope point I raised on claim 003.** Claim 003's nulls included frozen prices. Here every null is a genuine driftless local-volatility diffusion, positive and continuous if the alternative is, under P = Q or any equivalent physical law. So "local volatility, positivity and continuity alone" cannot give power above uniform size, which is the right baseline for D3's restricted identified sets.

**Scope; "Not shown" is honest.** Two items D3 must carry:
1. **The physical-law construction (7) does not preserve physical dynamics.** P_n replaces P above n by a rescaled pricing law. So a D3 test that assumes a specified physical drift, or a bound on the likelihood ratio dP/dQ, escapes this no-go. The claim says so. Any positive-power D3 result must state exactly such a restriction, or a tail restriction on σ.
2. **Population identification is different.** Under P = Q with the full path law known, the defect is identified, as in claim 003 part 2. This claim concerns uniformly sized finite-sample tests only, as it says.

**Prior art.** It is cited correctly: [jarrow2011detect] for the extrapolation problem, claims 002 and 003, and [karatzas2015distribution] Proposition 9.1. Bahadur–Savage remains wanted and unread, and no general novelty is claimed.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the completion, stopped-law equality (6) via AX-09, the physical null (7) incl. equivalence and r_n=0, and bound (3); finite-space checks; scope honest (physical-drift/LR restrictions escape)


Claim 002 supplies the deterministic completion. The restricted-law
comparison, physical construction (7), product-event bound and no-go
conclusion are now proved using Mathlib measure operations. AX-09 enters
through `Upstream.StoppedUniqueness`, with its genuine degenerate instance
audited at `fd9b581`. Its weak-existence assertion is not an Upstream field:
`PricingFamily` explicitly assumes laws for all admissible coefficients,
with the required probability and absorbed-path properties. This is the
reduced formal scope. AX-02's nonexplosion argument and AX-03's martingale
classification remain part of the conditional stochastic interpretation,
not the Lean proof of the no-go statement.

Formalizer, 2026-10-06, on `form/d3-local-vol-no-go`. **Status: formalized**, with the reduced scope disclosed below. The statement is in `lean/Standalone/D3LocalVolNoGo.lean` and the proof in `lean/Novel/D3LocalVolNoGoProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **Inputs.** The statement is conditional on AX-09's stopped uniqueness in law, restated as `AX09` and derived from the new `Upstream.StoppedUniqueness` by `ax09_of_upstream`. That structure's instance is degenerate. The pricing laws are a **premise** (`PricingFamily`), not a construction: a law `ν_σ` exists for every σ ∈ Σ (AX-09's weak existence, with no exit at infinity by AX-02), each is a probability, and almost every path is nonnegative, starts at s₀ and is absorbed at zero. This is the reduced formal scope the notes above ask to disclose. AX-02's scale computation and AX-03 are not used formally: H₀ and H₁ are defined by I∞, as in the claim.
- **Encodings.**
  - Paths are continuous real paths on [0,T] with the trace σ-algebra. Tests are Borel on k paths, with values in [0,1].
  - Σ is claim 002's `Admissible`, and I∞ < ∞ is claim 001's `IInftyFinite`.
  - The flags `cont` (positive coefficients continuous on (0,∞)) and `pricing` (P = ν_σ) give all four families. Each restriction applies to alternatives and nulls alike.
  - σ_n is claim 002's `completion σ n 1`.
- **Proved.**
  - (1) at every alternative of each family.
  - For each integer n > s₀: σ_n is in the family with I∞ = ∞; equality (6); and the physical null (7), which is in the family, equal to P on A_n, and equal to ν_{σ_n} when P = ν_σ. Both r_n = 0 and r_n > 0 are handled.
  - The bound (3), both inequalities, and p_n → 0.
  - Sharpness at φ ≡ ε, and the limsup consequence.
- **Proof differences.**
  - The closed-level stop Θ_n is not needed. On absorbed paths, H_n leaves A_n-paths unchanged and maps every other path outside A_n, so B ∩ A_n agrees almost surely with its own preimage under H_n.
  - The measurability of H_n, which the claim argues through rational times, is proved in the Upstream file. The proof uses a countable dense set of times and joint measurability of evaluation on continuous paths.
- **Not separately stated.** Composition with a Borel observation map, and total variation, are immediate: a measurable function of a test is a test, and an indicator is a test.
