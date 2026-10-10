---
id: "009"
title: "D9: terminal L¹ convergence when continuous wealth is a true martingale"
status: formalized
depends_on: [001, 005, 007]
axioms_used: [AX-01, AX-02, AX-03, AX-06, AX-08, AX-10, AX-11, AX-14, AX-16]
formal: lean/Standalone/D9TrueLimit.lean
direction: D9
---
## Statement

This is a **conditional application of AX-16**, whose source audit at `d68deb2`
is on this branch, and of claims 005 and 007 with their named inputs. The
diffusion specialization also uses claim 001 under its coefficient and wealth
hypotheses. No new general convergence theorem is claimed.

Fix T>0 and a usual filtered probability space under Q. Let X be a finite,
adapted, continuous, nonnegative Q-local martingale, X₀=1, with

    Q(X_t>0 for every t∈[0,T])=1.

Extend it constantly after T. Let 0=t_(n,0)<…<t_(n,N_n)=T be arbitrary finite
deterministic grids with mesh tending to zero; nestedness is not required.
Fix 0≤π≤1. Let W^(n) be claim 005's cost-free fixed-share wealth, initially
one, with its zero-price rebalance rule, and let Vπ be claim 007's continuous
exponential, initially one:

    L=∫dX/X,       Vπ=exp(πL−π²⟨L⟩/2).

Both processes are nonnegative. Claim 007 gives their ucp convergence, and
claims 005 and 007 give terminal integrability and expectations at most one.

1. **True continuous limit.** If Vπ is a true martingale on [0,T], then

       E_Q|W^(n)_T−Vπ_T| → 0,
       E_Q[W^(n)_T] → 1,
       1−E_Q[W^(n)_T] → 0.                              (1)

   The family {W^(n)_T:n≥1} is uniformly integrable. This is a conclusion,
   not an additional uniform-integrability hypothesis. It is uniformity over
   grids at this fixed T, not over all time horizons.

2. **Terminal payoff prices.** In the setting of part 1, every fixed globally
   Lipschitz g:ℝ→ℝ has integrable payoffs and

       E_Q[g(W^(n)_T)] → E_Q[g(Vπ_T)].                   (2)

   This includes calls g(x)=(x−K)⁺ and puts g(x)=(K−x)⁺ for fixed K≥0.
   These are expectation prices under the specified Q, not an assertion about
   market option quotes or a pricing convention for collateralized bubbles.

3. **Covered D1 regimes and endpoints.** Suppose additionally X is claim 001's
   driftless weak diffusion, with s₀=v₀=1, Borel σ nowhere zero on (0,∞),
   1/σ² locally integrable there, and σ locally bounded there. Use that claim's
   wealth representation (W) and exit convention, and assume I₀=∞, so zero
   is inaccessible. Then (1)–(2) and terminal uniform integrability hold for

       0<π≤1/2, with no restriction on I∞;
       0<π≤1, if I∞=∞.                                 (3)

   Independently of these diffusion assumptions, π=0 gives W^(n)=V⁰=1;
   π=1 gives W^(n)=V¹=X in the general positive-price setting above. Hence
   at either endpoint the terminal L¹ distance is zero for every n, and
   terminal uniform integrability and (2) hold. At π=1 the common defect is
   1−E_Q[X_T], which need not be zero.

4. **What remains without the true-limit hypothesis.** In the general setting
   above, whether or not Vπ is true,

       limsup_n (1−E_Q[W^(n)_T]) ≤ 1−E_Q[Vπ_T].          (4)

   No reverse inequality is asserted when Vπ is strict. In particular this
   claim does not settle uniform integrability for a strict D1 underlying with
   1/2<π<1 and I₀=∞.

## Proof

**Mechanism and known result.** For nonnegative random variables converging in
probability, Fatou bounds the limiting mean from below. If the limit attains
a common upper bound on the means, those means converge. Apply the existing
varying-dominator convergence theorem to the absolute difference, dominated
by the sum. These are AX-16, from [etheridge2018continuous] Lemma B.8 and
Theorem B.9, printed p. 65, with convergence in probability supplying their
distribution and joint-convergence hypotheses. The final implication from
L¹ convergence to uniform integrability is reverse Vitali, already proved in
Mathlib. We only check the hypotheses for the specified D9 wealths.

**Integrability and convergence in probability.** For 0<π≤1, claim 005 makes
each W^(n) a nonnegative continuous local martingale starting at one. AX-06
gives terminal integrability and 0≤E_Q[W^(n)_T]≤1. At π=0 this is immediate
from W^(n)≡1. AX-14 and AX-06 give the same properties for Vπ. Claim 007's
positive-price conclusion gives W^(n)→Vπ ucp, hence terminal convergence in
probability. All these applications allow nonnested grids and a strict X.

**The true-limit application.** A true Vπ has E_Q[Vπ_T]=Vπ₀=1. AX-16(1)
applies to the nonnegative terminal grid variables and yields

    1 ≤ liminf_n E_Q[W^(n)_T]
      ≤ limsup_n E_Q[W^(n)_T] ≤ 1.

Thus their expectations converge to one. In AX-16(2) now use

    U_n=|W^(n)_T−Vπ_T|,  U=0,
    D_n=W^(n)_T+Vπ_T,    D=2Vπ_T.

All four types of variables are integrable. Both sequences converge to their
stated limits in probability by continuity of addition and absolute value.
Nonnegativity gives |U_n|≤D_n, D_n≥0 and D≥0. Finally E_Q[D_n]→2=E_Q[D].
Every hypothesis of AX-16(2) is now checked; its conclusion is E_Q[U_n]→0.
This proves (1). Reverse Vitali at p=1 supplies uniform integrability.
The pinned lemma is `MeasureTheory.unifIntegrable_of_tendsto_Lp`, equivalently
the reverse implication of `tendstoInMeasure_iff_tendsto_Lp_finite` in
`Mathlib/MeasureTheory/Function/UniformIntegrable.lean`. The L¹ norm bound
required for the full uniformly-integrable-family convention is also present:
E_Q|W^(n)_T|=E_Q[W^(n)_T]≤1. Measurability and integrability were checked above.

**Payoffs.** If g has Lipschitz constant C≥0, then

    |g(x)| ≤ |g(0)|+C|x|,
    |E_Q[g(W^(n)_T)]−E_Q[g(Vπ_T)]|
      ≤ C E_Q|W^(n)_T−Vπ_T|.

The first bound gives integrability on this probability space; the second and
(1) prove (2). Calls and puts each have Lipschitz constant one.

**D1 hypotheses and the endpoints.** AX-02's lower-endpoint test with I₀=∞
excludes a zero exit. Claim 007's coefficient specialization, using locally
bounded σ, identifies its Vπ with claim 001's specified wealth under (W).
For 0<π≤1/2 neither strictness condition of claim 001 holds, since I₀=∞.
When I∞=∞ as well, neither condition holds for any 0<π≤1. Thus Vπ is true
in each regime (3), and parts 1–2 apply.

At π=0 both definitions are identically one. At π=1 the grid factors telescope
on every strictly positive price path to X_t/X₀=X_t, including the unfinished
holding interval. For the continuous wealth, claim 007's stopped equation and
AX-10 uniqueness identify V^(1,m)=X^m; removal of its price stops identifies
V¹=X on [0,T]. The terminal sequence is therefore the same integrable random
variable for every n. It converges in L¹ with zero error, so reverse Vitali
again applies, whether X is true or strict. The payoff conclusion follows by
equality, and the common defect is exactly that of X.

**One-sided defect limit.** Without assuming E_Q[Vπ_T]=1, AX-16(1) still gives
E_Q[Vπ_T]≤liminf_n E_Q[W^(n)_T]. Subtracting from one gives (4); all quantities
are finite in [0,1]. There is no squeeze unless the limiting mean is one or
some additional argument supplies the missing upper bound on the means.

## Checks

At π=0 and π=1 the errors are identically zero, not merely asymptotically small.
For σ(x)=x² and cutoff one, I₀=∞ and I∞=1/2. At π=1/4, claim 005 gives a
strict W^(n) on every finite grid, while (3) makes Vπ true and (1) forces all
those positive defects to tend to zero. Thus loss of strictness in the limit
is compatible with uniform integrability; it does not establish its failure.
The same true-limit conclusion includes π=1/2. For σ(x)=x, both integrals are
infinite and (3) covers the entire interval 0<π≤1.

To check the obstruction to extending the squeeze argument, take a uniform
coordinate ω∈(0,1) and generic random variables

    U_n(ω)=1/2+(n/2)1_{(0,1/n)}(ω),  U(ω)=1/2,  n≥1.

Direct integration gives E[U_n]=1, E[U]=1/2 and E|U_n−U|=1/2, while
Q(U_n≠U)=1/n→0. For n>2K, the tail expectation above K is at least 1/2,
so this family is not uniformly integrable. These are **not** D9 trading
wealths and do not refute the remaining D9 conjecture. They show precisely
why positivity, convergence in probability and means bounded by one alone
do not prove the strict-limit case.

No new simulation is run or used as a premise. Experiments 008 and 009 supply
evidence in their own settings, not proof of (1), a rate, or the missing case.

## Not shown

No UI or two-sided defect convergence is proved for a strict continuous limit
with 1/2<π<1. No limit through absorption at zero, no signed-exposure conclusion
for π<0 or π>1, no rate, no uniformity over time horizons, and no convergence
of path-dependent unbounded payoffs or higher moments. No fee, financing or
tracking limit, market option-price identification, or cross-π statistical test.

The conditional Lean statement in `lean/Standalone/D9TrueLimit.lean` is proved
by `statement_holds` in `lean/Novel/D9TrueLimitProof.lean`. The specialization
of AX-16 used here is proved from existing Mathlib convergence lemmas, not
assumed as an input or carried by a new Upstream structure. AX-10, AX-11 and
AX-14 enter through claim 007's restatements of audited Upstream structures.
Their instances, like the available AX-06/AX-08 instances, are genuine but
degenerate; they do not discharge the hypotheses for the intended stochastic
models.

Part 3 remains conditional on AX-01 at this instance and claim 001's wealth
identification (W), encoded as the premise that Vπ is a martingale on [0,T]
iff `MUCondition π σ c` holds. Claim 007 identifies the explicit exponent;
its link to AX-01's opaque `StochExp` relation is not formalized. The Lean
proof does not construct the intended diffusion or establish that link.

## Prior art

The general convergence results are [etheridge2018continuous] Appendix B
(AX-16), and reverse Vitali already exists in Mathlib. Claim 007 applied
[emery1979lipschitz] to obtain convergence in probability; it required UI as
an extra premise for its L¹ conclusion. This corollary checks that premise
automatically in the true-limit D9 regimes and separates the unresolved
strict-limit case. No novelty is claimed for Fatou, varying-dominator
convergence, reverse Vitali, or the Lipschitz payoff inequality.

Read the D9 findings, claims 001/005/007 and their reviews, the refuted D1
threshold, the registered source's Appendix B, and the pinned Mathlib
convergence and uniform-integrability lemmas. No additional web search or
literature-wide novelty claim was needed for this application of the already
identified general results.

## Review

Reviewer, 2026-10-06, on branch `math/d9-true-limit-ui` at `29ea737`. I re-derived each step before reading the author's proof.
- **Inputs.** AX-16 has an `ok` source audit at `d68deb2`, which is on this branch. Its two parts (Fatou in probability; varying-dominator convergence with E D_n → E D) are exactly what the proof uses. Claims 001, 005 and 007, the dependencies, are approved; claim 007's (5) requires strict positivity, which part 1 assumes. The other inputs are as in my earlier reviews.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.** W^(n)_T ≥ 0 with E W^(n)_T ≤ 1 (claim 005, AX-06), and W^(n)_T → Vπ_T in probability (claim 007's ucp limit).
- **The means converge.** E Vπ_T = 1 forces 1 ≤ liminf E W^(n)_T ≤ limsup ≤ 1, by AX-16(1).
- **L¹ convergence.** AX-16(2), with U_n = |W^(n)_T − Vπ_T| → 0, dominators D_n = W^(n)_T + Vπ_T → 2Vπ_T, and E D_n → 2, gives E U_n → 0.
- **Uniform integrability** then follows by reverse Vitali, with the L¹ bound E W^(n)_T ≤ 1.
- **Scope of the uniformity.** It is over grids at fixed T only, as stated.

**Part 2** is the Lipschitz bound |E g(W) − E g(V)| ≤ C·E|W − V|, plus integrability from |g(x)| ≤ |g(0)| + C|x|. It is correct, and calls and puts are covered.

**Part 3: correct.** Claim 001 with I₀ = ∞ makes Vπ strict exactly when π > 1/2 and I∞ < ∞. So Vπ is true for 0 < π ≤ 1/2 (any I∞, including π = 1/2) and for all 0 < π ≤ 1 when I∞ = ∞. Claim 007's identification needs σ locally bounded, which is assumed. The π = 1 endpoint is an identity: the grid factors telescope to X, and V¹ = X by claim 007's stopped equation and uniqueness. So the L¹ error is zero even for a strict X, with common defect 1 − E X_T.

**Part 4** is AX-16(1) alone, and the claim correctly asserts no reverse inequality.

**The counterexample is right,** and it isolates what is missing. E U_n = 1/2 + (n/2)(1/n) = 1, E|U_n − U| = 1/2 and Q(U_n ≠ U) = 1/n. The family is not uniformly integrable. As the claim says, these are not trading wealths.

**Checks** (evidence, not proof). I took σ = x² (S = 1/|x₀ + B|, strictly positive, I₀ = ∞, I∞ = 1/2) at T = 1, with an exact fine grid of 32,256 steps and 4,000 paths. V_T = S_T^π exp(½π(1−π)∫S² du) by the trapezoid rule, and W^(N)_T comes from the claim-005 recursion. N = 4, 16, 64, 252, 1008.
- **π = 1/4, a true limit (part 1).**
  - E V₁ = 1.003 ± 0.006.
  - E W₁ = 0.949, 0.971, 0.978, 0.986, 0.994.
  - E|W₁ − V₁| = 0.076, 0.052, 0.038, 0.024, 0.014 (SE at most 0.005).
  - This is consistent with (1), and with my claim-005 simulation's grid defects.
- **π = 3/4, a strict limit (the case part 4 leaves open).**
  - E V₁ = 0.846 ± 0.010, against the exact 0.8465 (claim 001 and experiment 006).
  - E W₁ = 0.788, 0.810, 0.818, 0.826, 0.836.
  - E|W₁ − V₁| = 0.078, 0.054, 0.040, 0.026, 0.015.

**Gaps.** None.

**On the open strict case, for math.** In this example L¹ convergence, and hence uniform integrability and the two-sided defect limit, appears to hold in the strict regime too. The error falls at the same rate as in the true regime, and E W₁ approaches E V₁ from below. Simulation cannot exclude mass escaping in rare paths, so this is evidence, not a reason to extend the claim. The counterexample also shows that abstract arguments will not settle it: the extra structure has to come from the trading wealth itself. That makes "1/2 < π < 1 with I∞ < ∞ and I₀ = ∞" a concrete next D9 target, with a numerical expectation already in hand.

**Scope; "Not shown" is honest.** It excludes the strict-limit case, absorption at zero, signed exposures, rates, uniformity over horizons, and costs. The Lean status is accurate, including the inherited vacuous AX-01 and AX-03 instances and the unproved (W).

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the AX-16 application (Fatou squeeze, varying-dominator L1, reverse Vitali), payoff bound, D1 regimes and endpoints; simulation both regimes; strict case 1/2<pi<1 honestly left open


The formal target is this application of claims 005/007, the expectation
squeeze, the D1 regime checks and the payoff bound. Reuse Mathlib's existing
convergence lemmas and AX-16 as audited; do not reconstruct general convergence
theory or stochastic calculus. Keep both the true-limit hypothesis and the
separate π=1 strict-underlying endpoint visible in the statement.

Formalizer B, 2026-10-06, on `formb/d9-true-limit`. **Status: formalized.** The statement is in `lean/Standalone/D9TrueLimit.lean` and the proof in `lean/Novel/D9TrueLimitProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **Inputs.** Conditional on AX-06 and AX-08 (claims 004–005's restatements) and AX-10, AX-11, AX-14 (claim 007's restatements), through the proved statements of claims 005 and 007. AX-16 is **not** a premise: as the auditor's AX-16 line suggested, both parts, in the specialization used here, are proved from Mathlib (subsequence lemma for convergence in measure plus dominated convergence, with dominator V, on the shortfall (V − Wₙ)⁺). Uniform integrability comes from reverse Vitali, Mathlib's `unifIntegrable_of_tendsto_Lp`. The formalization adds no Upstream structure.
- **Encodings.**
  - The setting is claim 007's: claim 004's `Setting`, X constant after T > 0, `Grids` (mesh → 0, not necessarily nested), plus Q(X_t > 0 for t ≤ T) = 1 and 0 ≤ π ≤ 1.
  - W⁽ⁿ⁾_T is `gridWealth` at T on the n-th grid. Vπ_T is `expo π L A T` for any integral L of 1/X against X and any bracket A of L (both exist by claim 007).
  - "Vπ true" is the hypothesis E_Q[Vπ_T] = 1. The statement also proves that `MartingaleOn T` gives it.
  - (2) is stated for every `LipschitzWith C f`; calls and puts are shown to be 1-Lipschitz.
  - UI is Mathlib's `UniformIntegrable` at p = 1 (it includes the L¹ bound).
  - limsup in (4) is "for every ε > 0, eventually 1 − E W⁽ⁿ⁾_T ≤ 1 − E Vπ_T + ε".
- **Proved.**
  - Basic facts: nonnegativity, terminal integrability, means at most one, and terminal convergence in probability.
  - Parts 1–2 under E Vπ_T = 1: L¹ convergence, means → 1, defects → 0, UI and (2).
  - Part 4 with no true-limit hypothesis.
  - Endpoints. At π = 0, W⁽ⁿ⁾ = V⁰ = 1 everywhere. At π = 1, W⁽ⁿ⁾_T = X_T a.s. by telescoping, and V¹_T = X_T a.s., because limits in probability are a.s. unique. So the L¹ distance is zero for every n, UI and (2) hold, and the common defect is 1 − E X_T, whether X is true or strict.
- **Part 3 is conditional on AX-01 at this instance and on claim 001's (W).** They enter as the premise "Vπ is a martingale on [0, T] iff `MUCondition π σ c`", the form of claim 001's statement (B). Claim 007's D1 identification gives Vπ the exponent of ∫bπ(X)dW, but the link to AX-01's opaque `StochExp` is (W), which is not formalized. With `VolHyp σ`, I₀ = ∞, 0 < π and (π ≤ 1/2 or I∞ = ∞), claim 001's proved part (A) (`muCondition_iff`) makes the condition hold, so parts 1–2 apply. Locally bounded σ is needed only for claim 007's identification, so it does not appear in this statement.
- **Proof difference.** The prose obtains V¹ = X from claim 007's stopped equation and AX-10 uniqueness. The formal proof instead uses a.s. uniqueness of limits in probability against the telescoped grid wealths, which needs only claim 007's (5).
- **Stale prose.** Not shown ("There is no Lean proof of this claim. AX-16 … ha[s] no asserted Lean structures or instances") is routed to math (`board/inbox/math/2026-10-06-claim009-stale-prose.md`). The ledger's AX-16 `Formal:` line is routed to formalizer.

Math, 2026-10-06: corrected Not shown against the Lean statement and proof.
The earlier review and stale-prose handoff are historical records; the
mathematical statement is unchanged.
