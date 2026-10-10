---
id: "014"
title: "D9: an option-interval outer set and a conditional cross-π test"
status: formalized
depends_on: [005]
axioms_used: [AX-06, AX-08, AX-18]
formal: lean/Standalone/D9CrossPi.lean
direction: D9
---
## Statement

This is a conditional application of claim 005 and the proved algebra AX-18
(source/formal audit `2406eea`). It supplies an outer confidence set and a
test under supplied simultaneous price coverage. It does not supply that
coverage, a sharp identified set, or a market option-pricing theorem.

Fix T>0 and a nonempty finite index set J. On one usual filtered probability
space with pricing measure Q, let X be a finite continuous nonnegative local
martingale, X₀=1. For each j∈J fix 0<π_j≤1 and a deterministic grid with N_j≥1
intervals from 0 to T. W^j is exactly claim 005's cost-free fixed-share fund:
on a holding interval its value is W_i^j[1−π_j+π_j X_t/X_i], and at a zero-price
rebalance it freezes in cash. All funds use this same X, Q and T. Define

    δ_T = 1−E_Q[X_T],   d_j = 1−E_Q[W^j_T],
    a_j = π_j^(N_j) > 0.                                  (1)

All values are normalized to initial value one, and the discount rate is zero.
For a fixed strike K_j≥0 observe a European call and put under the explicitly
declared **expectation-pricing operator**:

    C_j = E_Q[(W^j_T−K_j)⁺],   P_j = E_Q[(K_j−W^j_T)⁺].    (2)

These are Q-expectations, not arbitrary market quotes. Given real interval
endpoints Clo_j≤Chi_j and Plo_j≤Phi_j, set

    L_j = 1−K_j−Chi_j+Plo_j,
    U_j = 1−K_j−Clo_j+Phi_j.                              (3)

The following scalar construction also permits arbitrary L_j,U_j, including
inconsistent intervals. Define B_out(L,U) to be the set of δ∈[0,1] for which
there exist real z_j, for all j∈J, satisfying

    L_j≤z_j≤U_j,   0≤z_j≤1,   a_j δ≤z_j,
    (z_j=0 ⇔ δ=0).                                       (4)

1. **Containment and explicit computation.** If every price interval contains
   its target in (2), then δ_T∈B_out(L,U). Define b_j=min(1,U_j).
   The zero part of B_out is {0} if L_j≤0≤U_j for every j, and is empty otherwise.
   The positive part is empty if some j has b_j≤0 or L_j>b_j. In every other
   case it is exactly

       (0, min(1, min_(j∈J) b_j/a_j)].                    (5)

   Thus B_out is computable using finitely many comparisons and a minimum.
   This is exact elimination of (4), not attainability by stochastic models.
   In particular, if L_j=U_j=d_j, values outside [0,1] or a mixture of zero
   and positive values make the set empty; all zero gives {0}; all positive
   values in [0,1] give (5). In the last case the set excludes zero but has
   infimum zero. No positive monetary lower bound follows from (4).

2. **Coverage and size.** Let the endpoints in (3) be measurable real random
   variables on a separate observation probability space with law P_obs.
   This law describes uncertainty in the option-price observations; it need
   not be Q or the physical path law. Let E_cov be the event that all 2|J|
   intervals contain their respective fixed targets (2). For any model with

       P_obs(E_cov) ≥ 1−α,   0≤α≤1,                      (6)

   the random set satisfies P_obs(δ_T∈B_out)≥1−α. Define

       φ_out = 1{0∉B_out},   φ_+ = 1{some j has L_j>0}.    (7)

   Under the null δ_T=0, both rejection probabilities are at most α. If (6)
   holds uniformly over a declared null family, their size is at most α
   uniformly over that family. Uniform confidence coverage over a larger
   family requires (6) throughout that larger family.

   The tests have distinct interpretations. Zero exclusion is equivalent to
   some L_j>0 or some U_j<0. A negative U_j signals incompatibility with the
   nonnegative-defect benchmark, rather than positive bubble evidence.
   φ_+ uses only positive residual evidence; it need not reject an empty set
   caused solely by negative upper bounds. Empty sets must be reported as
   model/observation incompatibility. Neither test identifies the cause of a
   rejection when the pricing or fund assumptions fail.

3. **Pointwise consistency with increasingly accurate prices.** Keep J,
   the grids, the model and the strikes fixed. Suppose along observations
   indexed by n each call interval endpoint tends in P_obs-probability to C_j
   and each put endpoint to P_j. At every fixed alternative δ_T>0, both
   rejection probabilities tend to one. A uniform power rate, consistency
   with refining grids N_j→∞, and a construction of such observations are
   not asserted. The bound a_jδ_T may be extremely small.

4. **Declared costs and tracking.** Instead of (2), suppose the observed
   expectation-priced payoffs are on integrable terminal NAVs
   Y^j_T=W^j_T−c^j_T+e^j_T, with known deterministic d_(T,j)=E_Q[c^j_T]
   and supplied ε_j≥0 satisfying E_Q|e^j_T|≤ε_j. These terminal adjustments
   include effects on later holdings, as in claim 005. Compute raw L_j,U_j
   from the options on Y^j and replace them everywhere in parts 1–2 by

       L_j^c = L_j−d_(T,j)−ε_j,
       U_j^c = U_j−d_(T,j)+ε_j.                           (8)

   The containment and coverage/size conclusions still hold. For the
   endpoint-consistency premise of part 3 applied to the NAV option targets,
   consistency follows if d_j>2ε_j for at least one j; no such separation
   condition is needed when all ε_j=0. No Q-cost or Q-tracking bound is
   inferred from physical return data.

## Proof

**Mechanism and known results.** First map a rectangular confidence region
through an affine observation identity, then project deterministic inequalities.
The statistical step is ordinary confidence-set inversion: on the coverage
event the true parameter is feasible. Probability monotonicity gives the
coverage and size bounds. We use existing integration and measure lemmas,
not a new general inference theorem. The D9-specific step is inserting claim
005's common-zero restriction and quantitative defect bound into this projection.

**Accounting and containment.** Claim 005 gives 0≤δ_T≤1, 0≤d_j≤1,
a_jδ_T≤d_j, and d_j=0 iff δ_T=0. Its nonnegative integrable terminal fund
also has integrable call and put payoffs: they are bounded by W^j_T+K_j.
Integrate AX-18's pointwise payoff identity to obtain
C_j−P_j=E_Q[W^j_T]−K_j. Its `expectation_residual` lemma therefore gives
1−K_j−C_j+P_j=d_j. On price containment, `quote_bounds` gives L_j≤d_j≤U_j.
Taking z_j=d_j proves (4).

**Elimination.** For δ=0 the last condition in (4) forces every z_j=0.
This is feasible exactly when L_j≤0≤U_j for every j. For δ>0, feasibility
forces 0<a_jδ≤z_j≤b_j and L_j≤b_j. Hence b_j>0 and δ≤b_j/a_j for every j,
as well as δ≤1. Conversely, under these conditions set

    z_j=max(L_j,a_jδ).

It is positive, at least L_j and a_jδ, and at most b_j≤1,U_j.
It meets every constraint in (4). This proves (5), including its closed
upper endpoint and excluded lower endpoint. The exact-price specializations
follow by setting L_j=U_j. If their positive upper endpoint is u, the values
u/(n+1) lie in the set and tend to zero; that is a property of the outer
constraints, not evidence that models attain these values.

**Probability argument.** All events are measurable: for fixed δ the
elimination uses finitely many comparisons of measurable scalar endpoints.
On E_cov the preceding containment proof applies pointwise. Thus
{δ_T∉B_out}⊆E_covᶜ. Apply probability monotonicity and the complement identity
to get the coverage bound. Under δ_T=0, {φ_out=1} is that failure event;
{φ_+=1}⊆{φ_out=1} by the zero-feasibility criterion. This proves both size
bounds. Taking a supremum over a null family preserves the bound if (6)
holds for each member. Marginal coverage of individual intervals is not
the simultaneous hypothesis (6).

**Consistency.** Endpoint convergence implies L_(j,n)→d_j in probability
by the affine identity (3). Under a fixed alternative claim 005 gives
d_j≥a_jδ_T>0 for every j. Fix any j. On
{|L_(j,n)−d_j|<d_j/2}, φ_+=φ_out=1; its probability tends to one.
This gives pointwise consistency without asserting any uniform rate or any
automatic coverage property of the endpoint estimates.

**Costs and tracking.** Linearity of expectation gives the NAV residual
1−E_Q[Y^j_T]=d_j+d_(T,j)−E_Q[e^j_T]. Since
|E_Q[e^j_T]|≤E_Q|e^j_T|≤ε_j, price containment implies
L_j^c≤d_j≤U_j^c. The same witnesses and event inclusion prove parts 1–2.
Under consistent raw endpoints, the corrected lower endpoint tends to
d_j−E_Q[e^j_T]−ε_j≥d_j−2ε_j. If that lower bound is strictly positive for
some j, the same consistency argument applies. Persistent tracking bounds
need not shrink, so consistency at every positive defect is not claimed.

## Checks

`checks/014/check.py` uses exact rational arithmetic. It checks interval
projection boundaries, exact mixed-zero incompatibility, positive outer sets
with infimum zero, and a finite observation model attaining size α under
simultaneous coverage. A separate two-fund example gives rejection probability
2α when each fund's price rectangle has only marginal coverage 1−α.
The cost fixture shows a false positive before correcting known drag and the
loss of power permitted by a persistent tracking bound. These are checks of
scalar restrictions and observation laws; none constructs a diffusion,
calibrates market intervals, or demonstrates a gain from fund-option data.

## Not shown

No sharp stochastic identified set, sufficiency of (4) for model existence,
uniform consistency, estimated coverage, empirical size or power, or superiority
to a literature baseline. No claim is made for inverse liquidated funds,
π_j>1, non-expectation option pricing, American exercise, or unknown costs.
Claim 011's inverse liquidated funds can have zero defect over a strict X,
so they cannot be inserted into the common-zero constraint here.

An exact expectation-priced underlying call-put pair already identifies δ_T
by AX-18. Added fund pairs then cannot improve identification of that scalar.
This claim does not show that multiple rebalances improve on incomplete
underlying option information; that comparison still requires a simulation
before any fund-option data request. Likewise, replacing expectation calls
by C_Y⁰+(1−E_Q[Y_T]) makes their residual zero by AX-18. The test is not valid
for that pricing operator. Bid-ask spreads alone are not confidence intervals.

The deterministic elimination is formalized in `lean/Standalone/OuterSet.lean`
and proved in `lean/Novel/OuterSetProof.lean`. The stochastic and statistical
application is stated in `lean/Standalone/D9CrossPi.lean` and proved by
`proof` in `lean/Novel/D9CrossPiProof.lean`. Its stochastic interpretation
still inherits claim 005's AX-06/AX-08 hypotheses and degenerate formal
instances. Simultaneous price coverage remains a supplied premise, and the
formalization does not establish stochastic attainability or market pricing.

## Prior art

Read the D9 cross-π and D4 findings, refuted targets, claim 005, AX-18 and its
audit, and the local source texts. [kardaras2015strict] Example 4.8 already
gives the expectation call-put identity. [carr2012hedging] Corollaries 3.7–3.8,
(3.5)–(3.6), give a different exchange-rate pricing operator restoring parity;
we do not transfer that pricing theorem to ETFs. AX-18 proves the finite
algebra and interval arithmetic, rather than treating them as assumptions.
The new application is the simultaneous use of claim 005's fund-defect
restrictions, explicit projection, and cost adjustment. Confidence-set
inversion itself is standard. Mathlib already has `measure_mono`,
`measure_compl`, integral linearity and the absolute-integral bound; use
those directly. No new stochastic or statistical upstream theorem is needed.

## Review

Reviewer, 2026-10-06, on branch `math/d9-cross-pi-claim` at `8c8fbe8`. I re-derived each part before reading the author's proof, and wrote my own checks before reading `checks/014/check.py`.
- **Inputs.** AX-18 has an `ok` source-and-formal audit at `2406eea`, which is on this branch; it is proved algebra in Lean (`expectation_residual`, `quote_bounds`). AX-06 and AX-08 are as before. Claim 005, the dependency, is approved.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- **Containment.** E[(W−K)⁺] − E[(K−W)⁺] = E[W] − K, with both payoffs integrable because they are bounded by W + K. So d_j = 1 − K_j − C_j + P_j, and price containment gives L_j ≤ d_j ≤ U_j. Claim 005 supplies 0 ≤ a_jδ_T ≤ d_j ≤ 1 and d_j = 0 ⇔ δ_T = 0, so z_j = d_j witnesses δ_T ∈ B_out.
- **Elimination.** δ = 0 forces every z_j = 0, which needs L_j ≤ 0 ≤ U_j for every j. For δ > 0 it needs 0 < a_jδ ≤ z_j ≤ b_j and L_j ≤ b_j, and conversely z_j = max(L_j, a_jδ) is a valid witness. So (5) holds, with a closed upper endpoint and an open lower endpoint.

**Part 2: correct.** {δ_T ∉ B_out} ⊆ E_covᶜ, so the coverage is at least 1 − α. Under δ_T = 0, rejection by φ_out is exactly that failure event, and φ₊ ⊆ φ_out. Simultaneous coverage (6) is correctly a supplied premise, and the distinction between P_obs and Q is kept. The interpretive warnings (negative U_j signals incompatibility, not a bubble; empty sets must be reported) are right.

**Part 3: correct.** L_{j,n} → d_j ≥ a_jδ_T > 0, and on {|L_{j,n} − d_j| < d_j/2} both tests reject.

**Part 4: correct.** 1 − E[Y] = d_j + d_{T,j} − E[e], with |E[e]| ≤ ε_j, so d_j lies in [L_j − d_{T,j} − ε_j, U_j − d_{T,j} + ε_j]. The corrected lower endpoint tends to d_j − E[e] − ε_j ≥ d_j − 2ε_j, which gives the stated consistency condition.

**Checks** (evidence, not proof).
- **(a) The elimination.** Over 3,000 random instances (1–3 funds, including inconsistent intervals and boundary L_j = 0), I decided feasibility of (4) directly at 4,002 values of δ. Because the z_j constraints are independent across j, each is a per-fund interval check. There were zero mismatches with (5).
- **(b) The author's check.** I ran `checks/014/check.py` afterwards. It passes 1,185 exact rational fixtures, the endpoint cases, the joint-against-marginal coverage example (size α against 2α), and the cost and tracking fixtures.

**Gaps.** None.

**How much this can deliver in practice, for D9 and the human's data decision.**
1. **The quantitative bound is empty at realistic rebalancing.** a_j = π_j^{N_j} is 3·10⁻⁷ for π = 3/4 and weekly rebalancing over a year, and 3·10⁻³² daily. So min(1, b_j/a_j) = 1 whenever b_j is more than a vanishing amount, and the positive part of B_out is just (0, 1]. In my computation, with a fund defect of 0.05, the upper endpoint is 1 for every π < 1 already at N = 52. In practice the claim's content is the zero-exclusion test, d_j > 0 ⇔ δ_T > 0. Only π = 1, which is the underlying itself, gives a quantitative bound.
2. **The zero test is weak at daily frequency for low exposure.** By claims 007 and 009, for π ≤ 1/2 with zero inaccessible, the daily-fund defect d_j tends to 0 as rebalancing refines, even when δ_T > 0. My claim-005 simulation gives 0.023 at N = 64 against δ_T = 0.317 for σ = x², π = 1/4. For π > 1/2 the defect tends to claim 001's continuous defect, so more signal survives.
3. **The fund class excludes the actual leveraged and inverse ETFs.** 0 < π_j ≤ 1 with cost-free fixed shares excludes every fund D9 names (QLD, TQQQ, SSO, UPRO at π = 2, 3; the inverse funds at π < 0). "Not shown" says this. Any data request for those funds' options needs a different claim first.
4. **Fund options cannot improve on the underlying's own options.** If the underlying's own exact call-put pair is observed, it identifies δ_T by AX-18, and fund options cannot improve on it. The claim says so, and correctly defers the value of fund options under incomplete underlying data to a simulation. This bears directly on the human's no-purchase decision: nothing here makes fund-option data informative yet.

**Scope; "Not shown" is honest.** It excludes a sharp stochastic identified set, model attainability, uniform consistency, coverage construction, π_j > 1, inverse liquidated funds (whose zero defect over a strict X breaks the common-zero constraint), and non-expectation pricing. The prior-art citations ([kardaras2015strict] Example 4.8, [carr2012hedging] Corollaries 3.7–3.8) are used for exactly what they supply.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived containment, exact elimination (3,000-instance feasibility check), coverage/size by event inclusion, consistency and cost correction; practical limits (vacuous bound, excluded ETF class) stated


Formalize the finite feasibility elimination separately from its application
to claim 005 and the measurable-event inclusion. Preserve the zero equivalence,
the open lower endpoint, the distinction between P_obs and Q, and the
simultaneous coverage hypothesis. AX-18 is a proved algebraic lemma, not an
Upstream field. Do not reconstruct stochastic integration or confidence-region
calibration; the latter is an explicit premise not supplied by this claim.

Formalizer, 2026-10-06, on `form/d9-cross-pi`. **Status: formalized.** There is no `sorry`, and the axiom audit is clean.
- **Deterministic elimination.** `lean/Standalone/OuterSet.lean`, proved in `lean/Novel/OuterSetProof.lean`, with no probability.
  - `Bout` is (4) for a nonempty finite index type and arbitrary, possibly inconsistent, L and U.
  - The zero part is {0} iff Lⱼ ≤ 0 ≤ Uⱼ for all j. Zero is excluded iff some Lⱼ > 0 or some Uⱼ < 0.
  - The positive part is empty if some bⱼ ≤ 0 or Lⱼ > bⱼ, and otherwise exactly (0, min(1, minⱼ bⱼ/aⱼ)], with the closed upper and open lower endpoint.
  - With exact prices: ∅ for a value outside [0,1] or for mixed zero and positive values; {0} if all are zero; and (0, upper] with upper > 0 if all lie in (0,1]. In the last case the set excludes zero but contains values below every ε > 0.
- **Application.** `lean/Standalone/D9CrossPi.lean`, proved in `lean/Novel/D9CrossPiProof.lean` (`proof`).
  - **Setting.** It is conditional on AX-06 and AX-08 through claim 005, whose Lean proof supplies 0 ≤ δ_T ≤ 1, 0 ≤ dⱼ ≤ 1, aⱼδ_T ≤ dⱼ and dⱼ = 0 ⇔ δ_T = 0. X is in claim 005's `Setting`, and the funds are claim 005's `gridWealth` with 0 < πⱼ ≤ 1 and Nⱼ ≥ 1 intervals from 0 to T. AX-18 enters as its proved lemmas `expectation_residual` and `quote_bounds`, after integrating the call–put payoff identity. T > 0 and Kⱼ ≥ 0 are not needed by the proof.
  - **Part 1:** price containment gives δ_T ∈ Bout, with the witness zⱼ = dⱼ.
  - **Part 2:** on a separate observation space with law P_obs (not Q), with measurable endpoints and simultaneous coverage P_obs(E_cov) ≥ 1−α, 0 ≤ α ≤ 1. Then P_obs(δ_T ∈ Bout) ≥ 1−α, and under δ_T = 0 both φ_out and φ₊ reject with probability at most α. Uniform size over a declared family is this bound at each member.
  - **Part 3:** with endpoints converging in P_obs-probability to the targets, at δ_T > 0 both rejection probabilities tend to one.
  - **Part 4:** for integrable Yʲ = Wʲ_T − cʲ + eʲ with E_Q cʲ = d_{T,j} and E_Q|eʲ| ≤ εⱼ, containment and coverage/size hold with the corrected endpoints (8). Consistency holds if some dⱼ > 2εⱼ; with all εⱼ = 0 that is δ_T > 0.
