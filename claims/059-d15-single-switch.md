---
id: "059"
title: "D15: a calibrated Gaussian single-switch null with minimum segment length"
status: formalized
depends_on: ["027", "053", "054", "055"]
axioms_used: [AX-53, AX-55, AX-56, AX-58]
formal: lean/Standalone/D15Switch.lean
direction: D15
---
## Statement

**Conditional on the cited inputs and the actual conditional-law premise
below.** The mechanism is a finite maximum of products of the already
proved Gaussian profiles in claim 055, followed by dominated split
likelihood (AX-58, [wasserman2019universal]) and the mixture integration
used in claim 027. No new inference theorem, Gaussian profile theorem
or stochastic-calculus result is asserted.

Keep claim 055's finite nonempty panel, known positive starts, fixed grids,
nonempty training split, ordered finite CEV catalogue with a retained
p≤1 null, and mixed reference measure μ_CEV. Keep its training-only
first-maximizer numerator Ĝ_i, normalized at every training value, and
all retained catalogue-null densities with maximum G_(i,0). The whole
observation domain is all nonnegative arrays, including impossible ones.
The actual training and alternative-name laws are unrestricted.

For each name require n_e≥4 evaluation increments. Before observing any
data declare a nonempty set K_i^sw⊆{2,…,n_e−2}. Each c∈K_i^sw splits
evaluation increments into H_L={1,…,c}, H_R={c+1,…,n_e}. Durations Δ_j
are fixed and positive. All cuts refer to evaluation increments, not
the full training-plus-evaluation record.

For each c and θ=(b_L,κ_L,b_R,κ_R)∈R×(0,∞)×R×(0,∞), let
g^sw_(c,θ)(v|u) be the price density of independent log returns with

    R_j ~ Normal((b_L−κ_L²/2)Δ_j, κ_L²Δ_j), j≤c,
    R_j ~ Normal((b_R−κ_R²/2)Δ_j, κ_R²Δ_j), j>c.          (1)

Use claim 055's positive-price Jacobian ∏1/y_j. From a positive last
training price the density is zero if any evaluation price is zero;
from endpoint zero it is one on the all-zero suffix and zero otherwise.
These are normalized densities on the same mixed observation space.
Separate segment drifts enlarge the family with common physical drift.
A no-switch Gaussian law is included by taking both parameter pairs equal.

Supply a fixed true-null set N₀. At every i∈N₀, for almost every actual
training record u, require the actual evaluation law to be a probability
mixture of the retained CEV null laws and the laws (1). Precisely, on
the disjoint union of the finite CEV null index set and
K_i^sw×R×(0,∞)×R×(0,∞), supply a measurable probability kernel ν_i(u,dθ)
such that

    Law_P(V_i | U_i=u) = ∫ H_(i,θ)(u,·) ν_i(u,dθ).      (2)

Here H is the probability law with the displayed component density.
Mixture weights, cut and component parameters may depend on training
through ν_i, but the score does not observe or fit this latent variable.
This is a premise about the actual law, not a fitted mixing distribution.
It does not follow from merely bounding the number of apparent changes
in a realized price path. Panel dependence is arbitrary.

Define D_sw=sup_(c∈K_i^sw,θ) g^sw_(c,θ), D=max(G_(i,0),D_sw) and

    E_i^sw = 0           if Ĝ_i=0 or D=∞,
           = Ĝ_i/D     otherwise.                     (3)

1. **Exact profile and exceptional arrays.** On a positive evaluation
   path from a positive endpoint, for either segment H put

       n_H=|H|, τ_H=Σ_(j∈H)Δ_j,
       a_H=Σ_(j∈H)R_j/τ_H,
       Q_H=Σ_(j∈H)(R_j−a_HΔ_j)²/Δ_j.

   If Q_H>0 define the positive finite segment price-density maximum

       log D_G,H = −n_H/2 [log(2πQ_H/n_H)+1]
                   −(1/2)Σ_(j∈H)log Δ_j−Σ_(j∈H)log y_j. (4)

   If Q_H=0 set D_G,H=∞. Then

       D_sw = max_(c∈K_i^sw) D_G,H_L · D_G,H_R.         (5)

   Both factors are strictly positive on this stratum, so (5) has no
   ambiguous zero-times-infinity product. On other strata use the
   zero/trapped values of (1) for D_sw directly. The maximum is finite
   precisely when every allowed segment has Q_H>0. It is a measurable
   extended nonnegative function. E_i^sw is finite, nonnegative and
   measurable on every input array.

   Each zero-residual segment has at least two increments. Its return
   vectors lie in a proper linear subspace, so the union of these
   exceptional positive-path sets over the finite cut set is Lebesgue
   null. In particular D_sw is finite almost surely under each law
   (2), including its retained CEV components. Exceptional arrays are
   still in the domain and give zero evidence by (3).

2. **Inference.** Every actual null has

       E_P[E_i^sw | U_i]≤1,       E_P E_i^sw≤1.          (6)

   The strict test E_i^sw>1/α_i has size at most α_i, for fixed
   0<α_i<1. Its reciprocal capped at one, set to one at zero, is a
   valid p-value. The union bound is Σ_(i∈N₀)α_i. Base e-BH from claim
   053 has FDR≤q_FDR|N₀|/m, conditional on AX-53; measurable zero masks
   keep the bound with the original m. No arbitrary postfiltering or
   conditional-on-screen guarantee is asserted. A supplied measurable
   finite nonnegative score bounded above by (3) preserves these results.

3. **Ordering and scope of the restriction.** Pointwise on every array,

       E_i^sw ≤ E_i^drift ≤ E_i.                         (7)

   Enlarging K_i^sw decreases the score and enlarges its covered family.
   Thus this repair cannot increase per-name power relative to claim
   055 on the same observations and numerator; useful power is not
   established. It is not identically zero: choose any positive training
   record and positive evaluation prices with R_j=jΔ_j. Every permitted
   segment then has Q_H>0, and the CEV numerator is strictly positive,
   so E_i^sw>0. This does not establish a rejection at any chosen level.

   If the permitted set instead contains c=1 or c=n_e−1, the supremum
   is infinite on every positive path: that singleton's Q_H is zero.
   The resulting score is identically zero there. Merely limiting the
   model to one switch, without a minimum segment length, is insufficient.
   For admissible absorbed arrays E_i^sw=E_i≤1, so these arrays cannot
   enter the base or zero-masked e-BH list at q_FDR<1.

4. **Interpretation.** This is a null for at most one parameter change
   per latent component at a permitted evaluation cut, with component
   Gaussian independence. It does not cover arbitrary repeated switches,
   Gaussian states selected using contemporaneous return noise, general
   stochastic-volatility dynamics, jumps or rounded observations. A
   bubble interpretation needs a separate premise that actual pricing-null
   names satisfy (2). No pricing measure, equivalent-measure construction,
   or strict-local-martingale label is deduced from fitting a switch law.

## Proof

**Known mechanism and component normalization.** Apply claim 055's
Gaussian density/profile to each segment. The second segment starts at
y_c; its Jacobian includes only y_(c+1),…,y_(n_e), so multiplying the
segments gives exactly one factor 1/y_j per evaluation price. Integration
of the second normalized kernel at each first-segment endpoint gives
one; integration of the first gives one. At endpoint zero the trapped
law is normalized against μ_CEV. From a positive endpoint any zero has
zero Gaussian density. These component kernels are jointly measurable
in parameters, training endpoint and observations by their finite
Gaussian expressions and measurable strata. Their probability-mixture
interpretation in (2) is supplied, as in claim 027, not inferred from
a stochastic differential equation.

**Checking the profile application.** At a fixed cut, parameters of
the two segments vary independently. Claim 055 supplies each factor's
supremum (4), with finite maxima attained at κ_H²=Q_H/n_H and
b_H=a_H+κ_H²/2 when Q_H>0. Choosing both maximizers attains their
product. If either factor is unbounded, hold the other at any positive
finite Gaussian density and let the unbounded factor grow; the product
is unbounded. This verifies (5), including its extended cases, without
re-proving Gaussian maximization. A finite maximum over cuts and the
explicit stratum definitions give measurability. When Ĝ_i>0, claim
054's support implication gives G_(i,0)>0, so a finite D gives a finite
ratio; an infinite D gives zero by definition. The remaining cases
have zero numerator. This proves every-array finiteness and measurability.

For any segment with at least two increments, Q_H=0 implies, for two
distinct j,l∈H, R_jΔ_l−R_lΔ_j=0. This is a proper hyperplane. Hence its
Lebesgue measure is zero; the finite union over segments is null. The
return-to-price map from a fixed positive endpoint is a smooth bijection
with positive Jacobian, so these sets remain null in positive-price
coordinates. Every Gaussian component and every retained CEV component
restricted to the positive orthant has a density there. Their mixtures
give zero mass to this set by integration. On zero-containing arrays
D_sw is either zero or one, proving the almost-sure assertion without
discarding any observed array.

**Checking the inference application.** For every training value, D
dominates each retained CEV density and each switch density. The selected
numerator is the same normalized training-only density as claim 055.
These verify the pointwise reference-moment hypotheses of AX-58, so
the integral of (3) under every component H_(i,θ)(u,·) is at most one.
Apply claim 027's mixture integration to this raw reference moment:
integrating with respect to ν_i(u,dθ) in (2) keeps the bound one. This
also covers mixing over retained CEV components. It does not require
the mixture itself to have a pointwise finite density. Integrate over
actual training to obtain (6). Markov, the reciprocal p-value argument
of claim 055 and the union bound give the per-name/panel size results.
Finite measurable scores and null means at most one verify AX-53's
conditions; masks and certified lower scores reduce these means.

**Ordering, nonzero example and absorption.** At any permitted cut,
choosing identical segment parameters includes every constant Gaussian
law, so D_sw≥D_G of claim 055. Maxing with the unchanged G_(i,0) and
using the same zero/infinity conventions gives (7). Set inclusion for
cuts gives the other ordering. In the constructed example R_j/Δ_j=j,
so two distinct indices in every segment have distinct rates and Q_H>0;
positivity of every CEV transition on positive prices supplies Ĝ_i>0.
A singleton segment instead has Q_H=0 for every return, proving the
collapse directly by claim 055. On absorption the switch density is
zero from a positive endpoint and one on a trapped suffix from zero;
claim 054's bound gives the stated score and e-BH exclusion.

## Checks

`checks/059/profile.py` composes the existing Gaussian segment profiles.
`checks/059/scoring.py` keeps every record, with invalid observations or
reported numerical failures masked to zero and invalid fixed design
raising an error. An infinite switch supremum is a mathematical boundary,
not a numerical failure. `checks/059/check.py` checks fixed irregular
profiles against direct segment Gaussian densities, singleton and
zero-residual cases, the price Jacobian, all support strata, cut inclusion,
training-only selection and retained failure records. These checks are
not proofs, error certificates or simulations of size/power.

## Not shown

- Parts 1–3 are formalized in `lean/Standalone/D15Switch.lean`, proved
  by `lean/Novel/D15SwitchProof.lean` (`statement_holds`), including
  the exact profile (5), the μ_CEV-null exceptional set and mixture
  inference. AX-58 is proved from Mathlib. CEV normalization remains
  conditional on AX-55/56 with vacuous instances, and FDR on AX-53
  with a degenerate instance. In the nonzero example, the formal
  result assumes Ĝ_i>0 rather than deriving CEV numerator positivity
  on positive arrays. Part 4's interpretation remains commentary.
- No useful power, practical superiority, consistency or economic reason
  for a chosen cut set/minimum duration. Positive score is weaker than
  a nonempty rejection region at a useful threshold.
- No jump coverage, general regime process or automatic model coverage
  from a realized path that appears to switch once. No pricing-null
  identification from a physical likelihood.
- No data-chosen cut set, repeated-date or outcome-selected window
  guarantee. Profiling over a predeclared family is different from
  changing that family after seeing the evaluation data.
- No rounding/noise likelihood, certified numerical denominator or
  numerator, nor proof that a successful diagnostic status bounds error.
  Exact ties and near-zero segment residuals need special numerical care.

## Prior art

The mechanism is [wasserman2019universal], Theorem 3 and its conditional-
likelihood and likelihood-upper-bound discussions, via audited AX-58.
Claim 055 already proves the whole Gaussian optimization used here;
claim 027 gives the relevant mixture integration, and claim 053 applies
[wang2020false]. The D15 sweep and the refuted unrestricted-supremum note
were checked. Gaussian-mixture collapse is known ([snoussi2001mixtures]);
the single-switch boundary here follows from claim 055's singleton
profile. The application checks segment composition, cut restrictions,
measurability/support and conditional coverage, rather than claiming a
new mixture or inference theorem. AX-59's jump law is not used.

## Review

Reviewer, 2026-10-06, on branch `mathb/d15-single-switch` at `36cc7a1`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/059/`.
- **Inputs.** AX-53, AX-55, AX-56 and AX-58 are audited, and AX-58 is proved. Claims 027 and 053–055, the dependencies, are approved.
- **The new citation** [snoussi2001mixtures] is registered.
- **Script.** My check is committed as `checks/review/059/reproduce.py`, with its rerun command and seed (`default_rng(59)`) in its header. It is not a CI `check.py`.

**Part 1: correct.**
- **The factorization (5).** At a fixed cut, the switch density factors into two segment Gaussian price densities with independent parameters, and the Jacobians split as ∏1/y_j over each segment. So the supremum is the product of claim 055's segment suprema. It is infinite iff some segment has Q_H = 0, with the other factor positive and finite, so there is no 0·∞ case.
- **The null set.** With segments of at least two increments, Q_H = 0 is a proper hyperplane in return space. A finite union of these is Lebesgue-null, and every component of (2) has a density on the positive orthant, so D_sw < ∞ almost surely.
- **Singletons.** A singleton segment always has Q_H = 0, which gives the collapse for c ∈ {1, n_e − 1}.

**Part 2: correct.** D dominates every retained CEV null and every switch component pointwise, so AX-58 gives the reference moment ≤ 1 per component. Integrating against ν(u, dθ), as in claim 027, preserves it for the mixture (2). Markov, the p-value and AX-53 follow.

**Part 3: correct.**
- **The ordering (7).** Equal segment parameters recover every constant Gaussian, so D_sw ≥ D_G, which gives (7). Cut inclusion gives the cut-set ordering.
- **The nonzero example** R_j = jΔ_j gives Q_H > 0 on every segment.

**Checks** (evidence, not proof).
- **(a) The profile.** On 10 random short paths (n_e = 4–8, irregular steps), the switch supremum (5) at every permitted cut matches a direct 4-parameter Nelder–Mead maximization to a relative 6×10⁻¹⁶ (the price-free part). A singleton segment gives +∞.
- **(b) Monte Carlo.**
  - **The setup.** Daily prices for two years, training on year one (n_e = 252), the absorbed CEV catalogue p ∈ {½, 1, 3/2} × κ ∈ {0.2, 0.3, 0.45}, α = 0.1 and 10,000 paths per case.
  - **The cut sets.** K_month = {21, 42, …, 231} and K_all = {2, …, 250}.

  | Truth | Claim 055 E^drift: mean / FA | Claim 059, K_month | Claim 059, K_all |
  |---|---|---|---|
  | GBM σ 0.25 → 0.40 at cut 126 | **17 / 0.028** | 0.0002 / 0 | 0.0001 / 0 |
  | Switch at cut 130 (outside K_month) | **263 / 0.031** | 0.0002 / 0 | 0.0001 / 0 |
  | Switch at a random K_month cut (latent mixture) | **83 / 0.020** | 0.0009 / 0 | 0.0003 / 0 |
  | Constant GBM 0.30 | 0.40 / 0.0003 | 0.056 / 0 | 0.013 / 0 |
  | CEV p = 3/2, κ = 0.30: power | 0.057 | **0.000** | **0.000** |
  | CEV p = 3/2, κ = 0.45: power | 0.205 | **0.003** | **0.001** |

  - The ordering (7) and cut-set monotonicity held on every path.
- **The author's check.** I ran `checks/059/check.py` afterwards, and it passes.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The switch null repairs exactly the failure in my claim-027 review.** A mid-window volatility switch breaks claim 055's raw e-moment (means 17–263), and claim 059's score restores validity. In my runs it also stayed valid for a switch slightly outside the declared cut set, though that case carries no guarantee.
2. **The power cost is almost total at daily sampling.** Against CEV p = 3/2, power falls from 6–20% to 0–0.3%. A one-switch Gaussian fits the level-dependent volatility of a CEV path about as well as the CEV alternative does, so little evidence remains.
3. **The repair is therefore valid but not useful** in this design, which the claim correctly does not contradict, since it asserts no power. A usable test would need a structural restriction separating "volatility changes over time" from "volatility depends on the price level", or higher-frequency data.
4. **Not covered:** jumps, repeated switches, general SV, rounding and the pricing link, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the segment factorization, a.s. finiteness with min segment 2, the singleton collapse, AX-58 domination with latent-switch mixture, and the ordering; committed review script; valid-but-powerless scope stated

Formalizer B, 2026-10-06, on `formb/d15-single-switch` (promoted from `provisional/formb-d15-single-switch`). **Status: formalized.**
- **Files.** The statement is in `lean/Standalone/D15Switch.lean` (`statement := profile ∧ score ∧ nullSet`). The proof is `lean/Novel/D15SwitchProof.lean` (`statement_holds`), which combines `D15SwitchProfileProof.lean` (`profile_holds`), `D15SwitchScoreProof.lean` (`score_holds`) and `D15SwitchNull.lean` (`Dsw_top_null`). There is no `sorry`, and the axiom audit is clean.
- **Inputs.**
  - AX-58 is proved from Mathlib and enters through its pointwise step.
  - FDR is conditional on AX-53 (claim 053's `AX53`).
  - AX-55 and AX-56 supply claim 054's kernels, on a base carrying a Brownian motion.
  - The Gaussian profile, the switch-law normalization, the mixture integration and the null exceptional set are proved.
- **Encodings.**
  - Indices are 0-based, and a cut c splits the increments into {j < c} and {j ≥ c}. The claim's K ⊆ {2, …, n_e − 2} is `2 ≤ c ∧ c + 2 ≤ m`.
  - (1) is claim 027's increment-varying price density `gV`, with piecewise-constant drift and scale. It includes the price Jacobian and the zero/trapped extension.
  - (2) uses a Markov kernel ν(u, ·) on the disjoint union of the catalogue-null indices and the switch parameters. The switch parameters are a subtype of ℕ × ℝ⁴: c ∈ K, κ_L > 0, κ_R > 0. The premise is that the actual conditional law equals the ν-mixture of the component laws (density times μ_CEV^m), P∘U⁻¹-a.e.
  - The score is AX-58's `Edrift(Ĝ, max(G₀, D_sw))`, which is (3).
- **Part 1.**
  - **Factorization.** At a cut with nonempty segments, on positive paths, the supremum over both segments' parameters equals the product of the segment maxima (4). Each segment maximum is ∞ at zero residual, and both factors are positive.
  - **The supremum (5).** It is the supremum over the declared cuts on every array, with the zero/trapped values off positive paths.
  - **Finiteness and measurability.** D_sw is finite iff every allowed segment has Q_H > 0, and it is measurable.
  - **Collapse.** A cut at 1 or n − 1 gives D_sw = ∞ on every positive path.
  - **The null set.** The arrays where (5) is infinite form a μ_CEV^m-null set. For two indices i < l of a zero-residual segment, R_iΔ_l = R_lΔ_i fixes y_l given the other prices, so each section along coordinate l is at most one positive point. Fubini (`measurePreserving_piFinSuccAbove`) then gives the null set. So P(D_sw(U, V) = ∞) = 0 under every law (2).
  - **The score (3).** It is finite and measurable on every array.
- **Part 2.**
  - **Moments.** Each component, catalogue null or allowed switch law, has the score's reference moment: D dominates it, and AX-58's pointwise step applies. Claim 027's averaging with zero budget then gives the conditional and unconditional moments under (2).
  - **Tests.** Markov gives size ≤ α, and the p-value is valid (claim 054's `zval_valid`).
  - **Panel.** The union bound holds, and base and masked e-BH with the original m hold under AX-53. Lower implemented scores are covered by the panel conjunct.
  - **Normalization.** The switch laws are normalized against μ_CEV^m.
- **Part 3.**
  - **(7).** E^sw ≤ E^drift ≤ E, since equal segment parameters give D_sw ≥ D_G.
  - **Cuts.** Enlarging K decreases the score.
  - **Nonzero.** E^sw > 0 when Ĝ > 0 and every allowed segment has Q_H > 0. Returns R_j = jΔ_j (1-based) give Q_H > 0 on every segment of at least two increments.
  - **Absorption.** Training absorption gives E^sw = 1. A zero evaluation price from a positive endpoint gives E^sw = E ≤ 1.
- **Not formalized.**
  - In the nonzero example, the step "the CEV numerator is strictly positive on positive arrays" (claim 054's transition positivity) is taken as the hypothesis Ĝ > 0.
  - Part 4's interpretation is commentary.
- **Stale prose.** The "Not shown" bullet ("No Lean formalization of this application yet") is routed to mathb (`board/inbox/mathb/2026-10-06-claim059-stale-prose.md`).
