---
id: "055"
title: "D13: a continuous Gaussian physical null for the absorbed CEV score"
status: formalized
depends_on: ["053", "054"]
axioms_used: [AX-03, AX-53, AX-55, AX-56, AX-58]
formal: lean/Standalone/D13DriftNull.lean
direction: D13
---
## Statement

**Conditional on the cited inputs and the observation/pricing premises
below.** The mechanism is the composite-null split likelihood ratio of
[wasserman2019universal], Theorem 3, Remark 4 and Section 6, registered
and source-audited as AX-58 at `f8beaf3` (audit commit `3a324ce`).
The new application verifies its hypotheses for the union of the finite
absorbed CEV null and a continuous Gaussian physical null. No general
inference or stochastic theorem is re-proved.

Fix claim 054's finite nonempty panel, positive known starts,
deterministic grids and nonempty training/evaluation split, and ordered
finite catalogues Θ_i of (p,κ), p,κ>0, containing a p≤1 candidate.
Keep its mixed kernels, training-only first maximizer (including ties
when all training likelihoods are zero), normalized evaluation density
Ĝ_i, null maximum G_(i,0), and finite old score E_i.
Here the **design and likelihood functions** are kept, but the actual
physical law need not satisfy claim 054's exact finite-catalogue premise.

The observation domain is every nonnegative price array after the known
start, with U_i∈[0,∞)^k_i and V_i∈[0,∞)^n_e, n_e=N_i−k_i≥1.
The whole panel has an arbitrary joint physical law P on this domain.
All conditioning uses only the same name's U_i. Supply a fixed set N₀
of actual null names. For each i∈N₀ assume the actual conditional law
of V_i given U_i has, P_Ui-almost surely, either:

- one of the finite null densities g_(i,ϑ), ϑ∈Θ_(i,0), or
- the Gaussian price density g^G_(b,κ) below, for some fixed b∈ℝ, κ>0.

The choice of null law and its parameters may differ across names.
The training distribution is unrestricted. No conditional-law premise
is imposed at i∉N₀. The null condition concerns the actual law, not a
model selected from data. A pricing interpretation of N₀ requires the
separate link stated in part 4.

**Gaussian conditional family.** Set y_0=u_(k_i). If y_0>0 and every
evaluation price y_j>0, let R_j=log(y_j/y_(j−1)), Δ_j the corresponding
positive grid steps, τ_e=ΣΔ_j, and define

    g^G_(b,κ)(v|u) = ∏_(j=1)^n_e
      exp(−[R_j−(b−κ²/2)Δ_j]²/(2κ²Δ_j))
      / [y_j sqrt(2πκ²Δ_j)].                           (1)

This density is relative to μ_CEV^n_e, exactly the reference measure
used for Ĝ_i and G_(i,0). From positive y_0 it is zero if any y_j=0.
From y_0=0 it is one on the all-zero suffix and zero otherwise. This
trapped extension defines a normalized version for every training value;
a positive geometric-Brownian physical model never uses a zero endpoint.

Let D_G=sup_(b∈ℝ,κ>0) g^G_(b,κ), D=max(G_(i,0),D_G), and

    E_i^drift = 0         if Ĝ_i=0 or D=∞,
              = Ĝ_i/D   otherwise.                    (2)

The second case always has 0<D<∞. Supremum means the actual continuum
supremum, not a numerical grid maximum or an optimizer output.

1. **Explicit measurable denominator and finite score.** On a positive
   evaluation path from a positive endpoint put

       a_G = ΣR_j/τ_e,
       Q_G = Σ(R_j−a_GΔ_j)²/Δ_j.

   If Q_G>0, the supremum is attained at
   κ²=w_G=Q_G/n_e, b=a_G+w_G/2, and

       log D_G = −(n_e/2)[log(2πQ_G/n_e)+1]
                 −(1/2)Σlog Δ_j−Σlog y_j.             (3)

   If Q_G=0, D_G=∞; the supremum is not attained at any κ>0.
   Off that positive-path set use the zero/trapped values in (1).
   Consequently D_G and D are extended nonnegative measurable functions,
   and E_i^drift is a measurable finite nonnegative function on every
   nonnegative input array, including model-impossible arrays.

2. **Null moments and testing.** For every i∈N₀,

       E_P[E_i^drift | U_i]≤1,   E_P E_i^drift≤1.

   Thus rejecting at E_i^drift>1/α_i has size at most α_i for fixed
   0<α_i<1. The p-value equal to one at E_i^drift=0 and otherwise
   min(1,1/E_i^drift) is valid. A union bound controls any null rejection
   by Σ_(i∈N₀)α_i. These bounds are uniform over all b∈ℝ, κ>0 in (1),
   without a drift/volatility grid or a TV penalty for that subclass.

3. **FDR under arbitrary panel dependence.** Apply claim 053's base
   e-BH rule to all m scores E_i^drift: choose the largest k such that
   k E_[k]^drift≥m/q_FDR, or choose none, at fixed 0<q_FDR<1.
   Conditional on AX-53, FDR≤q_FDR|N₀|/m. Any measurable zero-masking
   screen followed by the same procedure with the original m has this
   guarantee. It is not conditional FDR given the screen, and arbitrary
   trimming of the completed discovery list is not allowed.

4. **Pricing scope and cost.** These become bubble false-discovery
   bounds only if every actual pricing-null name satisfies the stated
   physical conditional-law premise. For the existing finite CEV
   specialization one may keep P=Q and p≤1, as in claim 054 and AX-03.
   For the Gaussian addition one may instead supply physical
   S_t=s_i exp((b−κ²/2)t+κW_t^P) and a pricing law Q under which the
   same discounted price has the driftless p=1 law with scale κ.
   Its true-martingale pricing label then follows from AX-55. The
   physical Gaussian conditional law follows from the supplied
   Brownian independent-increment model. **Existence/equivalence of
   that pricing law is not proved here.** Neither a good Gaussian fit
   nor the physical drift's sign supplies it.

   Pointwise E_i^drift≤E_i. With the same numerator the enlarged-null
   rejection event is a subset of the old raw rejection event, so no
   raw per-name power improvement at a fixed alternative follows.
   On admissible absorbed paths it still never rejects or enters a
   base/masked e-BH list: training absorption gives E_i^drift=1 and
   first evaluation absorption gives E_i^drift=E_i≤1. A positive
   path with Q_G=0 gives E_i^drift=0. If n_e=1, E_i^drift≤1 on
   every input array, so that name can never be flagged at these levels.

## Proof

**Normalization and domain.** Claim 054 verifies that each CEV g and
the selected Ĝ_i are finite nonnegative jointly measurable functions,
normalized for every training vector, and that the first training
maximizer is measurable even on all-zero training likelihoods.
These are properties of the design, independent of which actual law
generated the array. It also proves Ĝ_i>0 implies G_(i,0)>0
pointwise, including model-impossible arrays.

For (1), at a positive endpoint the triangular substitution from prices
to log returns has absolute Jacobian ∏1/y_j. The transformed law is a
product of normalized normal densities, hence integrates to one. Its
mass at all boundary strata with a zero coordinate is zero. At endpoint
zero its sole mass is the all-zero suffix, whose product reference
measure mass is one. The density is finite and jointly measurable on
the positive-path set and the complementary boundary pieces. All
training/evaluation spaces are standard Borel and the finite product
reference measure is sigma-finite. No conditioning on survival occurs.

**Profile and its boundary.** Write a=b−κ²/2 and w=κ². For each w>0,
a ranges over all real numbers. Expanding the squares and using
Σ(R_j−a_GΔ_j)=0 gives

    Σ(R_j−aΔ_j)²/Δ_j = Q_G+τ_e(a−a_G)².

The log likelihood is therefore

    −(n_e/2)log(2πw)−(1/2)Σlog Δ_j−Σlog y_j
      −[Q_G+τ_e(a−a_G)²]/(2w).

It is maximized in a at a_G. If Q_G>0, its derivative in w is
(Q_G−n_e w)/(2w²), positive below Q_G/n_e and negative above.
This proves the global maximum and (3). If Q_G=0, take a=a_G and
w↓0: the log likelihood tends to +∞. Every fixed w>0 still has a
finite value, so no maximizer exists. The boundary cases outside the
positive-path set are constant in (b,κ), giving exactly the stated
zero/trapped suprema.

Formula (3) is continuous where Q_G>0. The positive-path set, the
residual-zero subset, and the zero-price boundary pieces are Borel.
Their piecewise formula thus proves measurability of D_G directly;
we do not presume that an arbitrary uncountable supremum is measurable.
The finite null maximum is measurable, so D is too. If Ĝ_i>0 and
D<∞, claim 054's support fact gives 0<G_(i,0)≤D<∞. In that case
the ratio is finite. In the other cases it is zero by definition.
Piecewise division establishes measurability and nonnegativity.

**Checking AX-58.** The numerator is a normalized measurable density
depending on training alone in its choice of candidate. The denominator
dominates every finite CEV null density because D≥G_(i,0), and every
Gaussian conditional density because D≥D_G. It is measurable and uses
the same reference measure as all these densities. The actual null
conditional law is one of them by the explicit premise. These check
all AX-58 hypotheses. Its conditional and unconditional moment bounds
give part 2 by direct application, not by reconstructing the source
theorem. Markov gives the strict test bound. For 0<a<1 the p-value
event {z≤a} is {E_i^drift≥1/a}; Markov gives its bound, while a=0
is empty by score finiteness and a=1 is automatic. The union bound
does not require independence.

**Checking AX-53.** Part 1 supplies finite measurable nonnegative
scores at all names, including alternatives with arbitrary laws on the
domain. Part 2 gives every actual null's moment bound. On the fixed
panel these are exactly AX-53's hypotheses, yielding part 3. A
measurable zero mask decreases each score and preserves the same null
moments, so AX-53 applies again using the original family size. The
source's weak threshold is retained; it differs from the strict
per-name test at equality. No FDR conclusion is inferred merely from
being a subset of some other valid list.

**Cost and absorption.** If Ĝ_i=0 both scores are zero. Otherwise,
when D<∞, division by D≥G_(i,0)>0 decreases the old ratio; D=∞
gives zero. This proves pointwise domination and rejection nesting.
If the training endpoint and suffix are zero, every CEV likelihood and
every Gaussian likelihood is one, so both scores equal one. If an
admissible path first hits zero during evaluation, D_G=0, hence the
score is unchanged and at most one by claim 054. Every per-name
threshold exceeds one and every e-BH threshold is at least 1/q_FDR>1;
these paths cannot be selected, including after masking.

With one evaluation increment and two positive endpoints the residual
is exactly zero, so the new score is zero. From a zero endpoint it is
one on the zero suffix and zero on a positive suffix. From a positive
endpoint to zero, a fitted nonabsorbing candidate gives numerator zero;
a fitted absorbing candidate belongs to the null and bounds the score
by one. These exhaust the domain and prove the single-increment limit.
The pricing reading uses only the supplied link and the already cited
AX-03/55 labels, not an inference about a pricing measure from data.

## Checks

`checks/055/check.py` exercises the total diagnostic scorer on fixed
nonnegative arrays, including impossible training histories, resurrection,
absorption, unchanged training fits under changed evaluation data,
zero residuals and a single evaluation increment. It compares the
Gaussian denominator with directly evaluated candidate densities and
checks domination by the old score. Exact finite conditional-density
fixtures add a continuum of null mixtures outside the pilot catalogue,
then enumerate null moments, size and dependent-panel e-BH with the
original family size. These fixtures are not CEV or Gaussian laws.
The previously committed Gaussian profile checks remain applicable.
No diffusion simulations or performance results are claimed.

## Not shown

- The profile and score conclusions in parts 1–4 are formalized in
  `lean/Standalone/D13DriftNull.lean`, proved by `statement_holds` in
  `lean/Novel/D13DriftNullProof.lean`. Gaussian normalization and
  AX-58 (`Novel.SplitLikelihoodDominated.ax58_holds`) are proved from
  Mathlib, not assumed. The score application still uses claim 054's
  AX-55/56 kernel inputs, whose instances are vacuous; FDR remains
  conditional on AX-53, whose instance is degenerate. Part 4's
  pricing interpretation remains commentary, not a formalized result.
- No construction of a pricing measure, proof of its equivalence to
  P, or empirical evidence that actual pricing nulls have these laws.
- No physical drift at every CEV power, continuous coverage of all
  CEV exponents, stochastic volatility, jumps, time-varying Gaussian
  parameters, measurement noise or robustness outside the supplied
  null family. Gaussian membership is a conditional-law premise.
  Evaluating these exact-price densities at rounded quotes is not
  covered; a matched observation likelihood would need its own analysis.
- No confidence coverage of Gaussian drift/volatility or off-grid CEV
  block integrals. Claim 054's finite-catalogue confidence set and old
  band rule do not acquire new null validity merely from (2).
- No useful power, consistency or empirical superiority. Enlarging
  only the denominator decreases the score and may erase evidence.
- No certified floating-point numerator or upper denominator. The
  high-precision implementation is diagnostic; a finite optimizer or
  grid value is not a conservative approximation of a supremum.
  Near zero residuals need particular numerical care. Out-of-domain
  and numerical failures must be reported, not silently discarded.
- No repeated-date or conditional-on-selection guarantee.

## Prior art

[wasserman2019universal] already supplies the composite-null method,
arbitrary fitted density class, conditional likelihoods and the validity
of an upper denominator. Gaussian likelihood maximization is elementary
finite-data algebra; it is not presented as a new statistical principle.
The application-specific work is the exact measurable profile on the
mixed price domain, its infinite boundary, and its combination with
claim 054's support argument to supply finite scores for AX-53
([wang2020false]). The price kernels/labels remain the cited inputs
[makarov2009exact], [etheridge2018continuous] and
[mijatovic2010martingale]. The sources, audited AX-58, D13/D14
findings, refuted filtering target and existing Mathlib likelihood
proofs were checked before proposing. No projection-coverage result
from [park2023robust] or a convex-family result is assumed.

## Review

Reviewer, 2026-10-06, on branch `mathb/d13-drift-null-claim` at `3d48880`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/055/`.
- **Inputs.** AX-58 is source-audited ok at `f8beaf3` (`ledger/AUDIT_LOG.md`). AX-03, AX-53, AX-55 and AX-56 are audited. Claims 053 and 054, the dependencies, are approved.
- **The AX-58 edits** on the branch are status-only.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- **The profile.** With a = b − κ²/2 and w = κ², weighted least squares gives Σ(R_j − aΔ_j)²/Δ_j = Q_G + τ_e(a − a_G)², minimized at a_G. The w-derivative (Q_G − n_e w)/(2w²) changes sign once at w = Q_G/n_e, which gives (3).
- **The boundary.** Q_G = 0 sends the likelihood to +∞ as w ↓ 0, so D_G = ∞ and E = 0.
- **Measurability.** The piecewise construction is measurable directly, without assuming a measurable uncountable supremum.

**Part 2: correct.** This is AX-58. D dominates every finite CEV null density and every Gaussian null density pointwise on the same reference measure. So at any actual null, E[Ĝ/D | U] ≤ ∫_{g_true>0} Ĝ ≤ 1, with D = ∞ mapped to 0. The Gaussian density (1) is the actual conditional law of a physical GBM given its own training prices, by independent increments.

**Part 3: correct.** AX-53 applies to the finite scores.

**Part 4: correct.**
- **Domination.** E^drift ≤ E pointwise.
- **Absorbed paths.** Training absorption makes every likelihood 1. First absorption during evaluation gives D_G = 0, so the score is unchanged and ≤ 1.
- **One evaluation increment.** n_e = 1 always gives Q_G = 0 from a positive endpoint.
- **The pricing link.** The physical-to-pricing link (Girsanov for GBM) is correctly stated as a supplied premise, not proved.

**Checks** (evidence, not proof).
- **(a) The profile.** (3) matches direct Nelder–Mead maximization over (b, κ) on 20 random paths to 2×10⁻¹⁴ in log D_G, and n_e = 1 gives D_G = ∞.
- **(b) Monte Carlo.** Daily prices for two years, training on year one, 20,000 paths per truth, α = 0.1. The catalogue is p ∈ {½, 1, 3/2} × κ ∈ {0.2, 0.3, 0.45}, with the full absorbed CEV kernels (AX-55/56).

  | Truth | Claim 054's E: mean, P(> 1/α) | E^drift: mean, P(> 1/α) |
  |---|---|---|
  | GBM b = 0, σ = 0.30 (in catalogue) | 0.76, 0.0013 | 0.38, 0.0000 |
  | GBM b = 0.10, 0.30, −0.20; σ = 0.30 | 0.75–0.78, ≤ 0.0014 | 0.30–0.38, ≤ 0.0002 |
  | GBM b = 0, σ = 0.35 (off-grid) | **26.6, 0.068** | 0.13, 0.0003 |
  | GBM b = 0.10, σ = 0.25 (both) | **13.2, 0.075** | 0.14, 0.0001 |
  | CEV p = 3/2, κ = 0.3 (alternative) | power 0.409 | power **0.053** |
  | CEV p = 3/2, κ = 0.45 (alternative) | power 0.591 | power **0.198** |

  - E^drift ≤ E held on every path.
  - **The fix works where claim 054 fails.** Off-grid volatility breaks the old score's null mean, as claim 023 showed. The enlarged Gaussian null restores a mean ≤ 1 for any physical drift and volatility.
- **The author's check.** I ran `checks/055/check.py` afterwards. It passes 81 fixed arrays, 27 single-increment arrays, 144 dominance comparisons, and the moment, size and FDR/screen fixtures.

**Gaps.** None.

**Scope; "Not shown" is honest, and the power cost is large.**
1. **This is the first null in the D13 line that is valid for an unknown physical drift and a continuum of volatilities,** with no grid and no TV penalty. It answers the off-grid failure of claims 023 and 054 for the GBM part of the null.
2. **The price is power.** In my daily two-year runs, power against p = 3/2 fell from 41% to 5% (κ = 0.3) and from 59% to 20% (κ = 0.45). The claim correctly asserts no power. The continuous Gaussian null absorbs much of the evidence a mild CEV alternative leaves in daily returns.
3. **Not covered:** physical drift at CEV powers other than 1, stochastic volatility and jumps, rounded quotes (claim 024), and the existence of the pricing measure, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the closed-form Gaussian profile and boundary, AX-58 domination and moment bound, AX-53 FDR and dominance/absorption properties; Nelder-Mead and Monte Carlo checks incl. off-grid nulls and power; scope honest


Reuse the mixed-kernel definitions and support domination of claim 054.
The profile identity, derivative sign and piecewise measurability are
the application obligations. For AX-58 apply the existing Mathlib
integration results behind AX-52/57 with pointwise domination; do not
rebuild universal inference or stochastic calculus. Preserve D_G=∞
at zero residuals and the finite/∞=0 convention. AX-53 applies only
after finiteness is established under all admitted panel laws.

Formalizer B, 2026-10-06, on `formb/d13-drift-null` (stage A, the profile, merged) and `formb/d13-drift-null-score` (the score and parts 1–4). **Status: formalized.** The statement is in `lean/Standalone/D13DriftNull.lean` (`statement := profile ∧ drift`). The proof is `lean/Novel/D13DriftNullProof.lean` (`statement_holds`), which combines `lean/Novel/D13DriftProfileProof.lean` (`profile_holds`) and `lean/Novel/D13DriftScoreProof.lean` (`drift_holds`). There is no `sorry`, and the axiom audit is clean.
- **Inputs.**
  - AX-58 is restated as `Standalone.SplitLikelihoodDominated.AX58` and proved from Mathlib (`Novel.SplitLikelihoodDominated.ax58_holds`). It is applied here, not re-proved.
  - FDR is conditional on AX-53 (claim 053's `AX53`).
  - AX-55 and AX-56 (claims 052 and 054's restatements, on a base carrying a Brownian motion) supply claim 054's kernel normalization and positivity, as in claim 054.
  - The Gaussian family's normalization is **proved**, not cited: the substitution y = x eʳ (`lintegral_image_eq_lintegral_abs_deriv_mul`) and Mathlib's Gaussian integral, chained by claim 054's `chainN_norm`.
- **Encodings.**
  - Arrays are nonnegative: training u ∈ [0,∞)^(k+1), evaluation v ∈ [0,∞)^m, with claim 054's grids, catalogue, chains `gC` and first maximizer `selC`.
  - (1) is `gG`, with the trapped extension, from the last training price.
  - D = max(sup over catalogue nulls of g_ϑ, D_G).
  - The score is AX-58's `Edrift(Ĝ, D)`: 0 if Ĝ = 0 or D = ∞, else Ĝ/D. D > 0 whenever Ĝ > 0, so this is (2).
  - In part 2 the actual conditional law of V given U is, for the name, one catalogue-null density or one Gaussian density (1). The training law is arbitrary.
- **Part 1.**
  - **Supremum.** For every input array, the continuum supremum over b ∈ ℝ, κ > 0 equals the closed form D_G.
  - **Q_G > 0.** (3) holds and is attained at κ² = Q_G/n, b = a_G + w_G/2.
  - **Q_G = 0.** D_G = ∞, with no maximizer.
  - **Boundary.** Off positive paths D_G takes the zero and trapped values.
  - **Measurability.** D_G is measurable from its closed form. D and E^drift are measurable.
  - **Domination and finiteness.** D dominates every catalogue-null and every Gaussian density, and E^drift is finite on every array.
- **Part 2.** For P∘U⁻¹-a.e. u, the integral of E^drift against the actual conditional law is ≤ 1. Also E_P E^drift ≤ 1, P(E^drift > 1/α) ≤ α, and the p-value (1 at E = 0, else min(1, 1/E)) is valid. The union bound holds without independence.
- **Part 3.** Conditional on AX-53, FDR ≤ q|N₀|/m with the original m, with or without a measurable zero mask. e-BH never selects a score ≤ 1.
- **Part 4.**
  - E^drift ≤ E pointwise.
  - Training absorption (zero last training price and zero suffix) gives E^drift = 1.
  - A zero evaluation price from a positive endpoint gives E^drift = E ≤ 1.
  - A positive path with Q_G = 0 gives E^drift = 0.
  - With one evaluation increment, E^drift ≤ 1 on every array.
- **Not formalized.** Part 4's pricing reading (the AX-03/AX-55 labels, and the existence of the pricing law Q) is commentary, as the claim states. Its "not proved here" items stay unproved.
- **Stale prose.** The first "Not shown" bullet ("No Lean formalization of this application or AX-58 yet") is routed to mathb (`board/inbox/mathb/2026-10-06-claim055-stale-prose.md`).
