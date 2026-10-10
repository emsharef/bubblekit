---
id: "057"
title: "D13: exact Gaussian null profiling over declared drift and scale intervals"
status: formalized
depends_on: ["053", "054", "055", "056"]
axioms_used: [AX-03, AX-53, AX-55, AX-56, AX-58]
formal: lean/Standalone/D13DriftRect.lean
direction: D13
---
## Statement

**Conditional on the cited inputs and the explicit observation/pricing
premises below.** The general mechanism remains the composite-null split
likelihood ratio of [wasserman2019universal], Theorem 3, Remark 4 and
Section 6 (source-audited AX-58). The new application computes its
Gaussian denominator on a compact drift/scale rectangle. No general
inference theorem or stochastic theory is re-proved.

Keep claim 056's fixed finite panel, positive known starts, deterministic
grids and nonempty training/evaluation split, ordered finite CEV
catalogues containing a null p≤1, and mixed reference measure μ_CEV.
Keep the training-only normalized selected evaluation density Ĝ_i and
**all** finite catalogue nulls in G_(i,0), including their scales outside
the Gaussian interval below. These are design functions independent of
the actual physical law. The observation domain remains all nonnegative
price arrays after the known start, with arbitrary joint panel law.

Before any observations, declare for each name finite closed intervals

    B_i=[b_lo,i,b_hi,i],        C_i^scale=[s_lo,i,s_hi,i],
    b_lo,i≤b_hi,i,              0<s_lo,i≤s_hi,i<∞.             (1)

Either interval can be a singleton. Here b is physical proportional
drift of the discounted price; κ is its Gaussian scale per square root
of the declared time unit. For annual units these are annual drift and
annualized volatility. Define w_lo,i=s_lo,i² and w_hi,i=s_hi,i².

Supply a fixed true-null set N₀. At each i∈N₀ the actual evaluation law
given its own training U_i must almost surely be either a retained
finite CEV null conditional density, or g^G_(b,κ) of claim 055 for some
fixed b∈B_i, κ∈C_i^scale. The choice and parameters can differ across
names; training laws are unrestricted. Alternative names have arbitrary
laws on the domain. Gaussian membership is the independent-normal
log-return conditional-law premise, not merely bounds on drift and
instantaneous volatility.

Thus every Gaussian null in the rectangle and every retained finite
CEV null is covered. **A continuum of CEV exponents or scales outside
the finite catalogue is not covered by imposing (1).** The continuous
profile below concerns only the Gaussian (p=1) family. CEV catalogue
nulls are retained even outside the Gaussian rectangle, rather than
silently deleted to increase the score.

Set

    D_(G,B,C) = max_(b∈B_i, κ∈C_i^scale) g^G_(b,κ),
    D_(B,C)   = max(G_(i,0),D_(G,B,C)),
    E_i^(B,C) = 0                      if Ĝ_i=0,
              = Ĝ_i / D_(B,C)         otherwise.             (2)

1. **Exact finite profile.** On a positive evaluation path from a
   positive last training price, use R_j, Δ_j, n_e, τ_e, a_G, Q_G,
   ℓ_G(b,w) and A_G(b) from claim 056. Let
   clip_[l,h](x)=min(h,max(l,x)). The maximum is the largest value of
   ℓ_G at the following at most five pairs:

   - For each c∈{b_lo,b_hi}, the drift-edge candidate

         (c, clip_[w_lo,w_hi](v_c)),
         v_c = 2 A_G(c)/(n_e+sqrt(n_e²+τ_e A_G(c))).           (3)

     If A_G(c)=0 this formula gives v_c=0, so the variance is w_lo.
   - For each d∈{w_lo,w_hi}, the variance-edge candidate

         (clip_[b_lo,b_hi](a_G+d/2), d).                      (4)

   - The interior candidate

         (a_G+Q_G/(2n_e), Q_G/n_e)                            (5)

     if both coordinates lie in their respective closed intervals.
     Since w_lo>0, this automatically excludes Q_G=0.

   Duplicate pairs are harmless, including singleton intervals. Every
   candidate is feasible. The Gaussian price density includes the
   Jacobian ∏1/y_j through ℓ_G, exactly as in claim 056.
   The maximum is strictly positive and finite on this positive-path
   set, even when Q_G=0 or n_e=1. On the remaining mixed-domain strata
   it is zero if the starting endpoint is positive and any evaluation
   price is zero; from endpoint zero it is one on the all-zero suffix
   and zero otherwise. Consequently D_(G,B,C) and D_(B,C) are finite
   nonnegative measurable functions, and E_i^(B,C) is finite,
   nonnegative and measurable on every nonnegative input array.

2. **Conditional moments and inference.** For every actual null,

         E_P[E_i^(B,C) | U_i]≤1,       E_P E_i^(B,C)≤1.        (6)

   The strict test E_i^(B,C)>1/α_i has size at most α_i for fixed
   0<α_i<1. Its reciprocal capped at one, set to one at score zero,
   is a valid p-value. A union bound gives any-false-rejection
   probability at most Σ_(i∈N₀)α_i. Claim 053's base e-BH rule with
   weak threshold k E_[k]^(B,C)≥m/q_FDR has
   FDR≤q_FDR|N₀|/m, conditional on AX-53, under arbitrary panel
   dependence. Measurable zero masks preserve the bound with the
   original m. No arbitrary postfiltering or conditional-on-screen
   FDR conclusion is asserted.

3. **Comparison and boundaries.** With the same numerator and retained
   CEV null maximum, inclusion of Gaussian rectangles decreases the
   score. In particular, with B fixed,

         E_i^drift ≤ E_i^B ≤ E_i^(B,C) ≤ E_i.                 (7)

   Here the outer scores are claims 055 and 054, and E_i^B is claim
   056. The corresponding strict per-name rejection events are nested
   under every actual law. This is only weak power ordering. For nested
   scale intervals increasing to (0,∞), E_i^(B,C) decreases to E_i^B,
   including its zero-at-infinite-supremum case. With a fixed positive
   lower scale, the zero-residual Gaussian maximum is always finite;
   no automatic zero score follows from Q_G=0 or one increment.
   Admissible absorbed paths retain score at most one and cannot enter
   the base or zero-masked e-BH list at q_FDR<1.

4. **Pricing and misspecification scope.** The bubble interpretation
   requires every actual pricing-null name to satisfy the displayed
   physical conditional-law premise. The finite CEV specialization
   retains P=Q with AX-03's p≤1 label; for the Gaussian addition supply
   physical GBM with parameters in (1) and a pricing law under which
   that discounted price is driftless p=1 with the same κ (AX-55).
   Neither existence nor equivalence of that pricing law is proved.
   A Gaussian parameter outside the rectangle loses this guarantee
   unless a retained finite CEV null represents the same law. A D14
   conditional-law envelope can be considered separately; the interval
   declarations or training point estimates do not supply one.

## Proof

**General mechanism and normalized design.** Claims 054–056 establish
that Ĝ_i is jointly measurable, finite, nonnegative, normalized at
every training vector and chosen using training alone, including all-zero
training likelihoods. They also establish Ĝ_i>0 ⇒ G_(i,0)>0 pointwise.
Each Gaussian conditional density is normalized relative to μ_CEV^n_e,
by the log-return Jacobian from a positive endpoint and the trapped
extension from zero. Restricting its parameter set changes none of these
facts. The standard Borel observation spaces and common sigma-finite
reference measure are unchanged. No survival conditioning occurs.

**Maximization on the rectangle.** The rectangle in (b,w) is compact
and nonempty, with w bounded away from zero. The positive-path log
likelihood is continuous, so it attains a finite maximum. Use claim
056's finite-data identity

    ℓ_G(b,w) = C − (n_e/2)log w − A_G(b)/(2w)
                 −τ_e(a_G−b)/2 −τ_e w/8.                    (8)

On a drift edge b=c with A_G(c)>0, the derivative in w has the sign
of 4A_G(c)−4n_e w−τ_e w²: it is positive below v_c of (3) and
negative above. Hence its maximum over [w_lo,w_hi] is the clipped
root. If A_G(c)=0, the derivative is strictly negative for every w>0,
so w_lo is the maximizer, again (3). This handles each drift edge
including its corners.

On a variance edge w=d, differentiating with respect to b gives
τ_e(a_G−b)/d+τ_e/2 with strictly negative slope −τ_e/d. Hence the
unique unconstrained drift maximum is a_G+d/2, and its clipped value
is the maximum on that edge, proving (4).

If both intervals have nonempty interior, any maximizer in the
interior of their product has both partial derivatives zero. The drift
equation gives b=a_G+w/2; substitution into the variance equation
gives w=Q_G/n_e, hence (5). If the maximizer is on the boundary, it
lies on one of the four edges and its value is bounded by that edge's
listed maximum. If an interval is a singleton, its two coincident
edges exhaust the rectangle and the same edge argument applies.
Every candidate is feasible; therefore the largest candidate value is
exactly the global maximum. When Q_G=0, (5) is infeasible but the four
edge candidates are still well defined and finite. The argument needs
no optimizer convergence claim, local-to-global concavity assumption,
or replacement of the rectangle by a numerical grid.

**Domain and measurability.** Formula (3), including its zero-residual
root, is continuous before and after clipping; (4) is continuous.
Candidate (5) is used on a Borel set; setting its exponential value to
zero off that set makes the finite maximum a measurable density value.
The positive-path set and zero-state strata are Borel. Their displayed
mixed-density values follow from claim 055's Gaussian extension and
are constant in the parameters. This proves finite measurability of
the supremum directly. G_(i,0) is also finite measurable. If Ĝ_i>0,
its support implication gives 0<G_(i,0)≤D_(B,C)<∞, making (2) finite.
Piecewise division establishes the remaining score properties, even
at alternative names with arbitrary laws on the domain.

**Applying AX-58 and AX-53.** The selected numerator is a normalized
training-only conditional density. The measurable denominator is at
least each retained CEV null by its first maximum term, and at least
each Gaussian conditional density in the rectangle by its second.
The actual conditional null law has one of these densities by premise.
These verify all AX-58 hypotheses and its zero-numerator convention,
so (6) follows by application of that cited input. Markov's inequality
gives strict size and the reciprocal p-value guarantee; the event for
p-value ≤a is score ≥1/a when 0<a<1. The p-value endpoints follow
from score finiteness. The union bound does not require independence.
Finite nonnegative scores on the whole panel and null means at most
one meet AX-53's premises, yielding the stated FDR bound. A measurable
zero mask reduces scores and null moments while keeping original m,
so the same result applies. No FDR inheritance by arbitrary subsets is
used.

**Ordering, limits and absorption.** Enlarging the Gaussian parameter
set increases its maximum and the full denominator, while the numerator
and retained CEV null are unchanged. If the numerator is zero all
scores are zero; otherwise division and the earlier zero-at-infinity
convention prove (7) and the rectangle ordering. For increasing scale
intervals whose union is (0,∞), the suprema increase to the claim-056
supremum by its definition over that union; the ratios decrease to its
score, including a zero limit when the supremum diverges. Strict test
event nesting holds pointwise and hence under any alternative law.
On admissible training absorption with a zero suffix, all densities
are one; on first evaluation absorption the Gaussian term is zero and
the old score remains at most one by claim 054. All strict per-name
thresholds and all possible e-BH thresholds exceed one. The pricing
reading uses only the separately supplied link and AX-03/55 labels.

## Checks

`checks/057/check.py` checks fifteen fixed profiles by an independent
scalar search of directly evaluated normal densities, including all
four edges, all four corners, an interior solution, singleton intervals,
zero residuals and one increment. It checks 135 direct density bounds,
price Jacobians and zero-state strata. On 81 fixed nonnegative arrays it
checks three nested scale intervals against claim 056, unchanged training
selection and raw-score domination. The total diagnostic adapter
`checks/057/scoring.py` retains outside-domain and numerical-failure
records as zero scores; an infinite computed rectangle supremum is a
failure, since the mathematical supremum here is finite. Invalid fixed
configuration stops a run. No simulation or performance result is given.
Checks are not proofs or numerical certificates.

## Not shown

- Parts 1–3 are formalized in `lean/Standalone/D13DriftRect.lean`,
  proved by `lean/Novel/D13DriftRectProof.lean`: the exact five-candidate
  profile is proved, not assumed. AX-58 is proved from Mathlib. FDR
  remains conditional on AX-53 (a degenerate Lean instance), and claim
  054's kernels on AX-55/56 (vacuous Lean instances). Claim 056's E^B
  enters (7) through its supremum definition; its closed-form profile
  is not used. Part 4's pricing reading remains commentary, conditional
  on the supplied pricing law and AX-03/55 labels (vacuous instances);
  existence or equivalence of that law is not formalized.
- No continuous CEV scale/exponent coverage beyond the retained finite
  catalogue. Bounds on drift and volatility alone do not give the
  required Gaussian conditional law. SV, jumps and time-varying
  parameters remain outside the guarantee.
- No economic justification or data-based certification of either
  interval, no correction for choosing intervals after observing data,
  no out-of-bound Gaussian calibration absent another included law,
  and no repeated-date or selection-conditional guarantee.
- No useful power gain, consistency or practical superiority proved.
  The same finite CEV null remains, which can limit any gain.
- No positive-price likelihood formula for rounded/noisy observations,
  new confidence bands, or Gaussian-parameter coverage from the score.
- No certified likelihood arithmetic. The exact finite candidate formula
  is not a floating-point upper certificate; approximate numerator and
  denominator errors need control even when no failure is reported.

## Prior art

The statistical mechanism and arbitrary fitted numerator are supplied by
[wasserman2019universal], and arbitrary-dependence FDR by [wang2020false]
through AX-53. The source/full-text review and AX-58 application in claims
055/056 are reused. The new finite-data calculation is constrained
Gaussian maximization on a rectangle, using edge derivatives already
computed for claim 056; it is not a new inference principle. Checked the
current D13/D14 findings, claim 056's review and committed reviewer-script
scope, the refuted postfilter target and existing formalization route.
No reviewer power number is reproduced or adopted as a premise here.
Stochastic kernels and labels remain the same cited inputs; no new
ledger axiom or reconstruction of textbook theory is needed.

## Review

Reviewer, 2026-10-06, on branch `mathb/d13-volatility-range` at `f7a00c5`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/057/`.
- **Inputs.** AX-58 is source-audited, and AX-03, AX-53, AX-55 and AX-56 are audited. Claims 053–056, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/057/reproduce.py`, with its rerun command and seed (`default_rng(57)`) in its header. It is not a CI `check.py`.
- **Experiment 024.** The branch also registers the analyst's experiment 024 design. It has no results yet and is not reviewed here.

**Part 1: correct.**
- **Existence.** The (b, w) rectangle is compact with w ≥ w_lo > 0, so the continuous log likelihood (8) attains a finite maximum, including when Q_G = 0 or n_e = 1.
- **Drift edges (3).** On b = c, ∂_w ℓ has the sign of 4A − 4n_e w − τ_e w², which is strictly decreasing. So the edge maximum is the root clipped to [w_lo, w_hi]. When A = 0 the derivative is negative everywhere, giving w_lo.
- **Variance edges (4).** On w = d, ℓ is strictly concave in b with stationary point a_G + d/2, so the clipped value is the edge maximum.
- **The interior (5).** The interior critical point is claim 056's. Every boundary maximizer lies on an edge, and every candidate is feasible, so the candidate maximum is the global maximum.
- **The mixed-domain strata** are claim 055's.

**Part 2: correct.** The denominator dominates every retained CEV null and every Gaussian null in the rectangle, so AX-58 gives (6) and AX-53 the FDR bound, as in claims 055–056.

**Part 3: correct.** Nested parameter sets give nested suprema, which gives (7). As C increases to (0, ∞), the suprema increase to claim 056's.

**Checks** (evidence, not proof).
- **(a) The profile.** 60 random rectangle profiles, including singleton intervals, Q_G = 0 and n_e = 1, match direct bounded Nelder–Mead maximization to a relative 9×10⁻¹⁶. All are finite.
- **(b) Monte Carlo.** Daily prices for two years, training on year one, 10,000 paths per truth, B = [−0.10, 0.20], α = 0.1. The catalogue is p ∈ {½, 1, 3/2} × κ ∈ {0.2, 0.3, 0.45} with the full absorbed kernels. Cells are mean / P(score > 1/α); power for the alternatives.

  | Truth | 054 E | 055 E^drift | 056 E^B | 057, C = [0.25, 0.35] | 057, C = [0.28, 0.32] |
  |---|---|---|---|---|---|
  | GBM b = 0.05, σ = 0.33 (in both rectangles) | 4.4 / 0.034 | 0.17 / 0.0003 | 0.18 / 0.0003 | 0.18 / 0.0003 | 0.31 / 0.0027 |
  | GBM σ = 0.30 (on grid) | 0.77 / 0.0017 | 0.39 / 0.0001 | 0.42 / 0.0001 | 0.42 / 0.0001 | 0.42 / 0.0001 |
  | GBM σ = 0.40 (outside both) | 5.9 / 0.041 | 0.12 / 0.0001 | 0.13 / 0.0002 | **1.22 / 0.021** | **5.5 / 0.040** |
  | GBM σ = 0.25 (outside the narrow one) | 10 / 0.086 | 0.15 / 0.0002 | 0.15 / 0.0002 | 0.20 / 0.0007 | **2.15 / 0.023** |
  | CEV p = 3/2, κ = 0.3 | 0.406 | 0.056 | 0.073 | **0.125** | **0.239** |
  | CEV p = 3/2, κ = 0.45 | 0.596 | 0.200 | 0.229 | **0.445** | **0.524** |

  - The ordering (7) held on every path.
- **The author's check.** I ran `checks/057/check.py` afterwards. It passes 15 independent optimizations, 135 density bounds and 81 arrays with nested intervals.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **A declared scale interval is where the power is.** This confirms the diagnosis in my claim-056 review: restricting the drift recovered almost nothing, whereas restricting the scale recovers much of the power claim 055 gave up. At κ = 0.45, power goes from 20% to 44–52% against claim 054's 60%; at κ = 0.3, from 6% to 13–24%. The true-martingale nulls inside the rectangle keep mean ≤ 1 and essentially no false alarms.
2. **The price is sensitivity to the declaration.** A true Gaussian scale outside the declared interval loses the guarantee, as stated. In my runs that gave a null mean above one (1.2–5.5) and false alarms of 2–4% at α = 0.1. The narrower the interval, the more power and the more fragile.
3. **The interval must therefore be justified in advance,** not chosen from the data. Choosing it from training data voids the guarantee, as the claim says, and how to declare it for a real asset is unaddressed. Experiment 024's preregistered design measures exactly this trade-off.
4. **Not covered:** stochastic volatility, jumps (claim 026), rounding (claim 024) and the pricing link, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived rectangle existence, edge and interior maximizers and their completeness, AX-58 domination, AX-53 and nested ordering; committed review script; power recovery and out-of-interval fragility stated

Formalizer B, 2026-10-06, on `formb/d13-drift-scale-rectangle` (stage 1, the exact profile, merged) and `formb/d13-drift-scale-rectangle-score` (the score and parts 1–4). **Status: formalized.** The statement is in `lean/Standalone/D13DriftRect.lean` (`statement := profile ∧ score`). The proof is `lean/Novel/D13DriftRectProof.lean` (`statement_holds`), which combines `lean/Novel/D13DriftRectProfileProof.lean` (`profile_holds`) and `lean/Novel/D13DriftRectScoreProof.lean` (`score_holds`). There is no `sorry`, and the axiom audit is clean.
- **Inputs.**
  - AX-58 is proved from Mathlib (`Novel.SplitLikelihoodDominated.ax58_holds`) and applied.
  - FDR is conditional on AX-53 (claim 053's `AX53`).
  - AX-55 and AX-56 supply claim 054's kernels, as in claims 054 and 055.
  - The Gaussian normalization is proved (claim 055's `gGN_norm`).
- **Part 1.**
  - **Exact supremum.** For every nonnegative input array, the continuum supremum of (1) over b ∈ [b_lo, b_hi], κ ∈ [s_lo, s_hi] (0 < s_lo) equals `DGR`. On positive paths `DGR` is the exponential of the largest of `ellG` (claim 056's ℓ_G, with the price Jacobian) at the ≤ 5 candidates: the drift edges (3), at the clipped root 2A_G(c)/(n + √(n² + τA_G(c))); the variance edges (4); and the interior pair (5) when feasible. On the other strata it takes claim 055's zero/trapped values.
  - **Feasibility.** Every candidate lies in the rectangle.
  - **The supremum.** It is finite, positive on positive paths and measurable.
  - **Method.** Proved with no optimizer, grid or concavity assumption. A derivative-sign unimodality lemma handles the drift-edge profile (root identity τv² + 4nv = 4A) and the ridge b = a_G + w/2 (peak Q_G/n). A covering argument assigns every rectangle point to a candidate.
  - **The score (2).** It is finite and measurable, 0 exactly when Ĝ = 0, and positive otherwise, since claim 054's support gives G₀ > 0.
- **Part 2.** The null law is a catalogue null or a Gaussian (1) with (b, κ) in the rectangle; the training law is arbitrary. Under it:
  - for a.e. training value, the integral against the actual conditional law is ≤ 1, and E_P E ≤ 1;
  - the strict test has size ≤ α, and the p-value (1 at 0, else min(1, 1/E)) is valid.

  On the panel, the union bound holds without independence. Conditional on AX-53, base and zero-masked e-BH with the original m have FDR ≤ q|N₀|/m, and e-BH never selects a score ≤ 1.
- **Part 3.**
  - **(7).** E^drift ≤ E^B ≤ E^(B,C) ≤ E pointwise, so the strict rejection events are nested.
  - **Rectangles.** Enlarging the rectangle decreases the score.
  - **Limit.** For scale intervals [s_k, S_k] with s_k ↓ 0 and S_k ↑ ∞, the scores decrease and converge to E^B, including the zero limit when the supremum diverges.
  - **Absorption.** Training absorption gives score 1. A zero evaluation price from a positive endpoint gives score = E ≤ 1.
- **Encoding of claim 056.** E^B enters only through its definition: AX-58's ratio with denominator max(G₀, sup of (1) over b ∈ B, κ > 0) (`DGB`). Claim 056's closed form for that supremum is not used. Claim 056 (formalizer's) is not yet formalized.
- **Not formalized.** Part 4's pricing reading (AX-03/55 labels; the pricing law's existence) is commentary.
