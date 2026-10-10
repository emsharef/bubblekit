---
id: "056"
title: "D13: exact likelihood profiling under a declared physical-drift interval"
status: formalized
depends_on: ["053", "054", "055"]
axioms_used: [AX-03, AX-53, AX-55, AX-56, AX-58]
formal: lean/Standalone/D13BoundedDrift.lean
direction: D13
---
## Statement

**Conditional on the cited inputs and the observation/pricing premises
below.** The mechanism is a split likelihood ratio with a dominating
composite-null denominator, already supplied by [wasserman2019universal]
Theorem 3, Remark 4 and Section 6, source-audited as AX-58. The work here
is the constrained finite-data likelihood maximization and checking that
application's hypotheses. General inference theory is not re-proved.

Keep claim 055's fixed finite panel, known positive starts, deterministic
grids and nonempty split, finite ordered CEV catalogues containing a p≤1
candidate, mixed reference measure μ_CEV, and training-only selected
normalized evaluation density Ĝ_i. Keep the finite CEV null maximum
G_(i,0) and the old claim-054 score E_i. These are design functions;
the actual law need not be the finite-catalogue law.

For each name declare a nonempty finite closed interval
B_i=[b_lo,i,b_hi,i] before observing any data; equality of endpoints is
allowed. Time is measured in the declared units (years for annual drift).
The parameter b is proportional physical drift of the discounted price,
not its log-return mean. The whole panel has an arbitrary joint physical
law on the nonnegative price arrays. Supply a fixed set N₀ of actual
null names. For each i∈N₀ its evaluation law conditional on its own
training U_i must, almost surely, have either one of the retained finite
CEV null densities or claim 055's Gaussian price density g^G_(b,κ),
for fixed b∈B_i and any fixed κ>0. Parameters and the selected null
family may differ across names; the training law is unrestricted.
There is no conditional-law premise for alternatives.

Thus the new guarantee covers **every law satisfying this conditional
Gaussian/CEV premise**, uniformly over the declared Gaussian drift
interval and all positive Gaussian scales. Merely having drift inside
B_i, without this conditional-law premise, is insufficient. It does not
cover arbitrary stochastic volatility, jumps or time-varying drift.

Set

    D_(G,B_i) = sup_(b∈B_i, κ>0) g^G_(b,κ),
    D_(B_i) = max(G_(i,0), D_(G,B_i)),
    E_i^B = 0              if Ĝ_i=0 or D_(B_i)=∞,
          = Ĝ_i/D_(B_i)   otherwise.                         (1)

The supremum is over the entire interval and all positive scales.
The second case has a strictly positive finite denominator.

1. **Exact profile, including the boundaries.** On a strictly positive
   evaluation path starting at a positive last training price, use claim
   055's R_j=log(y_j/y_(j−1)), Δ_j>0, n_e≥1, τ_e=ΣΔ_j,
   a_G=ΣR_j/τ_e and Q_G=Σ(R_j−a_GΔ_j)²/Δ_j. Suppress i.
   For w=κ²>0 define

       ℓ_G(b,w) = −(n_e/2)log(2πw)−(1/2)Σlog Δ_j−Σlog y_j
                   −Σ[R_j−(b−w/2)Δ_j]²/(2wΔ_j),
       A_G(b) = Q_G+τ_e(a_G−b)².                            (2)

   Here A_G(b) is a residual function local to this profile, distinct
   from the D14 Gaussian affinity A_G without an argument.
   If Q_G=0 and a_G∈B, then D_(G,B)=∞. Otherwise, for each endpoint
   c∈{b_lo,b_hi} put

       w_c = 2 A_G(c)/(n_e+sqrt(n_e²+τ_e A_G(c))).             (3)

   These endpoint variances are strictly positive. Form the candidate
   pairs (b_lo,w_blo), (b_hi,w_bhi), and additionally

       (a_G+Q_G/(2n_e), Q_G/n_e)                             (4)

   if Q_G>0 and the first coordinate lies in B. Then

       log D_(G,B) = max over these candidates of ℓ_G(b,w).   (5)

   Duplicate endpoints are harmless. From a positive training endpoint
   any zero evaluation price gives D_(G,B)=0. From endpoint zero the
   supremum is one on the all-zero suffix and zero otherwise. These
   formulas make D_(G,B) extended measurable and E_i^B finite,
   measurable and nonnegative on every nonnegative input array,
   including arrays impossible under all the stated models.

2. **Calibration and false discoveries.** Under every actual null
   conditional law just specified,

       E_P[E_i^B | U_i]≤1,        E_P E_i^B≤1.                (6)

   The strict test E_i^B>1/α_i has size at most α_i for any fixed
   0<α_i<1. Setting z_i=1 at E_i^B=0 and otherwise
   z_i=min(1,1/E_i^B) gives a valid p-value; the probability of any
   false rejection is at most Σ_(i∈N₀)α_i without independence.
   Applying claim 053's base e-BH rule, with its weak rank threshold
   k E_[k]^B≥m/q_FDR, gives FDR≤q_FDR|N₀|/m conditional on AX-53.
   Measurable zero masks preserve this guarantee with the original m.
   There is no conditional-on-screen FDR guarantee or permission to
   trim a finished discovery list arbitrarily.

3. **Declared choice and score ordering.** With a fixed numerator and
   finite CEV null, B⊆B′ implies E_i^B≥E_i^B′ pointwise, and

       E_i^drift ≤ E_i^B ≤ E_i.                              (7)

   Therefore the strict per-name rejection sets are nested in this
   order, at any fixed level and any actual alternative law. This is
   weak power ordering only, not proof of useful power or superiority.
   Increasing intervals whose union is ℝ give scores decreasing to
   E_i^drift. The interval cannot be chosen after inspecting the scores
   to obtain the most favorable rejection; no such selection guarantee
   is asserted. Absorbed admissible paths still have score at most one
   and cannot enter a base or zero-masked e-BH list. With n_e=1,
   Q_G=0 but the Gaussian supremum is finite when a_G lies outside B:
   claim 055's automatic zero on every positive one-increment path
   does not carry over. No positive one-increment power is asserted.

4. **Pricing and misspecification.** For a bubble interpretation supply
   the same physical-to-pricing link as claim 055: every actual pricing
   null must obey the displayed physical conditional-law premise. One
   specialization retains P=Q for the finite CEV null, with AX-03's
   label, or supplies physical GBM with b∈B, κ>0 and a pricing law
   under which that discounted price is driftless p=1 with scale κ,
   whose true-martingale label follows from AX-55. Existence or
   equivalence of the pricing law is not proved. If the actual Gaussian
   drift lies outside B, the bounded-Gaussian guarantee no longer
   applies; another retained null representation or a separate D14
   misspecification bound would be required. Membership in B is a
   premise, not something established by failing to reject a drift test.

## Proof

**Domain and normalization.** Approved claims 054 and 055 verify that
Ĝ_i is a finite measurable conditional density normalized at every
training vector, including those with zero training likelihood, and
that Ĝ_i>0 implies G_(i,0)>0 pointwise. They also verify each Gaussian
conditional density's normalization relative to μ_CEV^n_e: on positive
prices it is a product normal density under log returns with Jacobian
∏1/y_j; from endpoint zero it is unit mass on the all-zero suffix.
Restricting the Gaussian parameter set does not change these facts.
The observation spaces remain standard Borel with common sigma-finite
reference measure. No conditioning on survival is introduced.

**Constrained maximum.** Set n=n_e, τ=τ_e and a=a_G within this proof.
The weighted residual identity in claim 055 gives, with a constant C
independent of (b,w),

    ℓ_G(b,w) = C − (n/2)log w − A_G(b)/(2w)
                 − τ(a−b)/2 − τw/8.                        (8)

For fixed b with A_G(b)>0, its derivative in w has the sign of
4A_G(b)−4nw−τw². This expression is strictly decreasing on w>0,
positive at zero and negative eventually. Its unique positive root is
(3), obtained by rationalizing the quadratic root. Thus (3) is the
unique global fixed-b maximizer; the likelihood tends to zero at
both variance boundaries.

If Q_G=0 and a∈B, take b=a and w↓0 in (8). The term −(n/2)log w
forces ℓ_G→∞ while the remaining w-dependent term tends to zero.
No fixed w>0 has infinite likelihood. This proves the exceptional case,
including a equal to either endpoint and singleton intervals.

Otherwise δ=Q_G+τ dist(a,B)² is strictly positive. For every b∈B,
A_G(b)≥δ. Since B is compact, the linear term −τ(a−b)/2 is bounded,
and (8) tends uniformly to −∞ as w↓0 (the term −δ/(2w) dominates
|log w|), and as w↑∞ (the term −τw/8 dominates). Comparing with any
fixed feasible pair, choose a common compact variance interval outside
which the log likelihood is smaller. Continuity on its product with B
then gives a global maximizer.

If its drift coordinate is an endpoint, the preceding fixed-b
calculation forces (3). If it is interior, differentiation in b in
(8) gives b=a+w/2. Substituting this value into the derivative in w
gives w=Q_G/n. This can be positive only if Q_G>0, and yields (4).
These cases exhaust the maximizers, including a singleton B where
only the endpoint case is possible. Every listed pair is feasible;
therefore their largest likelihood equals the global supremum (5).
This also treats Q_G=0 with a outside B: δ>0, only endpoints qualify.

**Measurability and finiteness.** Each formula is continuous where its
strict inequalities and positive variance permit evaluation. The
exceptional set {Q_G=0, a_G∈B}, candidate-feasibility tests and price
boundary strata are Borel. The piecewise finite maximum (with an
optional candidate) consequently gives an extended measurable D_(G,B).
The zero/trapped values follow directly from the constant-in-parameter
Gaussian density on those strata. No general measurability of an
uncountable supremum is assumed. The maximum with G_(i,0) is measurable.
When Ĝ_i>0 and this maximum is finite, support domination gives a
strictly positive denominator, so (1) is finite. Its other values are
zero. This proves the all-array requirements, including alternatives.

**Applying the known inference results.** The normalized numerator is
chosen from training alone. The measurable denominator dominates every
finite CEV null by its first maximum term and every Gaussian null with
b∈B by its second. The actual null has one of these conditional
densities by premise. These are exactly AX-58's hypotheses and ratio
conventions, so its moment conclusions yield (6). Markov's inequality
gives the strict size bound and the p-value bound (at 0<a<1 the event
z_i≤a is E_i^B≥1/a; the endpoints follow from finiteness). The union
bound needs no panel independence. Finite nonnegative measurable scores
at all names and (6) at the actual nulls are exactly AX-53's hypotheses.
Applying it gives part 2. Zero masking reduces each score and preserves
null moments, so the same application works at original m. This does
not appeal to an invalid inheritance of FDR by arbitrary subsets.

**Ordering and scope.** Inclusion of parameter sets increases the
supremum, and all denominators include G_(i,0). Ordinary division when
the numerator is positive and the zero-at-infinity convention prove
(7) and the interval ordering. For intervals increasing to ℝ, the
suprema increase to the unrestricted supremum by the definition of a
supremum over a union; ratios then decrease to the stated limit,
including an infinite limiting denominator. Strict rejection nesting
is pointwise and hence holds under any law. If training ends at zero
and the suffix is all zero, every likelihood is one; if first absorption
occurs in evaluation, D_(G,B)=0 and claim 054's score is unchanged and
at most one. All rejection/rank thresholds exceed one. Finally n_e=1
forces Q_G=0, so part 1 gives the stated distinction according to a_G.
Pricing labels use the supplied link and AX-03/55 only. They do not
follow from the likelihood maximization itself.

## Checks

`checks/056/check.py` compares seven fixed constrained profiles with an
independent scalar optimization of directly evaluated normal densities,
checks 105 pointwise candidate-density bounds, endpoint/interior and
singleton solutions, both zero-residual cases, a single increment,
price Jacobians and zero-state strata. It checks the score ordering for
four nested intervals on 81 fixed nonnegative arrays, retaining training
fits and boundary/failure records. The total diagnostic adapter is
`checks/056/scoring.py`; invalid fixed drift bounds stop a run, while
reported data/profile failures get zero evidence without raw-score
fallback. No diffusion simulations or performance results are supplied.
These are checks, not proofs or certified upper rounding.

## Not shown

- The exact profile and score results are formalized in
  `lean/Standalone/D13BoundedDrift.lean`, proved by
  `lean/Novel/D13BoundedDriftProof.lean`; AX-58 is proved from Mathlib.
  FDR remains conditional on AX-53 (a degenerate instance), and the
  CEV kernels on AX-55/56 (vacuous instances). Part 4's supplied pricing
  link and the interval-choice and power remarks remain commentary.
  Strict rejection-set nesting is not separately formalized, although
  the pointwise score ordering from which it follows is proved.
- No validity for arbitrary physical laws merely sharing a bounded
  drift, unknown time-varying parameters, SV, jumps or out-of-bound
  Gaussian drift. No economic justification of a particular interval.
- No validity from choosing the drift interval after seeing training
  or evaluation data, no repeated-date guarantee, and no practical
  power recovery established. Sensitivity rows cannot be searched for
  a favorable result and then reported as a single prespecified test.
- No observation model for rounded or noisy prices; claim 024's
  conditional cell likelihood is not computed by evaluating this
  continuous density at representatives.
- No certified numerical numerator or upper denominator. Numerical
  failures must stay as zero records; successful computations also
  need error control to obtain a formal implemented-score guarantee.
- No extension of claim 054's confidence sets or block-integral bands
  to the newly admitted Gaussian parameters.

## Prior art

The mechanism is composite-null universal inference, already in
[wasserman2019universal], with arbitrary dependence handled by
[wang2020false] via AX-53. Re-read the registered full text's Theorem 3,
Remark 4, likelihood-upper-bound paragraph and conditional-likelihood
paragraph, the AX-58 entry, claims 054/055, current D13/D14 findings,
and the refuted postfilter target before proposing. The explicit
constrained Gaussian maximum is elementary finite-data algebra, not a
new statistical method or a new cited stochastic input. Existing
Mathlib likelihood work and claim 055's source/application split supply
the formal route; no general inference theory should be reconstructed.

## Review

Reviewer, 2026-10-06, on branch `mathb/d13-bounded-drift` at `aa583e5`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/056/`.
- **Inputs.** AX-58 is source-audited, and AX-03, AX-53, AX-55 and AX-56 are audited. Claims 053–055, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/056/reproduce.py`, with its rerun command and seed (`default_rng(56)`) in its header. It is not a CI `check.py`.
- **Experiment 023.** The branch also registers the analyst's experiment 023 design. I did not review it as an experiment, since it has no results yet.

**Part 1: correct.**
- **The likelihood (8).** The log mean is (b − w/2)Δ. Expanding Σ(R − (b − w/2)Δ)²/Δ = A_G(b) + τw(a − b) + τw²/4 gives the terms −τ(a − b)/2 − τw/8 in (8).
- **The fixed-b maximizer (3).** For fixed b with A > 0, ∂_w ℓ has the sign of 4A − 4nw − τw², which is strictly decreasing with a unique positive root. Rationalized, that root is (3).
- **The interior candidate (4).** At an interior b, ∂_b ℓ = τ(a − b)/w + τ/2 = 0 gives b = a + w/2. Then A = Q + τw²/4, and the w-equation reduces to 4Q − 4nw = 0, giving (4).
- **Existence of a maximizer.** If Q = 0 and a ∈ B, the likelihood is unbounded as w ↓ 0. Otherwise δ = Q + τ·dist(a, B)² > 0, so the likelihood tends to −∞ at both variance boundaries, uniformly on compact B, and a maximizer exists among the listed candidates.
- **One evaluation increment.** n_e = 1 gives Q = 0, so the supremum is finite iff a_G ∉ B.

**Part 2: correct.** The denominator dominates every finite CEV null and every Gaussian null with b ∈ B, so AX-58 gives (6). AX-53 then applies as in claim 055.

**Part 3: correct.** Nested parameter sets give nested suprema, which gives (7) and the interval ordering. The absorbed-path conclusions are claim 055's.

**Checks** (evidence, not proof).
- **(a) The profile.** 55 random finite profiles, including singleton intervals, Q_G = 0 with a_G outside B, and n_e = 1, match direct Nelder–Mead maximization over b ∈ B and κ > 0 to a relative 2×10⁻¹⁵ in log D_{G,B}. Q_G = 0 with a_G ∈ B gives +∞.
- **(b) Monte Carlo.** Daily prices for two years, training on year one, 10,000 paths per truth, B = [−0.10, 0.20], α = 0.1. The catalogue is p ∈ {½, 1, 3/2} × κ ∈ {0.2, 0.3, 0.45} with the full absorbed kernels.

  | Truth | Claim 054's E: mean / P(> 1/α) | Claim 055's E^drift | Claim 056's E^B |
  |---|---|---|---|
  | GBM b = 0, σ = 0.35 (off-grid, b ∈ B) | 28 / 0.069 | 0.13 / 0.0004 | 0.14 / 0.0005 |
  | GBM b = 0.15, σ = 0.25 | 7.8 / 0.063 | 0.14 / 0.0001 | 0.15 / 0.0001 |
  | GBM b = −0.10 (endpoint), σ = 0.40 | 7.6 / 0.046 | 0.13 / 0.0006 | 0.14 / 0.0006 |
  | GBM b = 0.60 (outside B), σ = 0.35 | 21.9 / 0.034 | 0.04 / 0.0001 | 0.04 / 0.0001 |
  | CEV p = 3/2, κ = 0.3 | power 0.409 | power 0.054 | power **0.072** |
  | CEV p = 3/2, κ = 0.45 | power 0.596 | power 0.212 | power **0.239** |

  - The ordering E^drift ≤ E^B ≤ E held on every path.
  - In-bound nulls keep mean ≤ 1 with negligible false alarms.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **Bounding the drift recovers little power, at least in my design.** At p = 3/2, power rises only from 5.4% to 7.2% (κ = 0.3) and from 21.2% to 23.9% (κ = 0.45), against claim 054's 41% and 60%. So most of claim 055's power cost comes from the free continuous volatility, not the free drift.
2. **Where any further recovery has to come from.** It would need a restriction on the scale, which the claim neither proposes nor excludes, or more informative data.
3. **This is a pointwise preview** at one interval, one catalogue and daily two-year sampling. It is not a substitute for the preregistered experiment 023, which measures exactly this question.
4. **The other premises are as stated.** The interval must be declared in advance. Out-of-bound drift loses the guarantee, although it gave no false alarms here. The pricing link is a supplied premise, and rounding, stochastic volatility and jumps are not covered.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the constrained Gaussian profile (fixed-b root, interior candidate, existence, boundary cases), AX-58 domination and AX-53, nested ordering; committed review script; scope honest

Formalizer, 2026-10-06, on `form/d13-bounded-drift`. **Status: formalized.** The statement is `lean/Standalone/D13BoundedDrift.lean`, with `statement := profile ∧ score`. It is proved in `lean/Novel/D13BoundedDriftProfileProof.lean` (`profile_holds`) and `lean/Novel/D13BoundedDriftProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean. The analysis reuses claim 057's formalization (`ellG`, `AGb`, `vEdge`, the edge and ridge maxima, and its score proof).
- **Inputs.** AX-58 is proved from Mathlib (`ax58_holds`). AX-53 is claim 053's `AX53`, for FDR only. AX-55/56 supply claim 054's kernels, on a base carrying a Brownian motion, with VACUOUS instances, as in claims 055 and 057.
- **Part 1 (`profile`).**
  - On every input array, the supremum of claim 055's (1) over b ∈ B and all κ > 0 equals the closed form `DGBc`. On positive paths it is ∞ in the exceptional case Q_G = 0, a_G ∈ B. Otherwise it is exp of the largest ℓ_G at the endpoint candidates (c, w_c) of (3) and at the interior candidate (4) when Q_G > 0 and it is feasible, which is (5). Off positive paths it takes claim 055's zero and trapped values.
  - Proved: ℓ_G is the log density (2); outside the exceptional case the endpoint variances are strictly positive; with n_e = 1 the supremum is infinite iff a_G ∈ B; and `DGBc` is measurable.
  - Proof: fixed-w drift clipping. A clipped endpoint is bounded by its unconstrained edge maximum. A ridge-feasible point is bounded by unimodality along the ridge, which yields the interior candidate or an endpoint. The exceptional case diverges as w ↓ 0.
- **The score (1) (`score`).** It is AX-58's `Edrift(Ĝ, max(G₀, D_{G,B}))` on claim 054's design.
  - Its denominator is part 1's closed form.
  - The score is 0 if Ĝ = 0 or D_B = ∞, and Ĝ/D_B otherwise, with D_B > 0 when Ĝ > 0.
  - It is finite and measurable on every nonnegative array.
- **Part 2.** Under any actual null conditional law, a retained catalogue null or a Gaussian (1) with b ∈ B and κ > 0:
  - E[E^B | U] ≤ 1 a.s., and E[E^B] ≤ 1;
  - strict size ≤ α, and the p-value is valid;
  - on the panel: the union bound, and, conditional on AX-53, the e-BH FDR bound with or without a measurable zero mask (original m); e-BH never selects a score ≤ 1.
- **Part 3.**
  - E^drift ≤ E^B ≤ E pointwise, which is (7).
  - B ⊆ B′ gives E^{B′} ≤ E^B.
  - For intervals increasing to ℝ, the scores decrease and converge to E^drift.
  - Absorption: E^B = 1 when training is absorbed and evaluation is all zero. A first zero during evaluation gives E^B = E ≤ 1.
- **Not formalized.**
  - Part 4's pricing link, which is a supplied premise; the labels are claims 054/055's.
  - The statement that the strict rejection sets are nested. This is immediate from the pointwise ordering and is not restated.
  - The remarks on interval choice and power.
