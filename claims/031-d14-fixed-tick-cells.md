---
id: "031"
title: "D14: Gaussian cell envelopes for fixed monetary ticks, including zero quotes"
status: formalized
depends_on: ["029", "030", "053"]
axioms_used: [AX-53, AX-58]
formal: lean/Standalone/D14FixedTick.lean
direction: D14
---
## Statement

**Conditional on the declared rounding map and Gaussian law below.**
Apply claims 029–030's interval maxima and finite backward bounds to
monetary cells rather than a log lattice. The statistical mechanism is
the same AX-58 domination argument. In particular, no replacement of
a monetary tick by a single relative/log tick is assumed.

Fix δ_tick>0 and observe nonnegative exact prices through

    Q_δ(x)=δ_tick floor(x/δ_tick+1/2),
    C_0^δ=[0,δ_tick/2),
    C_z^δ=[δ_tick(z−1/2),δ_tick(z+1/2)), z≥1.             (1)

The observed data are the nonnegative integer labels. Keep a fixed
finite nonempty Gaussian null catalogue Γ_i, positive deterministic
evaluation gaps, and the whole rounded training prefix with last label
z_0. For each actual pricing-null name, supply θ_i=(b_i,κ_i)∈Γ_i with
κ_i>0 and an exact last state X_i∈C_(z_0)^δ. Given the rounded prefix
and X_i>0, future log returns are independent normals with means
(b_i−κ_i²/2)Δ_j and variances κ_i²Δ_j. Given X_i=0, the entire future
exact path is zero. This is the supplied trapped Gaussian extension;
it permits a training-endpoint atom at zero but no new hitting/default
mechanism from a positive endpoint. The conditional endpoint law in
the observed cell is otherwise arbitrary. Keep a fixed panel m≥1,
supplied pricing-null set N₀, 0<α_i<1, 0<q_FDR<1 and arbitrary panel
dependence. Pricing labels are not inferred from these observations.

For source monetary interval S=[a,b) and target T=[c,d), with
0≤a<b<∞, 0≤c<d<∞, write μ=(b_θ−κ_θ²/2)Δ and s=κ_θ sqrt(Δ).
Define W_θ^δ(S,T) by these three cases:

    c=0, a=0:    W=1;
    c=0, a>0:    W=Φ((log d−log a−μ)/s);
    c>0:         m*=clip_[log a+μ,log b+μ]((log c+log d)/2),
                 W=Φ((log d−m*)/s)−Φ((log c−m*)/s).       (2)

In the last line, a=0 means a lower mean endpoint of −∞, so clipping
means min(log b+μ,(log c+log d)/2). The trapped exact state 0
contributes zero probability to a positive target interval.

1. **The correct interval envelope, including the zero cell.** Formula
   (2) is the supremum of the one-step target probability over every
   exact source state in S, including the trapped state when a=0.
   It is strictly positive and at most one. Applying it to consecutive
   observed cells and multiplying gives the direct envelope

       B_(i,θ)^δ(u,v)=Π_j W_(θ,Δ_j)^δ(C_(z_(j−1))^δ,C_(z_j)^δ).

   At each null this dominates the actual joint conditional label mass,
   for every evaluation vector at almost every rounded training prefix.
   A zero quote does not reveal whether the exact state is zero.

2. **Subdivision and valid scores.** Divide each monetary cell into
   K=2^ℓ equal **price-width** half-open subintervals, at every observed
   time. The first subinterval of C_0^δ includes exact state zero;
   all others have strictly positive left endpoints. Use (2) for the
   transition matrix, and claim 030's backward recursion, including
   its minimum with one and its inherited parent bound. Let B_(i,θ)^δ,ℓ
   be the resulting maximal initial-subinterval bound. Then

       actual null conditional label mass ≤ B_(i,θ_i)^δ,ℓ,
       0<B_(i,θ)^δ,ℓ+1≤B_(i,θ)^δ,ℓ≤B_(i,θ)^δ≤1.          (3)

   For any fixed rounded-training-selected normalized forecast q_i^δ
   on {0,1,2,…}^n, define

       D_i^δ,ℓ=max_(θ∈Γ_i) B_(i,θ)^δ,ℓ,
       E_i^δ,ℓ=q_i^δ/D_i^δ,ℓ.                             (4)

   These finite nonnegative scores have conditional and unconditional
   null moments ≤1 and size ≤α_i at threshold 1/α_i. AX-53 gives
   FDR≤q_FDR|N₀|/m with original-m masks and nonnegative measurable
   lower implemented scores. Finite measurable data-selected refinement
   levels are allowed as in claim 030, with the numerator and family
   held fixed. Direct cost is O(n K² |Γ_i|) exact operations.

   One normalized forecast prototype is the product of one-step
   Gaussian **cell probabilities** from representative δ_tick z for
   z≥1 and δ_tick/4 for z=0, with forecast parameters fixed by training.
   This representative choice is for the numerator only; the null
   envelope always ranges over the whole source interval.

3. **Observation geometry and the boundary distinction.** For a positive
   quote y=δ_tick z, its log-cell width is

       log((y+δ_tick/2)/(y−δ_tick/2)),                     (5)

   which varies along a price path. It is asymptotic to δ_tick/y as
   δ_tick/y tends to zero, not identically equal to it. The zero-quote
   cell has no finite log width. Thus the fixed h_tick hypotheses of
   claims 028–030 cannot be replaced by a cent tick without checking
   a new cell geometry.

   A positive exact state δ_tick/4 has a strictly positive probability
   of a subsequent positive quote under the Gaussian law:

       P(Q_δ(X_next)≥δ_tick)=1−Φ((log 2−μ)/s)>0.           (6)

   An exactly zero trapped state has probability zero of that event.
   Treating every zero quote as an absorbed exact state is therefore
   not this observation model. On an all-zero quoted evaluation path
   starting at a zero quote, the envelope in (4) is one at every level,
   and E_i^δ,ℓ≤1, as expected from the admitted trapped starting state.

## Proof

For x>0, the next log price is Normal(log x+μ,s²). If c>0, the
positive target has finite log endpoints. Claim 029's interval
maximization gives the clipped midpoint in (2); when a=0 the allowed
mean interval extends to −∞. Its finite midpoint maximizer or finite
upper-endpoint supremum gives the displayed minimum. The exact trapped
state contributes zero, so it does not increase this supremum.

If c=0, for positive x the target probability is
Φ((log d−log x−μ)/s), decreasing in x. If a>0 its maximum is at a.
If a=0 its supremum as x decreases to zero is one; the trapped state
also gives exactly one. These statements prove (2), including the
half-open endpoint conventions. All probabilities of nonempty positive
intervals from positive x are strictly positive, so all suprema are
positive.

The monetary cells form a countable partition of [0,∞), retaining both
the zero atom and positive prices within C_0^δ. Conditional on the past
labels, the exact state is somewhere in its current cell. Integrating
the transition inequality over that actual posterior and multiplying
successive probabilities gives part 1. Subcells are finite partitions
too, including their zero-containing member. Claim 030's backward
finite-partition argument therefore applies unchanged to this kernel:
each transition probability is bounded by (2), the suffix probability
is bounded by one, and each inherited parent bound is valid on its
child. This proves (3), positivity, measurability and the complexity
count. Apply AX-58 with counting measure and the normalized forecast,
then AX-53 exactly as in claims 029–030.

For the forecast prototype, each strictly positive representative has
a lognormal next-price law. The target cells, including C_0^δ, exhaust
its probability mass, so each forecast row sums to one. Successive
nonnegative summation normalizes the full product. This supplies a
concrete nondegenerate Gaussian instance, but not a power guarantee.

Equation (5) follows by taking logarithms of the positive cell endpoints;
its ratio to δ_tick/y tends to one by the derivative of log at one.
Equation (6) is the Gaussian tail for a price doubling. From exact
state zero all-zero future observations have probability one, so
every valid upper bound there is at least one. The recursion caps it
at one, proving the last assertion of part 3.

## Checks

`checks/031/cells.py` implements the interval cases, arithmetic-cell
subdivision and a normalized Gaussian forecast prototype.
`checks/031/check.py` verifies interval suprema and two-step joint laws
against independent Gaussian integration, zero-quote re-emergence,
trapped-state/all-zero boundaries, refinement monotonicity, monetary
unit scaling, forecast normalization and invalid inputs. These are
deterministic calculations, not certified arithmetic or simulations.

`checks/d14-certified-cells/certify.py` separately evaluates the same
recursion with outward bounds using pinned python-flint 0.8.0
([pythonflint080balls]). It accepts exact rational designs and integer
labels, bounds the finite-null denominator above and the normalized
Gaussian forecast prototype below, and returns exact rational lower
scores. Threshold comparisons are exact; failed numerical enclosures
return zero evidence. Its `check.py` checks 32 transition enclosures,
seven paths at two precisions, three independent joint integrals,
extreme tails, threshold equality and failure handling. These checks
are evidence about the implementation, not a proof of the library.

## Not shown

- No assertion that any exchange or adjusted-price feed uses (1).
  Tick changes, bid/ask effects, noise and negative/missing records
  require their actual observation rules. A zero quote is not a default
  label. Positive Gaussian prices never hit zero in this model.
- No CEV/default, jump or SV extension, fitted-null coverage or pricing
  measure construction. The only latent zero behavior here is trapping
  from a supplied zero endpoint.
- No power measurement or general convergence rate, and no transfer of
  the numerical log-lattice costs in reviews 028–030 to monetary ticks.
- Parts 1–3 are formalized in `lean/Standalone/D14FixedTick.lean`,
  proved by `lean/Novel/D14FixedTickProof.lean` (`statement_holds`):
  the zero-cell and trapped-state cases, subdivision bounds and ordering,
  validity at data-selected levels, forecast normalization, log-cell
  geometry, re-emergence and the all-zero path. Part 2's operation count
  has no Lean statement. AX-58's domination step is proved; FDR remains
  conditional on AX-53 with its degenerate instance.
- The Lean proof covers the exact formulas, not the numerical
  implementation or a real feed's law. The separate outward-bound
  implementation above relies on FLINT's
  real ball arithmetic and the Python code; it supports the stated
  Gaussian forecast prototype, not arbitrary fitted numerators or an
  actual data feed. The original `checks/031/cells.py` remains uncertified.

## Prior art

Read claims 029–030 and their reviews, claim 024's observation-law
distinction, the D14 findings and the audited AX-58 entry. The general
upper-likelihood mechanism is [wasserman2019universal], Section 6;
AX-53 is from [wang2020false]. The interval maximum and finite backward
enclosure are reused. The application checks the actual fixed-monetary-
tick partition, its unbounded log cell and the mixture of zero and
positive latent states inside an observed zero quote.

## Review

Reviewer, 2026-10-06, on branch `math/d14-arithmetic-cells` at `2e04e8e`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/031/`.
- **Inputs.** AX-53 and AX-58 are audited, and AX-58 is proved. Claims 029, 030 and 053, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/031/reproduce.py`, with its rerun command and seed (`default_rng(31)`) in its header. It runs single-process under the CPU budget and is not a CI `check.py`.

**Part 1: correct.**
- **A positive target [c, d).** From x > 0 the next log price is N(log x + μ, s²). The feasible means form [log a + μ, log b + μ), with −∞ when a = 0. Claim 029's unimodality in the mean gives the clipped log-midpoint. The trapped state contributes zero.
- **The zero target [0, d).** The probability Φ((log d − log x − μ)/s) is decreasing in x, so its supremum is at x = a when a > 0, and equals 1 when a = 0, whether as x ↓ 0 or at the trapped state. That gives (2).
- **Domination.** Successive conditioning on the posterior within each observed cell (zero atom included) gives domination of the joint label mass.

**Part 2: correct.** The subcells, including the zero-containing first subcell of C₀, partition each cell. So claim 030's backward recursion with the parent minimum applies unchanged with kernel (2). AX-58 and AX-53 follow, and the forecast prototype rows sum to one over the monetary partition.

**Part 3: correct.**
- **The log width (5).** It is log((y + δ/2)/(y − δ/2)), asymptotic to δ/y.
- **Re-emergence (6).** From δ/4, a positive quote needs the next price ≥ δ/2, a doubling, so the probability is 1 − Φ((log 2 − μ)/s).
- **The all-zero path from a zero quote** is bounded by 1.

**Checks** (evidence, not proof).
- **(a) The supremum (2).** Against brute force over exact starts in the source interval (4,000 points, log-spaced toward 0 for the zero cell, plus the trapped state for that cell only), 90 (source, target, law) cases agree to 4×10⁻¹⁶. That covers zero-to-zero, zero-to-positive, positive-to-zero and positive-to-positive transitions.
  - My first harness wrongly added the trapped state to positive source cells. It was a test bug, not a claim error.
- **(b) Two-step domination.** Quadrature from exact starts inside the observed first cell (including x = 0, 10⁻⁶ and 0.001 within a zero quote) never exceeded the level-0 to level-4 bounds in 264 (start, path) cases. Refinement was monotone, and level 0 equals the direct product exactly.
- **(c) Re-emergence (6).** From δ/4 it is 9×10⁻²⁹⁵ at daily s = 0.019, 5×10⁻⁴⁴ at s = 0.05 and 0.010 at s = 0.3. All are positive, as claimed, but astronomically small at daily volatility. The all-zero path bound is exactly 1.
- **(d) The cost with cent ticks.** GBM null κ = 0.3, daily for one year, the claim's forecast prototype, Γ = {θ_true} and 40 paths per start:

  | Start | Level 0 | 1 | 2 | 3 | 4 |
  |---|---|---|---|---|---|
  | $5 (δ/S₀ = 0.002) | −10.3 | −5.2 | −2.7 | −1.4 | −0.72 |
  | $0.50 (δ/S₀ = 0.02) | −77.5 | −46.8 | −26.4 | −14.6 | −8.6 |

  - Level 0 at $5 matches claim 029's n·log S_cell for the equivalent log tick (about 10.4). Each level roughly halves the penalty.
- **The author's check.** I ran `checks/031/check.py` afterwards. It passes 78 interval and latent-start integrals, 27 joint-cell integrals, and the zero/trapped, normalization, unit-scaling and input checks.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **This is the correct likelihood geometry for real cent-tick data,** including zero quotes, which claims 028–030's fixed log lattice did not cover.
2. **The cost depends on the price level.** At $5, level 4 brings the penalty under 1 nat a year. At $0.50 it is still about 9 nats at level 4, so penny stocks need deeper refinement, at O(nK²) cost.
3. **Zero quotes are effectively absorbing at daily volatility** under this Gaussian model, since re-emergence is about 10⁻²⁹⁵. The distinction from trapping, which the claim rightly keeps, matters only for very volatile names or large steps.
4. **Not covered:** a CEV/default null, jumps, SV and real feed rules (bid/ask, tick changes), as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the clipped log-midpoint and one-sided zero-cell suprema, joint domination with a zero atom, subdivision with the parent minimum, the log width and re-emergence bound; committed review script; scope honest


Reuse the interval-bound and subdivision mechanisms of claims 029–030.
The boundary obligations are the one-sided Gaussian target, the source
cell containing zero and its trapped atom. Preserve the distinction
between observed zero and exact zero; no new diffusion theory is needed.

Formalizer B, 2026-10-06, on `formb/d14-fixed-tick-cells` (promoted from `provisional/formb-d14-fixed-tick-cells`). **Parts 1–3 are formalized**, except part 2's operation count. The status is left `red-passed` for the pm's approval.
- **Files.** The statement is in `lean/Standalone/D14FixedTick.lean` (`statement := part1 ∧ part2 ∧ part3`). The proof is `lean/Novel/D14FixedTickProof.lean` (`statement_holds`), with:
  - `D14FixedTickStep.lean`: one monetary step and (2);
  - `D14FixedTickWalk.lean`: the first-step decomposition and the direct envelope;
  - `D14FixedTickSub.lean`: the subcell recursion and the ordering (3);
  - `D14FixedTickValid.lean`: validity.

  It reuses claim 029's Gaussian cell lemmas (`Novel/GaussianCell.lean`). There is no `sorry`, and the axiom audit is clean.
- **Inputs.** AX-58 enters through its pointwise step with counting measure, proved directly. FDR is conditional on AX-53 (claim 053's `AX53`), with and without measurable masks at the original m; the union bound is proved.
- **The contract.** The training record U ends at label z₀. The exact endpoint X is in C_(z₀)^δ almost surely, and its law given U is otherwise arbitrary. Given (U, X) with X > 0, the future log returns R have the product Normal law of θ almost surely. Nothing is assumed about R at X = 0: the exact path X·exp(R₁ + ⋯ + R_j) is then zero, which is the trapped extension. The labels are V = labels of that path.
  - The mixture over X's law given U is derived (`mix0`, adapting claim 028's `mix` to the trapped state); it is not assumed.
- **Part 1.**
  - (2) for every source [a, b) and target [c, d) with 0 ≤ a < b and 0 ≤ c < d: it bounds the one-step probability from every exact source state, the trapped one included, and it is the least upper bound. The supremum is attained or approached by continuity at the open end, with no attainment assertion.
  - 0 < W ≤ 1.
  - The trapped state gives probability 0 to positive targets and 1 to zero-cell targets.
  - The direct envelope B^δ bounds the label law from every exact start in C_(z₀)^δ.
- **Part 2.**
  - Every U of claim 030's recursion on 2^ℓ equal price-width subcells (subcell 0 of C_0^δ contains 0) lies in (0, 1]. It bounds the remaining-path probability from every exact state of its subcell.
  - 0 < B^(δ,ℓ+1) ≤ B^(δ,ℓ) ≤ B^δ ≤ 1; level 0 equals B^δ.
  - Validity: (3) at every level and label vector, at almost every training record. D^(δ,ℓ) ∈ (0, 1] and the scores are finite.
  - With any data-selected level L(u, v), the conditional and unconditional moments are ≤ 1, size is ≤ α, and lower scores keep the moment.
  - The forecast prototype: each row of one-step cell probabilities from the representatives δ/4 and δz sums to one, and the path product is a normalized forecast with positive masses.
- **Part 3.**
  - (5) and its ratio to δ/y tending to 1.
  - The zero cell's log width is unbounded.
  - (6) from δ/4 is 1 − Φ((log 2 − μ)/s) > 0, and 0 from the trapped state.
  - On the all-zero path from a zero quote, B^δ = B^(δ,ℓ) = 1 at every level, and the walk from 0 gives that path probability 1.
- **Not formalized.** Part 2's O(n K² |Γ|) count is an operation count, with no mathematical assertion beyond the definitions.
