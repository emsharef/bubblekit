---
id: "030"
title: "D14: monotone subdivision of the Gaussian rounded-cell likelihood envelope"
status: formalized
depends_on: ["029", "053"]
axioms_used: [AX-53, AX-58]
formal: lean/Standalone/D14CellSubdivision.lean
direction: D14
---
## Statement

**Conditional on claim 029's Gaussian observation-law contract.** The
mechanism is again AX-58's likelihood upper bound, now computed by finite
backward sums over subcells. Each sum bounds a remaining-path probability;
taking its minimum with an already valid coarser bound preserves domination.
This is an application of finite partitions and the existing Gaussian
interval maximum, not a new general filtering or inference theorem.

Keep claim 029's positive log lattice h, fixed nonempty finite Gaussian
null family Γ_i, positive evaluation gaps Δ_1,…,Δ_n, fixed panel of
m≥1 names, and normalized label-space numerator q_i^h(v|u). Keep its
fixed supplied pricing-null set and actual conditional Gaussian law given
the whole rounded training prefix and latent exact endpoint. All exact
prices are positive. Fix 0<α_i<1 and 0<q_FDR<1. For an observed path
(z_0,…,z_n), z_0 is the final training label and z_1,…,z_n are evaluation
labels. The numerator and null family are unchanged by refinement.

At level ℓ≥0, divide each log cell I_(z_j) into K=2^ℓ equal half-open
subcells J_(j,a)^ℓ, a=0,…,K−1, in increasing order. Each fine subcell
has parent index floor(a/2). For fixed θ=(b,κ), let

    W_(θ,j,a,d)^ℓ
      = sup_(x∈J_(j,a)^ℓ)
          P(x+R_(j+1) ∈ J_(j+1,d)^ℓ),                    (1)

where R_(j+1) is Normal((b−κ²/2)Δ_(j+1),κ²Δ_(j+1)). For source
interval [l,r), target [L,R), drift mean μ and standard deviation s,
this is the explicit probability

    m*=clip_[l+μ,r+μ]((L+R)/2),
    W=Φ((R−m*)/s)−Φ((L−m*)/s).                           (2)

As in claim 029, a boundary maximum gives a supremum for the half-open
source. The probability uses the exact Gaussian CDF, not a density
sample or a grid maximum over possible exact starts.

Compute levels in increasing order, and within each level compute
remaining-path bounds backward in j. Set U_(θ,n,a)^ℓ=1 and, for j<n,

    T_(θ,j,a)^ℓ = Σ_(d=0)^(K−1) W_(θ,j,a,d)^ℓ U_(θ,j+1,d)^ℓ,
    U_(θ,j,a)^0 = min(1,T_(θ,j,a)^0),
    U_(θ,j,a)^ℓ = min(1,T_(θ,j,a)^ℓ,
                         U_(θ,j,floor(a/2))^(ℓ−1))  (ℓ≥1).     (3)

Define

    B_(i,θ)^ref,ℓ(u,v)=max_a U_(θ,0,a)^ℓ,
    D_i^ref,ℓ(u,v)=max_(θ∈Γ_i) B_(i,θ)^ref,ℓ(u,v),
    E_i^ref,ℓ=q_i^h(v|u)/D_i^ref,ℓ(u,v).                  (4)

1. **Domination at every level.** Every U in (3) is strictly positive
   and at most one. It bounds the probability of the remaining observed
   cell path from every exact log state in its subcell. In particular,

       P(V_i^h=v|U_i^h=u) ≤ B_(i,θ_i)^ref,ℓ(u,v)
                              ≤ D_i^ref,ℓ(u,v)            (5)

   for every v at almost every actual null training prefix u. The
   denominator is positive and finite on every label array. All level-ℓ
   scores have conditional and unconditional null moments ≤1, size ≤α_i
   at threshold 1/α_i, and AX-53 FDR≤q_FDR|N₀|/m, including original-m
   zero masks and nonnegative measurable lower implemented scores.

2. **Monotone improvement without renormalization.** Level zero equals
   claim 029's product envelope. For every path and null parameter,

       B_(i,θ)^ref,ℓ+1 ≤ B_(i,θ)^ref,ℓ,
       D_i^ref,ℓ+1 ≤ D_i^ref,ℓ,
       E_i^ref,ℓ+1 ≥ E_i^ref,ℓ.                          (6)

   In particular, per-name threshold rejections can only increase for
   the same numerator. The inherited bound in (3) is part of the
   construction; a sum of separately maximized subcell probabilities
   alone is not asserted to improve at every refinement. The envelope
   is never normalized to make its total mass one.

3. **Finite adaptive computation.** The final level may be any finite
   measurable L_i(u,v)≥0, even chosen using the evaluation labels, as
   long as the fixed family and normalized numerator remain unchanged
   and the returned denominator is the corresponding completed bound.
   Each choice still satisfies (5) pointwise and thus part 1. This is
   adaptive choice of a dominating computation, not adaptive choice of
   the null model or fitting a numerator to evaluation outcomes.

   Through a fixed maximum level L with K=2^L, direct dense computation
   takes O(n K² |Γ_i|) Gaussian cell-probability evaluations and finite
   arithmetic, with O(n K+K²) working storage when parameters and
   transition matrices are processed sequentially. Repeated transition
   geometries can be cached. No training-state filter or integration
   over all n future states is required. These are counts of exact
   operations, not a bit-complexity or numerical-certification claim.

## Proof

For fixed θ and the observed suffix, let F_(θ,j)(x) be the Gaussian
probability of the remaining prescribed cells z_(j+1),…,z_n from exact
log state x at time j. It is between zero and one, with F_(θ,n)=1.
Conditioning on the next Gaussian transition and partitioning its
target cell gives

    F_(θ,j)(x)=Σ_d ∫_(J_(j+1,d)^ℓ) F_(θ,j+1)(y) P_θ(x,dy).     (7)

The Gaussian interval-maximization argument of claim 029 does not
require equal source and target widths. Applying it to these subcells
gives (2). Suppose inductively that U_(θ,j+1,d)^ℓ bounds F_(θ,j+1)
on every target subcell. For x in source subcell a, each term of (7)
is at most U_(θ,j+1,d)^ℓ W_(θ,j,a,d)^ℓ. Hence T is an upper bound.
So is 1. At finer levels the previous level's bound is also valid on
the parent interval, hence on the child. Their minimum remains an
upper bound. Induction backward in j and then forward in ℓ proves
the subcell assertion. All W are positive; finite sums of products of
positive bounds, and minima with positive prior bounds, remain positive.

The conditional latent endpoint given rounded training lies in the
union of the initial subcells. Integrating F_(θ_i,0) against its actual
conditional law is at most max_a U_(θ_i,0,a)^ℓ. This proves (5), with
no approximation of that posterior. Countable label vectors permit a
common almost-sure set of training prefixes. The same Gaussian
nondegenerate instance as claim 029 meets the premises.

At level zero there is one subcell per cell. The backward bound is a
product of probabilities ≤1, so the extra minimum with 1 changes
nothing. Its initial value is exactly claim 029's B_θ^cell. The
parent minimum gives U_fine(child)≤U_coarse(parent). Maximizing over
children proves the first inequality in (6); finite parameter maxima
and division by positive denominators give the rest.

Each construction is a finite expression of CDFs, sums, minima and
maxima on countable label spaces. It is measurable. A finite integer
level selected measurably remains measurable, and (5) holds for every
such selected level. AX-58 now applies exactly as in claim 029:
Σ_v (q_i^h/D_i^ref,L)P(v|u)≤Σ_v q_i^h=1. Lower scores and AX-53
give the panel statements. The cost is the geometric sum of n4^ℓ
matrix entries through level L, times the finite null count. Previous
and current levels require O(n K) values; one matrix requires O(K²).

## Checks

`checks/030/refine.py` implements (1)–(4) with arbitrary precision.
`checks/030/check.py` verifies level-zero agreement with claim 029,
monotonicity, two-step domination against independent Gaussian
quadrature from several exact endpoints, translation invariance and
input boundaries. The report compares fixed synthetic label paths at
daily and five-minute gaps. These are deterministic computations,
not simulations, certificates or power measurements.

## Not shown

- No convergence rate or claim that the limit is an exact conditional
  likelihood. Even an exact supremum over starting states can exceed
  the posterior-averaged likelihood. No posterior is estimated here.
- No practical power guarantee. Increasing a finite score on a fixed
  path is not evidence of improved real-data bubble detection.
- The Gaussian family, log lattice and observation contract are the
  same as claim 029. No CEV/default, jump, SV, fixed-cent observation
  or noisy-price extension; no data-selected null coverage.
- Floating-point CDF and arithmetic outputs are not one-sided bounds
  merely because the exact formula is an upper envelope. An implemented
  guarantee still needs upper transition/bound arithmetic and a lower
  numerator, or a direct certificate for the reported score. The
  prototype supplies no such certificate.
- The interval maximum, subdivision bounds, level-zero identity,
  monotonicity and validity under measurable level choice are formalized
  in `lean/Standalone/D14CellSubdivision.lean`, proved by
  `lean/Novel/D14CellSubdivisionProof.lean` (`statement_holds`).
  Part 3's operation and storage counts, the nondegenerate-instance
  remark and numerical certification are not formalized. AX-58's
  domination step is proved; FDR remains conditional on AX-53 with
  its degenerate instance.

## Prior art

[wasserman2019universal], Section 6, already permits replacing the
null maximum by a computable upper bound; AX-58 supplies this result.
[wang2020false] supplies AX-53. Read claim 029's review, its interval
maximum and excess-mass obstruction, claims 024/028 and the D14
findings. The finite-partition integral enclosure uses those existing
mechanisms. The application checks a monotone backward subdivision
bound and its validity under a data-dependent finite computation
budget; it does not introduce a new inference or Markov-chain theorem.

## Review

Reviewer, 2026-10-06, on branch `math/d14-cell-refinement` at `988315d`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/030/`.
- **Inputs.** AX-53 and AX-58 are audited, and AX-58 is proved. Claims 029 and 053, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/030/reproduce.py`, with its rerun command and seed (`default_rng(30)`) in its header. It is not a CI `check.py`.

**Part 1: correct.**
- **The backward bound.** Write F_j(x) for the remaining-path probability. Partitioning the next target cell into subcells gives F_j(x) = Σ_d ∫_{J_d} F_{j+1} dP(x, ·). Suppose U_{j+1,d} bounds F_{j+1} on J_d. Then for x in source subcell a, each term is at most W_{a,d}·U_{j+1,d}, with W from claim 029's interval maximum (unequal widths are fine). So T bounds F_j there, and so do 1 and the parent's coarser bound. Their minimum is therefore valid.
- **The joint law.** Integrating F_0 against the actual latent-endpoint law, whatever it is, gives at most max_a U_{0,a}, which is (5).
- **The rest.** AX-58 with counting measure, and AX-53, follow as in claim 029.

**Part 2: correct.** At level 0 the recursion is claim 029's product, since each U ≤ 1 makes the min with 1 inactive. The parent minimum gives U_child ≤ U_parent, hence (6).

**Part 3: correct.** Every finite level gives a denominator that pointwise dominates P(v|u). So a level chosen measurably from the observed labels keeps AX-58's pointwise hypothesis. The numerator and the null family stay fixed, as required.

**Checks** (evidence, not proof).
- **(a) Structure.**
  - **Level 0** equals claim 029's product envelope to 3.6×10⁻¹⁵ on 30 random label paths.
  - **The bound is monotone** in level 0–4 on every path.
  - **Two-step domination.** The exact joint cell probability, by quadrature over the first step from five fixed exact starts including both cell edges, never exceeded the level-5 bound in 175 (start, path) cases.
- **(b) How much of claim 029's penalty subdivision removes.**
  - **The setup.** GBM null κ = 0.3, exact latent prices on the log lattice, Γ = {θ_true}, and a numerator of normalized one-step forecasts from representatives.
  - **Results.** Median log E by level 0–5:

    | Data | Log tick | Paths | Level 0 | 1 | 2 | 3 | 4 | 5 |
    |---|---|---|---|---|---|---|---|---|
    | Daily, one year | 10⁻³ | 200 | −5.25 | −2.65 | −1.34 | −0.68 | −0.35 | −0.18 |
    | 5-minute, one month | 10⁻⁴ | 60 | −30.2 | −15.2 | −7.6 | −3.8 | −1.9 | −0.97 |

  - **Each level roughly halves the penalty,** from claim 029's n·log S_cell (5.26 and 30.25). The excess mass per step scales with subcell width, and the backward recursion tracks the latent state so it does not compound.
- **The author's check.** I ran `checks/030/check.py` afterwards. It passes 27 joint-cell integrals at four levels, nine coarse/translation comparisons, the score ordering and 15 one-step dominations.

**Gaps.** None.

**Scope; "Not shown" is honest. This is a real practical improvement.**
1. **It removes the main obstruction in my claim-029 review.** At modest dyadic depth the rounded-price penalty becomes small: under 0.2 nats for a year of daily data at a 10⁻³ tick (level 5), and about 1 nat for a month of 5-minute data at 10⁻⁴ (level 5). The cost is O(nK²|Γ|), about 1.7×10⁶ transition probabilities per path per null at 5 minutes and level 5.
2. **Halving per level means sub-0.1-nat precision at 5 minutes needs about level 8.** That is K = 256, roughly 10⁸ evaluations per path per null, which is feasible but heavy, as the claim's operation count states.
3. **It inherits claim 029's limits:** the Gaussian null only, the log lattice rather than cents, no certified arithmetic, and no CEV, jumps or SV. Combined with the discouraging D13/D15 power results, its value is in making a valid rounded-observation likelihood affordable, not in creating power.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the backward subdivision bound with parent minimum, domination for any latent endpoint law, level-0 reduction and monotonicity, and data-chosen level validity; committed review script; scope honest


Reuse claim 029's interval bound and AX-58. Induct over the finite
suffix and dyadic levels to establish (7)'s bound; do not reconstruct
diffusion or filtering theory. Distinguish the exact upper-envelope
formula from certified numerical arithmetic. Adaptive resolution must
leave the numerator and null family fixed.

Formalizer, 2026-10-06, on `form/d14-cell-subdivision`. **Status: formalized.** The statement is `lean/Standalone/D14CellSubdivision.lean`, with
`statement := interval ∧ bounds ∧ level0 ∧ monotone ∧ validity ∧ panel`.
It is proved in `lean/Novel/D14CellSubdivisionProof.lean` (`statement_holds`). The deterministic parts are in `D14CellIntervalProof` and `D14CellSubdivisionBoundProof`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** FDR is conditional on AX-53 (claim 053's `AX53`), through claim 026's `panel`. Everything else is proved. The Gaussian interval maximum uses claim 029's Gaussian cell library (`Novel/GaussianCell.lean`). The observation contract's mixture is claim 028's `mix`. AX-58's domination is the finite sum Σ_v (q/D) P(v|u) ≤ Σ_v q = 1.
- **Encoding.**
  - Log coordinates. Cell z is [h(z − 1/2), h(z + 1/2)), split at level ℓ into 2^ℓ equal half-open subcells.
  - The observation contract is claim 028's. The rounded record U lies in any measurable space with measurable last label z(U). Almost surely X > 0 and Q_h(X) = exp(h z(U)). The conditional law of the evaluation log returns given (U, X) is claim 023's `lawR`. V is the label vector of X·exp(cumulative returns).
  - `Ub h b κ ℓ n Δ z v a` is U^ℓ_{θ,0,a}. The bounds at j > 0 are `Ub` of the suffix path, so (3)'s backward recursion is recursion on the suffix. At level 0 the parent term is 1, which leaves min(1, T).
  - W is computed by formula (2) (`Wf`).
- **`interval`, (1) = (2).** For source [l, r) and target [L, R) of any widths, with s > 0, `Wf` is the least upper bound over starts in [l, r) of the Gaussian probability of landing in [L, R), and it lies in (0, 1]. The interval mass is antitone in the distance of its centre from zero, and the clipped start is a limit of starts in the half-open source.
- **`bounds`, part 1's subcell assertion.** Every U lies in (0, 1] and bounds the probability of the remaining label path from every exact log state in its subcell. Because the statement quantifies over all paths, it covers every suffix. The backward step is the generic `Novel.D14CellSubdivisionBound.partition_bound`: for any step law, any finite partition of the target and any transition bounds W, the mass is at most Σ_d W_d U_d.
- **`level0` and `monotone`, part 2.**
  - B^ref,0 equals claim 029's own envelope `Standalone.D14Cell.Bcell` (∏ K^cell).
  - B^{ℓ+1} ≤ B^ℓ and D^{ℓ+1} ≤ D^ℓ, and E^{ℓ+1} ≥ E^ℓ for q ≥ 0.
- **`validity`, parts 1 and 3.**
  - (5) holds simultaneously for every level and every label vector, at almost every training record.
  - D^ref,ℓ ∈ (0, 1].
  - For any level choice L(u, v), measurable in u for each v and allowed to depend on the evaluation labels, the score q/D^{L(u,v)} is measurable and nonnegative. It has conditional and unconditional null moments ≤ 1, and conditional and unconditional size ≤ α at 1/α. Every measurable score between 0 and it has moment ≤ 1.
  - The numerator and the family are fixed.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53, with arbitrary dependence, lower scores and measurable zero masks at the original m.
- **Not formalized.**
  - Part 3's operation and storage counts. They are cost statements about an algorithm, not mathematical claims.
  - The remark that the nondegenerate instance of claim 029 meets the premises.
  - The numerical caveats. Lean proves the exact formulas, not floating-point evaluations.
