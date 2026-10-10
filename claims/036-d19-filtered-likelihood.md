---
id: "036"
title: "D19: filtered Gaussian tick likelihoods with relative integration and parameter-cover bounds"
status: formalized
depends_on: ["024", "026", "031", "034"]
axioms_used: [AX-53, AX-58]
formal: lean/Standalone/D19FilteredLikelihood.lean
direction: D19
---
## Statement

**Mechanism.** Apply the proved AX-58 conditional-likelihood rule
[wasserman2019universal] to the exact cell likelihood from a declared
whole-prefix Gaussian model. Claim 024 already gives the conditional
joint/training mass ratio. The application supplies a finite integration
recursion and explicit *relative* error bounds for it and for a compact
parameter cover. It does not reconstruct a general filtering theorem.
FDR is conditional on AX-53; the scalar bounds use no stochastic upstream
input or CEV kernel.

Fix a known exact price s>0, tick δ>0, N=k+n increments with k,n≥1,
calendar gaps Δ_j>0, a nonempty finite set 𝒱 of positive **full-record**
variance clocks v=(v_1,...,v_N), and a compact rectangle
ℬ=[b_L,b_H]×[w_L,w_H], b_L≤b_H, 0<w_L≤w_H. All are declared before
observing the record. For θ=(v,b,w), the actual whole-record component
law starts at X_0=s and has independent log returns

    R_j ~ Normal(bΔ_j−wv_j/2, wv_j),   X_j=X_(j−1)exp(R_j).       (1)

Observe 031's monetary labels Z_j, with cells
C_z^δ=[δ max(0,z−1/2), δ(z+1/2)), z∈ℕ. Set U=(Z_1,...,Z_k) and
V=(Z_(k+1),...,Z_N). There is no observation of a rounded substitute
for s. A null may be any fixed component, or an arbitrary mixture of
these **whole-record** laws. Equivalently for the calibration conclusion,
its actual conditional mass given U must be a mixture of the conditional
component masses below, almost surely. This is not 034's contract allowing
an arbitrary joint parameter/endpoint posterior under an undeclared
training law.

Let P_(θ,j) be the lognormal price transition in (1). Define

    α_(θ,0)=point mass at s,
    α_(θ,j)(dy)=1_(C_zj^δ)(y) ∫P_(θ,j)(x,dy)α_(θ,j−1)(dx),
    L_(θ,j)(z_1,...,z_j)=α_(θ,j)((0,∞)),
    g_θ(v|u)=L_(θ,N)(u,v)/L_(θ,k)(u),
    D_filter(u,v)=max_(θ∈𝒱×ℬ) g_θ(v|u).                         (2)

Here v in g_θ(v|u) is a label vector; the clock is part of θ.

**1. Exact likelihood and validity.** All finite label strings have
strictly positive mass, and (2) is a normalized conditional mass in v.
The training endpoint distribution is exactly
π_(θ,k)=α_(θ,k)/L_(θ,k); continuing its transition integrals, without
restarting at a representative, yields g_θ. Each g_θ is continuous in
(b,w), including strings containing zero labels; the maximum in (2)
exists and 0<D_filter≤1. The data domain is countable, so this maximum
is a measurable statistic.

For any training-only normalized forecast q(u,v)≥0 with Σ_v q(u,v)=1,
let E_filter=q/D_filter. It is finite on every record and, under the
stated actual conditional mixture law,

    E[E_filter | U]≤1,   E[E_filter]≤1,
    P(E_filter≥1/α)≤α,   0<α<1.                                 (3)

The same conclusions hold for any nonnegative measurable lower score.
Claim 026's original-m zero masks and union bound apply; e-BH has
FDR≤q_FDR m_0/m conditional on AX-53, with arbitrary dependence across
names, when each null satisfies this contract and all panel scores are
finite. No pricing interpretation follows from (1) alone.

**2. Relative integration bound on positive labels.** Suppose every
z_1,...,z_N≥1. Put [a_j,d_j]=log C_zj^δ (using its finite endpoints),
a_0=d_0=log s, and

    R_j^max=max(|a_j−d_(j−1)|, |d_j−a_(j−1)|).

For one covering subbox B=[b_−,b_+]×[w_−,w_+]⊆ℬ, set
B_max=max(|b_−|,|b_+|) and

    C_j(B)=(R_j^max+B_max Δ_j+w_+v_j/2)/(w_−v_j).                (4)

Split each log cell into M≥1 equal subintervals. Their midpoints are
t_(j,l), their widths h_j=(d_j−a_j)/M, and radii r_j=h_j/2; r_0=0.
For a fixed parameter θ in B, let φ_(θ,j)(y−x) be the Normal density
with mean bΔ_j−wv_j/2 and variance wv_j. The finite recursion is

    A_(θ,1,l)=h_1 φ_(θ,1)(t_(1,l)−log s),
    A_(θ,j,l)=h_j Σ_m A_(θ,j−1,m) φ_(θ,j)(t_(j,l)−t_(j−1,m)),
    Q_(θ,J)=Σ_l A_(θ,J,l),     J=k or N,
    ε_J(B,M)=Σ_(j=1)^J C_j(B)(r_(j−1)+r_j).                     (5)

These are quadrature sums, not normalized transition probabilities.
Nevertheless they satisfy the deterministic relative enclosure

    exp(−ε_J) Q_(θ,J) ≤ L_(θ,J) ≤ exp(ε_J) Q_(θ,J).             (6)

Hence an exponentially small training mass does not require division by
an absolute-error subtraction: the positive Q_(θ,N)/Q_(θ,k) approximates
g_θ within factors exp(±(ε_N+ε_k)). The ε values are discretization
bounds, not floating-point error allowances.

**3. Cover the same continuous null family.** Cover ℬ by finitely many
closed subboxes B contained in ℬ; boundaries may overlap. For each box
use its midpoint (b_g,w_g), coordinate radii ρ_b,ρ_w, and the bounds

    L_b,J(B)=Σ_(j≤J) Δ_j C_j(B),
    L_w,J(B)=J/(2w_−)+Σ_(j≤J)(R_j^max+B_max Δ_j)^2/(2w_−²v_j)
                +Σ_(j≤J)v_j/8,
    η_J(B)=L_b,J(B)ρ_b+L_w,J(B)ρ_w,
    H_(B,v,M)=ε_N+ε_k+η_N+η_k.                                 (7)

Compute (5) at that single parameter and full clock. An upper bound on
the entire box's conditional mass is

    min(1, exp(H_(B,v,M)) Q_(θg,N)/Q_(θg,k)).                    (8)

The maximum of (8) over every covering box and every declared clock is
D_cert. It obeys D_filter≤D_cert≤1. The maximum of
exp(−ε_N−ε_k) Q_(θg,N)/Q_(θg,k) over centers/clocks is a lower bound
on D_filter. Thus the construction encloses the true maximum on both
sides; it is not the likelihood returned by an unconstrained optimizer.

The finite cover, M and computation precision may be chosen from the
whole observed record, provided the bounds hold and the original box and
all clocks remain covered. Each evaluated record still has the pointwise
domination. For records with any zero label, define D_cert=1. This is a
valid fallback on the original observation space, not conditioning on
positive labels. The score q/D_cert satisfies (3), including on these
fallback records where it is at most one.

For outward arithmetic, replace each expression (8) by a rational upper
enclosure, capped at 1. If the computed Q_k interval does not have a
positive lower endpoint, or any needed bound cannot be evaluated, use 1
for that component (using 1 globally also suffices). Use a certified
nonnegative lower numerator q_low≤q if evaluating a score. Then
q_low/D_cert≤E_filter. Ordinary quadrature, double-precision optimizer
values, and a floating-point q not known to lie below q do not suffice.

**4. Resolution, comparison and scope.** On any fixed positive-label
record, as the covering boxes' maximal coordinate widths tend to zero
and M→∞, both mathematical bounds in part 3 tend to D_filter. A sequence
of outward implementations has the same limit if its *relative*
arithmetic enclosure widths also tend to zero. No monotonicity of the
raw midpoint sums or successive certified bounds is asserted; taking
the minimum of previous valid upper bounds preserves domination.

For matched Gaussian parameters, evaluation clocks and the same q,

    D_filter ≤ D_endpoint ≤ D_clock^(h,ℓ),                      (9)

where D_endpoint is the supremum of the exact evaluation-cell likelihood
over parameters/clocks and every endpoint compatible with the last
training label, and the last quantity is 034's covering bound for that
evaluation design. Thus the *ideal* filtered score is at least the old
envelope score. There is no order between a finite-computation D_cert
and that old bound; their minimum is valid under the present contract.
Only D_endpoint, not D_filter, covers 034's arbitrary posterior contract.

One candidate uses O(NM²) kernel evaluations and arithmetic operations;
a G-box, |𝒱|-clock cover uses O(G|𝒱|NM²), excluding precision-dependent
bit complexity. Messages require O(M) storage if matrix entries are
computed as needed. Prefix messages are reused for the evaluation block.
For fixed resolutions the logarithmic allowances can grow linearly with
N. For each fixed finite record they can be made arbitrarily small;
no useful uniform runtime, power, or large-N error rate is asserted.

## Proof

**Exact conditional law.** The independent Gaussian returns in (1) have
a positive density on ℝ^N. Successive changes of variables from returns
to log prices have determinant one. Every finite cell string contains
a product of bounded positive-price intervals of positive length, so
its joint probability is positive. Integrating the nonnegative kernel
product in time order gives α and L. Splitting the same integral at k
gives (2) and its posterior formula. Summing all future partition cells
gives L_k, so g_θ is normalized. These are the existing cell-ratio and
kernel-product identities of 024/031, specialized to (1).

For continuity, couple all parameters for a fixed clock to the same N
independent standard Normal variables, using
R_j=bΔ_j−wv_j/2+√(wv_j)Z_j. Prices are continuous functions of (b,w)
for every such vector. At a fixed parameter the chance of hitting any
finite cell boundary is zero. Cell-event indicators therefore converge
almost surely along any parameter sequence tending to that parameter.
Bounded convergence yields continuity of each L, including zero cells.
L_k>0 gives continuity of g; compactness and the finite clock set give
the maximum and a positive minimum of L_k on the parameter domain for
this fixed record. Each g≤1, hence D_filter≤1. Conditioning a mixture
of the whole-record laws yields a mixture of the component conditional
laws with training-dependent parameter weights. Such a mixture is
pointwise bounded by their maximum.

AX-58 now applies with counting measure, the supplied normalized q,
and this dominating measurable denominator. Positivity of D_filter and
q≤1 give all-array finiteness. The conditional and unconditional moments
and Markov's inequality give (3). Lower scores and original-m panel
conclusions are exactly the existing AX-58/claim-026 application.

**Integration bound.** On a compatible log-price path y, let
f_θ(y)=∏_j φ_(θ,j)(y_j−y_(j−1)), with y_0=log s. Its derivative with
respect to a transition's return is

    −(R_j−bΔ_j+wv_j/2)/(wv_j),

whose absolute value is at most C_j(B). Given a product of log subcells,
join any point to its midpoint vector by a straight segment. It stays
in the product of observed log cells. The jth return changes by at most
r_j+r_(j−1). Integrating the derivative along this segment proves
|log f_θ(y)−log f_θ(t)|≤ε_J. Multiply exp(±ε_J) f_θ(t) by the
subcell volume and integrate. Sum over all subcell products. The sum of
midpoint densities times volumes is Q_J: distributing the sums in time
order gives exactly (5), preserving the same intermediate state in its
two adjacent transitions. This proves (6), without a state supremum or
an assumption that the finite transition matrix is stochastic.

**Parameter bound.** For the same latent path, direct differentiation
gives

    ∂_b log f_θ = Σ Δ_j(R_j−bΔ_j+wv_j/2)/(wv_j),
    ∂_w log f_θ = −J/(2w)+Σ(R_j−bΔ_j)^2/(2w²v_j)−Σv_j/8.

Taking absolute values over B gives (7). The segment from its midpoint
to any parameter stays inside B, so exp(±η_J) bounds f_θ/f_θg.
Integration over the same cells gives that bound for L_(θ,J)/L_(θg,J).
Use its upper side for the joint mass and lower side for training,
then apply (6) separately to Q_N and Q_k. This proves (8). At the
center η is unnecessary, giving the stated lower bound. All covers are
finite and contain every admissible parameter; maxima retain the bounds.
The capping, fallback and one-sided arithmetic rules follow because all
conditional probabilities are ≤1. Countability of the label records
also makes data-chosen finite computations measurable.

**Limit and comparison.** On a fixed positive-label record, all return
bounds are finite. Every subbox lies in the fixed compact ℬ, so (4)
and both derivative bounds admit common finite bounds, uniformly in
clock and subbox. Thus max ε_J→0 as M→∞ and max η_J→0 as cover widths
vanish. At a maximizing parameter choose a containing subbox: its
center's conditional likelihood differs by at most exp(η_N+η_k).
The upper bound differs from that center's exact likelihood by at most
exp(2ε_N+2ε_k+η_N+η_k). These factors tend to one, proving convergence
of both bounds to the positive maximum. Vanishing relative arithmetic
widths preserve the conclusion. No filter-forgetting result is used.

Finally π_(θ,k) is supported on the last training cell. Its integral of
the exact evaluation suffix is bounded by the initial-endpoint supremum.
Claim 034 bounds every such suffix pointwise at every admissible endpoint
and parameter, giving (9) after maxima. The operation and storage counts
follow from the two M-node loops per step of (5).

## Checks

`checks/036/check.py` exercises the outward evaluator
`checks/d19-filtered-likelihood/certify.py`: comparison with independent
nested integration on fixed short paths; a continuous-parameter grid
inside each declared box; two full clocks; refined integration and
parameter covers; zero-label and inadequate-precision fallbacks; invalid
input rejection; and tiny training/joint likelihoods. These are finite
diagnostics, not independent proof of interval-library correctness or
power measurements. The earlier `checks/d19-filter-inputs/check.py`
checks analytic derivatives and a separate absolute-error construction.

## Not shown

- The claim is formalized in `lean/Standalone/D19FilteredLikelihood.lean`
  and `lean/Novel/D19FilteredLikelihoodProof.lean` (`statement_holds`),
  including the deterministic relative integration and covering bounds.
  The filtering identity/calibration remains prior art. FDR remains
  conditional on AX-53, whose instance is degenerate. The Python
  implementation, its vanishing-relative-arithmetic-width limit, operation
  and storage counts, and the no-order remark for D_cert versus claim
  034's bound are not formalized; see the Formalizer note below.
- No coverage of an undeclared training law, arbitrary endpoint
  posterior, estimated clock, drift/scale outside ℬ, observation noise,
  jumps or stochastic volatility. No unrestricted rounded version of
  033, and no retained CEV null. No interpretation as a pricing bubble
  without the separate physical/pricing link.
- No informative zero-cell certificate; these records receive D_cert=1.
  Known initial absorption s=0 is outside this model. No claim that
  increasing resolution at fixed finite precision succeeds.
- The Python certificate trusts version-pinned real ball arithmetic
  [pythonflint080balls]; it is not verified by Lean. It certifies only
  the Gaussian denominator. A real scorer still needs a normalized
  numerator or a certified lower evaluation of one. Invalid inputs must
  not be dropped to obtain a selected-sample guarantee.
- No efficient full-year implementation, useful power recovery, bound
  independent of N, no-loss filtering-stability theorem, real-data run,
  or repeated-date guarantee. This is not a kill or closure of D19.

## Prior art

Read the D19 input and librarian findings, 024/031/034's exact cell
integrals, 026's panel statement, the refuted unrestricted density
supremum, and [wasserman2019universal] Section 6. Universal inference and
conditional likelihoods are already AX-58, and the forward recursion
only rearranges the existing nonnegative cell integrals. The filtering
and stability sources marked wanted in the librarian's sweep are not
premises. The application-specific content is (4)–(8), with the full
training posterior preserved and explicit distinction between integration
error, parameter-cover error and arithmetic error. No general filtering
or stochastic-analysis theory is reconstructed. The existing adopted
ball evaluator and registered [pythonflint080balls] supply the arithmetic
conventions, not a mathematical assumption replacing these bounds.

## Review

Reviewer, 2026-10-07, on branch `math/d19-filtered-likelihood` at `f7d2a79`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/036/` and `checks/d19-*`.
- **Inputs.** AX-53 and AX-58 are audited, and AX-58 is proved. Claims 024, 026, 031 and 034, the dependencies, are formalized. [pythonflint080balls] is registered.
- **Script.** My check is committed as `checks/review/036/reproduce.py`, with its rerun command and seed in its header. It is single-process and is not a CI `check.py`.

**Part 1 (the exact filter and validity): correct.**
- **The filter.** Returns have a positive density on ℝᴺ, and the log-price change of variables has unit Jacobian. So every finite cell string has positive mass, and α, L and g_θ = L_N/L_k are the time-ordered kernel integrals, normalized over future labels.
- **Continuity.** Coupling through common standard normals plus bounded convergence gives continuity in (b, w), because cell boundaries have probability zero. Compactness then gives the maximum.
- **The contract.** It is a mixture of *whole-record* laws, so conditioning on U gives a mixture of component conditionals, which is bounded by their maximum. AX-58 applies. This contract is stronger than claim 034's arbitrary-posterior one, and the claim says so plainly.

**Part 2 (the relative enclosure): correct.**
- **The derivative bound.** ∂ log φ_j/∂R_j = −(R_j − bΔ_j + wv_j/2)/(wv_j). Compatible returns satisfy |R_j| ≤ R_j^max, so on B the absolute derivative is at most C_j(B).
- **The step.** Moving every log price to its subcell midpoint changes R_j by at most r_j + r_{j−1}, and the segment stays inside the product of cells.
- **The result.** Integrating exp(±ε)·f(t) over the subcell products gives (6). The forward sums (5) are exactly the product midpoint sum.

**Part 3 (the cover): correct.**
- **The parameter derivatives.** ∂_b log f = Σ Δ_j(R_j − bΔ_j + wv_j/2)/(wv_j). For w, write e = R − bΔ: then (e + wv/2)²/(2wv) = e²/(2wv) + e/2 + wv/8, so ∂_w log f = −J/(2w) + Σ e²/(2w²v) − Σ v/8.
- **The bounds.** The triangle inequality on B gives (7). The upper side of η on L_N and the lower side on L_k, together with (6) on each Q, give (8). The centre value minus ε gives the lower bound.
- **The zero-label fallback** D_cert = 1 is valid.

**Part 4 (limits and comparison): correct.**
- **The limit.** ε → 0 as M → ∞ and η → 0 as boxes shrink, uniformly on compact ℬ for a fixed record.
- **The ordering (9).** It follows because π_k is supported on the last training cell, so the conditional mass is at most the endpoint supremum, which claim 034 bounds.

**Checks** (evidence, not proof).
- **(a) The enclosure.** Over 36 (path, M) cases with J = 2 and 3 and coarse ticks, |log L_quad − log Q| ≤ ε every time, with a slack of at least 0.02. Here L_quad is an independent 1-D or 2-D quadrature. The median ε is 0.79, 0.20 and 0.05 at M = 4, 16 and 64, so it falls as 1/M.
- **(b) The cover and normalization.**
  - **The cover.** On a four-step record with a nonproportional clock and a 24 × 24 cover at M = 64 (median H = 0.33), log D_cert = −0.97 is at least the brute-force upper side over 400 interior parameters (−1.28). The centre lower bound, −1.59, is at most the brute lower side, −1.42.
  - **Normalization.** The conditional mass over the next label is 1.000000.
- **(c) What the exact filter buys.**
  - **Setup.** A cent tick, a $5 GBM null with κ = 0.3, k = n = 30 days and 6 paths. The numerator is claim 031's forecast at the true law.
  - **Result.** Median log E:

    | Denominator | Median log E |
    |---|---|
    | Claim 031's envelope, true parameter | −0.19 |
    | Filtered, true parameter | in [−0.14, +0.14] |
    | Claim 034's box b ∈ [−0.1, 0.2] × κ ∈ [0.15, 0.45], h = 2 | −6.05 |
    | Filtered maximum over the same box, 41 × 41 grid of centres | ≤ −0.23 |

  - **Reading.** The *ideal* filtered maximum removes nearly all of claim 034's box cost. The certified allowance (7) for that same grid is H ≈ 31 nats, though. So (7) bounds L_N and L_k *separately* (η_N + η_k). That grows with the record length, even though the ratio's parameter sensitivity is far smaller, and certifying the gain needs a much finer cover at O(G|𝒱|NM²) cost.
- **The author's check.** I ran `checks/036/check.py` afterwards. It passes 18 fixed parameter and clock integrals, the certified cover, the relative quadrature and the fallbacks.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The whole-record contract excludes claim 034's arbitrary posterior.** Only D_endpoint covers that, as stated.
2. **There is no efficient certified evaluator.** My (c) shows the bottleneck is the separate-bound cover (7), not the filter. A sharper bound on the derivative of log(L_N/L_k) itself would be the natural next step, but the claim rightly asserts no efficiency.
3. **Not covered:** noise, jumps, rounding at zero and power, as stated.

**Correction by the reviewer, 2026-10-07.** Two statements in (c) above are wrong or overstated; the verdict is unaffected.
1. **"H ≈ 31 nats" was overstated.** I computed it with the whole box's w₋ and B_max, but (7) is defined with per-subbox constants. With per-subbox constants, claim 036's own certified median log E on this design is about −8 nats at 30 days (`checks/review/037/reproduce.py`).
2. **"Removes nearly all of claim 034's box cost" was not established here.** As math noted, the grid value ≤ −0.23 is only an upper bound on log E. The certified lower bound from claim 037's allowance on the same design is −1.31 nats, against claim 034's −6.81 on the same paths, so the gain at 30 days is substantial but not "nearly all". That bound is float evaluation, not outward arithmetic. See claim 037's review.

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red re-derived positivity and continuity of the exact filtered cell masses, the whole-record mixture contract under AX-58, the relative midpoint enclosure, the parameter-cover bounds and the ordering against 034; committed review script; certification-cost limit stated


Represent log-cell intervals with a fixed exact log start. Reuse existing
Gaussian product/cell-law and AX-58 machinery; avoid a new general HMM
formalization. The finite forward sum is a rearrangement of the product
midpoint sum. Prove the log-density derivative bounds, integrate their
pointwise exponential bounds, and divide joint by positive training
mass. Handle the zero-cell fallback separately on the countable label
space. The floating-point implementation itself is not a Lean target.

Formalizer, 2026-10-07, on `form/d19-filtered-likelihood` (promoted from `provisional/form-d19-filtered-likelihood`). **Status: formalized.** The statement is `lean/Standalone/D19FilteredLikelihood.lean`, with
`statement := exact ∧ validity ∧ quad ∧ cover ∧ limits ∧ comparison ∧ panel`.
It is proved in `lean/Novel/D19FilteredLikelihoodProof.lean` (`statement_holds`), from `D19FilteredLikelihood{Path,Joint,Cont,Exact,Valid,Compare,Density,Geom,Idx,Prev,Quad,Param,Cover,Limits}`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** FDR is conditional on AX-53 through claim 026's `panel`. AX-58's step is proved directly with counting measure. The scalar bounds use no stochastic upstream input; the Gaussian laws and densities are Mathlib's. Reused: claim 031's labels, cells and walk law `walkM`; claim 034's boxes and `Dclock`.
- **Encoding.** One name, with tick δ > 0, known start s > 0 and K training plus n evaluation increments. θ = (v, b, w) is a full-record clock with drift and scale; (1) has means bΔ_j − w v_j/2 and standard deviations √(w v_j).
  - `alphaF` is the forward measures of (2), built with the lognormal kernel `Ptr` and restricted to each observed cell. `Lz` is the label-string mass, `gF` is g_θ and `Dfilter` is the supremum over 𝒱 × ℬ.
  - (5) is `msg`/`Qs` on M midpoints per log cell, with the empty string carrying the start; `epsQ` is ε_J, and `Cj` is (4).
  - (7) and (8) are `Lb`, `Lw`, `etaQ` and `term`, with the lower term `termLow`. `Dcert` and `Dlow` are their maxima over a finite cover (`CoverIn`: valid closed subboxes of ℬ that cover it) and the clocks; `Dcert = 1` on records with a zero label.
- **Part 1 (`exact`, `validity`).**
  - Every finite label string has positive mass. The forward recursion is the label mass. Integrating the evaluation suffix against the unnormalized training endpoint law α_K gives the joint mass.
  - g_θ sums to one over future labels. It is continuous in (b, w) on w > 0, zero labels included. The maximum over 𝒱 × ℬ is attained, and 0 < D_filter ≤ 1.
  - **The null.** P(Z = z) = ∫ walk_θ{z} dν for a probability ν carried a.s. by 𝒱 × ℬ; a fixed component is a point mass.
  - **The conclusions.** They hold for any normalized q and any denominator D' with D_filter ≤ D' ≤ 1: finiteness, the conditional law bounded by D_filter a.s., the conditional and unconditional means ≤ 1, Markov, and every measurable lower score. This range covers D_cert from a cover and M chosen from the record, the zero-label fallback, outward enclosures capped at 1, the minimum with earlier valid bounds, and min(D_cert, D_clock).
- **Part 2 (`quad`).** For every prefix length, every M ≥ 1, all-positive labels and every parameter of a valid box, Q > 0 and (6) hold.
  - The proof is by induction on the string, not by a segment integral. Each step bounds the density ratio between a point and its midpoint pair by exp(C_j(r_(j−1) + r_j)), on each subcell and each cell of the previous partition. It gives the same ε_J.
- **Part 3 (`cover`).**
  - (8) bounds g_θ for every parameter of every box and every clock, and the lower term is at most g at the box center.
  - D_filter ≤ D_cert ≤ 1 on every record, and D_low ≤ D_filter on positive-label records.
  - The parameter step bounds the one-step log-density change. The b part is algebraic; the w part uses log x ≤ x − 1 in place of the derivative. Both give (7)'s constants.
- **Part 4 (`limits`, `comparison`).**
  - **`limits`.** On a fixed positive-label record, for every ε > 0 there are η > 0 and M₀ such that every cover with widths ≤ η and every M ≥ M₀ give D_cert ≤ e^ε D_filter and e^(−ε) D_filter ≤ D_low.
  - **`comparison`.** (9) holds as D_filter ≤ D_endpoint and D_endpoint ≤ claim 034's `Dclock` on the evaluation design (evaluation clocks and gaps, source cell the last training label), with K + 1 training labels.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53, with arbitrary dependence, lower scores and zero masks at the original m.
- **Not formalized.** These are commentary or about the Python evaluator:
  - the outward-arithmetic implementation and the statement that implementations with vanishing relative widths have the same limit;
  - the operation and storage counts;
  - the statement that no order holds between D_cert and claim 034's bound.
