---
id: "070"
title: "D23: budgeting joint drift and variance-scale changes"
status: formalized
depends_on: ["033", "035", "053", "059", "068", "069"]
axioms_used: [AX-53, AX-56, AX-58]
formal: lean/Standalone/D23JointSwitches.lean
direction: D23
---
## Statement

**Conditional on the actual whole-record Gaussian mixture law below.**
The mechanism is a finite union of products of already profiled densities,
followed by AX-58 [wasserman2019universal]. Apply 033 to a concatenated
segment, and 069's partition regrouping to those segment profiles. This
is 059's finite-switch principle for a declared number of day-boundary
changes in the **pair** (drift, scale), not a new inference or segmentation
theorem. In contrast to 069, drift cannot reset freely each day.

Use 069's fixed D≥1 consecutive evaluation days, positive lengths n_d,
positive deterministic calendar durations Δ_dj and shapes u_dj, total
N, exact positive training endpoint s(U), and every evaluation increment.
Shapes and their relative daily units are fixed before evaluation.
Declare K_joint∈{0,...,D−1}. Define

    count_pair(b,w)=#{d=2,...,D : (b_d,w_d)≠(b_(d−1),w_(d−1))}.

Thus a drift-only or a scale-only change each counts as one boundary;
simultaneous changes count once. Let Θ_joint contain all finite real
drift paths b and positive scale paths w with count_pair(b,w)≤K_joint.
For θ=(b,w) in this Borel space, let G_θ be the full price density of
conditionally independent returns

    R_dj ~ Normal(b_d Δ_dj−w_d u_dj/2, w_d u_dj),
    R_dj=log(y_dj/y_previous),                           (1)

including the Jacobian ∏1/y_dj and the previous day's endpoint at every
boundary. Parameters in each component are fixed given U and θ.

**Actual law.** Supply a probability kernel ν_joint(U,dθ) on Θ_joint
such that the actual conditional density on (0,∞)^N is

    p(y|U)=∫ G_θ(y|U) ν_joint(U,dθ).                     (2)

Require this density to be jointly measurable and finite at every
positive array. Continuous mixtures are permitted under this explicit
premise, exactly as in 069. Each component is normalized by 033's
Gaussian change of variables; hence (2) is normalized. This is a
whole-record conditional law, not an assertion that conditioning a
return-driven switching process on its switches yields (1). Common
drift with at most K_joint scale changes is included; independently
changing drift may use additional boundaries and exceed the budget.

Let q(U,y) be a finite nonnegative jointly measurable normalized density
on (0,∞)^N for every U, fixed using training alone. A proper joint
forecast is allowed. Claim 035's positive p>1 CEV forecast is optional
under AX-56 and supplies no CEV null coverage. Define

    P_joint(K_joint)=sup_(θ∈Θ_joint) G_θ,
    E_joint=0 if q=0 or P_joint=∞; otherwise q/P_joint.    (3)

Set E_joint=0 outside the positive-price domain.

**1. Segment calculation.** For a consecutive interval I of days,
concatenate all its returns, durations and shapes. Apply 033's
statistics A_u,B_u,C_u,T,V_u,S,Q_u,K_u,H_u to that concatenated
vector, denoting these with a superscript I. In particular

    Q_u^I=Σ_(d∈I) Q_du
              +Σ_(d∈I) A_du (B_du/A_du−B_u^I/A_u^I)².  (4)

The individual A,B,C,T,V,S add; Q,K,H must instead be recomputed
from their pooled A,B,C,T,V,S. Let P_I^joint be the segment supremum
over one common b,w. If Q_u^I>0, 033 gives

    w_I^joint=2Q_u^I/[N_I+sqrt(N_I²+H_u^I Q_u^I)],
    b_I^joint=(B_u^I+w_I^joint T^I/2)/A_u^I,
    log P_I^joint=c_I−(N_I/2)log w_I^joint
              −Q_u^I/(2w_I^joint)−K_u^I/2−w_I^joint H_u^I/8, (5)

with c_I=−(N_I/2)log(2π)−Σ_I log(u_dj)/2−Σ_I log(y_dj).
If Q_u^I=0, P_I^joint=∞. This occurs exactly when the ratios
R_dj/Δ_dj agree across the entire segment, not merely within each day.
All P_I^joint are strictly positive extended measurable functions.

**2. Exact budgeted profile.** Using 069's partitions Π_k,

    P_joint(K_joint)=max_(1≤k≤K_joint+1) max_(π∈Π_k)
                                      ∏_(I∈π) P_I^joint. (6)

It is infinite exactly when some allowed partition contains a segment
with Q_u^I=0; otherwise it is finite and attained. It is measurable.
The recurrence, using only valid states, is

    B_joint(1,b)=P_[1,b]^joint,
    B_joint(k,b)=max_(k−1≤a<b) B_joint(k−1,a) P_[a+1,b]^joint,
    P_joint=max_(1≤k≤K_joint+1) B_joint(k,D).             (7)

The formula takes O(N+(K_joint+1)D²) exact arithmetic operations
using additive raw segment statistics. Precision, elementary functions
and a numerically stable/certified implementation are not covered by
this count; the simple diagnostic code instead concatenates segments.

**3. Calibration and ordering.** Under (2), apply AX-58 to obtain

    E[E_joint|U]≤1, E[E_joint]≤1,
    P(E_joint>1/α)≤α for 0<α<1.                          (8)

Scores are finite, nonnegative and measurable on every array. Lower
nonnegative measurable scores preserve (8). For a fixed panel satisfying
this contract name by name, 053/AX-53 gives base e-BH with the original
m, arbitrary dependence and FDR≤q_FDR m_0/m, including zero masks.

For the same shapes, q, data and integer K, write P_sw(K) for 069's
free-daily-drift denominator. Then

    P_common=P_joint(0)≤P_joint(K)≤P_sw(K)≤P_day,
    P_joint(D−1)=P_day,                                 (9)

where P_day has singleton daily shape catalogues. P_joint is increasing
in K. The scores reverse these inequalities, with their zero-at-infinity
conventions. Thus the zero-switch score equals the common-profile score
exactly; any K can improve on 069 at that K, but no positive fraction of
common-profile power is guaranteed. In particular, whenever the profiles
are finite,

    E_joint(K)=E_common exp(−J_joint(K)),
    J_joint(K)=log P_joint(K)−log P_common≥0.             (10)

For calendar shape u_dj=Δ_dj on a fixed segment, put
Q_within,I=Σ_I Q_du>0. With ahat_d=S_d/T_d and
ahat_I=Σ_I S_d/Σ_I T_d, (4) becomes

    Q_u^I=Q_within,I+Σ_I T_d(ahat_d−ahat_I)².

The exact cost of allowing free daily drift while keeping a common
scale **on this fixed segment** is

    log P_I − log P_I^joint
                =(N_I/2)log(Q_u^I/Q_within,I)≥0,         (11)

where P_I is 069's segment profile. For a fixed partition, these costs
add. They must not be summed using independently maximizing partitions
for the two families. No such simplified cost formula for general
nonproportional shapes is asserted.

A common shape multiplication by c>0 preserves the family under
w_d↦w_d/c. Separate daily shape multipliers need not preserve the
joint-change count. A finite nonempty catalogue of full-record shapes
may be handled by a finite maximum, under the corresponding actual
mixture premise. At K=D−1 that denominator is max_u∏_d P_du,
not generally 068's ∏_d max_u P_du.

## Proof

**Apply the segment result.** Concatenating a segment of consecutive
days leaves exactly 033's design and Gaussian likelihood, with one
calendar drift and one variance scale. Its normalization, profile,
singular criterion and measurability therefore give (5) directly.
This reuses the formalized profile instead of reproving it. For (4),
write each R_dj as its daily fitted part (B_du/A_du)Δ_dj plus its
weighted residual. The weighted residual has zero inner product with
Δ_d. Expanding the square about the pooled coefficient B_u^I/A_u^I
eliminates the cross terms and gives the stated within/between identity.
The raw statistics add by their definitions. In calendar shapes,
A_du=T_d, K_u=H_u=0 both daily and pooled. Substitute w*=Q/N into
033 and 069 to subtract their logs; the common c_I and −N_I/2 cancel,
giving (11). The same calculation summed over a fixed partition proves
its qualified additive statement.

**Check the partition hypotheses.** A parameter pair path in Θ_joint
has at most K_joint+1 constant runs. Conversely, selecting one parameter
pair for each segment of any such partition gives an admissible path,
even if two adjacent pairs happen to agree. This identifies exactly the
union of segment-product families in (6). For a fixed partition, all
segment parameters are independent coordinates; endpoints are the fixed
observed prices, not parameters to be optimized or reset. Thus segment
maxima multiply when all profiles are finite. If a segment is singular,
fix finite parameters in every other segment, whose likelihoods are
positive, and let that segment's likelihood diverge. Its product diverges.
This is the same separation argument as 069, now using the pooled-drift
segment family. It proves (6) and the infinity criterion.

There are finitely many partitions. When no allowed segment is singular,
each partition's supremum is attained by (5), and the largest is attained.
Products and finite maxima of the positive measurable extended profiles
are measurable, with no zero-times-infinity operation. Group each
k-segment partition by its last boundary a as in 069. This yields (7).
Extending raw segment sums over all pairs of endpoints needs O(D²)
operations after O(N) statistics formation; the recurrence has at most
(K_joint+1)D² candidates. This proves only the stated arithmetic count.

**Apply the inference input.** Every component G_θ of (2) is pointwise
at most (6). Integration against the supplied probability kernel preserves
that upper bound, including the infinite-profile case. The actual finite
normalized p and the finite normalized q use the same reference measure.
We have checked the measurable positive denominator required by AX-58,
so its conditional bound and test conclusion give (8). Division by a
finite positive denominator and the explicit infinite case make E_joint
finite everywhere. Lower scores and the 053 fixed-panel result apply
exactly as in 069. No sequential inference result is used.

**Compare the families.** Budget zero forces both parameters to be common
on the entire record, which is exactly P_common. Larger budgets enlarge
the family. Any pair path with at most K changes has at most K scale
changes and admissible daily drifts for 069, so its likelihood is at most
P_sw(K). At D−1 all daily parameter pairs are unrestricted, giving the
singleton-shape product of 068. These inclusions prove (9) and the reversed
score inequalities; (10) is ordinary division on finite profiles. Scaling
all shapes by c is a bijection preserving equality of adjacent pairs.
The catalogue conclusions follow from a finite maximum and the same
mixture domination. No power or broader law coverage follows from nesting.

## Checks

`checks/070/check.py` compares the diagnostic `checks/070/profile.py` with
raw Gaussian optimization and exhaustive partitions on fixed records,
checks (4), (9), (11), singular middle/edge days, the price Jacobian,
global shape scaling and invalid designs, and independently checks the
float evaluator used by experiment 037. These are not proofs or numerical
upper certificates. Experiment 037 was registered before running and
reports its matched size/power diagnostic separately, including all saved
per-record log scores. Its findings are not part of the theorem.

## Not shown

- The segment profile, partition identity and recurrence, calibration,
  nesting, calendar drift cost and panel results are formalized in
  `lean/Standalone/D23JointSwitches.lean`, proved by `statement_holds`
  in `lean/Novel/D23JointSwitchesProof.lean`. Profile measurability is
  proved on the positive-price domain; the score is zero elsewhere.
  Operation counts and the Python code remain outside the formal result;
  see the Formalizer note for its precise scope. The component profile
  is formalized in 033; 069 is red-passed/approved. AX-58 is proved. The optional CEV
  forecast inherits AX-56's vacuous instance; FDR inherits AX-53's
  degenerate instance. Neither is needed for the Gaussian profile itself.
- No coverage under arbitrary daily drift changes at a small joint budget.
  Common drift with switching scale is included, but daily drift redraws
  generally are not. A sure conditional-law budget is needed; estimating
  few changes from training or fitting a small number after evaluation
  does not prove the actual mixture premise. The distinction is substantive,
  even if one out-of-class simulation shows small rejection rates.
- No claim that the globally common-drift, switching-scale profile is
  computed exactly: its parameters are coupled across segments. The
  segmentwise drift family here is a valid dominating enlargement of it.
- No uniform lower power bound. Experiment 037 finds no rejection in
  2,000 CEV paths at K=3; zero observed rejections is not zero population
  power or an impossibility theorem for every common-drift method.
- No within-day switches, arbitrary adaptive switching law, rounding/noise,
  jumps, omitted gaps, retained non-Gaussian CEV null, pricing-bubble
  interpretation, anytime guarantee or repeated-panel FDR.
- The Python profiles and experiment are approximate diagnostics, not
  outward upper likelihood bounds. A finite optimizer or grid subset
  does not certify the null supremum. No production runtime guarantee.

## Prior art

Read 033's profile, 059's finite switch-location maximum, 069's review and
recurrence, D23's accumulation findings and the disjoint-window and
evaluation-forecast-selection refutations. Reused the registered,
source-audited AX-58 [wasserman2019universal], Theorem 3 and Section 6;
no additional external theorem is needed. The mechanism is known finite
profiling and dominating split likelihood. The application contribution
is the joint day-boundary coverage contract, its pooled-drift segment
choice and singular cases, and the comparison isolating daily drift cost.
The general profiling, dynamic programming and inference methods are
not claimed as new or rebuilt from stochastic theory.

## Review

Reviewer, 2026-10-07, on the claim as of `410727a8` (`mathb/d23-joint-switches`). That branch is checked out in mathb's worktree, so per rule 11b this Review is committed on `rev/claim070-review`, built on that tip so that claim and verdict merge together. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/070/` and `experiments/037/`.
- **Inputs.** AX-53, AX-56 and AX-58 are audited, and AX-58 is proved. Claims 033, 035, 053, 059 and 068 are formalized, and 069 is approved.
- **Script.** My check is committed as `checks/review/070/reproduce.py`, with its rerun command and seeds in its header. It runs on 2 worker processes and is not a CI `check.py`.

**Part 1 (the segment calculation): correct.**
- **The segment profile.** A concatenated segment with one drift and one scale is exactly claim 033's design, so (5) is 033's profile on the pooled raw statistics.
- **Identity (4).** Write R = (B_d/A_d)Δ + residual within each day. The residual is orthogonal to Δ_d in the 1/u-weighted inner product, so expanding about the pooled coefficient leaves Σ_d A_d(B_d/A_d − B^I/A^I)² with no cross terms.
- **The singular case.** Q^I = 0 iff R ∝ Δ over the whole segment.

**Part 2 (the budgeted profile): correct.** Pair paths with at most K changes are exactly partitions into at most K + 1 runs, with possibly equal adjacent pairs. Segments are independent, and the last-boundary grouping gives (7), as in claim 069.

**Part 3 (calibration and ordering): correct.**
- **Calibration.** Kernel-mixture domination gives AX-58.
- **The ordering (9).** At K = 0 both parameters are common, giving P_common. A pair path with at most K changes has at most K scale changes and admissible daily drifts, so P_joint(K) ≤ P_sw(K). At K = D − 1 the family is free daily.
- **The drift cost (11).** With the calendar shape, w* = Q/N, so log P_I − log P_I^joint = (N_I/2)log(Q^I/Q_within). The claim correctly restricts this to a fixed segment.

**Checks** (evidence, not proof).
- **(a) The formulas.** On 10 random multi-day records with nonproportional shapes:
  - the additive-statistics segment profile equals the concatenated claim-033 profile to 7×10⁻¹⁵;
  - (4) holds to 4×10⁻¹⁶;
  - recurrence (7) equals exhaustive partitions exactly at every budget;
  - budget 1 matches direct Nelder–Mead over pair paths to a relative 6×10⁻¹⁶;
  - (9) holds, including P_joint(D − 1) = P_sw(D − 1) and monotonicity;
  - (11) holds to 5×10⁻¹⁵.
- **(b) Monte Carlo.**
  - **Setup.** My claim-068 and claim-069 review design: days of 7 equal increments, 60 training and 60 evaluation days, a training-selected exact CEV numerator, and 2,000 records per truth.
  - **Result.** P(E > 20):

  | Truth | E_common = E_joint(0) | E_joint(1) | E_joint(3) | E_joint(10) | E_sw(3) (claim 069) | Median J_joint(3) |
  |---|---|---|---|---|---|---|
  | N1: constant GBM | 0 | 0 | 0 | 0 | 0 | 10.5 |
  | N4: common drift, 3 scale switches (covered for K ≥ 3) | **0.026** (mean 1.5×10³) | 0 | 0 | 0 | 0 | 101.5 |
  | N3: daily drift draws and 3 scale switches (outside for K < 59) | 0.021 (mean 629) | 0 | 0 | 0 | 0 | 100.6 |
  | CEV p = 2, κ = 0.45 | 0.278 | **0.012** | **0** | 0 | 0 | 12.4 |

  - **Reading.** The claim works as stated, and it does what it was designed to do relative to claim 069.
    - **Calibration.** On a covered common-drift switching null, the common profile is invalid (2.6% rejections, mean E ≫ 1), while E_joint(3) is calibrated.
    - **The cost falls a lot.** The joint budget cuts the reset cost from about 31 nats (claim 069's free daily drifts at K = 0, in my claim-069 review) to a median 12.4 at K = 3 on the alternative.
    - **But not enough.** Power is still 0 at K = 3 in 2,000 CEV paths, and only 1.2% at K = 1. That matches the claim's report of experiment 037 and its "Not shown": zero observed rejections are not zero population power.
- **The author's check.** I ran `checks/070/check.py` afterwards. It passes the joint optimization, partitions, nesting, drift cost, singularities, Jacobian and the experiment evaluator.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The null is substantively narrower than claim 069's at the same budget.** Arbitrary daily drift redraws are not covered, and N3's zero rejections are an out-of-class observation only, as stated.
2. **The segmentwise-drift family dominates the exact globally-common-drift, switching-scale profile** but does not compute it, which the claim says.
3. **Experiment 037 is not reviewed here.** It is bundled on the claim branch and needs its own review. My (b) independently shows the same qualitative result.

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red re-derived the pooled segment profile and orthogonal drift identity, the joint-change partition recurrence, kernel-mixture calibration under AX-58, the nesting order between 068/069 and the fixed-segment drift cost; committed review script; scope honest


Reuse 033 for concatenated segment profiles and 069's finite partition
maximum. Check the pair-path family equality, pooled-residual decomposition,
conditional-mixture domination, nesting endpoints and calendar drift cost.
The globally shared-drift optimum, experiment and arithmetic runtime count
are not formal proof obligations asserted by a Lean result yet.

Formalizer, 2026-10-07, on `form/d23-joint-drift-scale-switches` (promoted from `provisional/form-d23-joint-drift-scale-switches`). **Status: formalized.** The statement is `lean/Standalone/D23JointSwitches.lean`, with
`statement := segment ∧ budget ∧ recurrence ∧ calibration ∧ nesting ∧ calendar ∧ panel`.
It is proved in `lean/Novel/D23JointSwitchesProof.lean` (`statement_holds`), from `D23JointSwitches{Seg,Part,Budget,Rec,Valid,Nest,Cal}`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** As claim 068: AX-58's step is proved directly from the supplied conditional density, and FDR is conditional on AX-53 through claim 026's `panel`.
  - **Reused from claim 033:** the density, the closed form `Dv` and its supremum identity, the unique optimizer, the singular criterion and scale invariance, applied to concatenated segments.
  - **Reused from claim 068:** the blocks, the flat record, the daily profile and its joint supremum.
  - **Not reused from claim 069.** 069 is not yet formalized, so its partition maximum is proved here as general machinery: `Composition D` partitions, the product–supremum exchange, and the runs of a pair path. Its denominator `P_sw` and segment profile are defined here from 069's own definitions.
- **Encoding.**
  - Claim 068's days of `NNR` prices, with each day's start in the flat record.
  - `G` is (1) for a pair path (b, w), day by day.
  - `countPair` counts pair changes and `countSw` scale changes.
  - `Pjoint K` is (3)'s supremum. A segment is a list of days `e`; a partition is a Mathlib `Composition D`, whose i-th segment is `c.embedding i`.
  - **The actual law (2)** is a Markov kernel ν(U, ·) over (catalogue shape, b, w), carried by admissible pair paths. The density ∫ G dν is measurable and finite, and the conditional law is a.e. the reference measure with that density.
- **Part 1 (`segment`).** For a consecutive segment, (5) holds: the common-parameter profile is claim 033's closed form on the concatenated segment. The singular criterion is that the ratios R/Δ agree across the whole segment. The pooled decomposition (4) holds, and the profile is positive on positive arrays.
- **Part 2 (`budget`, `recurrence`).**
  - **(6).** P_joint(K) is the maximum over partitions into at most K + 1 consecutive segments of the products of segment profiles.
  - **Infinity and attainment.** P_joint is infinite exactly when an allowed partition has a singular segment; otherwise it is finite and attained. It is positive.
  - **(7).** The recurrence B(k, b), grouping by the last segment, computes P_joint.
  - **Measurability.** Measurability of the segment profiles and of P_joint is stated on the positive-price domain. That is the probabilistic domain, and the score is zero elsewhere. Their suprema at boundary arrays (zero prices) are not claimed measurable.
- **Part 3 (`calibration`, `nesting`, `calendar`).**
  - **(8).** For a finite nonempty catalogue of full-record shapes (a single shape is a one-element catalogue) with denominator max_u P_joint(u): the score is finite and measurable, its conditional and unconditional means are at most 1, P(E > 1/α) ≤ α, and lower scores keep the mean.
  - **(9).** P_common = P_joint(0) ≤ P_joint(K) ≤ P_sw(K) ≤ P_day; P_joint is increasing in K; P_joint(D − 1) = P_day with singleton daily catalogues. Hence the catalogue denominator at K = D − 1 is max_u ∏_d P_du.
  - **Scores and (10).** The scores reverse these orderings, and (10) holds on finite profiles with J_joint ≥ 0.
  - **Common multiplier.** A common shape multiplier c > 0 leaves P_joint unchanged.
  - **(11).** For the calendar shape on a consecutive segment with Q_within > 0: the decomposition Q^I = Q_within + Σ T_d (â_d − â_I)², both profiles finite, log P_I − log P_I^joint = (N_I/2) log(Q^I/Q_within) ≥ 0, and additivity over a fixed partition. Claim 069's calendar segment profile is computed here from claim 033's per-day quadratic identity, maximizing each day's drift and then the common scale.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53, with arbitrary dependence, lower scores and zero masks at the original m.
- **Not formalized.** These are commentary or about the Python code:
  - the operation count and the diagnostic code;
  - the remark that separate daily shape multipliers need not preserve the change count;
  - the absence of a simplified cost formula for general shapes;
  - the globally shared-drift optimum, which the claim does not assert.
