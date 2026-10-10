---
id: "069"
title: "D23: a declared bound on daily variance-scale switches"
status: formalized
depends_on: ["033", "035", "053", "059", "068"]
axioms_used: [AX-53, AX-56, AX-58]
formal: lean/Standalone/D23ScaleSwitches.lean
direction: D23
---
## Statement

**Conditional on the supplied whole-record mixing-kernel law below.** The
mechanism is profiling a shared variance scale after separate daily
mean elimination, grouping a finite partition maximum by its last
segment, and applying AX-58 [wasserman2019universal]. Claim 059
already applies a finite switch-location maximum to calibrated
likelihoods. This is its constrained daily-scale application with
033's nonproportional clock and 068's free daily drifts, not a new
change-point inference principle or general algorithm theorem.

Use 068's exact positive start s(U), deterministic consecutive blocks
d=1,...,D with lengths n_d≥1, positive durations Δ_dj and total N.
Every observed evaluation increment belongs to one block. Declare
one positive within-block shape u_d for each day, with its units and
normalization fixed before observing evaluation data. Shapes are
not fitted or rescaled separately by day after defining the null.
Declare K_switch∈{0,...,D−1}. Write count_sw(w) for the number of indices
d=2,...,D such that w_d≠w_(d−1), where w_d>0 is a variance scale.

Let θ=(b_1,...,b_D,w_1,...,w_D), with each b_d finite real and
count_sw(w)≤K_switch. Its price likelihood is

    G_θ(y|U)=∏_d g_(d,u_d,b_d,w_d)(y_d|y_previous),          (1)

where g is 068's Gaussian block density: independent log returns
Normal(b_d Δ_dj−w_d u_dj/2,w_d u_dj) within each component and the
full-record price Jacobian. Conditional on U and θ, all evaluation
returns in (1) are independent. Daily drift remains free even when
adjacent days share their variance scale.

**Actual null.** Let Θ_sw be the admissible parameter-path space
above, with its Borel sigma-field. Supply a probability kernel
ν_sw(U,dθ) on Θ_sw and the actual conditional density

    p(y|U)=∫_(Θ_sw) G_θ(y|U) ν_sw(U,dθ).                  (1a)

Require p to be jointly measurable and finite on every positive
array. Each G_θ is normalized, so this integral is normalized by the
same nonnegative mixture integration used with 033's kernel model.
The kernel may have continuous support; its support constraint and
finite-density premise are explicit. Finite mixtures with measurable
weights/paths are special cases. This does not identify an arbitrary
posterior with a finite mixture, or assert that conditioning an
adaptive switching process on its realized path gives the Gaussian
component law (1). The actual law given U must be (1a).

Let q(U,y) be a finite nonnegative measurable density normalized for
every U on (0,∞)^N, selected using U alone, as in 068. A proper joint
forecast is allowed; an unnormalized evaluation fit is not. The
exact p>1 CEV forecast of 035 is optional under AX-56. It adds no
CEV null coverage. Put

    P_sw(K_switch)=sup_(θ: count_sw(w)≤K_switch) G_θ,
    E_sw=0 if q=0 or P_sw=∞; otherwise E_sw=q/P_sw.          (2)

As in 068, set the score to zero outside the positive-price domain.

**1. Segment profile with free daily drift.** Compute 033's
A_du,B_du,Q_du,K_du,H_du for each fixed u_d. Here the middle
quantity K_du is a residual statistic, not K_switch. For a nonempty
interval I=[a,b] of days define

    N_I=Σ_(d∈I)n_d,  Q_I=Σ_(d∈I)Q_du,
    K_I=Σ_(d∈I)K_du, H_I=Σ_(d∈I)H_du,
    c_I=−(N_I/2)log(2π)−(1/2)Σ_(d∈I,j)log u_dj
                            −Σ_(d∈I,j)log y_dj.

Let P_I be the supremum of the interval likelihood over a common
w>0 and independent b_d for d∈I. If Q_I>0 it is finite and attained
at

    w_I*=2Q_I/[N_I+sqrt(N_I²+H_I Q_I)],
    b_d*=(B_du+w_I* T_d/2)/A_du,
    log P_I=c_I−(N_I/2)log w_I*−Q_I/(2w_I*)
                                  −K_I/2−w_I* H_I/8.      (3)

If Q_I=0, P_I=∞. In particular, summing the within-day residual
statistics is essential: profiling one common drift on the
concatenated segment is a different, smaller family.

**2. Exact finite partition maximum.** Let Π_k be all partitions of
the D days into k nonempty consecutive intervals. Then

    P_sw(K_switch)=max_(1≤k≤K_switch+1) max_(π∈Π_k) ∏_(I∈π)P_I.
                                                               (4)

This includes paths with fewer switches, and adjacent segments may
choose the same scale. The positive extended values P_I and P_sw
are measurable. P_sw is infinite exactly when at least one allowed
partition has a segment with Q_I=0. Otherwise (4) is finite and
attained. This characterizes the singular case without declaring
every singular *day* fatal at every budget.

For exact real arithmetic, the same maximum is given by

    B_sw(1,b)=P_[1,b],
    B_sw(k,b)=max_(k−1≤a<b) B_sw(k−1,a) P_[a+1,b],
                        2≤k≤b≤D,
    P_sw=max_(1≤k≤K_switch+1) B_sw(k,D).                    (5)

Only valid states are used, so all multiplied terms are strictly
positive; there is no ambiguous zero-times-infinity operation.
Interval statistics can be accumulated in O(D²) arithmetic
operations and (5) uses O((K_switch+1)D²), plus O(N) to form the
daily statistics. These counts exclude precision and elementary
function evaluation costs. They are not runtime guarantees.

**3. Calibration and nested budgets.** E_sw is finite, nonnegative
and measurable on every array. Under the actual mixture premise,

    E[E_sw|U]≤1, E[E_sw]≤1, P(E_sw>1/α)≤α, 0<α<1.           (6)

Lower measurable nonnegative scores preserve the conclusion. Claim
053/AX-53 supplies fixed-panel e-BH at the original m with
FDR≤q_FDR m_0/m, arbitrary dependence and zero masks, when each
null satisfies its own declared contract and all scores are finite.

With q and all shapes fixed,

    P_common ≤ P_sw(0) ≤ ... ≤ P_sw(D−1)=P_day,             (7)

where P_common is 033's single Gaussian full-record profile with
one common b,w and concatenated shape, and P_day is 068's product
of daily profiles with singleton shape catalogues. Thus scores
have the reverse ordering, including the zero-at-infinity cases.
P_sw(0) keeps free daily drifts, so it need not equal P_common.
Increasing a budget trades a larger covered null class for a weakly
smaller score. No gain in power at a given valid null class follows.

A common multiplication of all shapes by c>0 preserves this family
via w_d↦w_d/c and hence preserves (2). Arbitrary separate daily
shape multipliers do not generally preserve the switch count.

One may also declare a finite nonempty catalogue of full-record
shapes and maximize P_sw over it, under an actual probability-kernel
mixture over those families with the same finite-density premise.
The same guarantee
and budget ordering hold. At the largest budget its denominator
is max_u ∏_d P_(d,u), not in general ∏_d max_u P_(d,u). The latter
permits separate day-by-day shape choices and is the larger 068
catalogue denominator. A comparison must not attribute that shape
restriction's gain to the scale-switch budget.

## Proof

**Profiling only the drift first.** Claim 033's square-completion
identity, applied within each day at a fixed common w, gives the
unique optimizer b_d(w)=(B_du+wT_d/2)/A_du and the profiled log
likelihood

    c_I−(N_I/2)log w−Q_I/(2w)−K_I/2−w H_I/8.              (8)

Here Q_I,H_I≥0. Its derivative has the sign of
4Q_I−4N_I w−H_I w². For Q_I>0 this expression strictly decreases
from a positive value to a negative one, giving the unique maximum
(3), by the same scalar calculation in 033. If Q_I=0, every Q_du
in that interval is zero; 033 then gives K_du=0 as well. As w↓0,
(8) tends to +∞ since N_I>0. Thus the supremum is infinite. Each
fixed-parameter likelihood is finite and positive in either case.

**Partitions and the recurrence.** An admissible scale path has at
most K_switch+1 constant runs, so its likelihood belongs to one
partition's family. Conversely every partition with at most that
many segments and one scale per segment gives an admissible path,
even if adjacent segment scales agree. This is equality of the
parameter families, not an approximation to switch locations.

For a fixed positive record and partition, segment parameters are
independent coordinates. If every Q_I>0, selecting (3) separately
attains the product of maxima. If one Q_I=0, fix finite admissible
parameters elsewhere; their densities are positive, and sending
the singular segment density to infinity makes the product
unbounded. This proves (4) and its exact infinity criterion.
All individual profiles are positive and measurable by the finite
formulas and their closed residual-zero branches; finite products
and maxima retain measurability. The maximum over finitely many
partitions is attained whenever finite.

Group a k-segment partition of days 1,...,b according to the last
boundary a. Its first k−1 segments partition 1,...,a and its last
segment is [a+1,b]. Conversely each such pair gives exactly a valid
partition. Taking the corresponding finite maxima proves (5) by
induction on k. This is a finite regrouping identity. Computing
all interval sums by extending their right endpoints takes O(D²)
additions; the displayed valid-state loops give the stated count.

**Application of AX-58.** Every component of the supplied actual
kernel mixture is bounded by (4) on each positive array. Integrating
this inequality against the probability measure ν_sw(U,·) gives the
same bound for p, including where the profile is infinite. Both the component and the
chosen forecast densities use the same positive-price reference;
the Gaussian kernel normalization is already 033's. The denominator
is measurable and strictly positive, and the explicit infinite
case makes the score finite everywhere. These verify AX-58's
hypotheses and prove (6). The fixed-panel extension follows from
053/AX-53, exactly as for 068. No sequential result is used.

**Ordering and scale convention.** A common b,w is a point of the
zero-switch family. The families are nested in their allowed
switch count; at D−1 every positive scale vector is allowed.
Its supremum separates by day and is the singleton-shape P_day
of 068. This proves (7) and the score comparison. Common shape
scaling is a bijective parameter substitution preserving each
equality w_d=w_(d−1); different daily scalings can destroy it.
Taking one finite maximum over full-record shapes preserves
domination. Finally max_u ∏_d P_(d,u)≤∏_d max_u P_(d,u), which
proves the stated distinction from freely chosen daily shapes.

## Checks

`checks/069/check.py` tests the proposed diagnostic evaluator in
`checks/069/profile.py` against exhaustive partitions and direct
joint Gaussian optimization on fixed records; singular interior
and endpoint segments; global and separate daily shape scaling;
the common-profile and free-daily endpoints; invalid inputs; and
price-Jacobian consistency. These checks are not proofs, simulation
results, power estimates or numerical upper certificates.
The script also checks one explicit continuous common-scale mixture
with a positive scale floor and the full-record/daily shape distinction.

## Not shown

- The segment profile, budget and recurrence, calibration, nesting,
  catalogue comparison and panel results are formalized in
  `lean/Standalone/D23ScaleSwitches.lean`, proved by `statement_holds`
  in `lean/Novel/D23ScaleSwitchesProof.lean`, reusing formalized
  claims 033, 068 and 070. Profile measurability is proved on the
  positive-price domain; the score is zero elsewhere. Operation
  counts, numerical arithmetic and the "not in general" remarks
  remain outside the formal result; see the Formalizer note for
  its precise scope. AX-58 is proved. The optional CEV forecast
  inherits AX-56's vacuous instance; FDR inherits AX-53's
  degenerate instance.
- No data-derived coverage of K_switch or shape normalization.
  Selecting a smaller budget after observing evaluation evidence
  does not cover a larger actual class. A penalized profile or a
  numerical optimizer is generally below the required supremum.
- The actual whole-record kernel law and its finite density are
  premises. Predictable switch rules driven by returns or a
  high-probability rather than sure path budget are not included
  merely by giving them a fitted switch count. Continuous mixing
  is allowed explicitly by (1a), unlike 068's finite-mixture prose;
  arbitrary actual daily laws still do not follow.
- No bounded-total-log-variation result, within-day switches,
  observation noise, rounded filter, omitted-gap treatment,
  stochastic-volatility coverage, pricing-measure link, or retained
  non-Gaussian CEV null. A CEV numerator does not supply any of these.
- No anytime stopping, intrablock capital reuse or repeated-panel
  FDR. This is one fixed-horizon density-ratio application.
- No empirical power or feasible certified production runtime.
  The diagnostic evaluator uses arbitrary-precision approximations,
  not outward bounds; its values cannot be used as certified
  denominators. A calibrated implementation needs upper likelihood
  and lower numerator evaluations, including singularity handling.

## Prior art

Read 059's finite switch maximum, 033's profile, 068's daily reset,
the D23 accumulation/conditional-law findings, the disjoint-window
and evaluation-selected-forecast refutations, and the registered
universal-inference input AX-58 [wasserman2019universal]. Searched
the bibliography for change-point/segmentation references; no new
external segmentation theorem is used. Dynamic programming is
not claimed as novel: (5) is an explicit finite maximum identity.
The application content is a shared scale with free daily drifts,
its aggregate residual profile, the declared switch-budget null,
its singular partitions, and the comparison holding the drift and
shape policies fixed. No known general inference theory is rebuilt.

## Review

Reviewer, 2026-10-07, on branch `mathb/d23-switch-budget` at `8806b29b`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/069/`.
- **Inputs.** AX-53, AX-56 and AX-58 are audited, and AX-58 is proved. Claims 033, 035, 053, 059 and 068, the dependencies, are formalized.
- **Script.** My check is committed as `checks/review/069/reproduce.py`, with its rerun command and seeds in its header. It runs on 2 worker processes and is not a CI `check.py`.

**Part 1 (the segment profile): correct.**
- **Profiling the drifts.** At a common w, claim 033's identity in each day gives Σ(R − bΔ + wu/2)²/u = A_d(b − b_d(w))² + Q_d + wK_d + w²H_d/4. Profiling each b_d and summing gives (8).
- **The scale.** Its w-derivative has the sign of 4Q_I − 4N_I w − H_I w², whose unique positive root is (3).
- **The singular case.** Q_I = 0 forces every Q_d = 0 and hence K_d = 0, and the supremum is infinite.
- **Why the sums matter.** Summing the per-day Q_d is exactly what keeps free daily drifts.

**Part 2 (the partition maximum): correct.** Paths with at most K switches are exactly the partitions into at most K + 1 runs, with possibly equal adjacent scales. Segment parameters are independent, and grouping by the last boundary gives (5). The infinity criterion is per allowed partition, as stated.

**Part 3 (calibration and ordering): correct.**
- **Calibration.** Each kernel component is at most P_sw, and integrating against ν_sw gives AX-58.
- **The ordering (7).** It follows from family nesting. At K = D − 1 the supremum separates by day and is 068's P_day.
- **Shapes.** max_u ∏ ≤ ∏ max_u distinguishes a full-record shape catalogue from 068's daily one.

**Checks** (evidence, not proof).
- **(a) The formulas.** On 10 small records with nonproportional shapes, recurrence (5) equals exhaustive partition enumeration at every budget, exactly. Budget 1 matches direct Nelder–Mead over all drifts and a one-switch scale path to a relative 5×10⁻¹⁵.
- **(b) Monte Carlo.**
  - **Setup.** My claim-068 review's design: days of 7 increments, 60 training and 60 evaluation days, a training-selected exact CEV forecast, and 2,000 records per truth.
  - **Result.** Mean E / P(E > 20):

  | Truth | E_common | E_sw(0) | E_sw(3) | E_sw(10) | E_sw(59) = E_day |
  |---|---|---|---|---|---|
  | N1: constant GBM | 0.37 / 0.0005 | ≈0 / 0 | ≈0 / 0 | ≈0 / 0 | ≈0 / 0 |
  | N3: daily drifts, exactly 3 scale switches (covered for K ≥ 3) | **1.6×10⁷ / 0.028** | ≈0 / 0 | ≈0 / 0 | ≈0 / 0 | ≈0 / 0 |
  | CEV p = 2, κ = 0.45 | 0.272 power | **0.0035** | 0 | 0 | 0 |

  - **The ordering checks.** E_sw(59) equalled E_day on every record, as (7) says.
  - **Reading.**
    - **The claim works as stated.** On a covered switching null the common profile is invalid, while E_sw(3) is calibrated.
    - **But the switch budget is not where the cost is.** The median log P_sw(0) − log P_common is 31.5 nats over 60 days. That is the price of the **free daily drifts** alone, at a budget of zero switches, and it takes power from 0.27 to 0.0035 before any scale switch is allowed. Each further budget level costs comparatively little.
    - **Consistency.** The claim says P_sw(0) need not equal P_common and asserts no power, so this is consistent. But it suggests the useful variant for D23 is a common, or budgeted, drift with a switching scale, not free daily drifts.
- **The author's check.** I ran `checks/069/check.py` afterwards. It passes the joint optimizations, exhaustive partitions, nested budgets, singular segments, shape units and the Jacobian checks.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The null is a whole-record kernel mixture over admissible paths.** It is not a predictable, return-driven switch rule, and it does not cover within-day switches.
2. **The budget and shapes must be declared,** not fitted.
3. **The evaluator is diagnostic, not certified,** and no power is claimed. (b) shows why.

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red re-derived the segment profile with free daily drifts and its closed-form scale root, the singular case, the partition-recurrence maximum, calibration by kernel domination and the nesting order to 068; committed review script; cost diagnosis stated


Reuse 033's fixed-w square completion and scalar maximization,
then prove finite segment-product and partition-maximum identities.
Use only valid recurrence indices and positive extended profiles
to avoid artificial 0·∞ states. The actual null kernel mixes complete
admissible paths with an explicitly finite joint density, not
arbitrary daily marginals or a silently finite posterior.
Apply AX-58 after showing the component domination explicitly;
reuse 053 for the fixed panel. Operation counts, Python arithmetic
and proposed numerical certificates are not Lean guarantees.

Formalizer B, 2026-10-07, on `formb/d23-bounded-scale-switches`. **Status: formalized.**
- **Files.** The statement is in `lean/Standalone/D23ScaleSwitches.lean` (`statement := segment ∧ budget ∧ recurrence ∧ calibration ∧ nesting ∧ catalogue ∧ panel`). The proof is `lean/Novel/D23ScaleSwitchesProof.lean` (`statement_holds`), with:
  - `D23ScaleSwitchesSeg.lean`: part 1, (3);
  - `D23ScaleSwitchesBudget.lean`: (4), its infinity criterion, attainment and measurability;
  - `D23ScaleSwitchesRec.lean`: (5);
  - `D23ScaleSwitchesValid.lean`: (6);
  - `D23ScaleSwitchesNest.lean`: (7), the common multiplier and the catalogue comparison.

  There is no `sorry`, and the axiom audit is clean.
- **Inputs.**
  - Claim 033's per-day statistics, density and square completion (`log_gV`).
  - Claim 068's blocks, flat record and daily profile.
  - Claim 070's `G`, `countSw`, `Psw`, `PswSeg`, `PsegE`, `Pcommon`, `mixDens`, `Escore`, its `Composition` partition machinery (`runs`, `countPair_comp_le`, `prod_iSup_eq`) and its calibration and recurrence arguments, adapted here.
  - AX-58's step is proved directly with the supplied density. AX-53 enters for the fixed panel only.
- **Encoding.**
  - A segment is the list of its days `e : Fin ℓ → Fin D`; a partition is a `Composition D`.
  - `N_I, Q_I, K_I, H_I` are sums of each day's statistics at that day's own start.
  - (3)'s `c_I − (N_I/2) log w` is written as `−(N_I/2) log(2πw) − (1/2)Σ log u − Σ log y`.
  - A scale-only change count is claim 070's pair count with a constant drift path, so claim 070's runs apply.
- **Part 1.**
  - For any segment, `P_I` is the supremum over `w` of `exp Φ(w)`, where `Φ` is claim 033's scalar profile with the summed statistics.
  - If `Q_I > 0`, `P_I` is (3), attained at `w_I*` and the daily drifts `b_d*`.
  - `Q_I = 0` exactly when every day of the segment has `Q_du = 0`; then `K_I = 0` and `P_I = ∞`.
  - `P_I` is positive and measurable, and at least the common-drift profile on the same days.
- **Part 2.**
  - (4) holds over `Composition D` with at most `K_switch + 1` blocks.
  - `P_sw = ∞` exactly when an allowed partition has a segment with `Q_I = 0`. Otherwise it is finite and attained by an admissible path (each segment's `w_I*`, each day's `b_d*`).
  - `P_sw` is positive and measurable on the positive domain, and (5) computes it.
- **Part 3.**
  - (6) holds under the kernel mixture (1a) over a finite nonempty catalogue of full-record shapes (one shape is a one-element catalogue): finite measurable score, conditional and unconditional means, size, and lower scores. The density premise is finiteness on positive arrays.
  - (7) holds, with the reversed score order including zero at infinity.
  - The common multiplier leaves `P_sw` unchanged.
  - For a catalogue, the budget order holds, and at `D − 1` its denominator is `max_u Π_d P_(d,u) ≤ Π_d max_u P_(d,u)`.
- **Not encoded.** The operation counts, the arithmetic, and the "not in general" remarks: `P_sw(0) ≠ P_common`, separate daily multipliers, and `Π max ≠ max Π`.
