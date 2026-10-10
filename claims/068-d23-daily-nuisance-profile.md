---
id: "068"
title: "D23: exact-price daily drift and scale profiles under a conditional block law"
status: formalized
depends_on: ["033", "035", "053"]
axioms_used: [AX-53, AX-56, AX-58]
formal: lean/Standalone/D23DailyProfile.lean
direction: D23
---
## Statement

**Conditional on the actual block-law premise below.** The mechanism is
separability of a likelihood supremum over block-specific nuisance
coordinates, followed by AX-58 [wasserman2019universal]. Claim 033
already proves the Gaussian profile; this claim applies it with daily
resets and quantifies their likelihood cost. It introduces no new
inference principle, diffusion law or sequential theorem. AX-56 is used
only for the optional claim-035 CEV forecast; FDR uses AX-53.

Fix an initial training record U with a known exact positive terminal
price s(U), a fixed number D≥1 of consecutive evaluation blocks, and
deterministic lengths n_d≥1, with N=Σ_d n_d. A block represents one
day. Every evaluation increment belongs to exactly one block; no
intervening return is silently omitted. Fix calendar durations
Δ_dj>0 and a nonempty finite catalogue 𝒰_d of positive shape vectors
u=(u_1,...,u_(n_d)) for each block, before seeing evaluation data.
The single-day case is D=1. A within-day training prefix is allowed
by placing that prefix in U and scoring only its suffix as the block.

Work first on strictly positive price arrays y∈(0,∞)^N with Lebesgue
reference measure. The start of a block is the previous block's last
price, or s(U). Put R_dj=log(y_dj/y_previous). Given a block start,
write g_(d,u,b,w) for 033's price density, namely

    g_(d,u,b,w) = ∏_j exp(−(R_dj−bΔ_dj+w u_j/2)²/(2w u_j))
                          / [y_dj sqrt(2πw u_j)],
    b∈ℝ, w>0.                                               (1)

**Actual null law.** Supply a jointly measurable, finite conditional
density of the entire evaluation array given U of the form

    p(y|U)=∏_(d=1)^D h_d(y_d | U,y_<d).                     (2)

For each d and each preceding history, h_d is a finite convex mixture
of (1), with shape in 𝒰_d and finite b and positive w. Mixture weights
and parameters may depend measurably on that history; they are fixed
before the block's returns are observed. The component count is fixed
and finite. This is the actual conditional law, not a fitted model.
In particular it allows arbitrary history-dependent changes in drift
and scale **between** blocks; conditional on its component, a block
has independent Gaussian returns with its one drift and scale.

Explicitly, write H_d=(U,y_<d) for this claim's pre-block record,
and Θ_d=𝒰_d×ℝ×(0,∞). For a fixed finite number L_d of components,
the mixing kernel is

    ν_d(H_d,A)=Σ_(l=1)^L_d λ_dl(H_d) 1_{θ_dl(H_d)∈A},
    λ_dl≥0,  Σ_l λ_dl=1,  θ_dl=(u_dl,b_dl,w_dl)∈Θ_d,
    h_d(y_d|H_d)=∫_(Θ_d) g_(d,θ)(y_d|H_d) ν_d(H_d,dθ).    (2a)

Weights and parameter maps are measurable. The integral is exactly
the finite sum above; its observation reference is Lebesgue measure
on (0,∞)^(n_d), with the actual block-start price supplied by H_d.
This states the kernel used here, not an arbitrary posterior. A
continuous parameter prior can have an infinite-support posterior;
such a posterior is not silently included in the finite-mixture
premise. Claim 033's wider formal Markov-kernel interface does not
change this claim's stated class.

Let q(U,y) be any jointly measurable finite nonnegative density
normalized in y for every U. Its selection uses U alone; it can be a
proper joint forecast whose later conditional predictions depend on
earlier evaluation observations. It cannot be an unnormalized
evaluation-fitted likelihood. Claim 035's exact p>1 CEV forecast is
one example, conditional on AX-56: at a positive start it has no zero
atom and hence is normalized on this positive domain. Its forecast
clock need not be a null clock. No CEV null is added by this choice.

For each d,u use 033's quantities A_du,B_du,C_du,T_d,V_du,S_d and
Q_du,K_du,H_du, computed within that block. Define

    P_du = sup_(b∈ℝ,w>0) g_(d,u,b,w),
    P_d  = max_(u∈𝒰_d) P_du,
    P_day = ∏_d P_d,
    E_day = 0 if q=0 or P_day=∞, and q/P_day otherwise.       (3)

Extend E_day by zero on arrays with any nonpositive or nonfinite
price; the probabilistic domain itself contains finite positive
prices. This convention permits zero masking outside the model; it
does not give those arrays a Gaussian likelihood.

1. **Exact profile and daily reset.** All P_d and P_day are measurable,
strictly positive extended values. If each block's return vector is
not proportional to its calendar vector, every profile is finite and
is given by 033's formula

    w_du* = 2Q_du/[n_d+sqrt(n_d²+H_du Q_du)],
    b_du* = (B_du+w_du* T_d/2)/A_du,
    log P_du = −(n_d/2)log(2πw_du*) −(1/2)Σ_j log u_j
               −Σ_j log y_dj −Q_du/(2w_du*)−K_du/2−w_du*H_du/8.
                                                               (4)

On those arrays P_day is the attained supremum of the product in
(1) over all independent daily choices (u_d,b_d,w_d). If any block
has R_d proportional to Δ_d, then every P_du for that block, and
P_day, is infinite; the joint supremum is infinite and E_day=0.
Consequently one unrestricted single-increment block makes the
entire score zero. If all n_d≥2, the singular set has probability
zero under (2). Each transformation u_d↦c_d u_d, c_d>0, with its
inverse w_d↦w_d/c_d, leaves the likelihood family and P_day unchanged.
Thus estimating only the scalar size of each day's shape cannot
change this profile. It does not license estimating the shape itself.

2. **Fixed-horizon calibration.** E_day is finite, nonnegative and
measurable on every array. Under (2),

    E[E_day | U]≤1,   E[E_day]≤1,
    P(E_day>1/α)≤α,   0<α<1.                               (5)

Any measurable lower nonnegative score preserves these conclusions.
For a fixed finite panel of m names, with each null name satisfying
its own contract (2) and arbitrary dependence among names, the base
e-BH rule of 053 has FDR≤q_FDR m_0/m under AX-53, using the original
m; zero masks are allowed. All panel scores, including alternatives,
must be finite as in (3). These are one fixed evaluation horizon's
guarantees, not monitoring or a guarantee conditional on an
evaluation-dependent screen.

3. **Cost of nuisance resets.** For a fixed full-record shape u,
split into the block shapes, P_day is at least the profile allowing
only one common b,w over the full record. More generally splitting
a block into subblocks with the restricted same shape and free new
parameters can only increase the profile. With the same numerator,
the score can only decrease. The comparison also holds against a
finite full-record clock catalogue when every clock's block
restriction is retained in the corresponding 𝒰_d.

There is an exact expression when there is just the calendar shape
u_dj=Δ_dj in each block. Define

    ahat_d = S_d/T_d,
    Q_d = Σ_j (R_dj−ahat_d Δ_dj)²/Δ_dj,
    ahat = (Σ_d S_d)/(Σ_d T_d),
    Q = Σ_d Q_d + Σ_d T_d(ahat_d−ahat)².

On the nonsingular domain Q_d>0 for every d, let P_common be 033's
single full-record calendar profile. The extra log denominator is

    J_day := log P_day−log P_common
           = (N/2)log(Q/N) − Σ_d (n_d/2)log(Q_d/n_d) ≥ 0.    (6)

Equality holds exactly when all ahat_d are equal and all Q_d/n_d are
equal. For the same positive numerator the loss in log score is
exactly J_day. This is a deterministic likelihood cost, not an
expected cost, size estimate or power bound.

## Proof

**Reuse of the block model and profile.** The normalized Gaussian
kernel and product density (1), and all quantities and formulas in
(4), are those of formalized 033 on that block. Successive finite
kernel products have the same normalization used in 035. Here (2)
also explicitly supplies the actual joint conditional density. There
is no assertion that conditioning a different process on an
estimated clock gives (2).

At any fixed positive array each g in (1) is finite and strictly
positive. Claim 033 proves P_du is its measurable supremum; it is
infinite exactly when R_d is proportional to Δ_d, independently of
u. Otherwise its unique drift/scale optimum is (4). Taking a finite
maximum over shapes gives a positive finite attained P_d. Choosing
each day's maximizer independently attains ∏P_d. Conversely every
product is bounded by ∏P_d, proving equality with the joint
supremum. If one factor is infinite, fix any admissible parameters
in the other blocks. Their densities are positive. A sequence of
parameters in the singular block with density tending to infinity
then makes the joint product unbounded. No 0·∞ convention is needed.

The displayed finite formulas, finite maxima, products and singular
branches prove measurability. Claim 033 supplies the singular-set
nullity for each block given its preceding history and each positive
Gaussian component. Finite mixtures retain it, and a finite union
over blocks is null under the supplied density (2). Claim 033's
bijective scale reparametrization applies separately to every block.

**Calibration is AX-58's application.** At each history, every
mixture component in h_d is at most P_d, so h_d≤P_d pointwise.
Equation (2) gives p≤P_day, including singular paths. P_day>0 and
q is finite, so (3) is finite on all positive arrays and the explicit
zero extension is finite elsewhere. The measurable dominating
denominator and normalized forecast therefore satisfy AX-58, giving
(5). This applies once to the whole fixed evaluation array; no
optional-stopping result is used. Lower scores preserve the moment.
Claim 053/AX-53 then gives the stated panel conclusion from the
finite null moments, without independence or changing m.

**Refinement and the cost identity.** Every common-parameter product
is an admissible point of the independently parameterized family.
The same inclusion holds when a block is split, and for every
retained catalogue restriction. Taking suprema proves the ordering,
with the infinite-profile convention preserving the score order.

For the calendar shape, 033 gives H_du=K_du=0 and w_du*=Q_d/n_d.
Weighted least-squares centering gives the finite identity

    Σ_(d,j)(R_dj−ahat Δ_dj)²/Δ_dj
       = Σ_d Q_d + Σ_d T_d(ahat_d−ahat)² = Q;

the cross terms vanish because Σ_j(R_dj−ahat_d Δ_dj)=0. Substitute
the calendar profile into log P_day and log P_common. All price
Jacobians, clock logarithms, log(2π) terms and −N/2 cancel, leaving
(6). Its nonnegativity already follows from the family inclusion.
For the equality condition, the common family is nonsingular since
Q≥ΣQ_d>0 and attains its profile. Equality of that product with the
product of positive individual maxima forces equality in every
factor. Claim 033's unique block optimum is
(b_d*,w_d*)=(ahat_d+Q_d/(2n_d),Q_d/n_d). A common optimum can equal
all of them exactly when the residual variances Q_d/n_d and the
ahat_d are both constant across d. This condition also suffices.

## Checks

`checks/068/check.py` independently evaluates the Gaussian density
and weighted sums, checks the daily profile against sampled fixed
parameters and direct numerical optimization, checks arbitrary
scale and calendar refinement, derives (6) by two separate
calculations, and exercises its equality and strict cases. It also
checks exact sphere standardization and an elementary finite-state
analogue with history-dependent conditional mixtures. All inputs
are deterministic. These are diagnostics, not proofs, simulations,
outward likelihood certificates or empirical size/power estimates.

## Not shown

- The profile, fixed-horizon calibration, refinement ordering,
  calendar reset cost and panel statement are formalized in
  `lean/Standalone/D23DailyProfile.lean`, proved by `statement_holds`
  in `lean/Novel/D23DailyProfileProof.lean`. Claim 033 is reused per
  block and the AX-58 step is proved from the supplied conditional
  density. The result permits any normalized numerator; the optional
  035 CEV forecast inherits AX-56's vacuous Brownian-base instance
  but is not a dependency of this formal result. FDR inherits
  AX-53's degenerate instance. The scalar-estimation interpretation,
  the remark about 035's zero atom, and the Python optimizer and
  numerical certification remain outside this formal statement;
  see the Formalizer note for the precise encoding.
- No estimated shape coverage, within-block volatility switches,
  jumps, stochastic volatility, leverage, observation noise or
  rounded-price validity. The actual conditional law is a premise;
  fitting a daily scale is not evidence that it holds. A switch
  inside a day in experiment 025 remains outside this null.
- The null here is the daily Gaussian mixture (2), not all of
  055's retained CEV nulls or all non-bubbles. A CEV numerator does
  not enlarge it. There is no physical/pricing-measure link supplied
  and no unconditional pricing-bubble identification claim.
- No boundary/absorption evidence: arrays outside the positive
  domain receive zero. The price Jacobian cannot be omitted unless
  numerator and denominator are both transformed to returns.
- No free handling of omitted overnight returns, data-selected day
  boundaries, future-conditioned openings or dropping a singular
  block after seeing it. The fixed disjoint blocks cover the
  observation sequence. A separate one-increment overnight block
  with unrestricted parameters makes (3) zero.
- No normalized conditional-on-scale forecast, latent rounded
  filter with daily parameters, calibrated numerical implementation,
  monitoring guarantee, repeated-panel FDR, or gain in realistic
  power. Daily profiling weakens the same-numerator score; an
  improved conditional or predictive numerator could change that
  comparison but is not asserted here.

**Interface to D22 (scope clarification, not a new sequential
conclusion).** For a single scored day or suffix, apply D=1 with U
replaced by a specified standard-Borel record U_d generating the
entire pre-score sigma-field 𝒢_d. Include all earlier observations,
the actual exact positive opening/start, and any unscored same-day
training prefix. Supply (2a) as the actual conditional mixing kernel
given this whole record, and a normalized forecast q_d(U_d,·) fixed
before the scored block. Then (5) is precisely
E[e_d^block|𝒢_d]≤1, with e_d^block=q_d/P_d and the same zero and
infinity conventions. The block density's being a finite mixture
must hold after this conditioning; it is not implied merely by
splitting observations or inserting a fitted scale.

This gives D22 its one-block premise. Its separate sequential
application uses the alternating checkpoint histories
ℋ_(d−1)⊆𝒢_d⊆ℋ_d⊆𝒢_(d+1), where ℋ_d includes the completed block.
Unscored gaps and prefixes contribute factor one while changing
information. Applying the one-day result afresh with the actual
opening is different from deleting increments out of the full-record
model (2). Do not condition earlier factors retrospectively on those
openings, or score a training observation again without a new
conditional-law argument. The full-record statement above remains
on its fixed consecutive partition.

Even if completed-block capital has checkpoint validity under
D22's additional source application, holding the last completed
capital constant inside a pending block does not automatically
give stopped-mean validity for the finer intraday filtration.
For example, terminal factor 2X for a fair bit X has mean one; if X
is revealed before settlement, stopping at the still-displayed one
when X=0 and at settlement when X=1 gives stopped mean 3/2.
An alarm using only completed-block values has the same crossing
event as at checkpoints. Reusing intraday-stopped capital, abandoning
a pending loss, or retaining max(1,e_d^block) requires a separate
argument and is not licensed here. The Gaussian finite-mixture and
exact-opening premises remain essential; rounded openings need
their actual conditional filter.

## Prior art

Read the D23 input and librarian findings, D22's distinction between
conditional profiles and current-prefix profiles, the disjoint-window
and evaluation-forecast-maximum refutations, and 033–038. Universal
inference and conditional likelihood domination are AX-58
[wasserman2019universal], not new results. The new application is
the block-law contract with unrestricted daily nuisance resets,
separable profile, singularity under refinement and exact calendar
reset cost. The sufficient-statistic route of [ramdas2023game]
§4.1.3 is an alternative; it is not used as an unadopted input here.
The first-day result requires no sequential ledger entry from D22.

## Review

Reviewer, 2026-10-07, on branch `mathb/d23-daily-profile` at `178b0061`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/068/`.
- **Inputs.** AX-53, AX-56 and AX-58 are audited, and AX-58 is proved. Claims 033, 035 and 053, the dependencies, are formalized. [ramdas2023game] is registered and is not used as an input.
- **Script.** My check is committed as `checks/review/068/reproduce.py`, with its rerun command and seeds in its header. It runs on 2 worker processes and is not a CI `check.py`.

**Part 1 (the daily profile): correct.**
- **Separability.** Block parameters are free and every density is positive, so the joint supremum of the product is the product of block suprema.
- **The singular case.** If one block has R_d ∝ Δ_d, its supremum is infinite (claim 033), and fixing admissible parameters elsewhere makes the product unbounded.
- **Measurability and scale.** These come per block from claim 033.

**Part 2 (calibration): correct.**
- **Domination.** Under (2), each h_d is a finite mixture of components at the block's actual start, each at most P_d. So p ≤ ∏P_d pointwise.
- **The test.** q is normalized given U, so AX-58 applies once to the whole evaluation array, and AX-53 gives the panel statement.
- **History-dependent parameters.** They are allowed because domination is pointwise for every history.

**Part 3 (the reset cost): correct.**
- **The ordering.** It follows from family inclusion.
- **The calendar profile.** For the calendar shape, H = K = 0 and w* = Q_d/n_d, so log P_d = −(n_d/2)[log(2πQ_d/n_d) + 1] − ½Σlog Δ − Σlog y.
- **The common profile.** The weighted decomposition Q = ΣQ_d + ΣT_d(â_d − â)² holds because the within-block residuals sum to zero. The difference is then (6), since the 2π, +1, Jacobian and clock-log terms cancel with Σn_d = N.
- **The equality case.** Equality needs both Jensen's step (equal Q_d/n_d) and Q = ΣQ_d (equal â_d), as stated.

**Checks** (evidence, not proof).
- **(a) The formulas.** On 12 random multi-block records, the summed claim-033 profiles match direct Nelder–Mead over all block parameters to a relative 7×10⁻¹⁶. Formula (6) matches log P_day − log P_common to 7×10⁻¹⁵.
- **(b) Monte Carlo.**
  - **Setup.** Days of 7 equal increments, 60 training days and D = 60 evaluation days, with a training-selected exact CEV forecast as the common numerator and 2,000 records per truth.

  | Truth | E_day: mean / P(E > 20) | E_common (one drift and scale): mean / P(E > 20) | Median J_day |
  |---|---|---|---|
  | N1: constant GBM | ≈0 / 0 | 0.34 / 0 | 67.8 |
  | N2: block-law null, daily scale switching {0.15, 0.45} with probability 1/10 per day and daily drift U[−0.5, 0.5] | ≈0 / 0 | **5×10⁷ / 0.032** | 166.8 |
  | CEV p = 2, κ = 0.45 | ≈0 / **0** | 8.8×10³⁷ / 0.268 | 71.0 |

  - **Reading.** The claim does what it says.
    - **It repairs between-day changes.** Under a null with daily drift and scale switches, which is inside (2), the common-profile score is invalid (mean far above 1 and 3.2% rejections), while E_day stays calibrated.
    - **But the reset is expensive.** It costs about 1.1 nats per day even on a constant GBM, so after 60 days this numerator has no power left (0.268 → 0).
    - **No contradiction.** That matches the claim's own "daily profiling weakens the same-numerator score", and the D15 pattern of my claim-059 and claim-061 reviews: each extra free nuisance shape absorbs the evidence.
- **The author's check.** I ran `checks/068/check.py` afterwards. It passes the joint optimizations, the daily profile, reset cost, scaling, singularity, Jacobian and conditional-mixture checks.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The block-law premise is strong.** It requires Gaussian returns within each day with one drift and scale, so within-day switches, as in experiment 025's regime null, are excluded, as stated.
2. **Omitted overnight returns are not free.** A one-increment block zeroes the score.
3. **The usefulness question is open.** A conditional or predictive numerator, which is not supplied, would be needed for power.

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red re-derived block separability and the singular case, pointwise domination of the block-law conditional mixture under AX-58 with history-dependent parameters, and the exact reset-cost decomposition; committed review script; power-cost scope stated


Reuse 033's profile, unique maximum, measurability, scale equivalence
and singularity, and apply the proved AX-58 to the finite product
denominator. Encode the actual finite conditional density (2) and
its component domination faithfully; a supplied global inequality
alone would omit the application step. Prove the finite product
supremum, refinement ordering and weighted residual decomposition
as deterministic lemmas. Use 033's unique optimizer for the
equality condition, without adding a new strict-Jensen input.
No new stochastic calculus or general sequential inference theory
is a formalization target. The Python optimizer and computation
certification are outside the theorem.

Formalizer, 2026-10-07, on `form/d23-daily-nuisance-profile`. **Status: formalized.** The statement is `lean/Standalone/D23DailyProfile.lean`, with
`statement := profile ∧ calibration ∧ refine ∧ calendar ∧ panel`.
It is proved in `lean/Novel/D23DailyProfileProof.lean` (`statement_holds`), from `D23DailyProfile{Flat,Sep,Null,Valid,Cost}`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** AX-58's step is proved directly from the supplied conditional density, and FDR is conditional on AX-53 through claim 026's `panel`. Claim 033's results are reused per block, not re-proved: the density, the closed form `Dv` and its supremum identity, the unique optimizer, the singular case and its null set, measurability, and scale invariance. Claim 035's CEV forecast is one admissible numerator; nothing depends on it.
- **Encoding.**
  - Block d has n_d prices as `NNR` values with claim 033's reference measure. On positive arrays that is Lebesgue measure; the null density vanishes off positive arrays, and the score is zero there.
  - The blocks are concatenated in order (`finSigmaFinEquiv`). A block's start is the price before it in that record, so `s(U)` or the previous block's last price; no increment is omitted.
  - P_d is the maximum of claim 033's `Dv` over the block catalogue, and P_day is the product over blocks.
  - **The block law (2).** Block d's factor is a finite mixture of claim 033's density at the block's start. Its weights, shapes in 𝒰_d, drifts and positive scales are jointly measurable and depend on the evaluation array only through the earlier blocks. The actual conditional law given U is, a.e., the reference measure with the product density.
- **Part 1 (`profile`).**
  - P_d and P_day are measurable and positive.
  - P_day equals the joint supremum of the product over independent daily choices (u_d, b_d, w_d) on every positive array.
  - Off the singular set every P_du is (4), P_day is finite, and the supremum is attained.
  - **Singular blocks.** A block with R_d ∝ Δ_d makes every P_du of that block and P_day infinite and the score zero, through a parameter sequence with all other blocks fixed at positive densities. A one-increment block is always singular.
  - With every n_d ≥ 2 the singular positive arrays are null.
  - Rescaling each block's shapes leaves P_day unchanged.
- **Part 2 (`calibration`).**
  - Each mixture component is at most its D_u ≤ P_d, so the density is at most P_day at every history.
  - Hence E_day is finite and measurable, its conditional and unconditional means are at most 1, P(E_day > 1/α) ≤ α, and every measurable lower score keeps the mean.
  - The singular set has probability zero when every n_d ≥ 2.
- **Part 3 (`refine`, `calendar`).**
  - **Groupings.** Any grouping of the blocks into common-parameter groups, with shape tuples whose block restrictions lie in the catalogues, has a profile at most P_day, so the same numerator's score is at least E_day. Splitting a block into sub-blocks is this with the sub-blocks as the fine blocks.
  - **Full-record clocks.** Claim 033's full-record profile on the concatenated record, for a full-record clock catalogue whose block restrictions are retained, is at most P_day. The full-record density at common parameters is the product of the block densities.
  - **The calendar shape.** The full record's Q is the weighted decomposition ΣQ_d + ΣT_d(â_d − â)². Both profiles are finite, and log P_day − log P_common is (6).
  - **Sign and equality.** J_day ≥ 0. J_day = 0 exactly when all â_d and all Q_d/n_d are equal. The equality case uses claim 033's unique optimizer: every block factor at the common optimum must attain its block maximum.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53, with arbitrary dependence, lower scores and zero masks at the original m.
- **Scope (2a), checked against mathb's clarification.** The block law is encoded as exactly the finite-atomic kernel (2a): `c_d` components, weights `wt ≥ 0` summing to one, measurable weight and parameter maps over 𝒰_d × ℝ × (0, ∞) that depend only on U and the earlier blocks, and the block's actual start. Continuous or infinite-support posteriors are not included; claim 033's wider kernel interface is not used for the premise. The D22 interface is the D = 1 case with U any standard-Borel pre-score record (the statement allows any such U), so `calibration` gives E[e_d^block | 𝒢_d] ≤ 1 there. No anytime, checkpoint or stopped-mean conclusion is encoded; that belongs to D22.
- **Not formalized.** These are commentary or about the Python checks:
  - the remark that estimating only each day's scalar size cannot change the profile (it follows from the scale invariance);
  - the remark that claim 035's forecast has no zero atom at a positive start;
  - the Python optimizer and computation certification.
