---
id: "028"
title: "D14: a Gaussian rounding budget without the latent training-state filter"
status: formalized
depends_on: ["023", "024", "027", "053"]
axioms_used: [AX-53, AX-58]
formal: lean/Standalone/D14RoundedStart.lean
direction: D14
---
## Statement

**Conditional on the specified Gaussian observation law.** The mechanism
is the existing equal-variance Gaussian affinity bound (claim 023),
followed by mapping and mixture integration (claims 024/027). The
unknown starting state changes only the first increment in coordinates
based at the rounded representative. No general robustness theorem or
stochastic calculus is new.

For each name fix a finite nonempty Gaussian null catalogue
Γ_i={(b,κ)}, with finite b and κ>0, before observing data. Fix positive
evaluation durations Δ_1,…,Δ_n, n≥1, and h_tick>0. Observe positive
prices using claim 024's log rounding map Q_h. Let U_i^h contain the
whole finite rounded training prefix, ending at the evaluation start,
and V_i^h be the n future integer cell labels. All spaces are standard
Borel. The last training label is z, with representative x_h=exp(h_tick z).

N₀ is a fixed supplied set of pricing-null names in a fixed panel of
size m. For each i∈N₀, assume a fixed (b_i,κ_i)∈Γ_i and a positive
latent exact training endpoint X_i. Conditional on (U_i^h,X_i), the
future log returns are independent normals with means
(b_i−κ_i²/2)Δ_j and variances κ_i²Δ_j, almost surely under the actual
training law. Also require Q_h(X_i)=x_h almost surely. The law of X_i
given the rounded prefix is otherwise arbitrary within that cell.
No independence across names is required. A Gaussian Markov law on
exact observations supplies this premise; disjoint timestamps alone do
not. No pricing measure is constructed from this observation contract.

For θ=(b,κ)∈Γ_i let g_(i,θ)^restart(v|u) be the probability of the
**entire rounded evaluation block** v when exact Gaussian prices start
at x_h. This is an integral over all future cells, not a product of
one-step probabilities restarted at each future rounded value. These
positive probability mass functions sum to one on Z^n. Supply any
measurable normalized forecast q_i^h(v|u)≥0 on Z^n selected using only
rounded training, and set

    D_i^restart(v|u)=max_(θ∈Γ_i) g_(i,θ)^restart(v|u),
    E_i^restart=q_i^h(V_i^h|U_i^h)/D_i^restart(V_i^h|U_i^h).       (1)

This score is finite on every label array. The reference null moment
is at most one at every training value and every θ∈Γ_i, by AX-58.
It is not claim 055's continuous-density score evaluated at rounded
prices. In particular, normalization of q_i^h on the label space is
a premise; evaluating an exact-price numerator at representatives does
not supply it.

1. **A filter-independent conditional budget.** Put

       κ_min,i = min_{(b,κ)∈Γ_i} κ,
       ε_i^round = sqrt(1−exp(−h_tick²/(16 κ_min,i² Δ_1))).       (2)

   At almost every rounded training prefix u under the actual law,

       TV(Law(V_i^h|U_i^h=u), g_(i,(b_i,κ_i))^restart(·|u))
         ≤ sqrt(1−exp(−h_tick²/(16 κ_i² Δ_1)))
         ≤ ε_i^round.                                          (3)

   The bound is uniform over the conditional latent-state distribution
   in the last cell, including its dependence on the entire earlier
   prefix. It depends on the first evaluation gap, not the count or
   durations of later evaluation observations. Rounding the future
   block can only reduce the distance used in this bound.

2. **Consequences for the restarted-cell score.** Applying claim 023's
   reference-moment comparison to (1) gives conditional and unconditional
   size at most min(1,α_i+ε_i^round) for the strict test E_i^restart>1/α_i.
   If ε_i^round<α_i, threshold 1/(α_i−ε_i^round) gives size at most α_i.
   For fixed finite c_i>0, the score

       E_i^round = min(E_i^restart,c_i)/(1+c_i ε_i^round)          (4)

   has conditional and unconditional null moments at most one. AX-53
   then gives FDR≤q_FDR|N₀|/m for base e-BH with arbitrary dependence,
   including measurable zero masks at original m. Nonnegative measurable
   implemented scores bounded above by (4) preserve the unconditional
   moment and FDR conclusions. No conditioning on a selected list is
   asserted. No raw e-moment guarantee is obtained from (3) alone.

3. **Sufficient design tolerance and its cost.** For 0<e<1,

       ε_i^round≤e  iff
       h_tick≤4 κ_min,i sqrt(Δ_1) sqrt(−log(1−e²)).              (5)

   Thus retaining this particular budget at a fixed first gap needs
   a supplied strictly positive lower scale. At fixed spacing and scale,
   the upper bound tends to one as Δ_1 decreases to zero. This does not
   assert that the actual rounded-law discrepancy grows monotonically
   or tends to one. An unrestricted scale family has no uniform bound
   below one from (2). A strict rejection with (4) requires
   ε_i^round<α_i and c_i>1/(α_i−ε_i^round), by claim 023. These are
   limits of this correction, not impossibility results for exact-cell
   filtering or other tests.

## Proof

Fix an actual null and a rounded training prefix u. Its conditional
latent endpoint has log displacement a=log(X_i/x_h) in
[−h_tick/2,h_tick/2). Given a, write future prices as

    x_h exp(a+R_1+…+R_j),  j=1,…,n.

Use the invertible cumulative-sum coordinates based at x_h: the first
increment is R_1+a, and every later increment is R_j. Against the
restarted law (a=0), the independent Gaussian vectors differ only in
the first mean. Claim 023's already proved one-dimensional Gaussian
affinity formula, or its product form used by claim 027, gives

    A=exp(−a²/(8 κ_i² Δ_1)),
    TV≤sqrt(1−A²)≤sqrt(1−exp(−h_tick²/(16 κ_i² Δ_1))).

No drift term remains because both laws have the same physical drift
and scale. Applying the common measurable map from increment vectors
to rounded future labels preserves the event bound: take the inverse
image of each label event. Then integrate the event difference against
the actual conditional law of a. As in claim 027's mixture step, every
component obeys the same bound against the same reference, so the
mixture does too. This proves (3); replacing κ_i by its catalogue lower
bound weakens it. This argument does not replace the unknown posterior
by a uniform distribution within the last cell.

Each restarted probability is strictly positive: every finite vector
of cells contains an open box and the joint Gaussian log-price density
is positive everywhere. The cells partition the positive price space,
so their probabilities sum to one. The maximum over Γ_i is measurable,
positive and at most one. The normalized numerator is at most one,
so its ratio is finite at each array. At every u and every null θ,

    Σ_v E_i^restart(u,v) g_(i,θ)^restart(v|u)
        ≤ Σ_v q_i^h(v|u)=1.

This verifies AX-58's existing domination mechanism; it is not a new
split-likelihood theorem. Apply claim 023's event and bounded-function
comparisons using (3). Conditional Markov gives the raw-size bound;
the cap has conditional mean at most 1+c_i ε_i^round before division.
Integration and AX-53 give part 2, including lower scores and masks.
Solving (2) for h_tick gives (5); the cap constraint is claim 023 (5).

A nondegenerate instance is any fixed Gaussian pair from Γ_i, positive
start, and independent Gaussian returns through the training and
evaluation grids, followed by Q_h. Taking q_i^h to be one of the
restarted mass functions supplies a normalized forecast. This exercises
nonzero conditional latent-state uncertainty and positive future
variance, although it makes no assertion of power.

## Checks

`checks/028/check.py` compares (2) to the earlier nine rounded-cell
quadratures, checks Gaussian overlap bounds and independent affinity
integrals, verifies that shifting only the first increment gives the
same bound for different later grids, and checks inversion (5).
`checks/028/budget.py` reports supplied-design tolerances. All numerical
results are deterministic diagnostics, not certified error bounds or
simulations. The proof is the argument above, not these checks.

## Not shown

- No latent training-state filter is needed for the bound, but evaluating
  g^restart for a long rounded future block still requires joint cell
  integration. No scalable implementation or one-sided integration
  certificate is supplied.
- No calibration for continuous densities evaluated at rounded values,
  or products restarted at each future representative. No claim that
  this bound corrects the current usable test v1 without changing its
  likelihoods. No CEV, absorbing-zero, jump, SV or measurement-noise null
  is added; the actual pricing-null law must meet the Gaussian contract.
- Neither the catalogue nor its lower scale is estimated here. The
  reference must match the actual Gaussian parameters, not a nearby
  fitted pair. A scale floor chosen from an earlier window needs its
  own coverage argument.
- No power estimate, market tick assumption or repeated-date guarantee.
  A near-one upper bound is not evidence of actual size inflation.
- The cell laws, first-increment shift, conditional budget, score
  consequences and tolerance are formalized in
  `lean/Standalone/D14RoundedStart.lean`, proved by
  `lean/Novel/D14RoundedStartProof.lean` (`statement_holds`). FDR alone
  remains conditional on AX-53, whose available instance is degenerate;
  AX-58 is proved. The finite-grid Gaussian observation law remains a
  stated premise, with no additional stochastic-analysis input. The
  Markov/disjoint-timestamps commentary, the nondegenerate instance in
  the prose proof, and the general future-rounding contraction remark
  are not formalized; the budget is proved directly for rounded blocks.

## Prior art

Read the registered [wasserman2019universal] Section 6 conditional-
likelihood discussion and AX-58; its domination argument supplies the
reference moment. [wang2020false] supplies AX-53. Read claims 023, 024
and 027, the GaussianAffinity and D14Misspecification Lean proofs, the
D14 rounding findings and the disjoint-window refutation. The existing
results settle affinity, bounded-score transfer and mixture integration.
The application here checks that rounded-start uncertainty enters only
the first future increment, giving a posterior-independent budget and
an explicit scale/gap tolerance for a restarted **cell** likelihood.

## Review

Reviewer, 2026-10-06, on branch `math/d14-rounded-start-budget` at `8660fdc`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/028/`.
- **Inputs.** AX-53 and AX-58 are audited, and AX-58 is proved. Claims 023, 024, 027 and 053, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/028/reproduce.py`, with its rerun command and seed (`default_rng(28)`) in its header. It is not a CI `check.py`.

**Part 1: correct.**
- **The first-increment shift.** The latent displacement is a = log(X/x_h) ∈ [−h/2, h/2). In cumulative-sum coordinates based at x_h, only the first increment's mean shifts, by a, with variance κ²Δ₁.
- **The bound.** The equal-variance Bhattacharyya coefficient is exp(−a²/(8κ²Δ₁)), so TV ≤ √(1 − e^{−a²/(4κ²Δ₁)}) ≤ √(1 − e^{−h²/(16κ²Δ₁)}).
- **Uniformity.** The common rounding map preserves the event bound. Every latent component obeys the same bound against the same restarted reference, so the mixture does too, whatever the posterior of a given the rounded prefix. No uniform-in-cell assumption is used. This is the substantive improvement over claim 024's filtering requirement.

**Part 2: correct.**
- **The reference moment.** The cell probabilities are strictly positive and sum to one. D ≥ g_θ for every θ ∈ Γ, so Σ_v (q/D) g_θ ≤ Σ q = 1.
- **The bounds.** Claim 023's event and bounded-function comparisons then give the size bound, the shifted threshold and the capped moment (4). AX-53 gives FDR.

**Part 3: correct.** (5) is the inverse of (2): ε ≤ e ⟺ h² ≤ −16κ²Δ₁ log(1 − e²).

**Checks** (evidence, not proof).
- **(a) The bound against TV.**
  - **Exact one-step TV of rounded labels** at the worst displacement |a| = h/2 is 0.202, 0.155, 0.180 and 0.409, against ε = 0.260, 0.197, 0.231 and 0.595, for (h, κ, Δ) = (0.02, 0.3, daily), (0.01, 0.2, daily), (0.002, 0.3, 5-minute) and (0.05, 0.3, daily).
  - **For 3-step rounded blocks,** the Monte Carlo TV (4×10⁵ draws) is 0.203 at a = ±h/2, the same as one step, and 0.119 at a = 0.3h. Only the first gap matters, as part 1 states.
- **(b) The restarted-cell score, n = 1.**
  - **The setup.** True GBM null (0, 0.3); exact daily training prices rounded at h = 0.02, so the endpoint has its true posterior in the cell; Γ = {(0, 0.3), (0, 0.45)}; forecast q = the restarted cell law of (0, 0.2); 2×10⁵ paths.
  - **Results.** Raw mean 0.967. Capped mean at c = 20 is 0.156. P(E > 10) = 0, within the bound α + ε = 0.36.
  - **A limit of this check.** The posterior displacement here was close to uniform (sd 0.00578 against 0.00577), so it does not stress a strongly non-uniform posterior. The proof does not need one.
- **(c) The budget at realistic ticks**, κ_min = 0.2:

  | Tick | Log tick | Daily ε | 5-minute ε |
  |---|---|---|---|
  | 1 cent on $100 | 10⁻⁴ | 0.002 | 0.018 |
  | 1 cent on $10 | 10⁻³ | 0.020 | 0.174 |
  | 1 cent on $2 | 5×10⁻³ | 0.099 | 0.732 |

- **The author's check.** I ran `checks/028/check.py` afterwards. It passes nine rounded laws, 81 first-increment product comparisons, three affinity quadratures and eight tolerance inversions.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **This is the first informative D14 budget.** For daily data on normally priced stocks it is essentially free (ε ≈ 0.002). It also explains why experiment 022's 10⁻⁴-tick rounding changed no rate. At 5-minute sampling it is usable only for higher-priced names.
2. **It applies to the restarted-cell likelihood (1) only,** not to usable test v1. That test evaluates continuous densities at rounded prices, which claim 024 shows can break the e-moment. Computing (1) needs joint cell integrals over the evaluation block, for which no scalable implementation is supplied.
3. **The rest is as stated.** The Gaussian null catalogue and its lower scale must be fixed and true, and claim 058's coverage caveats apply to any declared scale floor. CEV, absorption, jumps and SV are not covered.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the first-increment shift and uniform rounded-start TV bound over the latent posterior, the cell-probability reference moment and claim-023 comparisons, and the inversion; committed review script; scope honest


Reuse the Gaussian affinity/product lemmas, existing event comparison
under a common measurable map, and integration against the conditional
endpoint kernel. Keep the future joint-cell mass distinct from sequential
representative substitution. Formalize the first-increment reduction
and apply claim 023's proved transfer, rather than rebuilding Gaussian
or conditional-likelihood theory. FDR alone uses AX-53.

Formalizer, 2026-10-06, on `form/d14-rounded-start`. **Status: formalized.** The statement is `lean/Standalone/D14RoundedStart.lean`, with
`statement := cells ∧ shift ∧ budget ∧ consequences ∧ panel ∧ tolerance`.
It is proved in `lean/Novel/D14RoundedStartProof.lean` (`statement_holds`), with the deterministic parts in `D14RoundedStartCellsProof`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** FDR is conditional on AX-53 (claim 053's `AX53`), through claim 026's `panel`. Everything else is proved. The Gaussian step is claim 027's component bound, which rests on claim 023's affinity. AX-58's domination is the finite sum Σ_v (q/D) g_θ ≤ Σ_v q = 1.
- **Encoding.** One name, with n + 1 ≥ 1 evaluation steps.
  - g^restart(·|u) is the law on ℤ^(n+1) of the labels of x_h·exp(R₁ + … + R_j) under claim 023's `lawR`: an image of the whole block, not a product of restarted one-step masses.
  - The rounded training record U lives in any measurable space, with a measurable last label z(U).
  - The premises are:
    - X > 0 and Q_h(X) = exp(h z(U)) almost surely;
    - the conditional law of the future log returns R given (U, X) is `lawR Δ b κ` almost surely;
    - V = labels of X·exp(cumulative R).
  - The conditional law of X given U is otherwise arbitrary.
  - TV is sup_A |H(A) − G(A)|, without the factor two, as in claim 023.
- **`cells`.**
  - Each restarted law is a probability law. Every mass is in (0, 1], because each label set contains a nonempty open set of returns and `lawR` has a positive density, and the masses sum to one.
  - Masses are measurable in the start.
  - D^restart lies in (0, 1], so (1) is finite. Its reference moment is ≤ 1 at every positive start and every θ ∈ Γ, for any nonnegative q summing to one.
- **`shift`, part 1's reduction.** From x instead of y the labels are those from y with the first return moved by log(x/y). The moved Gaussian law is claim 027's `lawV` with the first drift raised by log(x/y)/Δ₁, whose affinity is exp(−log(x/y)²/(8κ²Δ₁)). So TV ≤ √(1 − exp(−log(x/y)²/(4κ²Δ₁))) after the label map.
- **`budget`, (3).** At almost every u, TV(Law(V | U = u), g^restart_(b,κ)(·|u)) ≤ √(1 − exp(−h²/(16κ²Δ₁))).
  - The proof writes the conditional law of V as the mixture of restarted laws over the conditional law of X given U. That law lives on the last cell, where |log(X/x_h)| ≤ h/2, and every component obeys the same bound.
  - The comparison with κ_min is in `tolerance`: the bound decreases in κ, and κ_min is a positive lower bound of the catalogue.
- **`consequences`, part 2,** with ε^round:
  - E^restart is jointly measurable and nonnegative;
  - the strict test has conditional size ≤ α + ε^round and unconditional size ≤ min(1, α + ε^round);
  - the threshold 1/(α − ε^round) has size ≤ α;
  - (4) has conditional and unconditional null moment ≤ 1, and so does every measurable score between 0 and (4);
  - a rejection by (4) at 1/α forces ε^round < α and c > 1/(α − ε^round).
  The proof applies claim 027's latent-mixture theorem with a one-point latent space, after replacing the conditional law by the reference on a null set of training values.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53, with arbitrary dependence, lower scores and measurable zero masks at the original m.
- **`tolerance`, part 3.**
  - 0 ≤ ε < 1, and ε decreases in κ.
  - (5) holds for 0 < e < 1.
  - The bound tends to one as Δ₁ ↓ 0, and as κ ↓ 0.
- **Not formalized.** Commentary only:
  - the remarks that a Gaussian Markov law supplies the premise and disjoint timestamps do not;
  - the nondegenerate instance in the proof;
  - the statement that rounding the future block can only reduce the distance. The bound is proved directly for the rounded block.
