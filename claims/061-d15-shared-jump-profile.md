---
id: "061"
title: "D15: a shared-parameter jump envelope with convergent two-dimensional enclosures"
status: formalized
depends_on: ["027", "053", "054", "055", "060"]
axioms_used: [AX-53, AX-55, AX-56, AX-58, AX-59]
formal: lean/Standalone/D15SharedJump.lean
direction: D15
---
## Statement

**Conditional on claim 060's cited inputs and actual-law premises.** The
mechanism is the same AX-58 upper-likelihood-bound application, with a
tighter deterministic envelope. Compact maximization and convergence
of interval bounds use the existing extreme-value and uniform-continuity
theorems, not a new optimization theorem. The application below checks
their hypotheses and supplies explicit enclosing formulas.

Keep all of claim 060's design and (1)–(3): a finite nonempty panel,
known positive starts, fixed grids and training split, n_e≥2 evaluation
increments, the ordered finite CEV catalogue with a retained p≤1 null,
mixed reference μ_CEV, and its normalized training-only selected
numerator Ĝ_i. Retain all CEV catalogue nulls and all constant Gaussian
drift/scale laws. Before any data fix σ_min>0 finite and Λ_J∈[0,∞].
The jump parameters have σ_J≥σ_min and finite 0≤λ_J≤Λ_J, arbitrary
finite a_J,μ_J and η_J>0, constant within the evaluation block. The
independent-return law is AX-59's Poisson mixture. At actual nulls the
law given actual training is a supplied measurable mixture of these
jump laws, retained CEV laws and constant Gaussian laws, as in claim
060 (3). Training/alternative laws and panel dependence are otherwise
arbitrary. No fitted value establishes these premises or a pricing label.

For a positive evaluation path from a positive training endpoint, put
r_j=log(y_j/y_(j−1)), d_j=Δ_j, n=n_e, J_y=∏1/y_j and
C_d=∏(2πd_j)^(-1/2). First suppose Λ_J<∞. Set

    q_j=exp(−Λ_J d_j),       p_j=1−q_j,
    F_J(a,s)=C_d s^(−n) ∏_j [p_j+q_j exp(−(r_j−a d_j)²/(2s²d_j))],
    V_J=J_y sup_(a∈R,s≥σ_min) F_J(a,s).               (1)

For Λ_J=∞ define V_J=M_J, claim 060's ceiling. These are likelihood
envelopes, not probability densities and not the exact jump-family
supremum. Off the positive stratum use the common zero/trapped
extension, without evaluating logarithms or reciprocals at zero.

1. **Coverage with a tighter envelope.** For every jump parameter
   in claim 060's family, on every array,

       g_J ≤ V_J ≤ U_J,                               (2)

   where U_J is claim 060's envelope. V_J is finite and measurable.
   Use D_*=max(G_(i,0),D_G,V_J) with the unchanged numerator and
   zero-at-zero-numerator/infinite-denominator convention to define
   E_i^prof. It has all of claim 060's conditional/unconditional null
   moments, size, reciprocal-p and original-m e-BH conclusions under
   the same assumptions. Pointwise

       E_i^J ≤ E_i^prof ≤ E_i^drift ≤ E_i.             (3)

   No jump-family restriction is added. At Λ_J=0 the score equals
   claim 055; at Λ_J=∞ it equals claim 060. Increasing the cap or
   lowering the floor weakly lowers the ideal score. Nonzero score
   examples, the inherited Q_G=0 zero-evidence convention and the
   absorbed-score bound ≤1 are as in claim 060. No useful power is
   asserted by these orderings.

2. **A data-dependent search rectangle, not a data-chosen null.**
   For finite cap define

       a_-=min_j r_j/d_j,       a_+=max_j r_j/d_j,
       a_0=Σr_j/Σd_j,          Q=Σ(r_j−a_0 d_j)²/d_j,
       s_0=max(σ_min,sqrt(Q/n)),    L=F_J(a_0,s_0)>0,
       s_+=(C_d/L)^(1/n).                            (4)

   Then s_+≥s_0≥σ_min, and

       sup_(a∈R,s≥σ_min) F_J(a,s)
         = max_(a,s∈[a_-,a_+]×[σ_min,s_+]) F_J(a,s). (5)

   Degenerate intervals are allowed. The rectangle depends on the
   evaluation data only to enclose the maximum of the unchanged null
   envelope. It excludes no potentially larger value and does not
   turn fitted parameters into a coverage premise.

3. **Finite analytic enclosures.** Cover the rectangle in (5) by
   finitely many closed rectangles B=[l_a,u_a]×[l_s,u_s]. For each
   put e_j(B)=dist(r_j,[l_a d_j,u_a d_j]) and

       W_J(B)=C_d l_s^(−n)
           ∏_j [p_j+q_j exp(−e_j(B)²/(2u_s²d_j))].    (6)

   Then F_J≤W_J(B) on B. Let L_P be the maximum of L and evaluations
   of F_J at finitely many feasible points, and let B_P=max_B W_J(B).
   One has L_P≤max F_J≤B_P. Subdivision makes the upper bound
   nonincreasing; retaining prior evaluation points makes L_P
   nondecreasing. For partitions whose largest side length tends to
   zero, both bounds converge to max F_J if at least one point is
   evaluated in each box. This follows also for log-scale partitions
   whose corresponding scale widths tend to zero.

   For any such finite cover, define the price upper bound

       V_J^P = min(U_J, J_y B_P),                    (7)

   with direct zero/trapped values off the positive stratum. Every
   measurable rule producing a finite cover as above gives g_J≤V_J^P.
   Its score E_i^P, with denominator max(G_(i,0),D_G,V_J^P), is valid
   under the same null premise, and

       E_i^J ≤ E_i^P ≤ E_i^prof ≤ E_i^drift.          (8)

   Refinement increases these analytic scores toward E_i^prof. No
   optimizer success flag or small gap is needed for domination by a
   correct upper bound; a budget can stop refinement early. Conversely,
   candidate evaluations L_P alone are lower bounds on a maximum and
   cannot be used as dominating denominators.

## Proof

**Shared-parameter domination.** Fix a jump parameter and an increment.
Its zero-count Gaussian has mean a_J d_j and variance σ_J²d_j. Every
positive-count component has variance at least σ_J²d_j and hence
density at most 1/(σ_J sqrt(2πd_j)). The count weights sum to one.
Consequently its return density is at most

    [exp(−λ_Jd_j) exp(−(r_j−a_Jd_j)²/(2σ_J²d_j))
       + 1−exp(−λ_Jd_j)] / (σ_J sqrt(2πd_j)).

This bound increases with λ_J, since the residual exponential is at
most one. Replace λ_J by Λ_J, multiply the nonnegative bounds, and
apply the price Jacobian to obtain g_J≤J_y F_J(a_J,σ_J)≤V_J.
Only the positive-count part is bounded by heights: a and s remain
shared across every increment.

To check V_J≤U_J, expand the product of two terms in (1). The all-
zero-count choice has weight ∏q_j=exp(−Λ_Jτ_e), and its density is
at most both D_G and M_J. Every other term, after its weight is
removed, is at most M_J: both the Gaussian factor and the height at
s≥σ_min are bounded by the height at σ_min. All these weights sum
to 1−exp(−Λ_Jτ_e). Claim 060's same mixture algebra gives U_J.
The infinite-cap case and zero strata follow directly from claim 060.

**Checking compact maximization.** If a<a_-, increasing a up to a_-
weakly reduces every residual absolute value; if a>a_+, decreasing it
to a_+ does the same. Thus the supremum can be restricted to that
closed interval without loss. Each bracket in (1) lies in (0,1], so
F_J(a,s)≤C_d s^(−n). At s_0 this implies s_+≥s_0. For s>s_+ the
ceiling is strictly less than L, which is already attained at the
feasible (a_0,s_0). The remaining rectangle is nonempty and compact,
and F_J is continuous with positive s. The existing extreme-value
theorem yields the attained maximum (5).

For measurability it is unnecessary to prove a separate selection
theorem: for fixed declarations, the supremum in (1) equals the
countable supremum over a∈Q and s∈{σ_min+t:t∈Q,t≥0}, by continuity.
Each function of the observations is measurable, so is their supremum.
Formula (2) bounds it by finite U_J. The explicit strata preserve
measurability and finiteness.

**Checking the enclosure.** On B, s^(−n)≤l_s^(−n), and
|r_j−a d_j|≥e_j(B), while s≤u_s. Each bracket is therefore bounded
by its displayed counterpart in (6). This proves domination on
every box and hence B_P≥max F_J. Subdivision raises l_s, lowers u_s
and cannot reduce e_j, so child upper bounds are at most their
parent's. The lower-bound assertions use feasible point evaluations.

The box-endpoint expression (6) is continuous on the compact set of
ordered endpoints within the search rectangle, with all scales
bounded away from zero. On a degenerate box it equals F_J at that
point. Apply the existing uniform-continuity theorem: as the box
diameters tend uniformly to zero, W_J(B) differs uniformly by o(1)
from any F_J evaluated in B. Thus the maximum upper and sampled lower
bounds have a gap tending to zero, proving convergence. This checks
the usual enclosure argument's hypotheses; no general compactness or
interval-optimization theorem is rebuilt.

Both terms in (7) dominate V_J, giving (8) after maxing with the
unchanged CEV/Gaussian denominator. A measurable finite-cover rule
makes the finite maximum measurable. Deterministic refinement with
fixed tie rules and a finite iteration budget is such a rule; an
arbitrary unmeasurable choice is not asserted to be valid. Standard
lower-score masking remains available for reported numerical failures.

**Inference and ordering.** The denominator dominates every component
of claim 060 (3), and the numerator is still normalized at every
training value. AX-58 and claim 027's mixture integration therefore
apply exactly as in claim 060, followed by AX-53. No stochastic
normalization theorem is re-proved here. The denominator comparisons
give (3) and (8). Raising the cap raises every F_J; lowering the floor
enlarges its parameter domain. At zero cap F_J is a Gaussian density
in return coordinates with scale at least the floor, so its supremum
is already dominated by D_G; at infinite cap V_J=M_J. Absorption and
the positive nonzero example inherit claim 060's support facts.

## Checks

`checks/061/profile.py` implements finite log-scale box refinement with
the analytic bounds, and `checks/061/scoring.py` retains all records
through the existing total adapter. `checks/061/check.py` checks
Poisson-series domination, individual box bounds, refinement nesting,
the zero/infinite-cap limits, support strata, training-only selection
and numerical failures. A fixed alternating-return example compares
envelope sizes; it is not a simulated price path or a power estimate.
All arithmetic is diagnostic, not certified outward rounding.

## Not shown

- No exact constrained jump-family supremum: the positive-count means
  and variances are still relaxed. The tight limit computed here is
  the supremum of F_J, itself an envelope. It can lose useful power.
- No useful power, superiority, uniform runtime or guarantee that a
  practical box budget gives a small gap. An analytic enclosure can
  remain loose while valid. Fixed-path envelope comparisons do not
  establish statistical performance.
- No certified implementation: search endpoints, point evaluations,
  box bounds, CEV/Gaussian likelihoods and final scores need controlled
  rounding for a numerical guarantee. A fitted maximum is insufficient.
- No new null coverage, honest floor/cap declaration, pricing-null link,
  jump-and-switch law, general SV, rounded observations or repeated-date
  validity. These remain exactly the supplied limitations of claim 060.
- Parts 1–3 are formalized in `lean/Standalone/D15SharedJump.lean` and
  `lean/Standalone/D15JumpProfileSearch.lean`, with proof assembled in
  `lean/Novel/D15SharedJumpProof.lean`: coverage (2), the score
  conclusions and orderings (3), the search rectangle (5), the box
  bounds (6) with refinement and convergence, and (7)–(8) for every
  measurable cover rule. Inference remains conditional on claim 060's
  AX-55/56 kernels (vacuous instances), with FDR conditional on AX-53
  (a degenerate instance). AX-58 is proved. AX-59 is not needed by the
  Lean proof, which integrates the supplied conditional mixture
  directly; its jump-process interpretation remains source-audited
  only. The numerical scripts are not formalized and have no
  outward-rounding certificate.

## Prior art

The general mechanism remains [wasserman2019universal] through AX-58,
with the AX-59 density from [merton1976jumps] and e-BH from [wang2020false].
The source discussion, D15 sweep, refuted unrestricted-supremum note,
FINDINGS and claim 060's review were checked. Compact maximization and
uniform continuity are existing Mathlib results (`IsCompact.exists_isMaxOn`
and `IsCompact.uniformContinuousOn_of_continuous`); use them directly.
Finite interval bounds and their refinement are standard, not new
optimization theory. The application supplies the shared-parameter
relaxation, the explicit compact search reduction and the box bounds
for this likelihood, while preserving the original covered null family.

## Review

Reviewer, 2026-10-06, on branch `mathb/d15-shared-jump-profile` at `6560540`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/061/`.
- **Inputs.** AX-59 is source-audited, and AX-53, AX-55, AX-56 and AX-58 are audited. Claims 027, 053–055 and 060, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/061/reproduce.py`, with its rerun command and seeds in its header. It runs on 2 worker processes under the CPU budget in `agents/START.md`, and it is not a CI `check.py`.

**Part 1: correct.**
- **Per-step domination.** At each increment the zero-count term is the Gaussian factor with weight e^{−λd}. Every positive-count term has variance ≥ σ_J²d, so it is at most the height 1/(σ_J√(2πd)). The return density is therefore ≤ [e^{−λd}e^{−z²/2} + (1 − e^{−λd})]/(σ_J√(2πd)), which is nondecreasing in λ.
- **Sharing (a, σ).** With (a, σ) shared across increments and the Jacobian applied, g_J ≤ J_y F_J(a_J, σ_J) ≤ V_J.
- **V_J ≤ U_J.** Expanding ∏[p_j + q_j·(·)] gives the all-zero term (≤ min(D_G, M_J)) with weight e^{−Λτ}, and the rest ≤ M_J, which is claim 060's algebra.
- **The rest.** AX-58, claim 027's mixture integration and AX-53 follow as in claim 060.

**Part 2: correct.**
- **The drift range.** Moving a into [min r/d, max r/d] reduces every residual.
- **The scale range.** F_J ≤ C_d s^{−n}, so above s₊ the value is below the attained L. The rectangle is compact and F_J is continuous, so the maximum is attained (5).
- **Measurability.** The countable rational supremum gives measurability without a selection theorem.

**Part 3: correct.** On a box, s^{−n} ≤ l_s^{−n}, residuals are ≥ e_j(B) and s ≤ u_s, which gives (6). Subdivision is monotone, and uniform continuity on the compact endpoint set gives convergence of B_P and L_P.

**Checks** (evidence, not proof).
- **(a) Domination.** On 200 random (θ, short path) cases (n_e = 2–5, irregular steps, Λ_J ∈ {0, 0.5, 5, 50}), the Merton series density (60 terms plus the tail bound) ≤ J_y F_J(θ) ≤ J_y B_P held every time. sup F stayed ≤ claim 060's U_J.
- **(b) The rectangle reduction.** In 200 cases, 4,000-point random searches over a, s far outside the rectangle never exceeded the rectangle's box upper bound.
- **(c) Enclosure.** Branch and bound over the boxes (6), pruning boxes below the best point value, gives a median gap log(B_P/L_P) of 0.013 on short paths. On daily one-year evaluation blocks it is 0.28–0.72 within the iteration budget.
  - **A practical note.** A fixed non-adaptive box grid left a 7–12-nat gap on daily blocks, because n·Δlog s compounds. Adaptive refinement in s is essential in practice.
- **(d) Monte Carlo.**
  - **The setup.** Daily prices for two years, training on year one, the absorbed CEV catalogue p ∈ {½, 1, 3/2} × κ ∈ {0.2, 0.3, 0.45}, σ_min = 0.20, α = 0.1 and 1,000 paths per cell.
  - **The scores.** E^P uses the valid denominator max(G₀, D_G, min(U_J, J_y B_P)). Its true ideal E^prof is at most e^{gap} times larger.

  | Truth | Cap Λ_J | Claim 055 | Claim 060 | Claim 061 E^P |
  |---|---|---|---|---|
  | GBM + jumps λ = 1 (covered) | 1 | 1.6 / 0.003 | 10⁻⁸⁷ / 0 | 0.021 / 0 |
  | GBM + jumps λ = 1 (covered) | 5 | 0.37 / 0.003 | 10⁻⁸⁸ / 0 | 6×10⁻⁵ / 0 |
  | GBM + jumps λ = 5 (covered) | 5 | 208 / 0.004 | 10⁻⁹⁶ / 0 | 4×10⁻⁶ / 0 |
  | CEV p = 3/2, κ = 0.30: power | 1 | 0.048 | 0 | **0.006** |
  | CEV p = 3/2, κ = 0.30: power | 5 | 0.048 | 0 | **0** |
  | CEV p = 3/2, κ = 0.45: power | 1 | 0.212 | 0 | **0.056** |
  | CEV p = 3/2, κ = 0.45: power | 5 | 0.201 | 0 | **0.002** |

  Cells are mean / P(E > 1/α).
- **The author's check.** I ran `checks/061/check.py` afterwards. It passes the box bounds, refinement, limits, Jacobian, score ordering and failure checks.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **This is a real improvement over claim 060's ceiling.** Sharing (a, σ) means only returns that look like jumps pay the per-step height, so covered jump nulls stay valid while some power returns. At a cap of 1 jump per year, power against p = 3/2, κ = 0.45 is 5.6%, against 0 for claim 060.
2. **It remains far below claim 055's uncovered 21%.** At a cap of 5 per year power is again essentially 0. The positive-count relaxation (heights at the shared σ, free jump means) still absorbs most of the evidence a mild CEV alternative leaves.
3. **A useful jump null would need the relaxation tightened toward the exact constrained jump-family supremum,** as "Not shown" says, or an honest small cap. Claim 058's coverage caveats apply to any declared cap.
4. **Not covered:** SV, regime changes, rounding, certified arithmetic and the pricing link, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived per-step domination with shared (a, sigma), V_J <= U_J, the compact rectangle reduction and attained maximum, measurability, and convergent box enclosures; committed review script; power limits stated


Reuse claim 060's score/AX-59 interface, AX-58 and the existing mixture
integration. Formalize the deterministic inequalities and check the
existing compactness/continuity lemmas' hypotheses. Do not reconstruct
Gaussian/Poisson process theory or a general global optimizer.

Formalizer B, 2026-10-06, on `formb/d15-shared-jump-cover` (stage 2; stage 1 is `formb/d15-jump-profile-search`). **Status: formalized.**
- **Files.** The statement is in `lean/Standalone/D15SharedJump.lean` (`statement := envelope ∧ score ∧ D15JumpProfileSearch.statement`). The proof is `lean/Novel/D15SharedJumpProof.lean` (`statement_holds`), with:
  - `D15SharedJumpEnvelope.lean`: V_J;
  - `D15SharedJumpBox.lean`: V_J^P;
  - stage 1, `Standalone/D15JumpProfileSearch.lean` and `Novel/D15JumpProfileSearchProof.lean`: (4)–(6) in return coordinates.

  There is no `sorry`, and the axiom audit is clean.
- **Inputs.** These are claim 060's, used through formalizer's `score_gen`, which proves claim 060's part-1 and part-2 score conclusions for any envelope that is measurable, finite, dominates every jump law in Θ_J, and takes D_G's values off the positive stratum.
  - AX-55 and AX-56 supply claim 054's kernels.
  - AX-58 is proved.
  - AX-53 is used only for FDR, through claim 060's panel.
  - AX-59 is not needed: the mixture (3) is integrated directly.
- **Part 1.**
  - (2): g_J ≤ V_J ≤ U_J for every θ ∈ Θ_J. Per increment, claim 060's `hJ_le` is taken with its scale set to σ_J, and the cap replaces λ_J.
  - V_J ≤ U_J follows from claim 060's count expansion `prod_le`.
  - V_J is finite, takes D_G's zero/trapped values off the positive stratum, and is measurable. For measurability, the supremum equals the supremum over rational a and rational s − σ_min, by continuity.
  - The orderings (3): E^J ≤ E^prof ≤ E^drift ≤ E. The score is weakly lower for a higher cap or a lower floor. It equals claim 055's score at cap 0 and claim 060's at cap ∞. The nonzero example and the absorbed-score identity hold.
  - E^prof has every claim-060 conclusion (`Valid`).
- **Part 2.**
  - (4)–(5): L > 0 and σ_min ≤ s₀ ≤ s₊. The supremum over a ∈ ℝ, s ≥ σ_min is attained in [a₋, a₊] × [σ_min, s₊] (`IsCompact.exists_isMaxOn`).
  - In price coordinates, a finite cap's V_J is J_y times that maximum.
- **Part 3.**
  - (6) bounds F_J on its box. It is monotone under subdivision and equals F_J on degenerate boxes.
  - A finite cover gives sup F_J ≤ B_P, and refinement does not raise B_P.
  - Convergence: for each ε there is a mesh η such that boxes inside the rectangle with sides ≤ η and one evaluated point each have B_P ≤ max F_J(p_i) + ε. This uses `IsCompact.uniformContinuousOn_of_continuous` on the box endpoints.
  - (7)–(8): for every measurable cover rule (a measurable box count and measurable boxes covering the rectangle on positive paths), V_J ≤ V_J^P ≤ U_J. V_J^P is finite and measurable, E^P has every claim-060 conclusion, and E^J ≤ E^P ≤ E^prof. Refinement raises E^P.
- **Not formalized.** The claim's checks and numerical scripts, which are diagnostics. There is no outward-rounding certificate, matching the claim's "Not shown".
