---
id: "032"
title: "D14: Gaussian model-mismatch budgets for rounded monetary-cell scores"
status: formalized
depends_on: ["023", "027", "031", "053"]
axioms_used: [AX-53, AX-58]
formal: lean/Standalone/D14RoundedModel.lean
direction: D14
---
## Statement

**Conditional on the actual conditional-law mixture and supplied budget
below.** The mechanism is claim 027's component comparison and averaging,
applied to claim 031's rounded-label score. Both laws use the same latent
starting price and observation map. Only the reference-moment hypothesis
and the observation transformation need checking; there is no new general
robustness theorem or Gaussian integral.

Keep claim 031's fixed monetary tick δ_tick, positive deterministic gaps
Δ_j, finite nonempty Gaussian catalogue Γ_i, normalized training-selected
label forecast q_i^δ, and fixed original panel m with supplied pricing-null
set N₀. Use E_i=E_i^δ,L_i, allowing the finite measurable level L_i(u,v)
of claim 031. The numerator and catalogue stay fixed during evaluation.
The conclusions also hold for any measurable score between zero and E_i.

For each actual null i supply a standard Borel latent space and the
**actual** conditional probability kernel ν_i(u,d(x,z)), with x in the
last observed monetary cell C_(z₀)^δ almost surely. Here z is a latent
variable, not a quote label. Given rounded training u, the evaluation law
is the ν_i-mixture of the following component laws H_(i,u,x,z):

- At x>0, generate independent returns with parameters b_ij(u,x,z) finite
  and σ_ij(u,x,z)>0 finite, all measurable:

      R_j ~ Normal((b_ij−σ_ij²/2)Δ_j, σ_ij²Δ_j).

  Start at exact price x and round the cumulative price path by Q_δ.
- At x=0, every future exact price and label is zero.

This contract permits training-dependent latent mixtures and a trapped
endpoint atom. It does not assert that conditioning on an arbitrary
stochastic-volatility path gives independent Gaussian returns.

For each θ=(b_θ,κ_θ)∈Γ_i and positive endpoint use claim 027's affinity:

    A_θ = ∏_j sqrt(2σ_ij κ_θ/(σ_ij²+κ_θ²))
        · exp(−Σ_j Δ_j [b_ij−b_θ+(κ_θ²−σ_ij²)/2]²
                                    /[4(σ_ij²+κ_θ²)]),
    ε_i(u,x,z) = min_(θ∈Γ_i) sqrt(1−A_θ²).                (1)

At x=0 set ε_i=0. Define

    εbar_i(u)=∫ ε_i(u,x,z) ν_i(u,d(x,z)).                  (2)

Supply a measurable e_i(u)∈[0,1] with εbar_i(u)≤e_i(u) at almost every
actual-null training record. Give e_i for every panel name, requiring its
validity only on N₀. The latent parameters, conditional weights and budget
are premises; a fitted scale, realized latent component or declaration
failure probability is not a replacement for (2).

1. **Rounded-law comparison.** There is a measurable reference mixture
   G_i(u,·), using the same ν_i and x but replacing each positive
   component by a constant-parameter Gaussian in Γ_i, such that

       TV(H_i(u,·),G_i(u,·)) ≤ εbar_i(u),
       ∫ E_i(u,v) G_i(u,dv) ≤ 1.                         (3)

   G_i need not itself have one fixed Gaussian parameter. Comparison
   parameters may vary with the latent component; this changes neither
   the scoring catalogue nor the forecast. Rounding contributes no
   additional error term in (3). No continuous density is evaluated at
   a rounded quote, and no latent price is replaced by a representative
   in the null denominator.

2. **Robust size and panel scores.** For fixed 0<α_i<1,

       P(E_i>1/α_i | U_i) ≤ min(1,α_i+e_i(U_i)),
       P(E_i>1/α_i) ≤ min(1,α_i+E e_i(U_i)).              (4)

   A supplied constant e_i≤e_*<α_i permits the strict threshold
   1/(α_i−e_*), with size ≤α_i. For a fixed finite cap c_i>0,

       E_i^δ,rob = min(E_i,c_i)/(1+c_i e_i(U_i))          (5)

   has conditional and unconditional null mean ≤1. AX-53 then gives
   FDR≤q_FDR|N₀|/m under arbitrary dependence, with original-m zero masks
   and any nonnegative measurable lower implemented scores. In
   particular a lower numerator/upper denominator implementation of
   claim 031 may be clipped using a certified upper budget. A numerical
   approximation to (2) without a one-sided bound is insufficient.

   The ceiling is c_i/(1+c_i e_i). Strict per-name rejection is impossible
   when e_i≥α_i; otherwise it requires c_i>1/(α_i−e_i). Refining cells
   cannot remove this ceiling for a fixed supplied budget. This is a
   limit of (5), not of every test or of the true rounded-law TV.

3. **Zero-cost mixtures and a uniform envelope.** If almost every
   positive component has b_ij=b_θ and σ_ij=κ_θ for all j for some
   θ∈Γ_i (possibly different components use different θ), then (2)=0
   and the raw E_i itself has null mean ≤1. Trapped components contribute
   zero to (2), even when the current quote is also compatible with
   positive exact prices.

   More generally claim 027's uniform bound applies unchanged if for
   each positive component some θ∈Γ_i satisfies, at every increment,

       σ_ij,κ_θ ∈ [s_min,s_max],
       |log(σ_ij/κ_θ)|≤h_vol,  |b_ij−b_θ|≤B_phys.

   Then a sufficient constant budget is

       e_* = sqrt(1−exp(−L_grid)),
       L_grid = n_e log(cosh h_vol)
          + τ_e [B_phys/(2s_min)+s_max sinh(h_vol)/2]².   (6)

   The positive constants/radii are supplied as in claim 027. Neither
   δ_tick nor a cell refinement level occurs in this sufficient bound.
   It can be loose: coarsening may reduce the actual TV substantially.

## Proof

**Reference moment.** Fix a training record u, a latent endpoint x in its
last cell and a reference θ∈Γ_i. Claim 031's pointwise envelope dominates
the mass of every rounded evaluation vector from that exact x, including
x=0. The domination holds at every level and hence at L_i(u,v).
Multiplying q_i^δ/D_i^δ,L by that mass and summing over the countable
label space gives at most Σ_v q_i^δ(v|u)=1 (AX-58's already-proved step).
Thus the moment holds separately at every (x,θ), not only under a fitted
or parameter-specific posterior of x. It remains true after integrating
against any actual ν_i and selecting a reference per component.

**Component comparison.** At x>0 the two return laws have claim 027's
Gaussian affinity A_θ. Their TV is at most sqrt(1−A_θ²). The map from
returns to monetary labels starts both paths at the same x and uses the
same Q_δ. Apply the existing eventwise TV bound to the preimage of each
label event under this measurable map; the rounded-law distance cannot
increase. At x=0 both label laws are the same point mass, so their
distance is zero. This step never compares a discrete law with a
continuous one and never restarts a null at a quoted representative.

Choose the first minimizing θ in a fixed enumeration of the finite Γ_i.
The Gaussian formula is measurable, so this selection is measurable.
Integrate those reference kernels with respect to the same ν_i used by
the actual law. Claim 027's componentwise averaging gives the first
inequality in (3); the reference-moment argument gives the second.
This checks both hypotheses of the existing bounded-function comparison.

**Consequences.** Reference Markov bounds the threshold event by α_i.
The eventwise comparison and (2) give (4). Applying the bounded-function
comparison of claims 023/027 to min(E_i,c_i) gives actual conditional mean
at most 1+c_i εbar_i, hence at most 1+c_i e_i. Division proves (5).
Integration under the actual training law gives the unconditional
moment, and AX-53 applies exactly as in claim 053. Lower scores and zero
masks preserve the moment. The threshold shift and ceiling condition
are claim 023's scalar consequences with this budget.

When every positive component is admitted, use its raw reference moment
and integrate; no cap limit is needed. The trapped component already
satisfies that moment. Finally apply claim 027's uniform Gaussian bound
to each supplied reference witness. Taking the minimum in (1) cannot
increase it, and averaging, with zero at trapping, proves (6).

## Checks

`checks/032/check.py` checks Gaussian affinity budgets after mapping to
coarse monetary-label events by independent two-step integration, their
actual latent mixtures with a trapped atom, and an exact finite-space
fixture for size, clipping, zero budgets and the danger of replacing
(2) by its smallest component. `checks/032/budget.py` reuses claim 027's
component formula for supplied finite mixtures. These are deterministic
checks, not simulations, certified budgets or estimates of an actual law.

## Not shown

- No inference of ν_i, actual parameters, e_i, or pricing labels from
  rounded data. The observation map and conditional-law contract must
  hold under the actual training law. Claim 058's declaration-failure
  correction is different and is not a conditional TV budget.
- No general stochastic-volatility, leverage, jump, CEV/default or
  observation-noise model. Zero endpoints are trapped, not new defaults
  from a positive Gaussian component. Only reference mixtures from the
  fixed finite Gaussian catalogue are used.
- No additional cell-rounding budget is needed, but (1)/(6) need not be
  sharp or useful. No power, convergence rate, continuous null coverage
  or real-feed guarantee follows. High-frequency scale mismatch may
  still make the clipped rule incapable of rejection.
- Parts 1–3 and the panel guarantees are formalized in
  `lean/Standalone/D14RoundedModel.lean`, with `statement_holds` in
  `lean/Novel/D14RoundedModelProof.lean`. The proof connects claim 027's
  component and averaging lemmas to claim 031's exact-start envelope
  through the common rounding map. AX-58's step is proved; FDR remains
  conditional on AX-53's degenerate instance. No CEV-kernel AX-55/56
  assumption is used. The ceiling and refinement remarks, the
  stochastic-volatility caveat and the numerical-approximation warning
  remain commentary, not formalized conclusions.

## Prior art

Read claims 023, 027 and 031, the D14 findings, the refuted disjoint-window
coverage assertion, and `D14VolPathsComponentProof`/`D14VolPathsAvgProof`
and `D14FixedTickValid`. The general inference mechanism is already
[wasserman2019universal], Section 6 (AX-58), and [wang2020false] (AX-53).
The Gaussian calculation and latent-mixture robustness are already
claim 027. This application checks that the reference score has its
moment at every exact endpoint and that both comparison laws use the
same rounding map, thereby connecting model-mismatch budgets to the
monetary-cell score. It does not re-prove the general comparison tools.

## Review

Reviewer, 2026-10-06, on branch `math/d14-rounded-model-budget` at `99c81f4`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/032/`.
- **Inputs.** AX-53 and AX-58 are audited, and AX-58 is proved. Claims 023, 027, 031 and 053, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/032/reproduce.py`, with its rerun command and seed (`default_rng(32)`) in its header. It runs single-process under the CPU budget and reuses my independent claim-031 implementation. It is not a CI `check.py`.

**Part 1: correct.**
- **The reference moment holds at every exact endpoint.** Claim 031's envelope dominates the rounded label mass from every exact start in the cell, x = 0 included, at every level. So Σ_v (q/D) P_θ(v | x) ≤ Σ q = 1 holds for each x and θ, not only on average over a posterior.
- **The comparison.** Both laws start at the same latent x and pass through the same Q_δ. So the eventwise TV bound applies to label events by taking preimages, and rounding cannot add distance.
- **The reference mixture.** A measurable first-minimizing θ per component, integrated against the same ν, gives the reference mixture G. Claim 027's averaging then gives (3).

**Part 2: correct.** Claims 023/027's event and bounded-function comparisons give (4) and (5). AX-53, lower scores and masks follow, and the cap condition is claim 023's.

**Part 3: correct.**
- **The zero-cost case.** Admitted components have a raw moment ≤ 1 by Part 1, and trapped components are point masses.
- **The uniform envelope (6)** is claim 027's, applied component by component.

**Checks** (evidence, not proof).
- **(a) Data processing.**
  - **The setup.** One-step exact TV of rounded cent labels between actual N(·, σ²Δ) and reference N(·, κ²Δ) from the same exact start (x ∈ {0.004, 0.012, 0.05, 1.003}; σ/κ ∈ {0.4/0.3, 0.25/0.3, 0.6/0.3, 0.31/0.30}; daily, weekly and 5-minute steps).
  - **Result.** It never exceeded the Gaussian budget √(1 − A²); the largest difference was −0.015.
- **(b) The per-endpoint reference moment.** With n = 2 and levels 0–3, from 10 exact starts, including 0, 10⁻⁵ and the edges of a zero quote, plus starts in cells 2 and 100, the label sum Σ_v q/D·P_θ(v | x) was ≤ 1 in all 40 cases.
- **(c) Size.**
  - **The setup.** Cent ticks from $1, daily, n = 15, Γ = {(0, 0.30)}, the forecast prototype with κ = 0.20, level 2, 300 paths and α = 0.1.
  - **In catalogue (σ = 0.30):** e = 0, P(E > 10) = 0.013 and raw mean 0.51.
  - **Off-grid (σ = 0.40):** budget (1) gives e = 0.68. P(E > 10) = 0 ≤ 0.78, and the clipped mean is 0.001.
- **The author's check.** I ran `checks/032/check.py` afterwards. It passes the latent endpoint/component cases, the two-step laws, mixture TV, the uniform envelopes, exact size and clipped moments, zero budgets, the unsafe-minimum fixture and cap equality.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **This correctly composes claim 027's model-mismatch budget with claim 031's rounded score, at no extra rounding cost.** The key check, a moment at every exact endpoint, is what makes the same-ν reference mixture legitimate.
2. **The budget is as weak as claim 027's.** In my run, a 0.30 → 0.40 volatility mismatch over only 15 daily steps already gives e = 0.68 > α, so the clipped rule cannot reject at all. Coarse rounding may shrink the true TV, but the sufficient budget (1)/(6) does not exploit that.
3. **Within-window variation, SV, jumps and CEV/default** remain uncovered, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the per-endpoint reference moment, data processing through the common rounding map, the same-nu reference mixture and claim 023/027 comparisons; committed review script; weak-budget scope stated

Formalizer, 2026-10-07, on `form/d14-rounded-model-robustness`. **Status: formalized.** The statement is `lean/Standalone/D14RoundedModel.lean`, with
`statement := comparison ∧ envelope ∧ panel`.
It is proved in `lean/Novel/D14RoundedModelProof.lean` (`statement_holds`), from `D14RoundedModelKernel`, `…Comp` and `…Main`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** FDR is conditional on AX-53 through claim 026's `panel`. Everything else is proved:
  - claim 027's component bound (`component_holds`), its measurability and envelope, and its latent-mixture averaging (`averaging_holds`);
  - claim 031's exact-start envelope (`walk_le_Bl`);
  - AX-58's step, as the finite sum Σ_v (q/D)·P_θ(v | x) ≤ Σ_v q = 1.
  No CEV kernel (AX-55/56) is used.
- **Encoding.** One name, with claim 031's tick δ > 0 and labels in ℕ.
  - Training records are u : Fin (k+1) → ℕ. The latent kernel ν(u, ·) lives on (x, z) ∈ ℝ × 𝒵, for any measurable 𝒵; the claim asks for standard Borel, which is not needed.
  - The component law is claim 031's `walkM` from the exact price x, with step means (b_j − σ_j²/2)Δ_j and standard deviations σ_j√Δ_j. At x = 0 it is the point mass at the zero path.
  - The premises are: x lies in the last cell almost surely; Law(V | U = u) is the ν(u, ·)-mixture of the component laws for a.e. u; and ε̄ ≤ e for a.e. u, with e taking values in [0, 1].
  - The score is claim 031's E = q/D^(δ,L) as a [0, ∞] value, with any level L(u, v).
  - TV is sup_A |H(A) − G(A)|, without the factor two, as in claims 023 and 027.
- **Part 1, (3).** A measurable θs(u, x, z) ∈ Γ, the first minimizer of (1) in a fixed enumeration of Γ, gives G(u) = ∫ walkM_θs(x) dν(u). For a.e. u, |H(u)(A) − G(u)(A)| ≤ ε̄(u) for every A, and ∫ E dG(u) ≤ 1.
  - The walk laws are claim 028's measurable kernel `Lk` over a standard Gaussian vector.
  - At x > 0 both laws are claim 027's `lawV`/`lawR`, pushed through the same label map. At x = 0 both are the same point mass.
  - Averaging needs its two hypotheses at every latent point. So off the last cell, which is ν-null, the reference starts at the cell's left end and the budget there is 1.
- **Part 2.**
  - (4) holds conditionally (≤ α + e(u)) and unconditionally (≤ min(1, α + E e(U))).
  - The threshold 1/(α − e*) has size ≤ α when e ≤ e* < α.
  - (5) has conditional and unconditional mean ≤ 1, and every measurable score between 0 and (5) has unconditional mean ≤ 1.
  - A rejection by (5) at 1/α forces e < α and c > 1/(α − e).
  - The claim's "any measurable score between zero and E" is stated for (4), the threshold and part 3's moments.
  - (4) is stated for every α > 0, not only α < 1.
- **Part 3.**
  - If a.e. positive component equals some θ ∈ Γ exactly, then ε̄ = 0 a.e. and the raw E (or any lower score) has conditional and unconditional mean ≤ 1.
  - (6): if a.e. positive component has some θ ∈ Γ within the radii, then ε̄ ≤ √(1 − exp(−L_grid)) a.e., with n_e = n and τ_e = Σ_j Δ_j.
  - `envelope` records the one-component form, epsC ≤ e*.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53, with arbitrary dependence, lower scores and measurable zero masks at the original m.
- **Not formalized.** Commentary only: the ceiling and refinement remarks, the stochastic-volatility caveat and the numerical-approximation warning.
