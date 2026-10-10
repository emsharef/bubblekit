---
id: "027"
title: "D14: conditional Gaussian volatility-path budgets for enlarged-null scores"
status: formalized
depends_on: ["023", "053", "055", "057"]
axioms_used: [AX-53, AX-55, AX-56, AX-58]
formal: lean/Standalone/D14VolPaths.lean
direction: D14
---
## Statement

**Conditional on the observation-law and envelope premises below.** The
mechanism is claim 023's one-step Gaussian affinity and bounded-function
comparison, followed by integration over a latent law. The reference
moment comes from the existing dominated split likelihood (AX-58), not
a new inference theorem. This is a finite-grid observation model; it
does not assert a conditional Gaussian law for a general stochastic-
volatility SDE or reconstruct stochastic calculus.

Fix claim 055's design, including its training-only selected normalized
CEV evaluation density and retained finite CEV nulls. For each name choose
once and for all either its score E_i^drift or claim 057's score E_i^(B,C)
with a fixed pre-data rectangle. Denote that chosen score by E_i. It is
finite and nonnegative on every nonnegative array. Neither the selected
numerator nor the chosen null family is allowed to depend on the latent
variable introduced below. The panel law P is arbitrary on these arrays;
N₀ is a supplied fixed set of actual pricing-null names. Pricing labels
are not inferred from an observation-law fit.

For each i∈N₀, supply a standard Borel latent space and a probability
kernel ν_i(u,dz), defined under the actual training law, such that

    Law_P(V_i | U_i=u) = ∫ H_(i,u,z) ν_i(u,dz)             (1)

almost surely in u. For a positive last training price, H_(i,u,z) is
the price law obtained from independent log returns

    R_j ~ Normal((b_ij(u,z)−σ_ij(u,z)²/2)Δ_j,
                  σ_ij(u,z)²Δ_j),   j=1,…,n_e.           (2)

Here Δ_j>0 are the fixed evaluation steps, τ_e=ΣΔ_j, all b_ij are
finite real measurable functions and all σ_ij are finite, strictly
positive measurable functions. At a zero endpoint require the trapped
all-zero evaluation law. The fields define measurable probability
kernels. The latent variable and its law may depend on training; (1)
uses that actual conditional law, not a fitted mixing distribution.

Supply measurable reference parameters b_ref,i(u,z), κ_i(u,z)>0 that
belong to the chosen score's Gaussian null family. For claim 055 these
may be any finite drift and positive scale. For claim 057 they must lie
in its fixed rectangle (a retained p=1 null with drift zero is also
allowed). They are comparison witnesses; they do not alter E_i.

1. **Component budget.** At a positive endpoint define

       A_(i,u,z) = ∏_j sqrt(2σ_ij κ_i/(σ_ij²+κ_i²))
          · exp(−Σ_j Δ_j [b_ij−b_ref,i+(κ_i²−σ_ij²)/2]²
                              / [4(σ_ij²+κ_i²)]),
       ε_(i,u,z) = sqrt(1−A_(i,u,z)²).                   (3)

   The Gaussian reference has drift b_ref,i and scale κ_i constant
   across evaluation increments. Its distance from H_(i,u,z) is at
   most ε_(i,u,z) in total variation. At a zero endpoint put ε=0.
   The functions are measurable and take values in [0,1]. Set

       εbar_i(u) = ∫ ε_(i,u,z) ν_i(u,dz).                (4)

   A supplied measurable upper bound in [0,1] for (4) may replace it
   in all conclusions. The realized latent component's budget alone
   cannot be substituted when that component is unobserved.

2. **Size and moments after averaging.** For fixed 0<α_i<1,

       P(E_i>1/α_i | U_i) ≤ min(1,α_i+εbar_i(U_i)),
       P(E_i>1/α_i) ≤ min(1,α_i+E εbar_i(U_i)).          (5)

   A fixed bound εbar_i≤e_i<α_i permits the strict threshold
   1/(α_i−e_i), with size ≤α_i. For fixed finite c_i>0,

       min(E_i,c_i)/(1+c_i εbar_i(U_i))                  (6)

   has conditional and unconditional null mean at most one. Supply
   a measurable budget in [0,1] for every name, with the model premises
   and (4) required only at actual nulls. Then base e-BH and any measurable zero mask with
   the original m have FDR≤q_FDR|N₀|/m, conditional on AX-53. Certified
   measurable finite lower scores may replace E_i. Arbitrary score
   deletion or trimming of a completed discovery list is not justified.

   If, for each component, all b_ij equal its admitted reference drift
   and all σ_ij equal its admitted reference scale, every ε is zero.
   In that case the **raw** E_i itself has null mean at most one.
   Thus conditional mixtures of admitted constant-parameter Gaussian
   laws require no TV penalty, even though the mixture need not itself
   be Gaussian. This does not cover arbitrary within-window variation.

3. **A supplied uniform variability envelope.** Suppose at each actual
   null, almost surely under its actual (u,z) law, all σ_ij and κ_i lie
   in supplied [s_min,s_max], 0<s_min≤s_max<∞, and

       |log(σ_ij/κ_i)|≤h_vol,
       |b_ij−b_ref,i|≤B_phys,

   for fixed finite h_vol,B_phys≥0. Then (4) is at most

       sqrt(1−exp(−L_grid)),
       L_grid = n_e log(cosh h_vol)
            + τ_e [B_phys/(2s_min)+s_max sinh(h_vol)/2]². (7)

   This is the earlier D14 grid-planning bound applied per increment,
   now to within-component variability rather than a scale grid error.
   It does not require estimation of ν_i once its bounds are supplied.
   For fixed positive h_vol, this sufficient upper budget tends to one
   as n_e grows at fixed τ_e. That fact alone is not a lower bound on
   true TV or a failure-of-size assertion: h_vol may be loose.

## Proof

**Reference moment.** At each (u,z), the chosen score's denominator
dominates the admitted reference density. Multiplication of the ratio
by that density is bounded by the selected normalized numerator;
infinite denominators in claim 055 contribute zero. The pointwise
AX-58 application in claims 055/057 gives ∫E_i(u,v) dG_(i,u,z)≤1.
It holds for every training vector, regardless of which components
or training values occur under P. Varying the comparison witness
does not refit the numerator or change the score.

**Affinity.** For each increment apply claim 023's Gaussian integral
with actual scale σ_ij, reference scale κ_i and physical drift
difference b_ij−b_ref,i, after translating both returns by the reference
drift times Δ_j. Product integration of the independent coordinates
gives (3). The log-return-to-price map is a measurable bijection from
the positive orthant at a fixed positive starting price; it preserves
TV. Claim 023's affinity comparison supplies ε. At the trapped endpoint
the actual and reference laws agree. Measurability follows from the
finite formula and integration against a probability kernel.

**Averaging.** Reference Markov and the component TV bound give
H_(i,u,z){E_i>1/α_i}≤α_i+ε_(i,u,z). For the capped function the
existing bounded-function comparison gives

    ∫ min(E_i,c_i) dH_(i,u,z) ≤ 1+c_i ε_(i,u,z).

Integrate these inequalities against ν_i(u,dz), using (1) and Tonelli.
This yields (5) and (6); integrate again under the actual training law.
The shifted threshold uses α_i−e_i in the same event bound. Finite,
measurable nonnegative scores and null moments check AX-53's hypotheses.
Pointwise masks and lower scores preserve them. If every component
equals its admitted reference, integrate the raw reference moment
directly in (1), without passing to a cap limit.

**Uniform envelope.** The per-increment contribution to −log(A²) is

    log(cosh(log(σ_ij/κ_i)))
      + Δ_j [b_ij−b_ref,i+(κ_i²−σ_ij²)/2]²
                                      / [2(σ_ij²+κ_i²)].

The covariance term is at most log(cosh h_vol). For the other term,
divide the absolute numerator by sqrt(2(σ_ij²+κ_i²)). Its drift part
is at most B_phys/(2s_min). Its variance part is at most
s_max sinh(h_vol)/2, since
|κ_i²−σ_ij²|=2σ_ij κ_i|sinh(log(σ_ij/κ_i))| and
σ_ij κ_i/sqrt(2(σ_ij²+κ_i²))≤s_max/2. Sum over increments and use
ΣΔ_j=τ_e. Monotonicity of sqrt(1−exp(−x)) gives (7), and averaging
does not increase this common bound. Only scalar algebra is new to
this application; the Gaussian integral and integration rules are reused.

## Checks

`checks/027/check.py` compares 64 variable-parameter affinity products
with the existing one-step formula and the uniform envelope. Nine
constant components give zero budget with admitted references. Exact
finite mixtures check averaging with training-dependent latent weights,
reference moments, raw size and capped moments. These are deterministic
diagnostics, not diffusion simulations or a numerical certificate.
`checks/027/budget.py` supplies the component and finite-mixture arithmetic.

## Not shown

- No conditional Gaussian representation for an arbitrary volatility
  process. Conditioning on volatility generated from the driving noise
  need not leave independent Gaussian returns. Correlated-volatility
  models and leverage effects are not covered merely by bounded scales.
- No estimation of the latent law, its parameters or (4). An observed
  volatility path, point estimate or average scale is not a substitute
  for the stated actual conditional-law mixture and its budget.
- No jump, rounding or measurement-noise extension; no continuous-time
  process or physical-to-pricing measure construction. Null labels are
  still separate premises. General CEV drift/scale mixtures outside
  the declared Gaussian component family are not asserted here.
- No useful power, repeated-window validity, new confidence bands or
  error certificate for a numerical likelihood or latent integral.
- Parts 1–3 are formalized in `lean/Standalone/D14VolPaths.lean`,
  proved by `lean/Novel/D14VolPathsProof.lean` (`statement_holds`),
  including the price-space applications to claims 055 and 057, the
  Gaussian affinity and the log-return-to-price step. The claim-057
  instance encodes references in its rectangle; the optional retained
  p=1 drift-zero reference outside that rectangle is not encoded.
  The CEV reference-score inputs remain conditional on AX-55/56
  (vacuous instances), and FDR remains conditional on AX-53, whose
  available instance is degenerate. AX-58 is proved from Mathlib.

## Prior art

[wasserman2019universal], Theorem 3 and Section 6 (AX-58), supplies the
dominated conditional likelihood principle; [wang2020false] supplies
AX-53. Integration of inequalities over mixtures is existing Tonelli
and linearity, not a new robustness theorem. The one-step affinity
and bounded comparison are already proved in claim 023 and its Lean
Gaussian files. The D14 grid-budget calculation, claims 026/055/057,
the existing findings and the refuted post-filter target were checked.
The new application specifies which latent observation laws can be
handled and which budget must be averaged before using the price score.
It imports no stochastic-volatility representation theorem and makes
no projection-coverage assertion of the kind cautioned against in
[park2023robust].

## Review

Reviewer, 2026-10-06, on branch `math/d14-volatility-path-budget` at `198b819`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/027/`.
- **Inputs.** AX-53, AX-55, AX-56 and AX-58 are audited, and AX-58 is proved. Claims 023, 053, 055 and 057, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/027/reproduce.py`, with its rerun command and seed (`default_rng(27)`) in its header. It is not a CI `check.py`.

**Part 1: correct.**
- **The affinity (3).** Each increment's Bhattacharyya coefficient between N((b − σ²/2)Δ, σ²Δ) and N((b_ref − κ²/2)Δ, κ²Δ) is √(2σκ/(σ² + κ²))·exp(−Δ[b − b_ref + (κ² − σ²)/2]²/(4(σ² + κ²))). Independent products give (3), and claim 023's sandwich gives TV ≤ ε.
- **The bijection.** The price/log-return bijection preserves TV.

**Part 2: correct.**
- **The bounds (5)–(6).** Both are linear in ε: H_z(event) ≤ α + ε_z, and ∫min(E, c) dH_z ≤ 1 + cε_z. So integrating against ν(u, dz) gives the averaged budget, and the training-measurable normalization in (6) gives the null moment.
- **The zero-budget case.** When every component equals an admitted constant reference, each component's raw conditional mean is ≤ 1 by claims 055/057, so the mixture's is too, with no penalty. This is correct, and a useful positive result.
- **FDR.** AX-53 and masking are as before.

**Part 3: correct.** Per increment, −log(BC_j²) = log cosh(log(σ/κ)) + Δ[·]²/(2(σ² + κ²)), and the first term is at most log cosh h.
- **The variance part.** |κ² − σ²| = 2σκ|sinh(log(σ/κ))|, and σκ/√(2(σ² + κ²)) ≤ √(σ² + κ²)/(2√2) ≤ s_max/2.
- **The drift part.** √(2(σ² + κ²)) ≥ 2s_min.
- **The sum.** Summing with ΣΔ_j = τ_e gives (7).

**Checks** (evidence, not proof).
- **(a) TV against (3).** For 12 variable-parameter Gaussian return vectors (n_e ∈ {5, 20, 60}, log-scale deviations up to 0.15, drift deviations up to 0.1), the Monte Carlo TV from the likelihood-ratio sign with 2×10⁵ draws never exceeded ε from (3). (3) never exceeded the uniform envelope (7).
- **(b) Price Monte Carlo of claim 055's E^drift.** Daily prices for two years, training on year one, the absorbed CEV catalogue p ∈ {½, 1, 3/2} × κ ∈ {0.2, 0.3, 0.45}, 10,000 paths per case, α = 0.1.

  | Truth | Raw mean | False alarm | Best constant-reference ε (3) |
  |---|---|---|---|
  | Latent 50/50 mixture of GBM σ = 0.25 and 0.40 | 0.14 | 0.0003 | 0 (part 2's zero-budget case) |
  | σ switches 0.25 → 0.40 halfway through evaluation | **13** | 0.028 | 1.000 |
  | Smooth σ = 0.30 ± 0.05 sin(2πt) | 1.0 | 0.0037 | 0.911 |
  | Heston-type SV with leverage −0.7 (outside (1)–(2)) | 0.28 | 0.0000 | not defined |

- **The author's check.** I ran `checks/027/check.py` afterwards. It passes 64 variable-parameter affinities, the uniform envelope, 9 constant components and the exact conditional-mixture moments and size.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The useful positive content is part 2's zero-budget case.** Random but constant-per-window volatility, a latent mixture of admitted GBMs, keeps claim 055's raw score valid with no penalty. My first row confirms it.
2. **Within-window variation makes the budget near-vacuous at daily sampling.** The budget concentrates on the full product, and a mild seasonal ±0.05 path already gives ε = 0.91. A real within-window change breaks the raw e-moment: the regime switch gives a mean of 13. So D14 still has no informative guarantee for genuine within-window volatility variation.
3. **Leverage and correlated SV are outside the representation (2).** The Heston row is a measurement, not a guarantee, and the claim correctly says so.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the per-increment affinity and TV bound, the latent-averaged size/clipping budgets incl. the zero-budget constant-component case, and the uniform envelope; committed review script; scope honest


Apply existing Gaussian-affinity product integration and conditional
kernel integration. Do not build an SDE or re-prove the general mixture
principle. A nonzero finite-grid instance is a two-point latent variable
with positive weights, positive scales (different across the components)
and independent nondegenerate Gaussian increments conditional on it.
For (6), normalize using the conditional latent average or a supplied
upper bound, not the unobserved component's value. The reference may
vary with (u,z) but the score and its numerator may not vary with z.

Formalizer B, 2026-10-06, on `formb/d14-conditional-volatility-paths` (promoted from `provisional/formb-d14-conditional-volatility-paths`). **Status: formalized.**
- **Files.** The statement is in `lean/Standalone/D14VolPaths.lean` (`statement := component ∧ averaging ∧ cev`). The proof is `lean/Novel/D14VolPathsProof.lean` (`statement_holds`), which combines:
  - `D14VolPathsComponentProof.lean` (`component_holds`);
  - `D14VolPathsAvgProof.lean` (`averaging_holds`);
  - `D14VolPathsCevProof.lean` (`cev_holds`);
  - the helpers `D14VolPathsPrice.lean` and `PriceChainJ.lean`.

  There is no `sorry`, and the axiom audit is clean.
- **Inputs.**
  - FDR is conditional on AX-53 (claim 053's `AX53`).
  - AX-55 and AX-56 (claims 052 and 054's restatements, on a base carrying a Brownian motion) supply claim 054's kernels, as in claims 054, 055 and 057.
  - AX-58 is proved from Mathlib and enters through its pointwise step g·E ≤ Ĝ.
  - The Gaussian affinity is proved, by claim 023's one-step integral and product integration.
  - The log-normal price substitution y = x eʳ is proved (`lintegral_image_eq_lintegral_abs_deriv_mul`).
- **Part 1 (`component`).**
  - **Log returns.** For log returns (2) with increment-varying drifts and scales, against a constant reference (b_ref, κ):
    - the affinity is exactly (3), with 0 ≤ A ≤ 1, and ε = √(1 − A²) ∈ [0, 1];
    - every event satisfies |H − G| ≤ ε, also after any measurable map to prices;
    - ε is measurable in the parameters;
    - ε = 0 for a component equal to its reference.
  - **Prices.** On prices, (2) is `gV`, claim 055's (1) with increment-varying parameters, against μ_CEV^m.
    - It is the chain of drifted log-normal steps (`gV_chain`).
    - Each step's affinity with the reference is claim 023's Gaussian coefficient, independent of the current price.
    - So the price-space affinity is (3) (`price_aff`, via the chain integration `chainJ_lint`), and TV on prices is at most ε (`price_tv`).
    - From a zero endpoint the two laws coincide.
- **Part 2 (`averaging`, then `cev`).**
  - **The abstract setting (`averaging`).**
    - A latent Markov kernel ν(u, dz).
    - Component laws within ε(u, z) of references against which the score has moment ≤ 1.
    - The actual conditional law equals the ν-mixture (1) of the components, P∘U⁻¹-a.e.
  - **Conclusions there.**
    - (5) conditionally and unconditionally, with ε̄(u) = ∫ ε(u, z) ν(u, dz) (4).
    - The shifted threshold 1/(α − e) for ε̄ ≤ e < α.
    - (6) with any measurable budget ≥ ε̄, conditionally and unconditionally.
    - The raw conditional and unconditional moment when every ε is zero.
    - On the panel: the union bound, and base and masked e-BH with the original m under AX-53.
  - **The instance (`cev`).**
    - The choices are claim 055's E^drift, or claim 057's E^(B,C) with references in its rectangle.
    - The components are (2) on prices, with measurable b(u, z) and σ(u, z) > 0.
    - The references are claim 055's Gaussian densities with measurable b_ref(u, z) and κ(u, z) > 0.
    - ε is (3) at a positive endpoint and 0 at a zero endpoint.

    The reference moment holds at every training value: the score's denominator dominates the reference, either through claim 055's D or through claim 057's rectangle supremum.
- **Part 3.** It is the uniform envelope (7). The identities 2σκ/(σ²+κ²) = 1/cosh(log(σ/κ)) and (σ²−κ²)/2 = σκ sinh(log(σ/κ)) reduce it to scalar inequalities, using √(2(σ²+κ²)) ∈ [2s_min, 2s_max].
- **Encodings and omissions.**
  - **Supplied upper bound.** The claim lets a supplied measurable upper bound replace (4). This is covered in (6), where any measurable budget ≥ ε̄ may be used, and in the shifted threshold, where the bound is a constant e.
  - **Lower scores.** The claim's lower implemented scores and masks are covered by the panel e-BH conjunct, applied to any finite measurable nonnegative scores with null moments ≤ 1.
  - **Optional p = 1 reference.** The optional retained p = 1 drift-zero CEV reference for claim 057 is not encoded; the rectangle references are.
- **Stale prose.** The last "Not shown" bullet ("No Lean proof of this application yet") is routed to math (`board/inbox/math/2026-10-06-claim027-stale-prose.md`).
