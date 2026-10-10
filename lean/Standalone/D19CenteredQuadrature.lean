import Standalone.D19CondSensitivity

/-!
# Claim 038 (D19): centered Gaussian cell integration with quadratic mesh allowances

Statement only; the proof is `Novel/D19CenteredQuadratureProof.lean`. Source claim:
`claims/038-d19-centered-quadrature.md`.

**Structure.** `statement := centered ∧ center ∧ chain ∧ scores ∧ rate ∧ panel`.
* `centered`: (2) with the allowances (1), and (3) with claim 036's first-order allowance.
* `center`: (4) at a box's center, and for every parameter of the box with claim 037's allowance
  `η(B) = min(η_N + η_k, η_cond)`.
* `chain`: (5). The resolution `M` may differ between boxes; the comparisons with claim 037's
  `D_cond` and claim 036's `D_cert` and lower bound are at a common `M`.
* `scores`: claim 036's conclusions for `q/D_center`.
* `rate`: part 3. Each allowance is its value at `M = 1` over `M²`, and on subboxes of `ℬ` at most
  `ℬ`'s value at `M = 1` over `M²`. On a fixed positive-label record both new bounds tend to
  `D_filter` as the boxes shrink and every box's `M` grows.

**Inputs.** As claim 036: AX-58's step is proved directly, and FDR is conditional on AX-53 through
claim 026's `panel`. The cosh bound is Mathlib's `Real.cosh_le_exp_half_sq`.

**Encodings.** Claim 036's model, cells, midpoints, forward sums `Qs`, `ε_J` (`epsQ`), `C_j(B)`
(`Cj`), subcell widths `hP` (with `hP 0 = 0`, so `r_j = hP_j/2` and `r_0 = 0`), boxes and covers;
claim 037's `η_cond` (`etaC`) and `D_cond`. A box's center is claim 036's `ctr`, which is claim 037's
`(b_g, w_g)`. For a prefix of length `J`, `Cpad` appends `C_(J+1) = 0`: the training prefix uses
`C_(k+1) = 0`. Part 3's operation counts and the conditional `O(N²)` count are commentary, not
formalized; the outward arithmetic and its safeguards concern the Python evaluator.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Standalone.D19CenteredQuadrature

open Standalone.D19FilteredLikelihood Standalone.D19CondSensitivity Standalone.D17ClockCells
  Standalone.D14FixedTick

/-- `C_1(B), …, C_J(B)` followed by `C_(J+1) = 0`. -/
noncomputable def Cpad (δ s : ℝ) {m : ℕ} (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) :
    Fin (m + 1) → ℝ :=
  Fin.snoc (Cj δ s Δ v B z) 0

/-- (1): `ε_J^− = Σ_j (r_j + r_(j−1))²/(2 w_− v_j)`. -/
noncomputable def epsMinus (δ : ℝ) (M : ℕ) {m : ℕ} (v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) : ℝ :=
  ∑ j : Fin m, (hP δ M z j.castSucc / 2 + hP δ M z j.succ / 2) ^ 2 / (2 * B.wL * v j)

/-- (1): `ε_J^+ = Σ_i r_i² (C_i(B) + C_(i+1)(B))²/2`, with `C_(J+1) = 0`. -/
noncomputable def epsPlus (δ s : ℝ) (M : ℕ) {m : ℕ} (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) : ℝ :=
  ∑ i : Fin m, (hP δ M z i.succ / 2) ^ 2 * (Cpad δ s Δ v B z i.castSucc + Cpad δ s Δ v B z i.succ) ^ 2 / 2

/-- (3): `ε̂_J^− = min(ε_J, ε_J^−)`. -/
noncomputable def epsMinusH (δ s : ℝ) (M : ℕ) {m : ℕ} (Δ v : Fin m → ℝ) (B : Box)
    (z : Fin m → ℕ) : ℝ :=
  min (epsQ δ s M Δ v B z) (epsMinus δ M v B z)

/-- (3): `ε̂_J^+ = min(ε_J, ε_J^+)`. -/
noncomputable def epsPlusH (δ s : ℝ) (M : ℕ) {m : ℕ} (Δ v : Fin m → ℝ) (B : Box)
    (z : Fin m → ℕ) : ℝ :=
  min (epsQ δ s M Δ v B z) (epsPlus δ s M Δ v B z)

/-- Part 1: (2) and (3), for every parameter of a box and every prefix length. -/
def centered : Prop :=
  ∀ (δ s : ℝ) (m M : ℕ) (Δ v : Fin m → ℝ) (B : Box) (b w : ℝ) (z : Fin m → ℕ), 0 < δ → 0 < s →
    0 < M → (∀ j, 0 < Δ j) → (∀ j, 0 < v j) → B.Valid → B.Mem (b, w) → (∀ j, 1 ≤ z j) →
    0 ≤ epsMinus δ M v B z ∧ 0 ≤ epsPlus δ s M Δ v B z ∧
    Real.exp (-epsMinus δ M v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z ≤
      Lz δ s (muF Δ v b w) (sdF v w) z ∧
    Lz δ s (muF Δ v b w) (sdF v w) z ≤
      Real.exp (epsPlus δ s M Δ v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z ∧
    Real.exp (-epsMinusH δ s M Δ v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z ≤
      Lz δ s (muF Δ v b w) (sdF v w) z ∧
    Lz δ s (muF Δ v b w) (sdF v w) z ≤
      Real.exp (epsPlusH δ s M Δ v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z

/-! ## Part 2 -/

/-- `R_g = Q_(θ_g,N)/Q_(θ_g,k)` at the box center. -/
noncomputable def Rg (δ s : ℝ) (M : ℕ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box) (u : Fin K → ℕ)
    (y : Fin n → ℕ) : ℝ :=
  Qs δ s M (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (Fin.append u y) /
    Qs δ s M (trn (muF Δ v (ctr B).1 (ctr B).2)) (trn (sdF v (ctr B).2)) u

/-- Claim 037's parameter allowance `η(B) = min(η_N + η_k, η_cond)`. -/
noncomputable def etaB (δ s : ℝ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box) (u : Fin K → ℕ)
    (y : Fin n → ℕ) : ℝ :=
  min (etaQ δ s Δ v B (Fin.append u y) + etaQ δ s (trn Δ) (trn v) B u) (etaC δ s Δ v B u y)

/-- The upper side of (4), capped at one. -/
noncomputable def termCen (δ s : ℝ) (M : ℕ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box)
    (u : Fin K → ℕ) (y : Fin n → ℕ) : ℝ :=
  min 1 (Real.exp (etaB δ s Δ v B u y + epsPlusH δ s M Δ v B (Fin.append u y) +
    epsMinusH δ s M (trn Δ) (trn v) B u) * Rg δ s M Δ v B u y)

/-- The lower side of (4) at the center. -/
noncomputable def termCenLow (δ s : ℝ) (M : ℕ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box)
    (u : Fin K → ℕ) (y : Fin n → ℕ) : ℝ :=
  Real.exp (-(epsMinusH δ s M Δ v B (Fin.append u y) + epsPlusH δ s M (trn Δ) (trn v) B u)) *
    Rg δ s M Δ v B u y

/-- (4): the center's two-sided bound, and every parameter of the box. -/
def center : Prop :=
  ∀ (δ s : ℝ) (M K n : ℕ) (Δ v : Fin (K + n) → ℝ) (B : Box) (u : Fin K → ℕ) (y : Fin n → ℕ),
    0 < δ → 0 < s → 0 < M → (∀ j, 0 < Δ j) → (∀ j, 0 < v j) → B.Valid →
    (∀ j, 1 ≤ Fin.append u y j) →
    0 < Rg δ s M Δ v B u y ∧
    termCenLow δ s M Δ v B u y ≤ gF δ s Δ v (ctr B).1 (ctr B).2 u y ∧
    ∀ p, B.Mem p → gF δ s Δ v p.1 p.2 u y ≤
      Real.exp (etaB δ s Δ v B u y + epsPlusH δ s M Δ v B (Fin.append u y) +
        epsMinusH δ s M (trn Δ) (trn v) B u) * Rg δ s M Δ v B u y

open Classical in
/-- `D_center`: the maximum of the capped upper sides over the cover and the clocks, box `B` at
resolution `Mb B`; the fallback `1` on records with a zero label. -/
noncomputable def Dcen (δ s : ℝ) (Mb : Box → ℕ) {K n : ℕ} (Δ : Fin (K + n) → ℝ) (C : Finset Box)
    (𝒱 : Finset (Fin (K + n) → ℝ)) (u : Fin K → ℕ) (y : Fin n → ℕ) : ℝ :=
  if ∀ j, 1 ≤ Fin.append u y j then
    (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (termCen δ s (Mb B) Δ v B u y)).toReal
  else 1

/-- `D_center^low`: the maximum of the lower sides over the centers and the clocks. -/
noncomputable def DcenLow (δ s : ℝ) (Mb : Box → ℕ) {K n : ℕ} (Δ : Fin (K + n) → ℝ)
    (C : Finset Box) (𝒱 : Finset (Fin (K + n) → ℝ)) (u : Fin K → ℕ) (y : Fin n → ℕ) : ℝ :=
  (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (termCenLow δ s (Mb B) Δ v B u y)).toReal

/-- (5), and the comparisons with claims 036 and 037 at a common resolution. -/
def chain : Prop :=
  ∀ (δ s : ℝ) (Mb : Box → ℕ) (K n : ℕ) (Δ : Fin (K + n) → ℝ) (𝒱 : Finset (Fin (K + n) → ℝ))
    (ℬ : Box) (C : Finset Box) (u : Fin K → ℕ) (y : Fin n → ℕ), 0 < δ → 0 < s →
    (∀ B ∈ C, 0 < Mb B) → (∀ j, 0 < Δ j) → 𝒱.Nonempty → (∀ v ∈ 𝒱, ∀ j, 0 < v j) → ℬ.Valid →
    CoverIn ℬ C →
    Dfilter δ s Δ 𝒱 ℬ u y ≤ Dcen δ s Mb Δ C 𝒱 u y ∧ Dcen δ s Mb Δ C 𝒱 u y ≤ 1 ∧
    ((∀ j, 1 ≤ Fin.append u y j) →
      0 < DcenLow δ s Mb Δ C 𝒱 u y ∧ DcenLow δ s Mb Δ C 𝒱 u y ≤ Dfilter δ s Δ 𝒱 ℬ u y) ∧
    ∀ M : ℕ, (∀ B ∈ C, Mb B = M) →
      Dcen δ s Mb Δ C 𝒱 u y ≤ Dcond δ s M Δ C 𝒱 u y ∧
      Dcond δ s M Δ C 𝒱 u y ≤ Dcert δ s M Δ C 𝒱 u y ∧ Dcert δ s M Δ C 𝒱 u y ≤ 1 ∧
      ((∀ j, 1 ≤ Fin.append u y j) → Dlow δ s M Δ C 𝒱 u y ≤ DcenLow δ s Mb Δ C 𝒱 u y) ∧
      ∀ q : ℝ, ENNReal.ofReal q / ENNReal.ofReal (Dcond δ s M Δ C 𝒱 u y) ≤
        ENNReal.ofReal q / ENNReal.ofReal (Dcen δ s Mb Δ C 𝒱 u y)

/-- Claim 036's conclusions for `q/D_center` under its whole-record mixture null. -/
def scores : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (δ s : ℝ)
    (Mb : Box → ℕ) (K n : ℕ) (Δ : Fin (K + n) → ℝ) (𝒱 : Finset (Fin (K + n) → ℝ)) (ℬ : Box)
    (C : Finset Box) (Z : Ω → Fin (K + n) → ℕ) (ν : Measure ((Fin (K + n) → ℝ) × ℝ × ℝ))
    [IsProbabilityMeasure ν] (q : (Fin K → ℕ) → (Fin n → ℕ) → ℝ),
    0 < δ → 0 < s → (∀ B ∈ C, 0 < Mb B) → (∀ j, 0 < Δ j) → 𝒱.Nonempty →
    (∀ v ∈ 𝒱, ∀ j, 0 < v j) → ℬ.Valid → CoverIn ℬ C →
    Measurable Z → (∀ᵐ θ ∂ν, θ ∈ Θset 𝒱 ℬ) →
    (∀ z, P (Z ⁻¹' {z}) = ∫⁻ θ, walkM δ (muF Δ θ.1 θ.2.1 θ.2.2) (sdF θ.1 θ.2.2) s {z} ∂ν) →
    (∀ u y, 0 ≤ q u y) → (∀ u, ∑' y, ENNReal.ofReal (q u y) = 1) →
    let U := fun ω => trn (Z ω)
    let V := fun ω => evl (Z ω)
    let E := fun u y => ENNReal.ofReal (q u y) / ENNReal.ofReal (Dcen δ s Mb Δ C 𝒱 u y)
    (∀ u y, E u y < ⊤) ∧
    (∀ᵐ u ∂(P.map U), ∫⁻ y, E u y ∂(condDistrib V U P u) ≤ 1) ∧
    ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      P {ω | ENNReal.ofReal (1 / α) ≤ E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
    ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1

/-! ## Part 3 -/

/-- Part 3: the exact `M⁻²` scaling, its uniformity over subboxes, and convergence of both bounds. -/
def rate : Prop :=
  (∀ (δ s : ℝ) (M m : ℕ) (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ),
    epsMinus δ M v B z = epsMinus δ 1 v B z / M ^ 2 ∧
    epsPlus δ s M Δ v B z = epsPlus δ s 1 Δ v B z / M ^ 2) ∧
  (∀ (δ s : ℝ) (M m : ℕ) (Δ v : Fin m → ℝ) (B ℬ : Box) (z : Fin m → ℕ), 0 < δ →
    (∀ j, 0 < Δ j) → (∀ j, 0 < v j) → (∀ j, 1 ≤ z j) → B.Valid → ℬ.Valid → B.Sub ℬ →
    epsMinus δ M v B z ≤ epsMinus δ 1 v ℬ z / M ^ 2 ∧
    epsPlus δ s M Δ v B z ≤ epsPlus δ s 1 Δ v ℬ z / M ^ 2) ∧
  ∀ (δ s : ℝ) (K n : ℕ) (Δ : Fin (K + n) → ℝ) (𝒱 : Finset (Fin (K + n) → ℝ)) (ℬ : Box)
    (u : Fin K → ℕ) (y : Fin n → ℕ), 0 < δ → 0 < s → (∀ j, 0 < Δ j) → 𝒱.Nonempty →
    (∀ v ∈ 𝒱, ∀ j, 0 < v j) → ℬ.Valid → (∀ j, 1 ≤ Fin.append u y j) →
    ∀ ε > 0, ∃ η > 0, ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ (C : Finset Box) (Mb : Box → ℕ), CoverIn ℬ C →
      (∀ B ∈ C, B.bH - B.bL ≤ η ∧ B.wH - B.wL ≤ η) → (∀ B ∈ C, M₀ ≤ Mb B) →
      Dcen δ s Mb Δ C 𝒱 u y ≤ Real.exp ε * Dfilter δ s Δ 𝒱 ℬ u y ∧
      Real.exp (-ε) * Dfilter δ s Δ 𝒱 ℬ u y ≤ DcenLow δ s Mb Δ C 𝒱 u y

/-- Claim 038. -/
def statement : Prop :=
  centered ∧ center ∧ chain ∧ scores ∧ rate ∧ Standalone.D14JumpRobustness.panel

end Standalone.D19CenteredQuadrature
