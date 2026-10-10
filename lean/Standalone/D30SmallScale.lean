import Standalone.PriceChain
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Claim 073 (D30): no uniform finite-grid separation without a positive scale floor

Statement only; the proof is `Novel/D30SmallScaleProof.lean`. Source claim:
`claims/073-d30-small-scale-obstruction.md`.

**Structure.** `statement := convergence ∧ obstruction ∧ increasing`.
* `convergence`: part 1. For every fixed grid:
  - the coordinates (2) carry `Γ_n` to the GBM price law (`p = 1`);
  - the reciprocal-Bessel price law (`p = 2`) is `Γ_n` with density `L_κ` (3), carried by the same
    coordinates;
  - `L_κ > 0` is integrable with mean one;
  - `L_κ(z) → 1` for every `z`, and `d_grid(κ) = ∫ |L_κ − 1| dΓ_n → 0` as `κ ↓ 0`;
  - (5): every Borel randomized test `ψ` has `|E_(2,κ) ψ − E_(1,κ) ψ| ≤ d_grid(κ)`.
* `obstruction`: part 2's (6). A test with null size at most `α` at every `κ > 0` has
  `inf_κ E_(2,κ) ψ ≤ α`, and the constant test `α` has size and power `α` under every law, so the
  maximin power is exactly `α`.
* `increasing`: part 3's (7) for any sequence of grids and uniformly level-`α` tests, and hence no
  sequence of worst-case power lower bounds tends to one.

**Inputs.** The price laws are claim 052's normalized chain laws `posVol^n.withDensity chain` from
`S₀ = 1`, with claim 052's kernels `f1` (AX-55) and `f2` (AX-54) (`P = Q`). The one-step
normalization of `f2` (`KernelNorm2`, AX-54's `norm` field) is a deterministic identity and is
proved, not assumed; that of `f1` follows from the coordinate identity. Nothing in the statement is
conditional. AX-16 enters through the lab's `Novel.D9TrueLimit.tendsto_l1_of_mean`.

**Encodings.**
* `κ ↓ 0` is the filter `𝓝[>] 0`.
* A randomized test is a measurable `ψ : (0, ∞)^n → [0, 1]`; `E_(p,κ) ψ = ∫ ψ dP_(p,κ)`. A family
  `ψ_κ` that knows `κ` is covered because (5) holds for every `κ` and every `ψ`.
* Part 2's remarks about larger classes, D30's separable model and the elasticity gap are
  commentary on (6), not separate statements.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Standalone.D30SmallScale

open Standalone.PriceChain

/-- `Γ_n`, the product standard-normal law. -/
noncomputable def Gam (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1

/-- (2): `r_(κ,j) = κ √Δ_j z_j − κ² Δ_j / 2`. -/
noncomputable def rk {n : ℕ} (κ : ℝ) (Δ : Fin n → ℝ) (z : Fin n → ℝ) (j : Fin n) : ℝ :=
  κ * Real.sqrt (Δ j) * z j - κ ^ 2 * Δ j / 2

/-- (2): `s_(κ,j) = exp(Σ_(i ≤ j) r_(κ,i))`. -/
noncomputable def sk {n : ℕ} (κ : ℝ) (Δ : Fin n → ℝ) (z : Fin n → ℝ) : Fin n → PosReal :=
  fun j => ⟨Real.exp (∑ i ∈ Finset.univ.filter (· ≤ j), rk κ Δ z i), Real.exp_pos _⟩

/-- (3): `L_κ(z) = Π_j (x_j/y_j²) exp[z_j²/2 − (1/y_j − 1/x_j)²/(2v_j)] (1 − exp[−2/(v_j x_j y_j)])`,
with `x_j = s_(κ,j−1)`, `y_j = s_(κ,j)` and `v_j = κ² Δ_j`. -/
noncomputable def Lk {n : ℕ} (κ : ℝ) (Δ : Fin n → ℝ) (z : Fin n → ℝ) : ℝ :=
  ∏ j : Fin n,
    let x := prev 1 (sk κ Δ z) j
    let y : ℝ := sk κ Δ z j
    let v := κ ^ 2 * Δ j
    x / y ^ 2 * Real.exp (z j ^ 2 / 2 - (1 / y - 1 / x) ^ 2 / (2 * v)) *
      (1 - Real.exp (-(2 / (v * x * y))))

/-- The price law of `dS = κ S^p dW` at the grid, from `S₀ = 1`: claim 052's normalized chain. -/
noncomputable def Plaw {n : ℕ} (f : ℝ → ℝ → ℝ → ℝ → ℝ) (κ : ℝ) (Δ : Fin n → ℝ) :
    Measure (Fin n → PosReal) :=
  (Measure.pi fun _ : Fin n => posVol).withDensity fun y => ENNReal.ofReal (chain (f κ) Δ 1 y)

/-- (4): `d_grid(κ) = ∫ |L_κ − 1| dΓ_n`. -/
noncomputable def dgrid {n : ℕ} (κ : ℝ) (Δ : Fin n → ℝ) : ℝ := ∫ z, |Lk κ Δ z - 1| ∂Gam n

/-- AX-54's one-step normalization of the reciprocal-Bessel kernel (proved in
`Novel/D30SmallScaleNorm.lean`). -/
def KernelNorm2 : Prop :=
  ∀ κ Δ x : ℝ, 0 < κ → 0 < Δ → 0 < x → ∫⁻ y, ENNReal.ofReal (f2 κ Δ x y) ∂posVol = 1

/-- A Borel randomized test. -/
def IsTest {n : ℕ} (ψ : (Fin n → PosReal) → ℝ) : Prop := Measurable ψ ∧ ∀ y, 0 ≤ ψ y ∧ ψ y ≤ 1

/-- Part 1. -/
def convergence : Prop :=
  ∀ (n : ℕ) (Δ : Fin n → ℝ), (∀ j, 0 < Δ j) →
    (∀ κ : ℝ, 0 < κ →
      (Gam n).map (sk κ Δ) = Plaw f1 κ Δ ∧
      Plaw f2 κ Δ = ((Gam n).withDensity fun z => ENNReal.ofReal (Lk κ Δ z)).map (sk κ Δ) ∧
      (∀ z, 0 < Lk κ Δ z) ∧ Integrable (Lk κ Δ) (Gam n) ∧ ∫ z, Lk κ Δ z ∂Gam n = 1) ∧
    (∀ z, Tendsto (fun κ => Lk κ Δ z) (𝓝[>] 0) (𝓝 1)) ∧
    Tendsto (fun κ => dgrid κ Δ) (𝓝[>] 0) (𝓝 0) ∧
    -- (5).
    ∀ κ : ℝ, 0 < κ → ∀ ψ, IsTest ψ →
      |∫ y, ψ y ∂Plaw f2 κ Δ - ∫ y, ψ y ∂Plaw f1 κ Δ| ≤ dgrid κ Δ

/-- Part 2's (6), and the maximin value `α`. -/
def obstruction : Prop :=
  ∀ (n : ℕ) (Δ : Fin n → ℝ) (α : ℝ), (∀ j, 0 < Δ j) → 0 < α → α < 1 →
    (∀ ψ, IsTest ψ → (∀ κ : ℝ, 0 < κ → ∫ y, ψ y ∂Plaw f1 κ Δ ≤ α) →
      ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∫ y, ψ y ∂Plaw f2 κ Δ ≤ α + ε) ∧
    IsTest (fun _ : Fin n → PosReal => α) ∧
    ∀ κ : ℝ, 0 < κ → ∫ _y, α ∂Plaw f1 κ Δ = α ∧ ∫ _y, α ∂Plaw f2 κ Δ = α

/-- Part 3's (7), for a sequence of grids `Δ m` with `n m` points and tests `ψ m`. -/
def increasing : Prop :=
  ∀ (n : ℕ → ℕ) (Δ : (m : ℕ) → Fin (n m) → ℝ) (ψ : (m : ℕ) → (Fin (n m) → PosReal) → ℝ) (α : ℝ),
    (∀ m j, 0 < Δ m j) → 0 < α → α < 1 → (∀ m, IsTest (ψ m)) →
    (∀ m (κ : ℝ), 0 < κ → ∫ y, ψ m y ∂Plaw f1 κ (Δ m) ≤ α) →
    (∀ m : ℕ, ∃ κ : ℝ, 0 < κ ∧ κ < 1 / (m + 1) ∧
      ∫ y, ψ m y ∂Plaw f2 κ (Δ m) ≤ α + 1 / (m + 1)) ∧
    -- No sequence of worst-case power lower bounds tends to one.
    ∀ c : ℕ → ℝ, (∀ m (κ : ℝ), 0 < κ → c m ≤ ∫ y, ψ m y ∂Plaw f2 κ (Δ m)) →
      ¬ Tendsto c atTop (𝓝 1)

/-- Claim 073. -/
def statement : Prop := convergence ∧ obstruction ∧ increasing

end Standalone.D30SmallScale
