import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Polish

/-!
# Claim 052, deterministic part: price kernels and their finite-grid chains

Statement only; the proof is `Novel/PriceChainProof.lean`. Source claim:
`claims/052-d3-price-catalogue.md`, the deterministic steps of parts 1 and 3. No probability enters.

**Vocabulary.** These definitions are shared, with identical bodies, with `Upstream.PriceKernels`:
* `PosReal = (0, ∞)` with Lebesgue measure `posVol`;
* the kernels `f1` (lognormal, AX-55) and `f2` (reciprocal Bessel, AX-54);
* `chain f Δ x₀ y = ∏ⱼ f(Δⱼ, y_{j−1}, yⱼ)` with `y_{−1} = x₀` (`prev`).

**Statement.**
* For positive arguments, `f1` and `f2` are strictly positive. They are jointly measurable in
  `(x, y)`.
* Chains of positive kernels are positive, and jointly measurable in the start and the coordinates.
* **Finite-product normalization.** If every one-step kernel integrates to one over `(0, ∞)` from
  every positive state, the chain integrates to one over `(0, ∞)^m` from every positive start.
  This is iterated integration, last coordinate first (Mathlib's `lintegral_prod_symm'`).
* **Fixed-grid equivalence** (part 3). For any two families of positive kernels, the two chain laws
  `posVol^m.withDensity chain` from a common positive start are mutually absolutely continuous.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Standalone.PriceChain

/-- `(0, ∞)`. -/
abbrev PosReal := {x : ℝ // 0 < x}

instance : PolishSpace PosReal := (isOpen_lt continuous_const continuous_id).polishSpace

instance : Nonempty PosReal := ⟨⟨1, one_pos⟩⟩

/-- Lebesgue measure on `(0, ∞)`. -/
noncomputable def posVol : Measure PosReal := Measure.comap Subtype.val volume

/-- The geometric-Brownian kernel (AX-55). -/
noncomputable def f1 (κ Δ x y : ℝ) : ℝ :=
  Real.exp (-(Real.log (y / x) + κ ^ 2 * Δ / 2) ^ 2 / (2 * (κ ^ 2 * Δ))) /
    (y * Real.sqrt (2 * Real.pi * (κ ^ 2 * Δ)))

/-- The reciprocal-Bessel kernel (AX-54). -/
noncomputable def f2 (κ Δ x y : ℝ) : ℝ :=
  x / (y ^ 3 * Real.sqrt (2 * Real.pi * (κ ^ 2 * Δ))) *
    (Real.exp (-(1 / y - 1 / x) ^ 2 / (2 * (κ ^ 2 * Δ))) -
      Real.exp (-(1 / y + 1 / x) ^ 2 / (2 * (κ ^ 2 * Δ))))

/-- The previous coordinate, `x₀` before the first. -/
def prev {n : ℕ} (x₀ : ℝ) (y : Fin n → PosReal) (j : Fin n) : ℝ :=
  if h : (j : ℕ) = 0 then x₀ else (y ⟨j - 1, by omega⟩ : ℝ)

/-- The chain density `∏ⱼ f(Δⱼ, y_{j−1}, yⱼ)`. -/
noncomputable def chain {n : ℕ} (f : ℝ → ℝ → ℝ → ℝ) (Δ : Fin n → ℝ) (x₀ : ℝ)
    (y : Fin n → PosReal) : ℝ :=
  ∏ j : Fin n, f (Δ j) (prev x₀ y j) (y j)

/-- The deterministic part of claim 052. -/
def statement : Prop :=
  (∀ κ Δ x y : ℝ, 0 < κ → 0 < Δ → 0 < x → 0 < y → 0 < f1 κ Δ x y ∧ 0 < f2 κ Δ x y) ∧
  (∀ κ Δ : ℝ, Measurable (Function.uncurry (f1 κ Δ)) ∧ Measurable (Function.uncurry (f2 κ Δ))) ∧
  (∀ (m : ℕ) (f : ℝ → ℝ → ℝ → ℝ) (Δ : Fin m → ℝ),
    (∀ j x y, 0 < x → 0 < y → 0 < f (Δ j) x y) →
      ∀ x₀ : ℝ, 0 < x₀ → ∀ y, 0 < chain f Δ x₀ y) ∧
  (∀ (m : ℕ) (f : ℝ → ℝ → ℝ → ℝ) (Δ : Fin m → ℝ), (∀ j, Measurable (Function.uncurry (f (Δ j)))) →
    Measurable fun p : ℝ × (Fin m → PosReal) => chain f Δ p.1 p.2) ∧
  (∀ (m : ℕ) (f : ℝ → ℝ → ℝ → ℝ) (Δ : Fin m → ℝ),
    (∀ j, Measurable (Function.uncurry (f (Δ j)))) →
    (∀ j x y, 0 < x → 0 < y → 0 < f (Δ j) x y) →
    (∀ j x, 0 < x → ∫⁻ y, ENNReal.ofReal (f (Δ j) x y) ∂posVol = 1) →
    ∀ x₀ : ℝ, 0 < x₀ →
      ∫⁻ y, ENNReal.ofReal (chain f Δ x₀ y) ∂(Measure.pi fun _ : Fin m => posVol) = 1) ∧
  (∀ (m : ℕ) (f f' : ℝ → ℝ → ℝ → ℝ) (Δ : Fin m → ℝ),
    (∀ j, Measurable (Function.uncurry (f (Δ j)))) → (∀ j, Measurable (Function.uncurry (f' (Δ j)))) →
    (∀ j x y, 0 < x → 0 < y → 0 < f (Δ j) x y) → (∀ j x y, 0 < x → 0 < y → 0 < f' (Δ j) x y) →
    ∀ x₀ : ℝ, 0 < x₀ →
      (Measure.pi fun _ : Fin m => posVol).withDensity (fun y => ENNReal.ofReal (chain f Δ x₀ y)) ≪
        (Measure.pi fun _ : Fin m => posVol).withDensity
          (fun y => ENNReal.ofReal (chain f' Δ x₀ y)))

end Standalone.PriceChain
