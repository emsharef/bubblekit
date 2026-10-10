import Standalone.DensityCancellation
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Density cancellation: proof

Proves `Standalone.DensityCancellation.statement` (`proof`). The weight
`f(x) = x / (σ(x)² Λ(x))` on `B ∩ {Λ > 0}` (and `0` elsewhere) is chosen after the path is fixed.
Against the time occupation it gives the left side (`lhs_pointwise`); against the level density it
gives `x/σ²` on `B ∩ {Λ > 0}` (`rhs_pointwise`). That set equals `B ∩ (m, M)` up to a Lebesgue-null
set.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Novel.DensityCancellation

open Standalone.DensityCancellation

/-- The selected weight. -/
noncomputable def selected (B : Set ℝ) (Λ σ : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  open Classical in
  if x ∈ B ∧ 0 < Λ x then ENNReal.ofReal (x / (σ x ^ 2 * Λ x)) else 0

theorem measurable_selected {B : Set ℝ} {Λ σ : ℝ → ℝ} (hB : MeasurableSet B) (hΛ : Measurable Λ)
    (hσ : Measurable σ) : Measurable (selected B Λ σ) := by
  classical
  refine Measurable.ite (hB.inter (measurableSet_lt measurable_const hΛ)) ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp (measurable_id.div ((hσ.pow_const 2).mul hΛ))

theorem lhs_pointwise {B : Set ℝ} {s k Λ σ : ℝ → ℝ} (hBpos : B ⊆ Ioi 0)
    (hσ0 : ∀ x, 0 < x → σ x ≠ 0) (_hΛ0 : ∀ x, 0 ≤ Λ x)
    (hk : ∀ u, k u = if 0 < s u then σ (s u) ^ 2 else 0) (u : ℝ) :
    selected B Λ σ (s u) * ENNReal.ofReal (k u) =
      B.indicator 1 (s u) * ENNReal.ofReal (weight s Λ u) := by
  classical
  by_cases hB : s u ∈ B
  · have hpos : 0 < s u := hBpos hB
    rw [indicator_of_mem hB, Pi.one_apply, one_mul, hk u]
    by_cases hL : 0 < Λ (s u)
    · have hσ2 : 0 < σ (s u) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hσ0 _ hpos)))
      simp only [selected, weight, hB, hL, hpos, and_self, ite_true]
      rw [← ENNReal.ofReal_mul (div_nonneg hpos.le (mul_pos hσ2 hL).le)]
      congr 1
      have h1 := hσ0 _ hpos
      have h2 := hL.ne'
      field_simp
    · simp only [selected, weight, hB, hL, hpos, and_false, ite_false, zero_mul,
        ENNReal.ofReal_zero]
  · simp [selected, hB]

theorem rhs_pointwise {B : Set ℝ} {Λ σ : ℝ → ℝ} (hBpos : B ⊆ Ioi 0)
    (hσ0 : ∀ x, 0 < x → σ x ≠ 0) (x : ℝ) :
    selected B Λ σ x * ENNReal.ofReal (Λ x) =
      (B ∩ {y | 0 < Λ y}).indicator (fun y => ENNReal.ofReal (y / σ y ^ 2)) x := by
  classical
  by_cases h : x ∈ B ∧ 0 < Λ x
  · have hpos : 0 < x := hBpos h.1
    have hσ2 : 0 < σ x ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hσ0 _ hpos)))
    rw [indicator_of_mem (show x ∈ B ∩ {y | 0 < Λ y} from h)]
    simp only [selected, h, and_self, ite_true]
    rw [← ENNReal.ofReal_mul (div_nonneg hpos.le (mul_pos hσ2 h.2).le)]
    congr 1
    have h1 := hσ0 _ hpos
    have h2 := h.2.ne'
    field_simp
  · rw [indicator_of_notMem (show x ∉ B ∩ {y | 0 < Λ y} from h)]
    simp only [selected, h, ite_false, zero_mul]

/-- The deterministic density cancellation. -/
theorem proof : Standalone.DensityCancellation.statement := by
  intro t m M s k Λ σ _ hΛ hσ hσ0 _ hΛ0 hk hocc hcov B hB hBpos
  have h := hocc _ (measurable_selected hB hΛ hσ)
  simp_rw [lhs_pointwise hBpos hσ0 hΛ0 hk] at h
  rw [h]
  simp_rw [rhs_pointwise hBpos hσ0]
  rw [lintegral_indicator (hB.inter (measurableSet_lt measurable_const hΛ))]
  refine setLIntegral_congr ?_
  filter_upwards [hcov] with x hx
  refine propext ?_
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hxB, hxL⟩; exact ⟨hxB, (hx (hBpos hxB)).2 hxL⟩
  · rintro ⟨hxB, hxI⟩; exact ⟨hxB, (hx (hBpos hxB)).1 hxI⟩

end Novel.DensityCancellation
