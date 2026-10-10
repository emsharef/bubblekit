import Novel.D19FilteredLikelihoodCompare

/-!
# Claims 036, parts 2–3: the transition density in log price

* `Ptr_density`: from `x > 0`, the transition puts on `A` the integral, over the log prices `t`
  with `e^t ∈ A`, of the Normal density at the log return `t − log x`.
* `pdf_ratio`: two values of the Normal density whose arguments are within `ρ` of each other, both
  within `R` of zero, differ by a factor at most `exp(ρ (R + |μ|)/v)`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick

theorem Ptr_density (μ : ℝ) {σ : ℝ} (hσ : σ ≠ 0) {x : ℝ} (hx : 0 < x) {A : Set ℝ}
    (hA : MeasurableSet A) :
    Ptr μ σ x A = ∫⁻ t in {t | Real.exp t ∈ A},
      ENNReal.ofReal (gaussianPDFReal μ (σ ^ 2).toNNReal (t - Real.log x)) := by
  have hv : (σ ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hS : MeasurableSet {t : ℝ | Real.exp t ∈ A} := Real.measurable_exp hA
  have hS' : MeasurableSet {ξ : ℝ | x * Real.exp ξ ∈ A} :=
    (measurable_const.mul Real.measurable_exp) hA
  rw [Ptr_apply _ _ _ hA, gaussianReal_of_var_ne_zero _ hv, withDensity_apply _ hS',
    ← lintegral_indicator hS', ← lintegral_indicator hS]
  rw [← lintegral_add_right_eq_self (μ := volume) (fun t => {t : ℝ | Real.exp t ∈ A}.indicator
    (fun t => ENNReal.ofReal (gaussianPDFReal μ (σ ^ 2).toNNReal (t - Real.log x))) t) (Real.log x)]
  refine lintegral_congr fun ξ => ?_
  have e : Real.exp (ξ + Real.log x) = x * Real.exp ξ := by
    rw [Real.exp_add, Real.exp_log hx, mul_comm]
  by_cases h : x * Real.exp ξ ∈ A
  · rw [indicator_of_mem (show ξ ∈ {ξ | x * Real.exp ξ ∈ A} from h),
      indicator_of_mem (show ξ + Real.log x ∈ {t | Real.exp t ∈ A} by simp [e, h]), add_sub_cancel_right]
    rfl
  · rw [indicator_of_notMem (show ξ ∉ {ξ | x * Real.exp ξ ∈ A} from h),
      indicator_of_notMem (show ξ + Real.log x ∉ {t | Real.exp t ∈ A} by simp [e, h])]

/-- The Normal density ratio between nearby arguments. -/
theorem pdf_ratio (μ : ℝ) {v : ℝ} (hv : 0 < v) {R₁ R₂ R ρ : ℝ} (h1 : |R₁| ≤ R) (h2 : |R₂| ≤ R)
    (h12 : |R₁ - R₂| ≤ ρ) :
    gaussianPDFReal μ v.toNNReal R₁ ≤
      Real.exp (ρ * ((R + |μ|) / v)) * gaussianPDFReal μ v.toNNReal R₂ := by
  unfold gaussianPDFReal
  rw [Real.coe_toNNReal _ hv.le, mul_left_comm, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have hq : (R₂ - μ) ^ 2 - (R₁ - μ) ^ 2 = (R₂ - R₁) * (R₂ + R₁ - 2 * μ) := by ring
  have hb : |R₂ + R₁ - 2 * μ| ≤ 2 * (R + |μ|) := by
    calc |R₂ + R₁ - 2 * μ| ≤ |R₂| + |R₁| + |2 * μ| := by
          refine (abs_sub _ _).trans ?_; gcongr; exact abs_add_le _ _
      _ ≤ 2 * (R + |μ|) := by rw [abs_mul, abs_two]; linarith
  have hp : (R₂ - μ) ^ 2 - (R₁ - μ) ^ 2 ≤ 2 * ρ * (R + |μ|) := by
    rw [hq]
    calc (R₂ - R₁) * (R₂ + R₁ - 2 * μ) ≤ |(R₂ - R₁) * (R₂ + R₁ - 2 * μ)| := le_abs_self _
      _ = |R₂ - R₁| * |R₂ + R₁ - 2 * μ| := abs_mul _ _
      _ ≤ ρ * (2 * (R + |μ|)) := by
          rw [abs_sub_comm]; exact mul_le_mul h12 hb (abs_nonneg _) ((abs_nonneg _).trans h12)
      _ = 2 * ρ * (R + |μ|) := by ring
  have e : ρ * ((R + |μ|) / v) + -(R₂ - μ) ^ 2 / (2 * v) =
      (2 * ρ * (R + |μ|) - (R₂ - μ) ^ 2) / (2 * v) := by field_simp; ring
  rw [e, div_le_div_iff_of_pos_right (by positivity)]
  linarith

end Novel.D19FilteredLikelihood
