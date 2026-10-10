import Novel.D31FilterScopeLaw

/-!
# Claim 043, part 2: the Gaussian counterexample

* A unit-variance normal density is at most `1/√(2π)`, with equality at its mean; so the profiled
  denominator is `1/√(2π)` and the score is `ε⁻¹ exp(−r²/(2ε²))`.
* Unfiltered: `∫ ε⁻¹ e^(−r²/(2ε²)) φ(r) dr` is a Gaussian integral with precision `1 + ε⁻²`, equal to
  `1/√(1+ε²)`.
* Filtered: on `{|R| > a}`, `Y = 0` and the score is `1/ε`, so the mean is at least `ρ/ε` and
  `P(score > 1/α) ≥ ρ` whenever `ε < α`.
* For any level `α < 1`, the cutoff `a = (1 − α)/2` leaves at most `2a/√(2π) ≤ a` of the normal mass
  in `[−a, a]`, so `ρ ≥ (1 + α)/2 > α`.
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace Novel.D31FilterScope

open Standalone.D31FilterScope

theorem gpdf_le (μ x : ℝ) : gaussianPDFReal μ 1 x ≤ 1 / √(2 * π) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, one_div]
  refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
  have := sq_nonneg (x - μ)
  linarith [div_nonneg this (by norm_num : (0 : ℝ) ≤ 2)]

theorem gpdf_at (x : ℝ) : gaussianPDFReal (x + 1 / 2 - 1 / 2) 1 x = 1 / √(2 * π) := by
  rw [gaussianPDFReal_def]; simp

theorem Dprof_eq (r : ℝ) : Dprof r = 1 / √(2 * π) := by
  have hb : BddAbove (range fun b : ℝ => gaussianPDFReal (b - 1 / 2) 1 r) :=
    ⟨1 / √(2 * π), forall_mem_range.2 fun b => gpdf_le _ r⟩
  exact le_antisymm (ciSup_le fun b => gpdf_le _ r)
    (le_ciSup_of_le hb (r + 1 / 2) (le_of_eq (gpdf_at r).symm))

theorem score_eq {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    score ε r = ε⁻¹ * Real.exp (-r ^ 2 / (2 * ε ^ 2)) := by
  unfold score
  rw [Dprof_eq, gaussianPDFReal_def]
  simp only [Real.coe_toNNReal _ (sq_nonneg ε), sub_zero]
  have h2 : √(2 * π * ε ^ 2) = √(2 * π) * ε := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hε.le]
  rw [h2]
  have : 0 < √(2 * π) := by positivity
  field_simp

theorem score_nonneg {ε : ℝ} (hε : 0 < ε) (r : ℝ) : 0 ≤ score ε r := by
  rw [score_eq hε]; positivity

theorem measurable_score (ε : ℝ) : Measurable (score ε) := by
  unfold score
  rw [show Dprof = fun _ => 1 / √(2 * π) from funext Dprof_eq]
  exact (measurable_gaussianPDFReal _ _).div_const _

theorem gauss_density : IsDensity (gaussianPDFReal 0 1) :=
  ⟨measurable_gaussianPDFReal 0 1, fun r => (gaussianPDFReal_pos 0 1 r one_ne_zero).le,
    lintegral_gaussianPDFReal_eq_one 0 one_ne_zero⟩

theorem gaussianReal_eq_lawOf : gaussianReal 0 1 = lawOf (gaussianPDFReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]; rfl

/-- The unfiltered mean. -/
theorem mean_unfiltered {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ r, ENNReal.ofReal (score ε r) ∂(gaussianReal 0 1) =
      ENNReal.ofReal (1 / √(1 + ε ^ 2)) := by
  set b : ℝ := 1 / 2 + 1 / (2 * ε ^ 2)
  have hb : 0 < b := by positivity
  set c : ℝ := (√(2 * π))⁻¹ * ε⁻¹
  have hpt : ∀ r, gaussianPDFReal 0 1 r * score ε r = c * Real.exp (-b * r ^ 2) := fun r => by
    rw [score_eq hε, gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero, c, b]
    rw [show (√(2 * π))⁻¹ * Real.exp (-r ^ 2 / 2) * (ε⁻¹ * Real.exp (-r ^ 2 / (2 * ε ^ 2))) =
      (√(2 * π))⁻¹ * ε⁻¹ * (Real.exp (-r ^ 2 / 2) * Real.exp (-r ^ 2 / (2 * ε ^ 2))) by ring,
      ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1)
      (measurable_score ε).ennreal_ofReal]
  have he : ∀ r, (gaussianPDF 0 1 * fun r => ENNReal.ofReal (score ε r)) r =
      ENNReal.ofReal (c * Real.exp (-b * r ^ 2)) := fun r => by
    simp only [Pi.mul_apply, gaussianPDF]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 r), hpt]
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_sq hb).const_mul c)
    (Filter.Eventually.of_forall fun r => by positivity), integral_const_mul, integral_gaussian]
  congr 1
  -- `c √(π/b) = 1/√(1+ε²)`, by comparing squares.
  have hl : 0 ≤ c * √(π / b) := by positivity
  have hsq : (c * √(π / b)) ^ 2 = 1 / (1 + ε ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    simp only [c, b, mul_pow, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * π)]
    field_simp
    ring
  rw [← Real.sqrt_sq hl, hsq, Real.sqrt_div' 1 (by positivity : (0 : ℝ) ≤ 1 + ε ^ 2), Real.sqrt_one]

section Sample

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {R : Ω → ℝ}
  (hR : Measurable R) (hlaw : P.map R = gaussianReal 0 1)
include hR hlaw

theorem prob_tail (a : ℝ) : P {ω | a < |R ω|} = ENNReal.ofReal (rho (gaussianPDFReal 0 1) a) := by
  rw [show {ω | a < |R ω|} = R ⁻¹' {r | a < |r|} from rfl,
    ← Measure.map_apply hR (measurableSet_tail a), hlaw, gaussianReal_eq_lawOf,
    ofReal_rho gauss_density, lawOf, withDensity_apply _ (measurableSet_tail a)]

/-- On the tail, the filtered score is `1/ε`. -/
theorem score_tail {ε : ℝ} (hε : 0 < ε) {a : ℝ} {ω : Ω} (h : a < |R ω|) :
    score ε (Ha a (R ω)) = ε⁻¹ := by
  rw [Ha, if_neg (not_le.2 h), score_eq hε]; simp

theorem mean_filtered_ge {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    ENNReal.ofReal (rho (gaussianPDFReal 0 1) a / ε) ≤
      ∫⁻ ω, ENNReal.ofReal (score ε (Ha a (R ω))) ∂P := by
  have hS : MeasurableSet {ω | a < |R ω|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hR)
  calc ENNReal.ofReal (rho (gaussianPDFReal 0 1) a / ε)
      = ∫⁻ ω in {ω | a < |R ω|}, ENNReal.ofReal ε⁻¹ ∂P := by
        rw [setLIntegral_const, prob_tail hR hlaw, ← ENNReal.ofReal_mul (by positivity),
          div_eq_mul_inv, mul_comm]
    _ = ∫⁻ ω in {ω | a < |R ω|}, ENNReal.ofReal (score ε (Ha a (R ω))) ∂P :=
        setLIntegral_congr_fun hS fun ω h => by rw [score_tail hR hlaw hε h]
    _ ≤ _ := setLIntegral_le_lintegral _ _

theorem reject_ge {ε α a : ℝ} (hε : 0 < ε) (hεα : ε < α) :
    ENNReal.ofReal (rho (gaussianPDFReal 0 1) a) ≤ P {ω | 1 / α < score ε (Ha a (R ω))} := by
  rw [← prob_tail hR hlaw]
  refine measure_mono fun ω h => ?_
  simp only [mem_setOf_eq] at h ⊢
  rw [score_tail hR hlaw hε h, one_div]
  exact inv_strictAnti₀ hε hεα

end Sample

/-- A small cutoff leaves at least `(1 + α)/2` of the normal mass in the tail. -/
theorem rho_small {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    (1 + α) / 2 ≤ rho (gaussianPDFReal 0 1) ((1 - α) / 2) := by
  set a := (1 - α) / 2
  have ha : 0 < a := by simp only [a]; linarith
  have hprob : IsProbabilityMeasure (lawOf (gaussianPDFReal 0 1)) :=
    ⟨by rw [lawOf, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, gauss_density.2.2]⟩
  have hS : {r : ℝ | a < |r|}ᶜ = Icc (-a) a := by
    ext r; simp [abs_le]
  have hc : 1 / √(2 * π) ≤ 1 / 2 := by
    rw [div_le_div_iff_of_pos_left one_pos (by positivity) two_pos]
    calc (2 : ℝ) = √4 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ √(2 * π) := Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])
  have hin : lawOf (gaussianPDFReal 0 1) (Icc (-a) a) ≤ ENNReal.ofReal a := by
    rw [lawOf, withDensity_apply _ measurableSet_Icc]
    calc ∫⁻ r in Icc (-a) a, ENNReal.ofReal (gaussianPDFReal 0 1 r)
        ≤ ∫⁻ _r in Icc (-a) a, ENNReal.ofReal (1 / 2) :=
          setLIntegral_mono measurable_const fun r _ =>
            ENNReal.ofReal_le_ofReal ((gpdf_le 0 r).trans hc)
      _ = ENNReal.ofReal a := by
          rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
  have htail : (lawOf (gaussianPDFReal 0 1) {r | a < |r|}).toReal = rho (gaussianPDFReal 0 1) a := by
    rw [lawOf, withDensity_apply _ (measurableSet_tail a)]; rfl
  have hcompl := prob_compl_eq_one_sub (μ := lawOf (gaussianPDFReal 0 1)) (measurableSet_tail a)
  rw [hS] at hcompl
  have hle : (lawOf (gaussianPDFReal 0 1) (Icc (-a) a)).toReal ≤ a :=
    ENNReal.toReal_le_of_le_ofReal ha.le hin
  have hsum : (lawOf (gaussianPDFReal 0 1) (Icc (-a) a)).toReal +
      (lawOf (gaussianPDFReal 0 1) {r | a < |r|}).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hcompl,
      tsub_add_cancel_of_le prob_le_one, ENNReal.toReal_one]
  rw [← htail]
  simp only [a] at hle
  linarith

theorem counterexample_holds : Standalone.D31FilterScope.counterexample := by
  refine ⟨fun r => ⟨Dprof_eq r, by rw [gpdf_at, Dprof_eq]⟩, fun ε r hε => score_eq hε r,
    fun P _ R a hR hlaw ha => ?_⟩
  have hρ := (rho_pos_lt ha gauss_density fun r => gaussianPDFReal_pos 0 1 r one_ne_zero).1
  refine ⟨fun ε hε => ⟨?_, mean_filtered_ge hR hlaw hε a⟩, ?_, ⟨?_, by linarith⟩, ?_⟩
  · rw [← lintegral_map (f := fun r => ENNReal.ofReal (score ε r)) (measurable_score ε).ennreal_ofReal hR,
      hlaw]
    exact mean_unfiltered hε
  · have := mean_filtered_ge hR hlaw (ε := rho (gaussianPDFReal 0 1) a / 2) (by positivity) a
    rwa [show rho (gaussianPDFReal 0 1) a / (rho (gaussianPDFReal 0 1) a / 2) = 2 by
      field_simp, ENNReal.ofReal_ofNat] at this
  · exact reject_ge hR hlaw (by positivity) (by linarith)
  · intro α hα hα1
    refine ⟨(1 - α) / 2, by linarith, by linarith [rho_small hα hα1], fun ε hε hεα => ?_⟩
    exact reject_ge hR hlaw hε hεα

end Novel.D31FilterScope
