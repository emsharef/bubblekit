import Novel.D30SmallScaleCoord

/-!
# Claim 073: the reciprocal-Bessel kernel is normalized

AX-54's one-step normalization `∫₀^∞ f₂(κ, Δ, x, y) dy = 1` is a deterministic identity about an
explicit function, so it is proved here rather than assumed (`kernelNorm2_holds`), as the auditor
suggested.
* With `u = 1/y` (Mathlib's one-dimensional change of variables), the integrand becomes
  `x u (φ(u; 1/x, v) − φ(u; −1/x, v))` on `(0, ∞)`, with `φ` the normal density of variance
  `v = κ²Δ`.
* Reflecting `u ↦ −u` in the second term turns it into minus the negative half-line part of
  `∫ u φ(u; 1/x, v) du`. Hence the integral is `x · ∫_ℝ u φ(u; 1/x, v) du = x · (1/x) = 1`, the
  mean of a normal law (`integral_id_gaussianReal`).
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace Novel.D30SmallScale

open Standalone.D30SmallScale Standalone.PriceChain Novel.PriceChain

theorem gpdf_reflect (m : ℝ) (v : ℝ≥0) (w : ℝ) : gaussianPDFReal (-m) v (-w) = gaussianPDFReal m v w := by
  rw [gaussianPDFReal_def, gaussianPDFReal_def]
  simp only
  congr 2
  ring

theorem integrable_pdf_mul (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable fun u => gaussianPDFReal m v u * u := by
  have h : Integrable id (gaussianReal m v) := MemLp.integrable (by norm_num) (memLp_id_gaussianReal 1)
  rw [gaussianReal_of_var_ne_zero m hv, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF m v) (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at h
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg m v u)]

theorem integral_pdf_mul (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : ∫ u, gaussianPDFReal m v u * u = m := by
  have := integral_id_gaussianReal (μ := m) (v := v)
  rw [integral_gaussianReal_eq_integral_smul hv] at this
  simpa using this

/-- AX-54's one-step normalization, proved. -/
theorem kernelNorm2_holds : KernelNorm2 := by
  intro κ Δ x hκ hΔ hx
  set v : ℝ := κ ^ 2 * Δ with hvdef
  have hv : 0 < v := mul_pos (pow_pos hκ 2) hΔ
  set V : ℝ≥0 := v.toNNReal
  have hVc : (V : ℝ) = v := Real.coe_toNNReal _ hv.le
  have hV : V ≠ 0 := by rw [← NNReal.coe_ne_zero, hVc]; exact hv.ne'
  set c := 1 / x
  set h : ℝ → ℝ := fun u => x * (gaussianPDFReal c V u * u - gaussianPDFReal (-c) V u * u)
  -- The integrand after `u = 1/y`.
  have hreal : ∀ u, 0 < u → (u ^ 2)⁻¹ * f2 κ Δ x u⁻¹ = h u := fun u hu => by
    simp only [h, f2, gaussianPDFReal_def, hVc, one_div_one_div, inv_inv, ← hvdef]
    rw [show (u - -c) = u + c by ring]
    simp only [c]
    have hs : 0 < √(2 * π * v) := Real.sqrt_pos.2 (mul_pos (mul_pos two_pos Real.pi_pos) hv)
    field_simp
  have himage : (fun u : ℝ => u⁻¹) '' Ioi 0 = Ioi 0 := by
    ext y
    simp only [mem_image, mem_Ioi]
    exact ⟨fun ⟨u, hu, hy⟩ => hy ▸ inv_pos.2 hu, fun hy => ⟨y⁻¹, inv_pos.2 hy, inv_inv y⟩⟩
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (f := fun u : ℝ => u⁻¹) (f' := fun u => -(u ^ 2)⁻¹)
    (fun u hu => (hasDerivAt_inv (ne_of_gt hu)).hasDerivWithinAt) inv_injective.injOn
    (fun y => ENNReal.ofReal (f2 κ Δ x y))
  rw [himage] at hcv
  have hIoi : IntegrableOn h (Ioi 0) :=
    ((integrable_pdf_mul c hV).sub (integrable_pdf_mul (-c) hV)).const_mul x |>.integrableOn
  have hR : ∫⁻ y, ENNReal.ofReal (f2 κ Δ x y) ∂posVol =
      ∫⁻ y in Ioi 0, ENNReal.ofReal (f2 κ Δ x y) := by
    rw [posVol, ← lintegral_subtype_comap measurableSet_Ioi]; rfl
  rw [hR, hcv]
  rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun u => ENNReal.ofReal (h u)) fun u hu => by
    rw [abs_neg, abs_of_pos (inv_pos.2 (pow_pos hu 2)), ← ENNReal.ofReal_mul
      (inv_pos.2 (pow_pos hu 2)).le, hreal u hu]]
  rw [← ofReal_integral_eq_lintegral_ofReal hIoi (ae_restrict_of_forall_mem measurableSet_Ioi
    fun u hu => by
      rw [← hreal u hu]
      exact mul_nonneg (inv_pos.2 (pow_pos hu 2)).le
        (f2_pos hκ hΔ hx (inv_pos.2 hu)).le)]
  rw [← ENNReal.ofReal_one]
  congr 1
  -- `∫_(0,∞) h = x (∫_(0,∞) u φ(c) − ∫_(0,∞) u φ(−c)) = x ∫_ℝ u φ(c) = x c = 1`.
  have hneg : ∫ u in Ioi 0, gaussianPDFReal (-c) V u * u =
      -∫ w in Iic 0, gaussianPDFReal c V w * w := by
    have h1 : ∫ u in Ioi (0 : ℝ), gaussianPDFReal (-c) V u * u =
        ∫ u in Ioi (0 : ℝ), (fun w => -(gaussianPDFReal c V w * w)) (-u) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      simp only
      rw [show gaussianPDFReal c V (-u) = gaussianPDFReal (-c) V u by
        rw [← gpdf_reflect (-c) V u, neg_neg]]
      ring
    rw [h1, integral_comp_neg_Ioi (0 : ℝ) (fun w => -(gaussianPDFReal c V w * w)), neg_zero,
      integral_neg]
  simp only [h]
  rw [integral_const_mul, integral_sub (integrable_pdf_mul c hV).integrableOn
    (integrable_pdf_mul (-c) hV).integrableOn, hneg, sub_neg_eq_add,
    show Iic (0 : ℝ) = (Ioi 0)ᶜ from compl_Ioi.symm, integral_add_compl measurableSet_Ioi (integrable_pdf_mul c hV),
    integral_pdf_mul c hV]
  simp only [c]
  field_simp

end Novel.D30SmallScale
