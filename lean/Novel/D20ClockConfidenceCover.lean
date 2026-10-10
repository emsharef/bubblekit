import Novel.D20ClockConfidenceSet

/-!
# Claim 067, part 1: clock coverage (3)

Fix a Gaussian component with clock `v`. Each reference density is claim 033's `g_(v,b_a,w_a)`,
at most its profile `D_(a,v)` (part 1 of claim 033), and each profile is positive on positive
arrays. So on positive reference arrays `T_v · ∏_a g_a ≤ q^ref`, and the statistic has mean at
most `∫ q^ref ≤ 1` under the actual reference law (AX-58's pointwise step). If `v` is excluded,
the reference inputs are positive and `T_v > 1/δ`, so Markov's inequality gives (3). No union
over the catalogue is involved.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal

namespace Novel.D20ClockConfidence

open Standalone.D20ClockConfidence Standalone.CEVSupport Standalone.D13DriftNull
  Standalone.D17ClockDrift

variable {r m : ℕ}

/-- Claim 033's profile is positive on positive paths. -/
theorem Dv_pos {Δ v : Fin m → ℝ} {y0 : ℝ} {y : Fin m → ℝ} (hp : PosPath y0 y) :
    0 < Dv Δ v y0 y := by
  unfold Dv
  simp only [hp, ↓reduceIte]
  split_ifs
  · exact ENNReal.ofReal_pos.2 (Real.exp_pos _)
  · exact ENNReal.zero_lt_top

/-- Claim 033's density is at most its profile. -/
theorem gV_le_Dv (hm : 0 < m) {Δ v : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j)
    (b : ℝ) {w : ℝ} (hw : 0 < w) (y0 : ℝ) (y : Fin m → ℝ) :
    ENNReal.ofReal (gV Δ v b w y0 y) ≤ Dv Δ v y0 y := by
  rw [← Novel.D17ClockDrift.sup_eq hm hΔ hv y0 y]
  exact le_iSup_of_le b (le_iSup_of_le w (le_iSup_of_le hw le_rfl))

/-- On positive reference arrays, `T_v` times the actual reference density is at most `q^ref`. -/
theorem Tref_mul_le (hm : 0 < m) {Δ v : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j)
    {s : Fin r → ℝ} {W : Fin r → Fin m → NNR} (hpos : RefPos s W) (bw : Fin r → ℝ × ℝ)
    (hbw : ∀ a, 0 < (bw a).2) {qr : ℝ} :
    Tref Δ v s qr W * ∏ a, ENNReal.ofReal (gV Δ v (bw a).1 (bw a).2 (s a) fun l => (W a l : ℝ)) ≤
      ENNReal.ofReal qr := by
  have hG : (∏ a, ENNReal.ofReal (gV Δ v (bw a).1 (bw a).2 (s a) fun l => (W a l : ℝ))) ≤
      Dref Δ v s W :=
    Finset.prod_le_prod fun a _ => gV_le_Dv hm hΔ hv _ (hbw a) _ _
  have hD0 : Dref Δ v s W ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => (Dv_pos (hpos a)).ne'
  unfold Tref
  by_cases hDt : Dref Δ v s W = ⊤
  · rw [hDt, ENNReal.div_top, zero_mul]; exact zero_le
  calc ENNReal.ofReal qr / Dref Δ v s W *
        ∏ a, ENNReal.ofReal (gV Δ v (bw a).1 (bw a).2 (s a) fun l => (W a l : ℝ))
      ≤ ENNReal.ofReal qr / Dref Δ v s W * Dref Δ v s W := by gcongr
    _ = ENNReal.ofReal qr := ENNReal.div_mul_cancel hD0 hDt

/-- (3) for one Gaussian component: under the actual reference law, the true clock is excluded
with probability at most `δ`. -/
theorem cover_ref (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) {Δ v : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j)
    (hv : ∀ j, 0 < v j) {𝒱 : Finset (Fin m → ℝ)} (hv𝒱 : v ∈ 𝒱) (s : Fin r → ℝ)
    {qr : (Fin r → Fin m → NNR) → ℝ} (hqm : Measurable qr)
    (hqn : ∫⁻ w in {w | RefPos s w}, ENNReal.ofReal (qr w)
      ∂(Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin m => muCEV) ≤ 1)
    (bw : Fin r → ℝ × ℝ) (hbw : ∀ a, 0 < (bw a).2) :
    ((Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin m => muCEV).withDensity fun w =>
        ∏ a, ENNReal.ofReal (gV Δ v (bw a).1 (bw a).2 (s a) fun l => (w a l : ℝ)))
      {w | v ∉ Csel δ Δ 𝒱 s (qr w) w} ≤ ENNReal.ofReal δ := by
  classical
  set μr : Measure (Fin r → Fin m → NNR) := Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin m =>
    muCEV
  set G : (Fin r → Fin m → NNR) → ℝ≥0∞ := fun w =>
    ∏ a, ENNReal.ofReal (gV Δ v (bw a).1 (bw a).2 (s a) fun l => (w a l : ℝ))
  set R := {w : Fin r → Fin m → NNR | RefPos s w}
  have hR : MeasurableSet R := measurableSet_RefPos measurable_const measurable_id
  have hG : Measurable G := by
    refine Finset.measurable_prod _ fun a _ => ENNReal.measurable_ofReal.comp ?_
    have hy : Measurable fun w : Fin r → Fin m → NNR => fun l => (w a l : ℝ) :=
      measurable_pi_iff.2 fun l => measurable_subtype_coe.comp ((measurable_pi_apply l).comp
        (measurable_pi_apply a))
    have := (Novel.D17ClockDrift.measurable_gV (Δ := Δ) (v := v) (bw a).1 (bw a).2).comp
      ((measurable_const (a := s a)).prodMk hy)
    exact this
  set T : (Fin r → Fin m → NNR) → ℝ≥0∞ := fun w => R.indicator (fun w => Tref Δ v s (qr w) w) w
  have hT : Measurable T :=
    (measurable_Tref (s := fun _ => s) measurable_const hqm measurable_id).indicator hR
  -- The excluded event: positive inputs and `T_v > 1/δ`.
  have hsub : {w | v ∉ Csel δ Δ 𝒱 s (qr w) w} ⊆ {w | ENNReal.ofReal (1 / δ) ≤ T w} := by
    intro w hw
    simp only [mem_ofPred_eq] at hw ⊢
    by_cases hp : RefPos s w
    · have hT' : ¬ Tref Δ v s (qr w) w ≤ ENNReal.ofReal (1 / δ) := fun h => hw (by
        unfold Csel; simp only [hp, ↓reduceIte]
        exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hv𝒱, h⟩))
      simp only [T, indicator_of_mem (show w ∈ R from hp)]
      exact (not_le.1 hT').le
    · exact absurd (by unfold Csel; simp only [hp, ↓reduceIte]; exact hv𝒱) hw
  -- AX-58's pointwise step: the statistic has mean at most one.
  have hmean : ∫⁻ w, T w ∂(μr.withDensity G) ≤ 1 := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hG hT]
    calc ∫⁻ w, (G * T) w ∂μr ≤ ∫⁻ w, R.indicator (fun w => ENNReal.ofReal (qr w)) w ∂μr :=
          lintegral_mono fun w => by
            simp only [Pi.mul_apply, T]
            by_cases hp : w ∈ R
            · rw [indicator_of_mem hp, indicator_of_mem hp, mul_comm]
              exact Tref_mul_le hm hΔ hv hp bw hbw
            · rw [indicator_of_notMem hp, indicator_of_notMem hp, mul_zero]
      _ = ∫⁻ w in R, ENNReal.ofReal (qr w) ∂μr := lintegral_indicator hR _
      _ ≤ 1 := hqn
  have hmk := mul_meas_ge_le_lintegral₀ (μ := μr.withDensity G) hT.aemeasurable
    (ENNReal.ofReal (1 / δ))
  have hle : ENNReal.ofReal (1 / δ) * (μr.withDensity G) {w | v ∉ Csel δ Δ 𝒱 s (qr w) w} ≤ 1 :=
    (mul_le_mul_right (measure_mono hsub) _).trans (hmk.trans hmean)
  have hinv : (ENNReal.ofReal (1 / δ))⁻¹ = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
  rw [← hinv, ENNReal.le_inv_iff_mul_le, mul_comm]
  exact hle

end Novel.D20ClockConfidence
