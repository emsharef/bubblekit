import Novel.D19FilteredLikelihoodQuad

/-!
# Claim 036, part 3: one step's density under a parameter change

With `X = R − bΔ`, the log density of the step is `−½ log(2π w v) − X²/(2wv) − X/2 − wv/8`.
* Changing `b` moves it by `(b₁ − b₂)Δ (X₁ + X₂ + wv)/(2wv)`, at most `|b₁ − b₂| Δ C_j`.
* Changing `w` moves `−½ log w` by at most `|w₁ − w₂|/(2 w_L)` (from `log x ≤ x − 1`), `X²/(2wv)` by
  at most `|w₁ − w₂| X²/(2 w_L² v)`, and `wv/8` by `|w₁ − w₂| v/8`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick Standalone.D17ClockCells

/-- The step's log density. -/
noncomputable def lpdf (Δ v b w R : ℝ) : ℝ :=
  -(1 / 2) * Real.log (2 * Real.pi * (w * v)) - (R - b * Δ) ^ 2 / (2 * (w * v)) -
    (R - b * Δ) / 2 - w * v / 8

theorem pdf_eq_exp {Δ v b w R : ℝ} (hv : 0 < v) (hw : 0 < w) :
    gaussianPDFReal (b * Δ - w * v / 2) (w * v).toNNReal R = Real.exp (lpdf Δ v b w R) := by
  have hwv : 0 < w * v := mul_pos hw hv
  unfold gaussianPDFReal lpdf
  rw [Real.coe_toNNReal _ hwv.le]
  have hsq : Real.sqrt (2 * Real.pi * (w * v)) = Real.exp ((1 / 2) * Real.log (2 * Real.pi * (w * v))) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity), mul_comm]
  rw [hsq, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem log_ratio_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {c : ℝ} (hc : 0 < c) (hac : c ≤ a)
    (hbc : c ≤ b) : |Real.log a - Real.log b| ≤ |a - b| / c := by
  rw [abs_le]
  constructor
  · have := Real.log_le_sub_one_of_pos (div_pos hb ha)
    rw [Real.log_div hb.ne' ha.ne'] at this
    have h2 : b / a - 1 ≤ |a - b| / c := by
      rw [div_sub_one ha.ne']
      calc (b - a) / a ≤ |a - b| / a := div_le_div_of_nonneg_right (by rw [abs_sub_comm]; exact le_abs_self _) ha.le
        _ ≤ |a - b| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc hac
    linarith
  · have := Real.log_le_sub_one_of_pos (div_pos ha hb)
    rw [Real.log_div ha.ne' hb.ne'] at this
    have h2 : a / b - 1 ≤ |a - b| / c := by
      rw [div_sub_one hb.ne']
      calc (a - b) / b ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb.le
        _ ≤ |a - b| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc hbc
    linarith

/-- The log-density change under a change of `(b, w)` within a box. -/
theorem lpdf_diff {B : Box} (hB : B.Valid) {b₁ w₁ b₂ w₂ : ℝ} (h1 : B.Mem (b₁, w₁))
    (h2 : B.Mem (b₂, w₂)) {Δ v R Rm : ℝ} (hΔ : 0 < Δ) (hv : 0 < v) (hR : |R| ≤ Rm) :
    |lpdf Δ v b₁ w₁ R - lpdf Δ v b₂ w₂ R| ≤
      |b₁ - b₂| * (Δ * ((Rm + Bmax B * Δ + B.wH * v / 2) / (B.wL * v))) +
      |w₁ - w₂| * (1 / (2 * B.wL) + (Rm + Bmax B * Δ) ^ 2 / (2 * B.wL ^ 2 * v) + v / 8) := by
  have hwL := hB.2.1
  have hw1 : 0 < w₁ := hwL.trans_le h1.2.1
  have hw2 : 0 < w₂ := hwL.trans_le h2.2.1
  have hBm : ∀ b, b ∈ Icc B.bL B.bH → |b| ≤ Bmax B := fun b hb => abs_le_max_of_mem hb.1 hb.2
  have hX : ∀ b, b ∈ Icc B.bL B.bH → |R - b * Δ| ≤ Rm + Bmax B * Δ := fun b hb => by
    calc |R - b * Δ| ≤ |R| + |b * Δ| := abs_sub _ _
      _ = |R| + |b| * Δ := by rw [abs_mul, abs_of_pos hΔ]
      _ ≤ _ := by have := mul_le_mul_of_nonneg_right (hBm b hb) hΔ.le; linarith
  -- The `b` part, at scale `w₁`.
  have hbpart : |lpdf Δ v b₁ w₁ R - lpdf Δ v b₂ w₁ R| ≤
      |b₁ - b₂| * (Δ * ((Rm + Bmax B * Δ + B.wH * v / 2) / (B.wL * v))) := by
    have e : lpdf Δ v b₁ w₁ R - lpdf Δ v b₂ w₁ R = (b₁ - b₂) * Δ *
        (((R - b₁ * Δ) + w₁ * v / 2) + ((R - b₂ * Δ) + w₁ * v / 2)) / (2 * (w₁ * v)) := by
      unfold lpdf; field_simp; ring
    have hY : ∀ b, b ∈ Icc B.bL B.bH → |(R - b * Δ) + w₁ * v / 2| ≤ Rm + Bmax B * Δ + B.wH * v / 2 :=
      fun b hb => by
        calc |(R - b * Δ) + w₁ * v / 2| ≤ |R - b * Δ| + |w₁ * v / 2| := abs_add_le _ _
          _ ≤ _ := by
              rw [abs_of_pos (by positivity : 0 < w₁ * v / 2)]
              have := mul_le_mul_of_nonneg_right h1.2.2 hv.le; linarith [hX b hb]
    rw [e, abs_div, abs_mul, abs_mul, abs_of_pos hΔ, abs_of_pos (by positivity : 0 < 2 * (w₁ * v))]
    have hsum := (abs_add_le _ _).trans (add_le_add (hY b₁ h1.1) (hY b₂ h2.1))
    have hnum : 0 ≤ Rm + Bmax B * Δ + B.wH * v / 2 := by
      have := (abs_nonneg R).trans hR; have := (abs_nonneg b₁).trans (hBm b₁ h1.1)
      have := hwL.trans_le hB.2.2; positivity
    calc |b₁ - b₂| * Δ * |(R - b₁ * Δ + w₁ * v / 2) + (R - b₂ * Δ + w₁ * v / 2)| / (2 * (w₁ * v))
        ≤ |b₁ - b₂| * Δ * (2 * (Rm + Bmax B * Δ + B.wH * v / 2)) / (2 * (w₁ * v)) := by
          gcongr; linarith
      _ = |b₁ - b₂| * (Δ * ((Rm + Bmax B * Δ + B.wH * v / 2) / (w₁ * v))) := by field_simp
      _ ≤ _ := by
          gcongr
          exact h1.2.1
  -- The `w` part, at `b₂`.
  have hwpart : |lpdf Δ v b₂ w₁ R - lpdf Δ v b₂ w₂ R| ≤
      |w₁ - w₂| * (1 / (2 * B.wL) + (Rm + Bmax B * Δ) ^ 2 / (2 * B.wL ^ 2 * v) + v / 8) := by
    set X := R - b₂ * Δ
    have hX2 : X ^ 2 ≤ (Rm + Bmax B * Δ) ^ 2 := by
      have := hX b₂ h2.1; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have e : lpdf Δ v b₂ w₁ R - lpdf Δ v b₂ w₂ R =
        -(1 / 2) * (Real.log w₁ - Real.log w₂) + X ^ 2 / (2 * v) * ((w₁ - w₂) / (w₁ * w₂)) -
          (w₁ - w₂) * v / 8 := by
      have hl : ∀ w : ℝ, 0 < w → Real.log (2 * Real.pi * (w * v)) =
          Real.log (2 * Real.pi) + Real.log w + Real.log v := fun w hw => by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hw.ne' hv.ne']; ring
      unfold lpdf
      rw [hl w₁ hw1, hl w₂ hw2]
      field_simp; ring
    have hlog := log_ratio_le hw1 hw2 hwL h1.2.1 h2.2.1
    have hprod : B.wL ^ 2 ≤ w₁ * w₂ := by
      rw [sq]; exact mul_le_mul h1.2.1 h2.2.1 hwL.le hw1.le
    have hfrac : |(w₁ - w₂) / (w₁ * w₂)| ≤ |w₁ - w₂| / B.wL ^ 2 := by
      rw [abs_div, abs_of_pos (mul_pos hw1 hw2)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hprod
    rw [e]
    calc |-(1 / 2) * (Real.log w₁ - Real.log w₂) + X ^ 2 / (2 * v) * ((w₁ - w₂) / (w₁ * w₂)) -
          (w₁ - w₂) * v / 8|
        ≤ (1 / 2) * |Real.log w₁ - Real.log w₂| + X ^ 2 / (2 * v) * |(w₁ - w₂) / (w₁ * w₂)| +
            |w₁ - w₂| * v / 8 := by
          refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
          · rw [abs_mul]; norm_num
          · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ X ^ 2 / (2 * v))]
          · rw [abs_div, abs_mul, abs_of_pos hv, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
      _ ≤ (1 / 2) * (|w₁ - w₂| / B.wL) + (Rm + Bmax B * Δ) ^ 2 / (2 * v) * (|w₁ - w₂| / B.wL ^ 2) +
            |w₁ - w₂| * v / 8 := by
          gcongr
      _ = _ := by field_simp
  calc |lpdf Δ v b₁ w₁ R - lpdf Δ v b₂ w₂ R|
      = |(lpdf Δ v b₁ w₁ R - lpdf Δ v b₂ w₁ R) + (lpdf Δ v b₂ w₁ R - lpdf Δ v b₂ w₂ R)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hbpart hwpart)

end Novel.D19FilteredLikelihood
