import Standalone.D28PredictableIV
import Novel.D17ClockDriftProfile

/-!
# Claim 042, part 1: the band-restricted profile

* **The product.** On a positive record, the product of normal return densities is claim 033's price
  density times `Π S_j`, so claim 033's `log_gV` gives
  `log G = ψ(w) − A_v (b − b(w))²/(2w)`, with
  `ψ(w) = −(n/2) log(2π) − (1/2)Σ log v_j − (n/2) log w − Q_v/(2w) − K_v/2 − wH_v/8`.
* **The clipped scale.** With `4Q_v = H_v w*² + 4n w*` (claim 033's `wstar_root`) and
  `log(c/w) ≤ c/w − 1`,
  `ψ(c) − ψ(w) ≥ (c − w)(H_v(w*² − wc) + 4n(w* − c))/(8wc)`,
  which is `≥ 0` whenever `c` lies between `w` and `w*`. Clipping `w*` to the band puts it between
  every band point and `w*`. For `Q_v = 0`, `ψ` is decreasing, so the lower endpoint is optimal.
  No calculus is needed.
-/

open Real Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Novel.D28PredictableIV

open Standalone.D28PredictableIV Standalone.D17ClockDrift Standalone.D13DriftNull
  Novel.D17ClockDrift

variable {n : ℕ} {Δ v : Fin n → ℝ}

theorem pIV_eq (Δ' v' b w r : ℝ) (hwv : 0 < w * v') :
    pIV Δ' v' b w r = Real.exp (-(r - b * Δ' + w * v' / 2) ^ 2 / (2 * w * v')) /
      Real.sqrt (2 * π * w * v') := by
  unfold pIV
  rw [gaussianPDFReal_def, Real.coe_toNNReal _ hwv.le, div_eq_inv_mul (Real.exp _)]
  ring_nf

theorem pIV_pos (Δ' v' b w r : ℝ) (hwv : 0 < w * v') : 0 < pIV Δ' v' b w r := by
  rw [pIV_eq _ _ _ _ _ hwv]
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.2 (by rw [mul_assoc]; positivity))

theorem Gfin_pos (hv : ∀ j, 0 < v j) {w : ℝ} (hw : 0 < w) (b y0 : ℝ) (y : Fin n → ℝ) :
    0 < Gfin Δ v b w y0 y :=
  prod_pos fun j _ => pIV_pos _ _ _ _ _ (mul_pos hw (hv j))

/-- Claim 033's price density is the return-density product over the price Jacobian. -/
theorem gV_mul (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ} (hp : PosPath y0 y) (b : ℝ) {w : ℝ}
    (hw : 0 < w) : gV Δ v b w y0 y * ∏ j, y j = Gfin Δ v b w y0 y := by
  unfold gV Gfin
  rw [ite_eq_left hp, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [pIV_eq _ _ _ _ _ (mul_pos hw (hv j))]
  have := (hp.2 j).ne'
  have : Real.sqrt (2 * π * w * v j) ≠ 0 :=
    (Real.sqrt_pos.2 (by have := hv j; positivity)).ne'
  field_simp

/-- `ψ`, the log profile at `b = b(w)`. -/
noncomputable def psi (Δ v : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (w : ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log (2 * π) - (1 / 2) * ∑ j, Real.log (v j) -
    ((n : ℝ) / 2) * Real.log w - Qv Δ v y0 y / (2 * w) - Kv Δ v y0 y / 2 - w * Hv Δ v / 8

theorem logDIV_eq (wL wH y0 : ℝ) (y : Fin n → ℝ) :
    logDIV Δ v wL wH y0 y = psi Δ v y0 y (wIV Δ v wL wH y0 y) := rfl

theorem Gfin_eq (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ}
    (hp : PosPath y0 y) (b : ℝ) {w : ℝ} (hw : 0 < w) :
    Gfin Δ v b w y0 y = Real.exp (psi Δ v y0 y w -
      Av Δ v * (b - (Bv Δ v y0 y + w * (∑ j, Δ j) / 2) / Av Δ v) ^ 2 / (2 * w)) := by
  rw [← gV_mul hv hp b hw, log_gV hn hΔ hv hp b hw,
    show ∏ j, y j = Real.exp (∑ j, Real.log (y j)) by
      rw [Real.exp_sum]; exact prod_congr rfl fun j _ => (Real.exp_log (hp.2 j)).symm,
    ← Real.exp_add]
  congr 1
  unfold phi psi c0
  rw [Real.log_mul (by positivity) hw.ne']
  ring

/-- `ψ(w) ≤ ψ(c)` when `c` lies between `w` and `w*`. -/
theorem psi_le (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ}
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (h : (w ≤ c ∧ c ≤ wstar Δ v y0 y) ∨ (wstar Δ v y0 y ≤ c ∧ c ≤ w)) :
    psi Δ v y0 y w ≤ psi Δ v y0 y c := by
  have hroot := wstar_root hn hΔ hv (y0 := y0) (y := y)
  have hH := Hv_nonneg hn hΔ hv
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set ws := wstar Δ v y0 y
  set Q := Qv Δ v y0 y
  set H := Hv Δ v
  have hlog : Real.log c - Real.log w ≤ c / w - 1 := by
    rw [← Real.log_div hc.ne' hw.ne']; exact Real.log_le_sub_one_of_pos (div_pos hc hw)
  have hkey : Q / (2 * w) - Q / (2 * c) - (c - w) * H / 8 - (n / 2) * (c / w - 1) =
      (c - w) * (H * (ws ^ 2 - w * c) + 4 * n * (ws - c)) / (8 * w * c) := by
    rw [show Q = (H * ws ^ 2 + 4 * n * ws) / 4 by linarith]
    field_simp
    ring
  have hprod : 0 ≤ (c - w) * (H * (ws ^ 2 - w * c) + 4 * n * (ws - c)) := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : w * c ≤ ws ^ 2 := by nlinarith
      exact mul_nonneg (by linarith) (by nlinarith)
    · have : ws ^ 2 ≤ w * c := by
        have := (wstar_pos hn (Δ := Δ) (v := v) (y0 := y0) (y := y))
        by_cases hQ : 0 < Q
        · nlinarith [this hQ]
        · have hQ0 : Q = 0 := le_antisymm (not_lt.1 hQ) (Qv_nonneg hn hΔ hv y0 y)
          have : ws = 0 := by
            show wstar Δ v y0 y = 0
            unfold wstar; rw [show Qv Δ v y0 y = 0 from hQ0]; simp
          rw [this, sq, zero_mul]; positivity
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by nlinarith)
  have hfrac : 0 ≤ (c - w) * (H * (ws ^ 2 - w * c) + 4 * n * (ws - c)) / (8 * w * c) := by
    positivity
  unfold psi
  nlinarith

theorem wIV_mem (hLH : wL ≤ wH) (y0 : ℝ) (y : Fin n → ℝ) :
    wIV Δ v wL wH y0 y ∈ Set.Icc wL wH := by
  unfold wIV
  split_ifs
  · exact ⟨le_rfl, hLH⟩
  · exact ⟨le_min hLH (le_max_left _ _), min_le_left _ _⟩

/-- The clipped scale maximizes `ψ` over the band. -/
theorem psi_le_wIV (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ}
    {wL wH : ℝ} (hL : 0 < wL) (hLH : wL ≤ wH) {w : ℝ} (hw : w ∈ Set.Icc wL wH) :
    psi Δ v y0 y w ≤ psi Δ v y0 y (wIV Δ v wL wH y0 y) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hw0 : 0 < w := hL.trans_le hw.1
  by_cases hQ : Qv Δ v y0 y = 0
  · rw [show wIV Δ v wL wH y0 y = wL by unfold wIV; rw [ite_eq_left hQ]]
    have hH := Hv_nonneg hn hΔ hv
    have h1 := mul_le_mul_of_nonneg_left (Real.log_le_log hL hw.1) (by positivity : (0 : ℝ) ≤ n / 2)
    have h2 := mul_le_mul_of_nonneg_right hw.1 hH
    unfold psi
    rw [hQ]
    simp only [zero_div, sub_zero]
    linarith
  · have hQp : 0 < Qv Δ v y0 y := lt_of_le_of_ne (Qv_nonneg hn hΔ hv y0 y) (Ne.symm hQ)
    have hs := wstar_pos hn (Δ := Δ) (v := v) hQp
    have he : wIV Δ v wL wH y0 y = min wH (max wL (wstar Δ v y0 y)) := by
      unfold wIV; rw [ite_eq_right hQ]
    have hc := (wIV_mem (Δ := Δ) (v := v) hLH y0 y)
    rw [he] at hc ⊢
    refine psi_le hn hΔ hv hw0 (hL.trans_le hc.1) ?_
    set ws := wstar Δ v y0 y
    rcases le_total ws wL with h1 | h1
    · rw [max_eq_left h1, min_eq_right hLH]
      exact Or.inr ⟨h1, hw.1⟩
    · rw [max_eq_right h1]
      rcases le_total ws wH with h2 | h2
      · rw [min_eq_right h2]
        rcases le_total w ws with h3 | h3
        · exact Or.inl ⟨h3, le_rfl⟩
        · exact Or.inr ⟨le_rfl, h3⟩
      · rw [min_eq_left h2]
        exact Or.inl ⟨hw.2, h2⟩

theorem Gfin_le (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ}
    (hp : PosPath y0 y) {wL wH : ℝ} (hL : 0 < wL) (hLH : wL ≤ wH) (b : ℝ) {w : ℝ}
    (hw : w ∈ Set.Icc wL wH) : Gfin Δ v b w y0 y ≤ Real.exp (logDIV Δ v wL wH y0 y) := by
  have hw0 : 0 < w := hL.trans_le hw.1
  have hA := Av_pos hn hΔ hv
  rw [Gfin_eq hn hΔ hv hp b hw0, logDIV_eq]
  have : 0 ≤ Av Δ v * (b - (Bv Δ v y0 y + w * (∑ j, Δ j) / 2) / Av Δ v) ^ 2 / (2 * w) := by
    positivity
  exact Real.exp_le_exp.2 (by linarith [psi_le_wIV hn hΔ hv (y0 := y0) (y := y) hL hLH hw])

theorem Gfin_attain (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ}
    (hp : PosPath y0 y) {wL wH : ℝ} (hL : 0 < wL) (hLH : wL ≤ wH) :
    Gfin Δ v (bIV Δ v wL wH y0 y) (wIV Δ v wL wH y0 y) y0 y = Real.exp (logDIV Δ v wL wH y0 y) := by
  rw [Gfin_eq hn hΔ hv hp _ (hL.trans_le (wIV_mem hLH y0 y).1), logDIV_eq]
  unfold bIV
  rw [sub_self, sq, zero_mul, mul_zero, zero_div, sub_zero]

theorem Dband_eq (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ}
    (hp : PosPath y0 y) {wL wH : ℝ} (hL : 0 < wL) (hLH : wL ≤ wH) :
    Dband Δ v wL wH y0 y = ENNReal.ofReal (Real.exp (logDIV Δ v wL wH y0 y)) := by
  refine le_antisymm (iSup₂_le fun b w => iSup_le fun hw =>
    ENNReal.ofReal_le_ofReal (Gfin_le hn hΔ hv hp hL hLH b hw)) ?_
  rw [← Gfin_attain hn hΔ hv hp hL hLH]
  exact le_iSup₂_of_le (f := fun (b : ℝ) (w : ℝ) => ⨆ (_ : w ∈ Set.Icc wL wH),
    ENNReal.ofReal (Gfin Δ v b w y0 y)) (bIV Δ v wL wH y0 y) (wIV Δ v wL wH y0 y)
    (le_iSup_of_le (wIV_mem hLH y0 y) le_rfl)

/-! ## Measurability in the whole record -/

section Meas

variable {Δ : Fin n → ℝ}

theorem measurable_retx (j : Fin n) :
    Measurable fun x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) => ret x.2.1 x.2.2 j :=
  (Novel.D13DriftNull.measurable_ret j).comp measurable_snd

theorem measurable_vx (j : Fin n) : Measurable fun x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) => x.1 j :=
  (measurable_pi_apply j).comp measurable_fst

theorem measurable_Avx : Measurable fun x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) => Av Δ x.1 :=
  Finset.measurable_sum _ fun j _ => measurable_const.div (measurable_vx j)

theorem measurable_Bvx : Measurable fun x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) => Bv Δ x.1 x.2.1 x.2.2 :=
  Finset.measurable_sum _ fun j _ => ((measurable_retx j).const_mul _).div (measurable_vx j)

theorem measurable_Qvx : Measurable fun x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) => Qv Δ x.1 x.2.1 x.2.2 :=
  (Finset.measurable_sum _ fun j _ => ((measurable_retx j).pow_const 2).div (measurable_vx j)).sub
    ((measurable_Bvx.pow_const 2).div measurable_Avx)

theorem measurable_Kvx : Measurable fun x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) => Kv Δ x.1 x.2.1 x.2.2 :=
  (Finset.measurable_sum _ fun j _ => measurable_retx j).sub
    ((measurable_Bvx.mul_const _).div measurable_Avx)

theorem measurable_Hvx : Measurable fun x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) => Hv Δ x.1 :=
  (Finset.measurable_sum _ fun j _ => measurable_vx j).sub (measurable_const.div measurable_Avx)

theorem measurable_logDIVx (wL wH : ℝ) :
    Measurable fun x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) => logDIV Δ x.1 wL wH x.2.1 x.2.2 := by
  classical
  have hws : Measurable fun x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) => wstar Δ x.1 x.2.1 x.2.2 :=
    (measurable_Qvx.const_mul _).div
      (measurable_const.add ((measurable_const.add (measurable_Hvx.mul measurable_Qvx)).sqrt))
  have hw : Measurable fun x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) => wIV Δ x.1 wL wH x.2.1 x.2.2 :=
    Measurable.ite (measurableSet_eq_fun measurable_Qvx measurable_const) measurable_const
      (measurable_const.min (measurable_const.max hws))
  unfold logDIV
  exact (((((measurable_const.sub ((Finset.measurable_sum _ fun j _ =>
    Real.measurable_log.comp (measurable_vx j)).const_mul _)).sub
      (measurable_const.mul (Real.measurable_log.comp hw))).sub
        (measurable_Qvx.div (hw.const_mul _))).sub (measurable_Kvx.div_const _)).sub
          ((hw.mul measurable_Hvx).div_const _))

theorem measurableSet_posx :
    MeasurableSet {x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) | (∀ j, 0 < x.1 j) ∧ PosPath x.2.1 x.2.2} := by
  have : {x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) | (∀ j, 0 < x.1 j) ∧ PosPath x.2.1 x.2.2} =
      (⋂ j, {x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) | 0 < x.1 j}) ∩ Prod.snd ⁻¹' {x : ℝ × (Fin n → ℝ) | PosPath x.1 x.2} := by
    ext x; simp
  rw [this]
  exact (MeasurableSet.iInter fun j => measurableSet_lt measurable_const (measurable_vx j)).inter
    (measurable_snd Novel.D13DriftNull.measurableSet_pos)

theorem measurable_Dband (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) {wL wH : ℝ} (hL : 0 < wL)
    (hLH : wL ≤ wH) :
    Measurable ({x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) | (∀ j, 0 < x.1 j) ∧ PosPath x.2.1 x.2.2}.indicator
      fun x => Dband Δ x.1 wL wH x.2.1 x.2.2) := by
  have : ({x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) | (∀ j, 0 < x.1 j) ∧ PosPath x.2.1 x.2.2}.indicator
      fun x => Dband Δ x.1 wL wH x.2.1 x.2.2) =
      {x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) | (∀ j, 0 < x.1 j) ∧ PosPath x.2.1 x.2.2}.indicator
      fun x => ENNReal.ofReal (Real.exp (logDIV Δ x.1 wL wH x.2.1 x.2.2)) :=
    Set.indicator_congr fun x hx => Dband_eq hn hΔ hx.1 hx.2 hL hLH
  rw [this]
  exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_logDIVx wL wH))).indicator
    measurableSet_posx

end Meas

theorem profile_holds : Standalone.D28PredictableIV.profile := by
  intro n Δ v wL wH y0 y hn hΔ hv hL hLH hp
  exact ⟨Av_pos hn hΔ hv, Qv_nonneg hn hΔ hv y0 y, Hv_nonneg hn hΔ hv, wIV_mem hLH y0 y,
    Gfin_attain hn hΔ hv hp hL hLH, fun b w hw => Gfin_le hn hΔ hv hp hL hLH b hw,
    Dband_eq hn hΔ hv hp hL hLH, measurable_Dband hn hΔ hL hLH,
    fun b w hw => gV_mul hv hp b hw⟩

end Novel.D28PredictableIV
