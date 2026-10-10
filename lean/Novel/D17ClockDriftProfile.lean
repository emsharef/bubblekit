import Novel.D17ClockDriftAlgebra
import Novel.D13DriftProfileProof
import Novel.D15SwitchNull

/-!
# Claim 033, part 1: the clock profile

* **The log density.** On a positive path with `w > 0`,
  `log g = −(n/2) log(2πw) − (1/2)Σ log v_j − Σ log y_j − S(b, w)/(2w)`,
  where `S` is the weighted square of (6).
* **The profile in `w`.** By (6), at `b = b*(w)` this is
  `φ(w) = −(n/2) log(2πw) − c − Q/(2w) − K/2 − wH/8`. With `t = w/w*` and `4Q = Hw*² + 4nw*`,
  `φ(w) − φ(w*) = −(n/2)(log t + 1/t − 1) − (H/8)(w − w*)²/w`. That is `≤ 0`, and `< 0` for `w ≠ w*`,
  because `log x < x − 1` for `x ≠ 1`. No calculus is needed.
* **`Q = 0`.** Then `K = 0` and, at `b = b*(w)`, `log g = −(n/2) log(2πw) − c − wH/8`, which is
  unbounded as `w ↓ 0`.
-/

open Real Finset MeasureTheory
open scoped ENNReal

namespace Novel.D17ClockDrift

open Standalone.D17ClockDrift Standalone.D13DriftNull

variable {n : ℕ} {Δ v : Fin n → ℝ}

/-- The weighted square `S(b, w) = Σ(R_j − bΔ_j + w v_j/2)²/v_j`. -/
noncomputable def Sq (Δ v : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (b w : ℝ) : ℝ :=
  ∑ j, (ret y0 y j - b * Δ j + w * v j / 2) ^ 2 / v j

/-- The constant `c = (1/2)Σ log v_j + Σ log y_j`. -/
noncomputable def c0 (v : Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ j, Real.log (v j) + ∑ j, Real.log (y j)

theorem gV_eq (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ} (hp : PosPath y0 y) (b : ℝ) {w : ℝ}
    (hw : 0 < w) :
    gV Δ v b w y0 y = Real.exp (-((n : ℝ) / 2) * Real.log (2 * π * w) - c0 v y -
      Sq Δ v y0 y b w / (2 * w)) := by
  unfold gV
  rw [ite_eq_left hp]
  have hfac : ∀ j, Real.exp (-(ret y0 y j - b * Δ j + w * v j / 2) ^ 2 / (2 * w * v j)) /
      (y j * Real.sqrt (2 * π * w * v j)) = Real.exp (-(ret y0 y j - b * Δ j + w * v j / 2) ^ 2 /
        (2 * w * v j) - Real.log (y j) - (Real.log (2 * π * w) + Real.log (v j)) / 2) := fun j => by
    have hy := hp.2 j
    have hvj := hv j
    have h2 : 0 < 2 * π * w := by positivity
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log hy, ← Real.log_mul h2.ne' hvj.ne',
      show Real.log (2 * π * w * v j) / 2 = Real.log (Real.sqrt (2 * π * w * v j)) by
        rw [Real.log_sqrt (by positivity)], Real.exp_log (Real.sqrt_pos.2 (by positivity)), div_div]
  rw [Finset.prod_congr rfl fun j _ => hfac j, ← Real.exp_sum]
  congr 1
  have hw' := hw.ne'
  have e1 : ∀ j, -(ret y0 y j - b * Δ j + w * v j / 2) ^ 2 / (2 * w * v j) - Real.log (y j) -
      (Real.log (2 * π * w) + Real.log (v j)) / 2 =
      -((ret y0 y j - b * Δ j + w * v j / 2) ^ 2 / v j / (2 * w)) - Real.log (y j) -
        (Real.log (2 * π * w) / 2 + Real.log (v j) / 2) := fun j => by
    have := (hv j).ne'
    rw [add_div]; congr 2; field_simp
  rw [sum_congr rfl fun j _ => e1 j, sum_sub_distrib, sum_sub_distrib, sum_neg_distrib,
    ← sum_div, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_div]
  unfold Sq c0
  ring

/-- The profile in `w` at `b = b*(w)`. -/
noncomputable def phi (Δ v : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (w : ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log (2 * π * w) - c0 v y - Qv Δ v y0 y / (2 * w) - Kv Δ v y0 y / 2 -
    w * Hv Δ v / 8

/-- The log density is the profile minus the `b`-square. -/
theorem log_gV (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ}
    (hp : PosPath y0 y) (b : ℝ) {w : ℝ} (hw : 0 < w) :
    gV Δ v b w y0 y = Real.exp (phi Δ v y0 y w -
      Av Δ v * (b - (Bv Δ v y0 y + w * (∑ j, Δ j) / 2) / Av Δ v) ^ 2 / (2 * w)) := by
  rw [gV_eq hv hp b hw]
  congr 1
  unfold phi Sq
  rw [quad_id hn hΔ hv]
  field_simp
  ring

theorem logDv_eq : logDv Δ v y0 y = phi Δ v y0 y (wstar Δ v y0 y) := by
  unfold logDv phi c0; ring

/-- `φ(w) − φ(w*) = −(n/2)(log t + 1/t − 1) − (H/8)(w − w*)²/w` with `t = w/w*`. -/
theorem phi_gap (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ}
    (hQ : 0 < Qv Δ v y0 y) {w : ℝ} (hw : 0 < w) :
    phi Δ v y0 y w - phi Δ v y0 y (wstar Δ v y0 y) =
      -((n : ℝ) / 2) * (Real.log (w / wstar Δ v y0 y) + wstar Δ v y0 y / w - 1) -
        Hv Δ v / 8 * ((w - wstar Δ v y0 y) ^ 2 / w) := by
  have hs := wstar_pos hn (Δ := Δ) (v := v) hQ
  have hroot := wstar_root hn hΔ hv (y0 := y0) (y := y)
  have hQ' : Qv Δ v y0 y = (Hv Δ v * wstar Δ v y0 y ^ 2 + 4 * n * wstar Δ v y0 y) / 4 := by
    linarith
  unfold phi
  rw [Real.log_div hw.ne' hs.ne', show 2 * π * w = 2 * π * wstar Δ v y0 y * (w / wstar Δ v y0 y) by
    field_simp, Real.log_mul (by positivity) (by positivity), Real.log_div hw.ne' hs.ne', hQ']
  field_simp
  ring

theorem log_gap_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ Real.log t + 1 / t - 1 := by
  have := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
  rw [Real.log_inv] at this
  rw [one_div]; linarith

theorem log_gap_pos {t : ℝ} (ht : 0 < t) (h1 : t ≠ 1) : 0 < Real.log t + 1 / t - 1 := by
  have := Real.log_lt_sub_one_of_pos (inv_pos.2 ht) (by simpa using h1)
  rw [Real.log_inv] at this
  rw [one_div]; linarith

theorem phi_le (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ}
    (hQ : 0 < Qv Δ v y0 y) {w : ℝ} (hw : 0 < w) :
    phi Δ v y0 y w ≤ phi Δ v y0 y (wstar Δ v y0 y) ∧
      (w ≠ wstar Δ v y0 y → phi Δ v y0 y w < phi Δ v y0 y (wstar Δ v y0 y)) := by
  have hs := wstar_pos hn (Δ := Δ) (v := v) hQ
  have hgap := phi_gap hn hΔ hv hQ hw
  have hH := Hv_nonneg hn hΔ hv
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have ht : 0 < w / wstar Δ v y0 y := div_pos hw hs
  have hid : wstar Δ v y0 y / w = 1 / (w / wstar Δ v y0 y) := by field_simp
  have hsq : 0 ≤ Hv Δ v / 8 * ((w - wstar Δ v y0 y) ^ 2 / w) := by positivity
  refine ⟨?_, fun hne => ?_⟩
  · have := log_gap_nonneg ht
    rw [hid] at hgap
    nlinarith
  · have hne' : w / wstar Δ v y0 y ≠ 1 := fun h => hne (by field_simp at h; linarith)
    have := log_gap_pos ht hne'
    rw [hid] at hgap
    nlinarith

/-! ## The maximum and the singular case -/

theorem bstar_eq : bstar Δ v y0 y = (Bv Δ v y0 y + wstar Δ v y0 y * (∑ j, Δ j) / 2) / Av Δ v := rfl

theorem gV_attain (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ}
    (hp : PosPath y0 y) (hQ : 0 < Qv Δ v y0 y) :
    gV Δ v (bstar Δ v y0 y) (wstar Δ v y0 y) y0 y = Real.exp (logDv Δ v y0 y) := by
  rw [log_gV hn hΔ hv hp _ (wstar_pos hn hQ), ← bstar_eq, sub_self, sq, zero_mul, mul_zero,
    zero_div, sub_zero, logDv_eq]

theorem gV_lt (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ}
    (hp : PosPath y0 y) (hQ : 0 < Qv Δ v y0 y) (b : ℝ) {w : ℝ} (hw : 0 < w) :
    gV Δ v b w y0 y ≤ Real.exp (logDv Δ v y0 y) ∧
      ((b, w) ≠ (bstar Δ v y0 y, wstar Δ v y0 y) → gV Δ v b w y0 y < Real.exp (logDv Δ v y0 y)) := by
  have hA := Av_pos hn hΔ hv
  rw [log_gV hn hΔ hv hp b hw, logDv_eq]
  have hsq : 0 ≤ Av Δ v * (b - (Bv Δ v y0 y + w * (∑ j, Δ j) / 2) / Av Δ v) ^ 2 / (2 * w) := by
    positivity
  obtain ⟨hle, hlt⟩ := phi_le hn hΔ hv hQ hw
  refine ⟨Real.exp_le_exp.2 (by linarith), fun hne => Real.exp_lt_exp.2 ?_⟩
  by_cases hww : w = wstar Δ v y0 y
  · subst hww
    have hb : b ≠ bstar Δ v y0 y := fun h => hne (by rw [h])
    have : 0 < Av Δ v * (b - bstar Δ v y0 y) ^ 2 / (2 * wstar Δ v y0 y) := by
      have := sub_ne_zero.2 hb
      have := wstar_pos hn hQ (Δ := Δ) (v := v)
      positivity
    rw [← bstar_eq]; linarith
  · linarith [hlt hww]

/-- `Q = 0` exactly when every residual `R_j − a₀Δ_j` vanishes. -/
theorem resid_zero (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ}
    (hQ : Qv Δ v y0 y = 0) (j : Fin n) : ret y0 y j = Bv Δ v y0 y / Av Δ v * Δ j := by
  rw [Qv_eq hn hΔ hv] at hQ
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => div_nonneg (sq_nonneg _) (hv j).le).1 hQ j
    (mem_univ _)
  have h2 := (div_eq_zero_iff.1 this).resolve_right (hv j).ne'
  linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h2]

theorem Kv_zero (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin n → ℝ}
    (hQ : Qv Δ v y0 y = 0) : Kv Δ v y0 y = 0 := by
  rw [Kv_eq hn hΔ hv]
  exact sum_eq_zero fun j _ => by rw [resid_zero hn hΔ hv hQ j, sub_self, zero_mul, zero_div]

/-- When `Q = 0` the densities are unbounded as `w ↓ 0`. -/
theorem gV_unbounded (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ}
    {y : Fin n → ℝ} (hp : PosPath y0 y) (hQ : Qv Δ v y0 y = 0) (r : ℝ) :
    ∃ b w, 0 < w ∧ r < gV Δ v b w y0 y := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hH := Hv_nonneg hn hΔ hv
  set t := (2 / n) * (max 0 (Real.log (|r| + 1) + c0 v y + Hv Δ v / 8) + 1)
  have ht : 0 < t := by positivity
  set w := Real.exp (-t) / (2 * π)
  have hw : 0 < w := by positivity
  have hw1 : w ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith [Real.two_le_pi]
  refine ⟨(Bv Δ v y0 y + w * (∑ j, Δ j) / 2) / Av Δ v, w, hw, ?_⟩
  rw [log_gV hn hΔ hv hp _ hw, sub_self, sq, zero_mul, mul_zero, zero_div, sub_zero]
  unfold phi
  rw [hQ, Kv_zero hn hΔ hv hQ, show 2 * π * w = Real.exp (-t) by simp only [w]; field_simp,
    Real.log_exp]
  have hkey : Real.log (|r| + 1) < -((n : ℝ) / 2) * -t - c0 v y - 0 / (2 * w) - 0 / 2 -
      w * Hv Δ v / 8 := by
    have e : -((n : ℝ) / 2) * -t = max 0 (Real.log (|r| + 1) + c0 v y + Hv Δ v / 8) + 1 := by
      simp only [t]; field_simp
    rw [e, zero_div, zero_div]
    have : w * Hv Δ v / 8 ≤ Hv Δ v / 8 := by nlinarith
    linarith [le_max_right 0 (Real.log (|r| + 1) + c0 v y + Hv Δ v / 8)]
  have := Real.exp_lt_exp.2 hkey
  rw [Real.exp_log (by positivity)] at this
  linarith [le_abs_self r]

/-- The continuum supremum is the closed form, on every array. -/
theorem sup_eq (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) (y0 : ℝ) (y : Fin n → ℝ) :
    (⨆ (b : ℝ) (w : ℝ) (_ : 0 < w), ENNReal.ofReal (gV Δ v b w y0 y)) = Dv Δ v y0 y := by
  classical
  by_cases hp : PosPath y0 y
  · unfold Dv
    rw [ite_eq_left hp]
    by_cases hQ : 0 < Qv Δ v y0 y
    · rw [ite_eq_left hQ]
      refine le_antisymm (iSup_le fun b => iSup_le fun w => iSup_le fun hw =>
        ENNReal.ofReal_le_ofReal (gV_lt hn hΔ hv hp hQ b hw).1) ?_
      rw [← gV_attain hn hΔ hv hp hQ]
      exact le_iSup_of_le _ (le_iSup_of_le _ (le_iSup_of_le (wstar_pos hn hQ) le_rfl))
    · have hQ0 : Qv Δ v y0 y = 0 := le_antisymm (not_lt.1 hQ) (Qv_nonneg hn hΔ hv y0 y)
      rw [ite_eq_right hQ]
      refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
      obtain ⟨b, w, hw, hlt⟩ := gV_unbounded hn hΔ hv hp hQ0 r
      refine le_iSup_of_le b (le_iSup_of_le w (le_iSup_of_le hw ?_))
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hlt.le
  · have hc : ∀ b w, gV Δ v b w y0 y = if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0 := fun b w => by
      unfold gV; rw [ite_eq_right hp]
    unfold Dv
    rw [ite_eq_right hp]
    simp_rw [hc]
    refine le_antisymm (iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => ?_) ?_
    · split_ifs <;> simp
    · refine le_iSup_of_le 0 (le_iSup_of_le 1 (le_iSup_of_le one_pos ?_))
      split_ifs <;> simp

/-! ## The singular set -/

theorem Qv_zero_iff (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) (y0 : ℝ)
    (y : Fin n → ℝ) :
    Qv Δ v y0 y = 0 ↔ ∀ j j', ret y0 y j / Δ j = ret y0 y j' / Δ j' := by
  constructor
  · intro hQ j j'
    rw [resid_zero hn hΔ hv hQ j, resid_zero hn hΔ hv hQ j', mul_div_assoc, mul_div_assoc,
      div_self (hΔ j).ne', div_self (hΔ j').ne']
  · intro h
    set c := ret y0 y ⟨0, hn⟩ / Δ ⟨0, hn⟩
    have hR : ∀ j, ret y0 y j = c * Δ j := fun j => by
      have := h j ⟨0, hn⟩
      rw [div_eq_iff (hΔ j).ne'] at this; rw [this]
    have hB : Bv Δ v y0 y = c * Av Δ v := by
      unfold Bv Av
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by rw [hR j]; ring
    rw [Qv_eq hn hΔ hv, hB, mul_div_assoc, div_self (Av_pos hn hΔ hv).ne', mul_one]
    exact sum_eq_zero fun j _ => by rw [hR j, sub_self, sq, zero_mul, zero_div]

theorem Qv_one (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) (h1 : n = 1) (y0 : ℝ) (y : Fin n → ℝ) :
    Qv Δ v y0 y = 0 := by
  subst h1
  refine (Qv_zero_iff one_pos hΔ hv y0 y).2 fun j j' => ?_
  rw [Subsingleton.elim j j']

theorem singular_null (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) (h2 : 2 ≤ n) (y0 : ℝ) :
    (Measure.pi fun _ : Fin n => Standalone.CEVSupport.muCEV)
      {y | PosPath y0 (fun j => (y j : ℝ)) ∧ Qv Δ v y0 (fun j => (y j : ℝ)) = 0} = 0 := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hil : ((0 : Fin (n' + 1)) : ℕ) < ((⟨1, by omega⟩ : Fin (n' + 1)) : ℕ) := by simp
  refine measure_mono_null (fun y hy => ?_) (Novel.D15SwitchNull.pair_null hΔ y0 hil)
  obtain ⟨hp, hQ⟩ := hy
  refine ⟨hp.2, ?_⟩
  have := (Qv_zero_iff (Nat.succ_pos _) hΔ hv y0 _).1 hQ 0 ⟨1, by omega⟩
  rw [div_eq_div_iff (hΔ 0).ne' (hΔ _).ne'] at this
  exact this

/-! ## Measurability -/

theorem gV_nonneg (b w y0 : ℝ) (y : Fin n → ℝ) : 0 ≤ gV Δ v b w y0 y := by
  unfold gV
  split_ifs with hp
  · exact prod_nonneg fun j _ => div_nonneg (Real.exp_pos _).le
      (mul_nonneg (hp.2 j).le (Real.sqrt_nonneg _))
  · exact zero_le_one
  · exact le_rfl

theorem measurable_gV (b w : ℝ) : Measurable fun x : ℝ × (Fin n → ℝ) => gV Δ v b w x.1 x.2 := by
  classical
  unfold gV
  refine Measurable.ite Novel.D13DriftNull.measurableSet_pos ?_
    (Measurable.ite Novel.D13DriftNull.measurableSet_trap measurable_const measurable_const)
  refine Finset.measurable_prod _ fun j _ => ?_
  have hy : Measurable fun x : ℝ × (Fin n → ℝ) => x.2 j := (measurable_pi_apply j).comp measurable_snd
  exact (Real.measurable_exp.comp (((((Novel.D13DriftNull.measurable_ret j).sub_const _).add_const
    _).pow_const 2).neg.div_const _)).div (hy.mul_const _)

theorem measurable_Bv : Measurable fun x : ℝ × (Fin n → ℝ) => Bv Δ v x.1 x.2 :=
  Finset.measurable_sum _ fun j _ =>
    ((Novel.D13DriftNull.measurable_ret j).const_mul _).div_const _

theorem measurable_Qv : Measurable fun x : ℝ × (Fin n → ℝ) => Qv Δ v x.1 x.2 := by
  unfold Qv Cv
  exact (Finset.measurable_sum _ fun j _ =>
    ((Novel.D13DriftNull.measurable_ret j).pow_const 2).div_const _).sub
    ((measurable_Bv.pow_const 2).div_const _)

theorem measurable_Dv : Measurable fun x : ℝ × (Fin n → ℝ) => Dv Δ v x.1 x.2 := by
  classical
  unfold Dv
  have hK : Measurable fun x : ℝ × (Fin n → ℝ) => Kv Δ v x.1 x.2 := by
    unfold Kv
    exact (Finset.measurable_sum _ fun j _ => Novel.D13DriftNull.measurable_ret j).sub
      ((measurable_Bv.mul_const _).div_const _)
  have hw : Measurable fun x : ℝ × (Fin n → ℝ) => wstar Δ v x.1 x.2 := by
    unfold wstar
    exact (measurable_Qv.const_mul _).div
      (measurable_const.add ((measurable_const.add (measurable_Qv.const_mul _)).sqrt))
  have hlog : Measurable fun x : ℝ × (Fin n → ℝ) => logDv Δ v x.1 x.2 := by
    unfold logDv
    refine (((((measurable_const.mul (Real.measurable_log.comp (hw.const_mul _))).sub
      measurable_const).sub ?_).sub (measurable_Qv.div (hw.const_mul _))).sub
        (hK.div_const _)).sub ((hw.mul_const _).div_const _)
    exact Finset.measurable_sum _ fun j _ =>
      Real.measurable_log.comp ((measurable_pi_apply j).comp measurable_snd)
  refine Measurable.ite Novel.D13DriftNull.measurableSet_pos ?_
    (Measurable.ite Novel.D13DriftNull.measurableSet_trap measurable_const measurable_const)
  exact Measurable.ite (measurableSet_lt measurable_const measurable_Qv)
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hlog)) measurable_const

theorem profile_holds : Standalone.D17ClockDrift.profile := by
  intro n Δ v hn hΔ hv
  refine ⟨fun b w y0 y => gV_nonneg b w y0 y, fun b w => measurable_gV b w, Av_pos hn hΔ hv,
    Hv_nonneg hn hΔ hv, fun y0 y => Qv_nonneg hn hΔ hv y0 y,
    fun y0 y b w => quad_id hn hΔ hv y0 y b w, fun y0 y => sup_eq hn hΔ hv y0 y,
    fun y0 y hp hQ => ⟨wstar_pos hn hQ, gV_attain hn hΔ hv hp hQ,
      fun b w hw hne => (gV_lt hn hΔ hv hp hQ b hw).2 hne⟩,
    fun y0 y hp hQ => ?_, fun y0 y _ => Qv_zero_iff hn hΔ hv y0 y,
    fun h1 y0 y _ => Qv_one hΔ hv h1 y0 y, fun h2 y0 _ => singular_null hΔ hv h2 y0,
    measurable_Dv⟩
  have hD : Dv Δ v y0 y = ⊤ := by
    unfold Dv; simp only [hp, hQ, lt_irrefl, ↓reduceIte]
  exact ⟨hD, fun b w _ => hD ▸ ENNReal.ofReal_lt_top⟩

end Novel.D17ClockDrift
