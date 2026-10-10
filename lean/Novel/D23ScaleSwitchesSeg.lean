import Standalone.D23ScaleSwitches
import Novel.D23JointSwitchesProof

/-!
# Claim 069, part 1: the segment profile with free daily drifts

* At a fixed scale `w`, claim 033's square completion (`log_gV`) gives each day's drift profile
  `exp φ_d(w)`, attained at `b_d(w) = (B_du + w T_d/2)/A_du` (`gday_le`, `gday_eq`).
* Free drifts with one scale on a segment: the profile at `w` is `exp Σ_d φ_d(w) = exp Φ(w)`, where
  `Φ` is claim 033's scalar profile with the summed statistics `N_I, Q_I, K_I, H_I` (`sum_phi`).
* `Φ` is maximized at `w_I*` when `Q_I > 0`: the gap `Φ(w) − Φ(w*)` is
  `−(N/2)(log t + 1/t − 1) − (H/8)(w − w*)²/w`, `t = w/w*` (`Phi_gap`), the scalar calculation of
  claim 033 with the summed statistics. When `Q_I = 0`, every day has `Q_du = 0`, so `K_I = 0`, and
  `Φ(w) → ∞` as `w ↓ 0` (`Phi_unbounded`).
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23ScaleSwitches

open Standalone.D23ScaleSwitches Standalone.D23JointSwitches Standalone.D23DailyProfile
  Standalone.D17ClockDrift Standalone.D13DriftNull Standalone.CEVSupport Novel.D17ClockDrift
  Novel.D23DailyProfile Novel.D23JointSwitches

/-! ### The scalar profile -/

/-- `Φ(w) = −(N/2) log(2πw) − C − Q/(2w) − K/2 − wH/8`. -/
noncomputable def Phi (N C Q K H w : ℝ) : ℝ :=
  -(N / 2) * Real.log (2 * π * w) - C - Q / (2 * w) - K / 2 - w * H / 8

/-- `w* = 2Q/(N + √(N² + HQ))`. -/
noncomputable def wr (N Q H : ℝ) : ℝ := 2 * Q / (N + Real.sqrt (N ^ 2 + H * Q))

section Scalar

variable {N Q H : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hH : 0 ≤ H)
include hN hQ hH

theorem wr_pos : 0 < wr N Q H := by
  unfold wr; have := Real.sqrt_nonneg (N ^ 2 + H * Q); positivity

theorem wr_root : H * wr N Q H ^ 2 + 4 * N * wr N Q H = 4 * Q := by
  have hr0 : 0 ≤ Real.sqrt (N ^ 2 + H * Q) := Real.sqrt_nonneg _
  have hr2 : Real.sqrt (N ^ 2 + H * Q) ^ 2 = N ^ 2 + H * Q := Real.sq_sqrt (by positivity)
  have hNr : 0 < N + Real.sqrt (N ^ 2 + H * Q) := by linarith
  unfold wr
  rw [div_pow]
  field_simp
  linear_combination (-4) * hr2

theorem Phi_gap (C K : ℝ) {w : ℝ} (hw : 0 < w) :
    Phi N C Q K H w - Phi N C Q K H (wr N Q H) =
      -(N / 2) * (Real.log (w / wr N Q H) + wr N Q H / w - 1) - H / 8 * ((w - wr N Q H) ^ 2 / w) := by
  have hs := wr_pos hN hQ hH
  have hroot := wr_root hN hQ hH
  set W := wr N Q H with hW
  clear_value W
  have hQ' : Q = (H * W ^ 2 + 4 * N * W) / 4 := by linarith
  unfold Phi
  rw [Real.log_div hw.ne' hs.ne', show 2 * π * w = 2 * π * W * (w / W) by field_simp,
    Real.log_mul (by positivity) (by positivity), Real.log_div hw.ne' hs.ne', hQ']
  field_simp
  ring

theorem Phi_le (C K : ℝ) {w : ℝ} (hw : 0 < w) : Phi N C Q K H w ≤ Phi N C Q K H (wr N Q H) := by
  have hs := wr_pos hN hQ hH
  have hgap := Phi_gap hN hQ hH C K hw
  have ht : 0 < w / wr N Q H := div_pos hw hs
  have hid : wr N Q H / w = 1 / (w / wr N Q H) := by field_simp
  have hsq : 0 ≤ H / 8 * ((w - wr N Q H) ^ 2 / w) := by positivity
  have := log_gap_nonneg ht
  rw [hid] at hgap
  nlinarith

end Scalar

/-- With `Q = K = 0`, `Φ` is unbounded as `w ↓ 0`. -/
theorem Phi_unbounded {N H : ℝ} (hN : 0 < N) (hH : 0 ≤ H) (C r : ℝ) :
    ∃ w, 0 < w ∧ r < Phi N C 0 0 H w := by
  set t := (2 / N) * (max 0 (r + C + H / 8) + 1)
  have ht : 0 < t := by positivity
  set w := Real.exp (-t) / (2 * π)
  have hw : 0 < w := by positivity
  have hw1 : w ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith [Real.two_le_pi]
  refine ⟨w, hw, ?_⟩
  unfold Phi
  rw [show 2 * π * w = Real.exp (-t) by simp only [w]; field_simp, Real.log_exp]
  have e : -(N / 2) * -t = max 0 (r + C + H / 8) + 1 := by simp only [t]; field_simp
  have : w * H / 8 ≤ H / 8 := by nlinarith
  rw [zero_div, zero_div]
  linarith [le_max_right 0 (r + C + H / 8)]

/-! ### One day at a fixed scale -/

variable {D : ℕ} {n : Fin D → ℕ} {Δ u : Fam n}

theorem measurable_Kv {m : ℕ} {Δ₁ v : Fin m → ℝ} :
    Measurable fun x : ℝ × (Fin m → ℝ) => Kv Δ₁ v x.1 x.2 := by
  unfold Kv
  exact (Finset.measurable_sum _ fun j _ => Novel.D13DriftNull.measurable_ret j).sub
    ((measurable_Bv.mul_const _).div_const _)

section Day

variable (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) (hu : ∀ d j, 0 < u d j)
  {s : ℝ} {y : Arr n} (hy : AllPos s y)
include hn hΔ hu hy

theorem gday_le (d : Fin D) (b : ℝ) {w : ℝ} (hw : 0 < w) :
    gV (Δ d) (u d) b w (start s y d) (toR y d) ≤
      Real.exp (phi (Δ d) (u d) (start s y d) (toR y d) w) := by
  rw [log_gV (hn d) (hΔ d) (hu d) (posPath_block hy hn d) b hw]
  refine Real.exp_le_exp.2 (sub_le_self _ ?_)
  have := Av_pos (hn d) (hΔ d) (hu d)
  positivity

theorem gday_eq (d : Fin D) {w : ℝ} (hw : 0 < w) :
    gV (Δ d) (u d) (bday Δ u s y d w) w (start s y d) (toR y d) =
      Real.exp (phi (Δ d) (u d) (start s y d) (toR y d) w) := by
  rw [log_gV (hn d) (hΔ d) (hu d) (posPath_block hy hn d) _ hw]
  unfold bday
  rw [sub_self, sq, zero_mul, mul_zero, zero_div, sub_zero]

end Day

/-! ### A segment -/

/-- `C_I = Σ_(d∈I) c0_d`. -/
noncomputable def CI (u : Fam n) {ℓ : ℕ} (e : Fin ℓ → Fin D) (y : Arr n) : ℝ :=
  ∑ j, c0 (u (e j)) (toR y (e j))

theorem sum_phi {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) (w : ℝ) :
    ∑ j, phi (Δ (e j)) (u (e j)) (start s y (e j)) (toR y (e j)) w =
      Phi (NI n e) (CI u e y) (QI Δ u e s y) (KI Δ u e s y) (HI Δ u e) w := by
  unfold phi Phi NI NSeg CI QI KI HI
  push_cast
  simp only [Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum, Finset.sum_mul, neg_mul,
    Finset.sum_neg_distrib]

theorem logPI_eq {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) :
    logPI Δ u e s y = Phi (NI n e) (CI u e y) (QI Δ u e s y) (KI Δ u e s y) (HI Δ u e)
      (wr (NI n e) (QI Δ u e s y) (HI Δ u e)) := by
  unfold logPI Phi CI c0 wI wr
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem wI_eq {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) :
    wI Δ u e s y = wr (NI n e) (QI Δ u e s y) (HI Δ u e) := rfl

theorem PsegE_le_PswSeg {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) :
    PsegE Δ u e s y ≤ PswSeg Δ u e s y :=
  iSup_le fun b => iSup_le fun w => iSup_le fun hw =>
    le_iSup₂_of_le (fun _ => b) w (le_iSup_of_le hw le_rfl)

section Seg

variable (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) (hu : ∀ d j, 0 < u d j)
  {ℓ : ℕ} (e : Fin ℓ → Fin D) (hℓ : 0 < ℓ)

include hn hℓ in
theorem NI_pos : 0 < NI n e := by
  have := N_pos hℓ (fun j => hn (e j))
  unfold NI NSeg; exact_mod_cast this

include hn hΔ hu in
theorem QI_nonneg (s : ℝ) (y : Arr n) : 0 ≤ QI Δ u e s y :=
  Finset.sum_nonneg fun j _ => Qv_nonneg (hn _) (hΔ _) (hu _) _ _

include hn hΔ hu in
theorem HI_nonneg : 0 ≤ HI Δ u e :=
  Finset.sum_nonneg fun j _ => Hv_nonneg (hn _) (hΔ _) (hu _)

variable {s : ℝ} {y : Arr n} (hy : AllPos s y)

include hn hΔ hu hy in
theorem prod_le_Phi (b : Fin ℓ → ℝ) {w : ℝ} (hw : 0 < w) :
    ∏ j, ENNReal.ofReal (gV (Δ (e j)) (u (e j)) (b j) w (start s y (e j)) (toR y (e j))) ≤
      ENNReal.ofReal (Real.exp (Phi (NI n e) (CI u e y) (QI Δ u e s y) (KI Δ u e s y) (HI Δ u e) w)) := by
  calc ∏ j, ENNReal.ofReal (gV (Δ (e j)) (u (e j)) (b j) w (start s y (e j)) (toR y (e j)))
      ≤ ∏ j, ENNReal.ofReal (Real.exp (phi (Δ (e j)) (u (e j)) (start s y (e j)) (toR y (e j)) w)) :=
        Finset.prod_le_prod fun j _ => ENNReal.ofReal_le_ofReal (gday_le hn hΔ hu hy _ _ hw)
    _ = _ := by
        rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le, ← Real.exp_sum,
          sum_phi]

include hn hΔ hu hy in
theorem prod_bday {w : ℝ} (hw : 0 < w) :
    ∏ j, ENNReal.ofReal (gV (Δ (e j)) (u (e j)) (bday Δ u s y (e j) w) w (start s y (e j))
      (toR y (e j))) =
      ENNReal.ofReal (Real.exp (Phi (NI n e) (CI u e y) (QI Δ u e s y) (KI Δ u e s y) (HI Δ u e) w)) := by
  simp_rw [gday_eq hn hΔ hu hy _ hw]
  rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le, ← Real.exp_sum, sum_phi]

include hn hΔ hu hy in
/-- The segment profile is the supremum of `exp Φ` over the scale. -/
theorem PswSeg_eq_sup : PswSeg Δ u e s y = ⨆ (w : ℝ) (_ : 0 < w),
    ENNReal.ofReal (Real.exp (Phi (NI n e) (CI u e y) (QI Δ u e s y) (KI Δ u e s y) (HI Δ u e) w)) := by
  unfold PswSeg
  refine le_antisymm (iSup_le fun b => iSup_le fun w => iSup_le fun hw =>
    (prod_le_Phi hn hΔ hu e hy b hw).trans (le_iSup₂_of_le w hw le_rfl))
    (iSup₂_le fun w hw => ?_)
  rw [← prod_bday hn hΔ hu e hy hw]
  exact le_iSup₂_of_le (fun j => bday Δ u s y (e j) w) w (le_iSup_of_le hw le_rfl)

include hn hΔ hu hy hℓ in
theorem PswSeg_pos : 0 < PswSeg Δ u e s y := by
  rw [PswSeg_eq_sup hn hΔ hu e hy]
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.exp_pos _)) (le_iSup₂_of_le 1 one_pos le_rfl)

include hn hΔ hu hy hℓ in
theorem PswSeg_fin (hQ : 0 < QI Δ u e s y) :
    PswSeg Δ u e s y = ENNReal.ofReal (Real.exp (logPI Δ u e s y)) := by
  have hN := NI_pos hn e hℓ
  have hH := HI_nonneg hn hΔ hu e
  rw [PswSeg_eq_sup hn hΔ hu e hy, logPI_eq]
  refine le_antisymm (iSup₂_le fun w hw => ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.2 (Phi_le hN hQ hH _ _ hw))) (le_iSup₂_of_le _ (wr_pos hN hQ hH) le_rfl)

include hn hΔ hu hy in
theorem QI_zero_iff : QI Δ u e s y = 0 ↔
    ∀ j, Qv (Δ (e j)) (u (e j)) (start s y (e j)) (toR y (e j)) = 0 := by
  unfold QI
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => Qv_nonneg (hn _) (hΔ _) (hu _) _ _]
  simp

include hn hΔ hu hy in
theorem KI_zero (hQ : QI Δ u e s y = 0) : KI Δ u e s y = 0 :=
  Finset.sum_eq_zero fun j _ =>
    Kv_zero (hn _) (hΔ _) (hu _) ((QI_zero_iff hn hΔ hu e hy).1 hQ j)

include hn hΔ hu hy hℓ in
theorem PswSeg_top (hQ : QI Δ u e s y = 0) : PswSeg Δ u e s y = ⊤ := by
  have hN := NI_pos hn e hℓ
  have hH := HI_nonneg hn hΔ hu e
  rw [PswSeg_eq_sup hn hΔ hu e hy, hQ, KI_zero hn hΔ hu e hy hQ]
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨w, hw, hlt⟩ := Phi_unbounded hN hH (CI u e y) r
  refine le_iSup₂_of_le w hw ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal (hlt.le.trans ?_)
  linarith [Real.add_one_le_exp (Phi (NI n e) (CI u e y) 0 0 (HI Δ u e) w)]

end Seg

theorem measurable_QI {ℓ : ℕ} (e : Fin ℓ → Fin D) :
    Measurable fun x : ℝ × Arr n => QI Δ u e x.1 x.2 :=
  Finset.measurable_sum _ fun j _ => by
    have := (measurable_Qv (Δ := Δ (e j)) (v := u (e j))).comp (measurable_block (n := n) (e j))
    exact this

theorem measurable_logPI {ℓ : ℕ} (e : Fin ℓ → Fin D) :
    Measurable fun x : ℝ × Arr n => logPI Δ u e x.1 x.2 := by
  have hQ := measurable_QI (Δ := Δ) (u := u) e
  have hK : Measurable fun x : ℝ × Arr n => KI Δ u e x.1 x.2 :=
    Finset.measurable_sum _ fun j _ => by
      have := (measurable_Kv (Δ₁ := Δ (e j)) (v := u (e j))).comp (measurable_block (n := n) (e j))
      exact this
  have hw : Measurable fun x : ℝ × Arr n => wI Δ u e x.1 x.2 := by
    unfold wI
    exact (hQ.const_mul _).div (measurable_const.add ((measurable_const.add (hQ.const_mul _)).sqrt))
  have hy : Measurable fun x : ℝ × Arr n => ∑ j, ∑ i, Real.log (toR x.2 (e j) i) :=
    Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun i _ =>
      Real.measurable_log.comp ((measurable_pi_apply i).comp ((measurable_toR (e j)).comp measurable_snd))
  unfold logPI
  exact (((((measurable_const.mul (Real.measurable_log.comp (hw.const_mul _))).sub
    measurable_const).sub hy).sub (hQ.div (hw.const_mul _))).sub (hK.div_const _)).sub
      ((hw.mul_const _).div_const _)

theorem measurable_PswSeg (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) (hu : ∀ d j, 0 < u d j)
    {ℓ : ℕ} (e : Fin ℓ → Fin D) (hℓ : 0 < ℓ) :
    Measurable ({x : ℝ × Arr n | AllPos x.1 x.2}.indicator fun x => PswSeg Δ u e x.1 x.2) := by
  classical
  set F : ℝ × Arr n → ℝ≥0∞ := fun x =>
    if 0 < QI Δ u e x.1 x.2 then ENNReal.ofReal (Real.exp (logPI Δ u e x.1 x.2)) else ⊤
  have hF : Measurable F := Measurable.ite (measurableSet_lt measurable_const (measurable_QI e))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_logPI e))) measurable_const
  have he : {x : ℝ × Arr n | AllPos x.1 x.2}.indicator (fun x => PswSeg Δ u e x.1 x.2) =
      {x : ℝ × Arr n | AllPos x.1 x.2}.indicator F := Set.indicator_congr fun x hx => by
    simp only [F]
    split_ifs with hQ
    · exact PswSeg_fin hn hΔ hu e hℓ hx hQ
    · exact PswSeg_top hn hΔ hu e hℓ hx
        (le_antisymm (not_lt.1 hQ) (QI_nonneg hn hΔ hu e x.1 x.2))
  rw [he]
  exact hF.indicator measurableSet_allPos

theorem segment_holds : Standalone.D23ScaleSwitches.segment := by
  intro D n Δ u hn hΔ hu ℓ e hℓ
  refine ⟨measurable_PswSeg hn hΔ hu e hℓ, fun s y hy => ⟨PswSeg_pos hn hΔ hu e hℓ hy,
    PsegE_le_PswSeg e s y, QI_nonneg hn hΔ hu e s y, HI_nonneg hn hΔ hu e, fun hQ => ?_,
    QI_zero_iff hn hΔ hu e hy, fun hQ => ⟨KI_zero hn hΔ hu e hy hQ, PswSeg_top hn hΔ hu e hℓ hy hQ⟩⟩⟩
  have hN := NI_pos hn e hℓ
  have hH := HI_nonneg hn hΔ hu e
  refine ⟨wr_pos hN hQ hH, PswSeg_fin hn hΔ hu e hℓ hy hQ, ?_⟩
  rw [wI_eq, prod_bday hn hΔ hu e hy (wr_pos hN hQ hH), PswSeg_fin hn hΔ hu e hℓ hy hQ, logPI_eq]

end Novel.D23ScaleSwitches
