import Novel.D19CondSensitivityPaths

/-!
# Claim 037, part 2: the evaluation bound `T_E`

* Up to a constant, the evaluation log density at `y*` is
  `F(b, w) = −(n/2) log w − Q_E(b)/(2w) + b ΣΔ/2 − w V_E/8`, with
  `Q_E(b) = C − 2b B_E* + b² A_E`. The term `−ΣR*_j/2` is a constant.
* Along the segment `t ↦ (b_g + tδ_b, w_g + tδ_w)` its first derivative is
  `δ_b S_b(t) + δ_w S_w(t)` and its second derivative is
  `−δ_b² A_E/w − 2δ_bδ_w (B_E* − bA_E)/w² + δ_w² (n/(2w²) − Q_E(b)/w³)`. On the box this is at
  most `H_bb ρ_b² + 2H_bw ρ_bρ_w + H_ww ρ_w²`: `−δ_b² A_E/w ≤ 0`, `|B_E* − bA_E|` is largest at an
  endpoint, and `Q_E ≥ 0`.
* A second-order Taylor bound along the segment (`taylor2`, by monotonicity twice) gives `T_E`.
-/

open Real Set

namespace Novel.D19CondSensitivity

open Standalone.D19CondSensitivity Standalone.D17ClockCells

/-- A second-order Taylor bound on `[0, 1]`. -/
theorem taylor2 {φ φ1 φ2 : ℝ → ℝ} {M : ℝ} (hd1 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ1 t) t)
    (hd2 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 t) t) (hM : ∀ t ∈ Icc (0 : ℝ) 1, φ2 t ≤ M) :
    φ 1 ≤ φ 0 + φ1 0 + M / 2 := by
  have hint : interior (Icc (0 : ℝ) 1) = Ioo 0 1 := interior_Icc
  -- `φ₁ − M t` is antitone.
  have hdg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => φ1 t - M * t) (φ2 t - M) t := fun t ht => by
    exact ((hd2 t ht).sub ((hasDerivAt_id' t).const_mul M)).congr_deriv (by ring)
  have hg : AntitoneOn (fun t => φ1 t - M * t) (Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun t ht => (hdg t ht).continuousAt.continuousWithinAt
    · rw [hint]
      exact fun t ht => (hdg t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · rw [hint]
      intro t ht
      rw [(hdg t (Ioo_subset_Icc_self ht)).deriv]
      linarith [hM t (Ioo_subset_Icc_self ht)]
  have hg' : ∀ t ∈ Icc (0 : ℝ) 1, φ1 t - φ1 0 - M * t ≤ 0 := fun t ht => by
    have := hg (left_mem_Icc.2 zero_le_one) ht ht.1
    simp only [mul_zero, sub_zero] at this
    linarith
  -- `φ − φ₁(0) t − M t²/2` is antitone.
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => φ t - φ1 0 * t - M * t ^ 2 / 2)
      (φ1 t - φ1 0 - M * t) t := fun t ht => by
    exact (((hd1 t ht).sub ((hasDerivAt_id' t).const_mul (φ1 0))).sub
      (((hasDerivAt_pow 2 t).const_mul M).div_const 2)).congr_deriv (by norm_num; ring)
  have hh : AntitoneOn (fun t => φ t - φ1 0 * t - M * t ^ 2 / 2) (Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · rw [hint]
      exact fun t ht => (hd t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · rw [hint]
      intro t ht
      rw [(hd t (Ioo_subset_Icc_self ht)).deriv]
      exact hg' t (Ioo_subset_Icc_self ht)
  have := hh (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [mul_zero, sub_zero, one_pow, mul_one] at this
  linarith

variable {n : ℕ}

/-- `C_E* = Σ R*_j²/v_j`. -/
noncomputable def CE (v R : Fin n → ℝ) : ℝ := ∑ j, R j ^ 2 / v j

theorem QE_eq (Δ v R : Fin n → ℝ) (b : ℝ) :
    QE Δ v R b = CE v R - 2 * b * BEs Δ v R + b ^ 2 * AE Δ v := by
  unfold QE CE BEs AE
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem QE_nonneg {Δ v R : Fin n → ℝ} (hv : ∀ j, 0 < v j) (b : ℝ) : 0 ≤ QE Δ v R b :=
  Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hv j).le

theorem AE_nonneg {Δ v : Fin n → ℝ} (hv : ∀ j, 0 < v j) : 0 ≤ AE Δ v :=
  Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hv j).le

/-- The evaluation log density up to a constant. -/
noncomputable def Fe (Δ v R : Fin n → ℝ) (b w : ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log w - (CE v R - 2 * b * BEs Δ v R + b ^ 2 * AE Δ v) / (2 * w) +
    b * (∑ j, Δ j) / 2 - w * VE v / 8

theorem ll_eq {Δ v R : Fin n → ℝ} (hv : ∀ j, 0 < v j) {b w : ℝ} (hw : 0 < w) :
    ll Δ v R b w = Fe Δ v R b w + ((-(1 / 2)) * ∑ j, Real.log (2 * π * v j) - (∑ j, R j) / 2) := by
  unfold ll lphi Fe
  rw [← QE_eq]
  unfold QE VE
  have hj : ∀ j, -(1 / 2) * Real.log (2 * π * (w * v j)) -
      (R j - (b * Δ j - w * v j / 2)) ^ 2 / (2 * (w * v j)) =
      -(1 / 2) * Real.log w - (R j - b * Δ j) ^ 2 / v j / (2 * w) + b * Δ j / 2 - w * v j / 8 +
        (-(1 / 2) * Real.log (2 * π * v j) - R j / 2) := fun j => by
    have hvj := hv j
    rw [show 2 * π * (w * v j) = w * (2 * π * v j) by ring,
      Real.log_mul hw.ne' (by positivity)]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun j _ => hj j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- `|B_E* − bA_E|` is largest at an endpoint of the drift interval. -/
theorem abs_BE_le {Δ v R : Fin n → ℝ} {B : Box} {b : ℝ} (hb : B.bL ≤ b ∧ b ≤ B.bH) :
    |BEs Δ v R - b * AE Δ v| ≤ max |BEs Δ v R - B.bL * AE Δ v| |BEs Δ v R - B.bH * AE Δ v| := by
  have := abs_affine_le (p := -AE Δ v) (q := BEs Δ v R) hb
  have e : ∀ x, -AE Δ v * x + BEs Δ v R = BEs Δ v R - x * AE Δ v := fun x => by ring
  simpa only [e] using this

section Segment

variable (Δ v R : Fin n → ℝ) (b0 w0 δb δw : ℝ)

/-- The drift along the segment. -/
noncomputable def bt (t : ℝ) : ℝ := b0 + t * δb

/-- The scale along the segment. -/
noncomputable def wt (t : ℝ) : ℝ := w0 + t * δw

/-- `Q_E` along the segment. -/
noncomputable def Qt (t : ℝ) : ℝ :=
  CE v R - 2 * bt b0 δb t * BEs Δ v R + bt b0 δb t ^ 2 * AE Δ v

/-- `F` along the segment. -/
noncomputable def phi (t : ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log (wt w0 δw t) - Qt Δ v R b0 δb t / (2 * wt w0 δw t) +
    bt b0 δb t * (∑ j, Δ j) / 2 - wt w0 δw t * VE v / 8

/-- Its first derivative. -/
noncomputable def phi1 (t : ℝ) : ℝ :=
  δb * ((BEs Δ v R - bt b0 δb t * AE Δ v) / wt w0 δw t + (∑ j, Δ j) / 2) +
    δw * (-(n : ℝ) / (2 * wt w0 δw t) + Qt Δ v R b0 δb t / (2 * wt w0 δw t ^ 2) - VE v / 8)

/-- Its second derivative. -/
noncomputable def phi2 (t : ℝ) : ℝ :=
  -δb ^ 2 * AE Δ v / wt w0 δw t -
    2 * δb * δw * (BEs Δ v R - bt b0 δb t * AE Δ v) / wt w0 δw t ^ 2 +
    δw ^ 2 * ((n : ℝ) / (2 * wt w0 δw t ^ 2) - Qt Δ v R b0 δb t / wt w0 δw t ^ 3)

theorem hasDerivAt_bt (t : ℝ) : HasDerivAt (bt b0 δb) δb t :=
  (((hasDerivAt_id' t).mul_const δb).const_add b0).congr_deriv (by ring)

theorem hasDerivAt_wt (t : ℝ) : HasDerivAt (wt w0 δw) δw t :=
  (((hasDerivAt_id' t).mul_const δw).const_add w0).congr_deriv (by ring)

theorem hasDerivAt_Qt (t : ℝ) : HasDerivAt (Qt Δ v R b0 δb)
    (-2 * δb * BEs Δ v R + 2 * bt b0 δb t * δb * AE Δ v) t :=
  (((((hasDerivAt_bt b0 δb t).const_mul 2).mul_const (BEs Δ v R)).const_sub (CE v R)).add
    (((hasDerivAt_bt b0 δb t).pow 2).mul_const (AE Δ v))).congr_deriv (by norm_num)

theorem hasDerivAt_phi {t : ℝ} (hw : wt w0 δw t ≠ 0) :
    HasDerivAt (phi Δ v R b0 w0 δb δw) (phi1 Δ v R b0 w0 δb δw t) t := by
  have h2w : 2 * wt w0 δw t ≠ 0 := mul_ne_zero two_ne_zero hw
  refine (((((hasDerivAt_wt w0 δw t).log hw).const_mul (-((n : ℝ) / 2))).sub
    ((hasDerivAt_Qt Δ v R b0 δb t).div ((hasDerivAt_wt w0 δw t).const_mul 2) h2w)).add
    (((hasDerivAt_bt b0 δb t).mul_const (∑ j, Δ j)).div_const 2)).sub
    (((hasDerivAt_wt w0 δw t).mul_const (VE v)).div_const 8) |>.congr_deriv ?_
  unfold phi1
  field_simp
  ring

theorem hasDerivAt_phi1 {t : ℝ} (hw : wt w0 δw t ≠ 0) :
    HasDerivAt (phi1 Δ v R b0 w0 δb δw) (phi2 Δ v R b0 w0 δb δw t) t := by
  have h2w : 2 * wt w0 δw t ≠ 0 := mul_ne_zero two_ne_zero hw
  have h2w2 : 2 * wt w0 δw t ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hw)
  have hA := (((((hasDerivAt_bt b0 δb t).mul_const (AE Δ v)).const_sub (BEs Δ v R)).div
    (hasDerivAt_wt w0 δw t) hw).add_const ((∑ j, Δ j) / 2)).const_mul δb
  have hB := (((((hasDerivAt_wt w0 δw t).const_mul 2).inv h2w).const_mul (-(n : ℝ))).add
    ((hasDerivAt_Qt Δ v R b0 δb t).div (((hasDerivAt_wt w0 δw t).pow 2).const_mul 2) h2w2) |>.sub_const
      (VE v / 8)).const_mul δw
  refine (hA.add hB).congr_deriv ?_
  unfold phi2
  simp only [Pi.pow_apply]
  field_simp
  ring

end Segment

theorem evalBound_holds : Standalone.D19CondSensitivity.evalBound := by
  intro n Δ v R B hv hB b w hm
  obtain ⟨hbl, hw0, hwl⟩ := hB
  obtain ⟨⟨hb1, hb2⟩, ⟨hw1, hw2⟩⟩ := hm
  simp only at hb1 hb2 hw1 hw2
  have hwp : 0 < w := hw0.trans_le hw1
  have hwg : 0 < wg B := by unfold wg; linarith
  have hδb : |b - bg B| ≤ rb B := by
    unfold rb bg; rw [abs_le]; constructor <;> linarith
  have hδw : |w - wg B| ≤ rw B := by
    unfold rw wg; rw [abs_le]; constructor <;> linarith
  -- The segment stays in the box.
  have hbt : ∀ t ∈ Icc (0 : ℝ) 1, B.bL ≤ bt (bg B) (b - bg B) t ∧ bt (bg B) (b - bg B) t ≤ B.bH :=
    fun t ht => by unfold bt bg; constructor <;> nlinarith [ht.1, ht.2]
  have hwt : ∀ t ∈ Icc (0 : ℝ) 1, B.wL ≤ wt (wg B) (w - wg B) t ∧ wt (wg B) (w - wg B) t ≤ B.wH :=
    fun t ht => by unfold wt wg; constructor <;> nlinarith [ht.1, ht.2]
  have hwtp : ∀ t ∈ Icc (0 : ℝ) 1, 0 < wt (wg B) (w - wg B) t := fun t ht =>
    hw0.trans_le (hwt t ht).1
  have hd1 := fun t (ht : t ∈ Icc (0 : ℝ) 1) =>
    hasDerivAt_phi Δ v R (bg B) (wg B) (b - bg B) (w - wg B) (hwtp t ht).ne'
  have hd2 := fun t (ht : t ∈ Icc (0 : ℝ) 1) =>
    hasDerivAt_phi1 Δ v R (bg B) (wg B) (b - bg B) (w - wg B) (hwtp t ht).ne'
  have hM : ∀ t ∈ Icc (0 : ℝ) 1, phi2 Δ v R (bg B) (wg B) (b - bg B) (w - wg B) t ≤
      Hbb Δ v B * rb B ^ 2 + 2 * Hbw Δ v R B * rb B * rw B + Hww Δ v R B * rw B ^ 2 := by
    intro t ht
    set δb := b - bg B
    set δw := w - wg B
    set W := wt (wg B) δw t
    have hwt' : B.wL ≤ W ∧ W ≤ B.wH := hwt t ht
    have hW : 0 < W := hwtp t ht
    have hA := AE_nonneg (Δ := Δ) hv
    have hQ : 0 ≤ Qt Δ v R (bg B) δb t := by
      have := QE_nonneg (Δ := Δ) (R := R) hv (bt (bg B) δb t)
      rwa [QE_eq] at this
    have t1 : -δb ^ 2 * AE Δ v / W ≤ Hbb Δ v B * rb B ^ 2 := by
      have : -δb ^ 2 * AE Δ v / W ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg δb]) hW.le
      exact this.trans (mul_nonneg (div_nonneg hA hw0.le) (sq_nonneg _))
    have hinv : 1 / W ^ 2 ≤ 1 / B.wL ^ 2 :=
      one_div_le_one_div_of_le (pow_pos hw0 2) (pow_le_pow_left₀ hw0.le hwt'.1 2)
    have hBE := abs_BE_le (Δ := Δ) (v := v) (R := R) (hbt t ht)
    have t2 : -(2 * δb * δw * (BEs Δ v R - bt (bg B) δb t * AE Δ v) / W ^ 2) ≤
        2 * Hbw Δ v R B * rb B * rw B := by
      have hab : |δb * δw| ≤ rb B * rw B := by
        rw [abs_mul]; exact mul_le_mul hδb hδw (abs_nonneg _) ((abs_nonneg _).trans hδb)
      have hrb : 0 ≤ rb B := (abs_nonneg _).trans hδb
      have hrw : 0 ≤ rw B := (abs_nonneg _).trans hδw
      set X := BEs Δ v R - bt (bg B) δb t * AE Δ v
      calc -(2 * δb * δw * X / W ^ 2) ≤ |2 * δb * δw * X / W ^ 2| := neg_le_abs _
        _ = 2 * |δb * δw| * |X| * (1 / W ^ 2) := by
            rw [abs_div, abs_of_pos (pow_pos hW 2), show 2 * δb * δw * X = 2 * (δb * δw) * X by ring,
              abs_mul, abs_mul, abs_two]
            ring
        _ ≤ 2 * (rb B * rw B) * max |BEs Δ v R - B.bL * AE Δ v| |BEs Δ v R - B.bH * AE Δ v| *
              (1 / B.wL ^ 2) := by
            have h2 : 0 ≤ 2 * (rb B * rw B) := mul_nonneg two_pos.le (mul_nonneg hrb hrw)
            refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hab two_pos.le) hBE
              (abs_nonneg _) h2) hinv (by positivity)
              (mul_nonneg h2 ((abs_nonneg _).trans (le_max_left _ _)))
        _ = _ := by unfold Hbw; ring
    have t3 : δw ^ 2 * ((n : ℝ) / (2 * W ^ 2) - Qt Δ v R (bg B) δb t / W ^ 3) ≤
        Hww Δ v R B * rw B ^ 2 := by
      have hq : 0 ≤ Qt Δ v R (bg B) δb t / W ^ 3 := div_nonneg hQ (pow_pos hW 3).le
      have hn : (n : ℝ) / (2 * W ^ 2) ≤ (n : ℝ) / (2 * B.wL ^ 2) := by
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        nlinarith [pow_le_pow_left₀ hw0.le hwt'.1 2]
      have hH : (n : ℝ) / (2 * B.wL ^ 2) ≤ Hww Δ v R B := by
        unfold Hww
        have : 0 ≤ max (QE Δ v R B.bL) (QE Δ v R B.bH) / B.wL ^ 3 :=
          div_nonneg ((QE_nonneg hv _).trans (le_max_left _ _)) (pow_pos hw0 3).le
        linarith
      have hsq : δw ^ 2 ≤ rw B ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδw 2
      have h0 : (0 : ℝ) ≤ (n : ℝ) / (2 * B.wL ^ 2) := by positivity
      calc δw ^ 2 * ((n : ℝ) / (2 * W ^ 2) - Qt Δ v R (bg B) δb t / W ^ 3)
          ≤ δw ^ 2 * ((n : ℝ) / (2 * B.wL ^ 2)) :=
            mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
        _ ≤ rw B ^ 2 * Hww Δ v R B := mul_le_mul hsq hH h0 (sq_nonneg _)
        _ = _ := mul_comm _ _
    unfold phi2
    linarith
  have hT := taylor2 hd1 hd2 hM
  -- Back to the log densities.
  have hφ0 : phi Δ v R (bg B) (wg B) (b - bg B) (w - wg B) 0 = Fe Δ v R (bg B) (wg B) := by
    unfold phi Qt bt wt Fe; ring_nf
  have hφ1 : phi Δ v R (bg B) (wg B) (b - bg B) (w - wg B) 1 = Fe Δ v R b w := by
    unfold phi Qt bt wt Fe; ring_nf
  have hS : phi1 Δ v R (bg B) (wg B) (b - bg B) (w - wg B) 0 ≤
      |Sb Δ v R B| * rb B + |Sw Δ v R B| * rw B := by
    have e : phi1 Δ v R (bg B) (wg B) (b - bg B) (w - wg B) 0 =
        (b - bg B) * Sb Δ v R B + (w - wg B) * Sw Δ v R B := by
      unfold phi1 Qt bt wt Sb Sw
      rw [QE_eq]
      ring_nf
    rw [e]
    have h1 : (b - bg B) * Sb Δ v R B ≤ |Sb Δ v R B| * rb B := by
      calc (b - bg B) * Sb Δ v R B ≤ |(b - bg B) * Sb Δ v R B| := le_abs_self _
        _ = |Sb Δ v R B| * |b - bg B| := by rw [abs_mul, mul_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_left hδb (abs_nonneg _)
    have h2 : (w - wg B) * Sw Δ v R B ≤ |Sw Δ v R B| * rw B := by
      calc (w - wg B) * Sw Δ v R B ≤ |(w - wg B) * Sw Δ v R B| := le_abs_self _
        _ = |Sw Δ v R B| * |w - wg B| := by rw [abs_mul, mul_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_left hδw (abs_nonneg _)
    linarith
  rw [ll_eq hv hwp, ll_eq hv hwg, ← hφ0, ← hφ1]
  unfold TE
  linarith

end Novel.D19CondSensitivity
