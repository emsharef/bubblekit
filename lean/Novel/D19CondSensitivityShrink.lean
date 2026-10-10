import Novel.D19CondSensitivityCert

/-!
# Claim 037: shrinking covers

On a fixed positive-label record, the path terms of (2) do not depend on the box. On a subbox `B`
of `ℬ` (floor `W = w_L(ℬ)`, drift bound `B_max(ℬ)`):
* `c₁(B) ≤ ρ_b/W + B_max ρ_w/W²` and `c₂(B) ≤ ρ_w/(2W²)`;
* `|S_b|`, `|S_w|` and the Hessian bounds are bounded by constants of the record and `ℬ`.
So `η_cond(B) ≤ L · max(ρ_b, ρ_w)` once the radii are at most one, and `η_cond → 0`. With
`D_filter ≤ D_cond ≤ D_cert`, claim 036's limits give `D_cond → D_filter`.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal

namespace Novel.D19CondSensitivity

open Standalone.D19CondSensitivity Standalone.D19FilteredLikelihood Standalone.D14FixedTick
  Standalone.D17ClockCells Novel.D19FilteredLikelihood

variable {m : ℕ}

theorem wB_nonneg (Δ v : Fin m → ℝ) {lo hi : Fin (m + 1) → ℝ} (h : ∀ i, lo i ≤ hi i) :
    0 ≤ wB Δ v lo hi :=
  Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (by unfold hw; linarith [h i])

theorem tw_nonneg {lo hi : Fin (m + 1) → ℝ} (h : ∀ i, lo i ≤ hi i) (j : Fin m) : 0 ≤ tw lo hi j := by
  unfold tw hw; linarith [h j.castSucc, h j.succ]

theorem OmC_nonneg {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) {lo hi : Fin (m + 1) → ℝ}
    (h : ∀ i, lo i ≤ hi i) : 0 ≤ OmC v lo hi := by
  refine Finset.sum_nonneg fun j _ => div_nonneg ?_ (hv j).le
  have ht := tw_nonneg h j
  have : max 0 (|Rst lo hi j| - tw lo hi j) ≤ |Rst lo hi j| + tw lo hi j :=
    max_le (by positivity) (by linarith)
  nlinarith [le_max_left 0 (|Rst lo hi j| - tw lo hi j)]

theorem dC_nonneg {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) {lo hi : Fin (m + 1) → ℝ}
    (h : ∀ i, lo i ≤ hi i) : 0 ≤ dC v lo hi :=
  Finset.sum_nonneg fun j _ => div_nonneg (by have := tw_nonneg h j; positivity) (hv j).le

/-- One corner of the box against the center. -/
theorem corner_bound {b' w' bg' wg' ρb ρw W Bm : ℝ} (hW : 0 < W) (hw' : W ≤ w') (hwg : W ≤ wg')
    (hb : |b' - bg'| ≤ ρb) (hw : |w' - wg'| ≤ ρw) (hbg : |bg'| ≤ Bm) :
    |b' / w' - bg' / wg'| ≤ ρb / W + Bm * ρw / W ^ 2 := by
  have hw'p : 0 < w' := hW.trans_le hw'
  have hwgp : 0 < wg' := hW.trans_le hwg
  have e : b' / w' - bg' / wg' = (b' - bg') / w' + bg' * (wg' - w') / (w' * wg') := by
    field_simp; ring
  rw [e]
  have h1 : |(b' - bg') / w'| ≤ ρb / W := by
    rw [abs_div, abs_of_pos hw'p]
    calc |b' - bg'| / w' ≤ ρb / w' := div_le_div_of_nonneg_right hb hw'p.le
      _ ≤ ρb / W := div_le_div_of_nonneg_left ((abs_nonneg _).trans hb) hW hw'
  have h2 : |bg' * (wg' - w') / (w' * wg')| ≤ Bm * ρw / W ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hw'p hwgp), abs_sub_comm]
    have hBm : 0 ≤ Bm := (abs_nonneg _).trans hbg
    have hρw : 0 ≤ ρw := (abs_nonneg _).trans hw
    calc |bg'| * |w' - wg'| / (w' * wg') ≤ Bm * ρw / (w' * wg') :=
          div_le_div_of_nonneg_right (mul_le_mul hbg hw (abs_nonneg _) hBm) (by positivity)
      _ ≤ Bm * ρw / W ^ 2 := div_le_div_of_nonneg_left (mul_nonneg hBm hρw) (by positivity)
          (by nlinarith)
  calc _ ≤ |(b' - bg') / w'| + |bg' * (wg' - w') / (w' * wg')| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

theorem inv_bound {w' wg' ρw W : ℝ} (hW : 0 < W) (hw' : W ≤ w') (hwg : W ≤ wg')
    (hw : |w' - wg'| ≤ ρw) : |1 / w' - 1 / wg'| / 2 ≤ ρw / (2 * W ^ 2) := by
  have hw'p : 0 < w' := hW.trans_le hw'
  have hwgp : 0 < wg' := hW.trans_le hwg
  have e : 1 / w' - 1 / wg' = (wg' - w') / (w' * wg') := by field_simp
  rw [e, abs_div, abs_of_pos (mul_pos hw'p hwgp), abs_sub_comm]
  have hρw : 0 ≤ ρw := (abs_nonneg _).trans hw
  have : |w' - wg'| / (w' * wg') ≤ ρw / W ^ 2 :=
    (div_le_div_of_nonneg_right hw (by positivity)).trans
      (div_le_div_of_nonneg_left hρw (by positivity) (by nlinarith))
  calc |w' - wg'| / (w' * wg') / 2 ≤ ρw / W ^ 2 / 2 :=
        div_le_div_of_nonneg_right this (by norm_num)
    _ = ρw / (2 * W ^ 2) := by ring

section Const

variable {n : ℕ} (Δ v R : Fin n → ℝ) (ℬ : Box)

/-- `B_max(ℬ)`. -/
noncomputable def Bmx : ℝ := max |ℬ.bL| |ℬ.bH|

/-- A bound on `Q_E` over the drifts of `ℬ`. -/
noncomputable def Qmx : ℝ := CE v R + 2 * Bmx ℬ * |BEs Δ v R| + Bmx ℬ ^ 2 * AE Δ v

/-- The bound on `|S_b|`. -/
noncomputable def G1f : ℝ := (|BEs Δ v R| + Bmx ℬ * AE Δ v) / ℬ.wL + |∑ j, Δ j| / 2

/-- The bound on `|S_w|`. -/
noncomputable def G2f : ℝ :=
  (n : ℝ) / (2 * ℬ.wL) + Qmx Δ v R ℬ / (2 * ℬ.wL ^ 2) + |VE v| / 8

/-- The bound on the Hessian entries. -/
noncomputable def G3f : ℝ :=
  AE Δ v / ℬ.wL + (|BEs Δ v R| + Bmx ℬ * AE Δ v) / ℬ.wL ^ 2 +
    ((n : ℝ) / (2 * ℬ.wL ^ 2) + Qmx Δ v R ℬ / ℬ.wL ^ 3)

end Const

section Bounds

variable {n : ℕ} {Δ v R : Fin n → ℝ} {ℬ B : Box} (hv : ∀ j, 0 < v j) (hℬ : ℬ.Valid)
  (hB : B.Valid) (hsub : B.Sub ℬ)
include hv hℬ hB hsub

omit hv hℬ hB hsub in
theorem Bmx_nonneg' : 0 ≤ Bmx ℬ := (abs_nonneg _).trans (le_max_left _ _)

omit hv hℬ hB in
theorem abs_le_Bmx {b : ℝ} (h1 : B.bL ≤ b) (h2 : b ≤ B.bH) : |b| ≤ Bmx ℬ :=
  Novel.D19FilteredLikelihood.abs_le_max_of_mem (hsub.1.trans h1) (h2.trans hsub.2.1)

omit hℬ hB hsub in
theorem QE_le_Qmx {b : ℝ} (hb : |b| ≤ Bmx ℬ) : QE Δ v R b ≤ Qmx Δ v R ℬ := by
  rw [QE_eq]
  unfold Qmx
  have hA := AE_nonneg (Δ := Δ) hv
  have hb2 : b ^ 2 ≤ Bmx ℬ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have h1 : -(2 * b * BEs Δ v R) ≤ 2 * Bmx ℬ * |BEs Δ v R| := by
    have h3 : -(b * BEs Δ v R) ≤ |b| * |BEs Δ v R| := by rw [← abs_mul]; exact neg_le_abs _
    have h4 : |b| * |BEs Δ v R| ≤ Bmx ℬ * |BEs Δ v R| :=
      mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    linarith
  have h5 : b ^ 2 * AE Δ v ≤ Bmx ℬ ^ 2 * AE Δ v := mul_le_mul_of_nonneg_right hb2 hA
  linarith

omit hℬ hB hsub in
theorem Qmx_nonneg : 0 ≤ Qmx Δ v R ℬ :=
  (QE_nonneg hv 0).trans (QE_le_Qmx hv (by simpa using Bmx_nonneg' (ℬ := ℬ)))

omit hv hℬ hsub in
theorem bg_in : B.bL ≤ bg B ∧ bg B ≤ B.bH := by unfold bg; constructor <;> linarith [hB.1]

omit hv hℬ in
theorem wg_ge : ℬ.wL ≤ wg B := by unfold wg; linarith [hB.2.2, hsub.2.2.1]

omit hℬ hB hsub in
theorem abs_BE_sub_le {b : ℝ} (hb : |b| ≤ Bmx ℬ) :
    |BEs Δ v R - b * AE Δ v| ≤ |BEs Δ v R| + Bmx ℬ * AE Δ v := by
  have hA := AE_nonneg (Δ := Δ) hv
  calc |BEs Δ v R - b * AE Δ v| ≤ |BEs Δ v R| + |b * AE Δ v| := abs_sub _ _
    _ = |BEs Δ v R| + |b| * AE Δ v := by rw [abs_mul, abs_of_nonneg hA]
    _ ≤ _ := by have := mul_le_mul_of_nonneg_right hb hA; linarith

theorem Sb_le : |Sb Δ v R B| ≤ G1f Δ v R ℬ := by
  have hW := hℬ.2.1
  have hwg := wg_ge hB hsub
  have hwgp : 0 < wg B := hW.trans_le hwg
  have hbg := abs_le_Bmx hsub (bg_in hB).1 (bg_in hB).2
  have h1 := abs_BE_sub_le (R := R) (Δ := Δ) hv hbg
  have hA := AE_nonneg (Δ := Δ) hv
  have h2 : |BEs Δ v R - bg B * AE Δ v| / wg B ≤ (|BEs Δ v R| + Bmx ℬ * AE Δ v) / ℬ.wL :=
    (div_le_div_of_nonneg_right h1 hwgp.le).trans
      (div_le_div_of_nonneg_left (by have := Bmx_nonneg' (ℬ := ℬ); positivity) hW hwg)
  unfold Sb G1f
  calc |(BEs Δ v R - bg B * AE Δ v) / wg B + (∑ j, Δ j) / 2|
      ≤ |(BEs Δ v R - bg B * AE Δ v) / wg B| + |(∑ j, Δ j) / 2| := abs_add_le _ _
    _ = |BEs Δ v R - bg B * AE Δ v| / wg B + |∑ j, Δ j| / 2 := by
        rw [abs_div, abs_div, abs_of_pos hwgp, abs_two]
    _ ≤ _ := by linarith

theorem Sw_le : |Sw Δ v R B| ≤ G2f Δ v R ℬ := by
  have hW := hℬ.2.1
  have hwg := wg_ge hB hsub
  have hwgp : 0 < wg B := hW.trans_le hwg
  have hbg := abs_le_Bmx hsub (bg_in hB).1 (bg_in hB).2
  have hq := QE_le_Qmx (R := R) (Δ := Δ) hv hbg
  have hq0 := QE_nonneg (Δ := Δ) (R := R) hv (bg B)
  have hQm0 := Qmx_nonneg (R := R) (Δ := Δ) (ℬ := ℬ) hv
  have e1 : (n : ℝ) / (2 * wg B) ≤ (n : ℝ) / (2 * ℬ.wL) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
  have hsq : ℬ.wL ^ 2 ≤ wg B ^ 2 := pow_le_pow_left₀ hW.le hwg 2
  have e2 : QE Δ v R (bg B) / (2 * wg B ^ 2) ≤ Qmx Δ v R ℬ / (2 * ℬ.wL ^ 2) :=
    (div_le_div_of_nonneg_right hq (by positivity)).trans
      (div_le_div_of_nonneg_left hQm0 (by positivity) (by linarith))
  unfold Sw G2f
  have t1 : |-(n : ℝ) / (2 * wg B)| = (n : ℝ) / (2 * wg B) := by
    rw [abs_div, abs_neg, Nat.abs_cast, abs_of_pos (by positivity : (0 : ℝ) < 2 * wg B)]
  have t2 : |QE Δ v R (bg B) / (2 * wg B ^ 2)| = QE Δ v R (bg B) / (2 * wg B ^ 2) :=
    abs_of_nonneg (by positivity)
  have t3 : |VE v / 8| = |VE v| / 8 := by rw [abs_div]; norm_num
  calc |-(n : ℝ) / (2 * wg B) + QE Δ v R (bg B) / (2 * wg B ^ 2) - VE v / 8|
      ≤ |-(n : ℝ) / (2 * wg B) + QE Δ v R (bg B) / (2 * wg B ^ 2)| + |VE v / 8| := abs_sub _ _
    _ ≤ |-(n : ℝ) / (2 * wg B)| + |QE Δ v R (bg B) / (2 * wg B ^ 2)| + |VE v / 8| := by
        linarith [abs_add_le (-(n : ℝ) / (2 * wg B)) (QE Δ v R (bg B) / (2 * wg B ^ 2))]
    _ ≤ _ := by rw [t1, t2, t3]; linarith

theorem H_le : Hbb Δ v B ≤ G3f Δ v R ℬ ∧ Hbw Δ v R B ≤ G3f Δ v R ℬ ∧
    Hww Δ v R B ≤ G3f Δ v R ℬ := by
  have hW := hℬ.2.1
  have hBwL : ℬ.wL ≤ B.wL := hsub.2.2.1
  have hA := AE_nonneg (Δ := Δ) hv
  have hBm := Bmx_nonneg' (ℬ := ℬ)
  have hQm0 := Qmx_nonneg (R := R) (Δ := Δ) (ℬ := ℬ) hv
  have hW2 : ℬ.wL ^ 2 ≤ B.wL ^ 2 := pow_le_pow_left₀ hW.le hBwL 2
  have hW3 : ℬ.wL ^ 3 ≤ B.wL ^ 3 := pow_le_pow_left₀ hW.le hBwL 3
  have hb1 : AE Δ v / B.wL ≤ AE Δ v / ℬ.wL := div_le_div_of_nonneg_left hA hW hBwL
  have hmx : max |BEs Δ v R - B.bL * AE Δ v| |BEs Δ v R - B.bH * AE Δ v| ≤
      |BEs Δ v R| + Bmx ℬ * AE Δ v :=
    max_le (abs_BE_sub_le hv (abs_le_Bmx hsub le_rfl hB.1))
      (abs_BE_sub_le hv (abs_le_Bmx hsub hB.1 le_rfl))
  have hb2 : Hbw Δ v R B ≤ (|BEs Δ v R| + Bmx ℬ * AE Δ v) / ℬ.wL ^ 2 :=
    (div_le_div_of_nonneg_right hmx (by positivity)).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hW2)
  have hq : max (QE Δ v R B.bL) (QE Δ v R B.bH) ≤ Qmx Δ v R ℬ :=
    max_le (QE_le_Qmx hv (abs_le_Bmx hsub le_rfl hB.1))
      (QE_le_Qmx hv (abs_le_Bmx hsub hB.1 le_rfl))
  have hb3 : Hww Δ v R B ≤ (n : ℝ) / (2 * ℬ.wL ^ 2) + Qmx Δ v R ℬ / ℬ.wL ^ 3 := by
    unfold Hww
    have e1 : (n : ℝ) / (2 * B.wL ^ 2) ≤ (n : ℝ) / (2 * ℬ.wL ^ 2) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
    have e2 : max (QE Δ v R B.bL) (QE Δ v R B.bH) / B.wL ^ 3 ≤ Qmx Δ v R ℬ / ℬ.wL ^ 3 :=
      (div_le_div_of_nonneg_right hq (pow_pos (hW.trans_le hBwL) 3).le).trans
        (div_le_div_of_nonneg_left hQm0 (by positivity) hW3)
    linarith
  have hp1 : 0 ≤ AE Δ v / ℬ.wL := by positivity
  have hp2 : 0 ≤ (|BEs Δ v R| + Bmx ℬ * AE Δ v) / ℬ.wL ^ 2 := by positivity
  have hp3 : 0 ≤ (n : ℝ) / (2 * ℬ.wL ^ 2) + Qmx Δ v R ℬ / ℬ.wL ^ 3 := by positivity
  unfold G3f
  refine ⟨?_, ?_, ?_⟩
  · show AE Δ v / B.wL ≤ _; linarith
  · linarith
  · linarith

omit hB hsub in
theorem G3f_nonneg : 0 ≤ G3f Δ v R ℬ := by
  have hW := hℬ.2.1
  have hA := AE_nonneg (Δ := Δ) hv
  have hBm := Bmx_nonneg' (ℬ := ℬ)
  have hQm0 := Qmx_nonneg (R := R) (Δ := Δ) (ℬ := ℬ) hv
  unfold G3f
  exact add_nonneg (add_nonneg (div_nonneg hA hW.le) (div_nonneg (add_nonneg (abs_nonneg _)
    (mul_nonneg hBm hA)) (by positivity))) (add_nonneg (by positivity) (div_nonneg hQm0 (by positivity)))

/-- `T_E` is at most linear in the radius once the radii are at most one. -/
theorem TE_le_lin {η : ℝ} (hη1 : η ≤ 1) (hρb : rb B ≤ η) (hρw : rw B ≤ η) :
    TE Δ v R B ≤ (G1f Δ v R ℬ + G2f Δ v R ℬ + 2 * G3f Δ v R ℬ) * η := by
  have hρb0 : 0 ≤ rb B := by unfold rb; linarith [hB.1]
  have hρw0 : 0 ≤ rw B := by unfold rw; linarith [hB.2.2]
  obtain ⟨h1, h2, h3⟩ := H_le (R := R) (Δ := Δ) hv hℬ hB hsub
  have hG3 := G3f_nonneg (R := R) (Δ := Δ) hv hℬ
  have hb : rb B ^ 2 ≤ η := by nlinarith
  have hbw : rb B * rw B ≤ η := by nlinarith
  have hw2 : rw B ^ 2 ≤ η := by nlinarith
  have hHbb0 : 0 ≤ Hbb Δ v B := div_nonneg (AE_nonneg hv) (hℬ.2.1.trans_le hsub.2.2.1).le
  have hHbw0 : 0 ≤ Hbw Δ v R B := div_nonneg ((abs_nonneg _).trans (le_max_left _ _))
    (pow_pos (hℬ.2.1.trans_le hsub.2.2.1) 2).le
  have hHww0 : 0 ≤ Hww Δ v R B := by
    unfold Hww
    have := (QE_nonneg (Δ := Δ) (R := R) hv B.bL).trans
      (le_max_left (QE Δ v R B.bL) (QE Δ v R B.bH))
    have : 0 < B.wL := hℬ.2.1.trans_le hsub.2.2.1
    positivity
  have q1 : Hbb Δ v B * rb B ^ 2 ≤ G3f Δ v R ℬ * η := mul_le_mul h1 hb (sq_nonneg _) hG3
  have q2 : Hbw Δ v R B * (rb B * rw B) ≤ G3f Δ v R ℬ * η :=
    mul_le_mul h2 hbw (mul_nonneg hρb0 hρw0) hG3
  have q3 : Hww Δ v R B * rw B ^ 2 ≤ G3f Δ v R ℬ * η := mul_le_mul h3 hw2 (sq_nonneg _) hG3
  have l1 : |Sb Δ v R B| * rb B ≤ G1f Δ v R ℬ * η :=
    mul_le_mul (Sb_le hv hℬ hB hsub) hρb hρb0 ((abs_nonneg _).trans (Sb_le hv hℬ hB hsub))
  have l2 : |Sw Δ v R B| * rw B ≤ G2f Δ v R ℬ * η :=
    mul_le_mul (Sw_le hv hℬ hB hsub) hρw hρw0 ((abs_nonneg _).trans (Sw_le hv hℬ hB hsub))
  unfold TE
  have e : Hbb Δ v B * rb B ^ 2 + 2 * Hbw Δ v R B * rb B * rw B + Hww Δ v R B * rw B ^ 2 =
      Hbb Δ v B * rb B ^ 2 + 2 * (Hbw Δ v R B * (rb B * rw B)) + Hww Δ v R B * rw B ^ 2 := by ring
  rw [e]
  linarith

end Bounds

theorem shrink_eta : ∀ (δ s : ℝ) (K n : ℕ) (Δ v : Fin (K + n) → ℝ) (ℬ : Box) (u : Fin K → ℕ)
    (y : Fin n → ℕ), 0 < δ → 0 < s → (∀ j, 0 < Δ j) → (∀ j, 0 < v j) → ℬ.Valid →
    (∀ j, 1 ≤ Fin.append u y j) →
    ∀ ε > 0, ∃ η > 0, ∀ B : Box, B.Valid → B.Sub ℬ → B.bH - B.bL ≤ η → B.wH - B.wL ≤ η →
      etaC δ s Δ v B u y ≤ ε := by
  intro δ s K n Δ v ℬ u y hδ hs hΔ hv hℬ hz ε hε
  have hu : ∀ j, 1 ≤ u j := all_pos_left hz
  have hy : ∀ j, 1 ≤ y j := fun j => by have := hz (Fin.natAdd K j); rwa [Fin.append_right] at this
  have hvT : ∀ j, 0 < trn v j := fun j => hv _
  have hvE : ∀ j, 0 < evl v j := fun j => hv _
  have hcT : ∀ i, aP δ s u i ≤ dP δ s u i := aP_le_dP hδ hu
  have hcE : ∀ i, loE δ s u y i ≤ hiE δ s u y i := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [loE, hiE, Fin.cons_zero]; exact hcT _
    · simp only [loE, hiE, Fin.cons_succ]; exact lA_le_lD hδ (hy j)
  obtain ⟨X1, hX1d⟩ : ∃ X1, X1 = 2 * wB (trn Δ) (trn v) (aP δ s u) (dP δ s u) +
      wB (evl Δ) (evl v) (loE δ s u y) (hiE δ s u y) := ⟨_, rfl⟩
  obtain ⟨X2, hX2d⟩ : ∃ X2, X2 = OmC (trn v) (aP δ s u) (dP δ s u) +
      dC (evl v) (loE δ s u y) (hiE δ s u y) := ⟨_, rfl⟩
  have hX1 : 0 ≤ X1 := by
    have := wB_nonneg (trn Δ) (trn v) hcT; have := wB_nonneg (evl Δ) (evl v) hcE; rw [hX1d]; linarith
  have hX2 : 0 ≤ X2 := by
    have := OmC_nonneg hvT hcT; have := dC_nonneg hvE hcE; rw [hX2d]; linarith
  set R := Rst (loE δ s u y) (hiE δ s u y)
  have hW : 0 < ℬ.wL := hℬ.2.1
  have hBm : 0 ≤ Bmx ℬ := (abs_nonneg _).trans (le_max_left _ _)
  -- The coefficient; the `G`'s are nonnegative on `ℬ` itself.
  have hℬsub : ℬ.Sub ℬ := ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  have hG1 : 0 ≤ G1f (evl Δ) (evl v) R ℬ := (abs_nonneg _).trans (Sb_le hvE hℬ hℬ hℬsub)
  have hG2 : 0 ≤ G2f (evl Δ) (evl v) R ℬ := (abs_nonneg _).trans (Sw_le hvE hℬ hℬ hℬsub)
  have hG3 : 0 ≤ G3f (evl Δ) (evl v) R ℬ := G3f_nonneg hvE hℬ
  obtain ⟨L, hLd⟩ : ∃ L, L = X1 * (1 / ℬ.wL + Bmx ℬ / ℬ.wL ^ 2) + X2 / (2 * ℬ.wL ^ 2) +
      (G1f (evl Δ) (evl v) R ℬ + G2f (evl Δ) (evl v) R ℬ + 2 * G3f (evl Δ) (evl v) R ℬ) := ⟨_, rfl⟩
  have hL : 0 ≤ L := by rw [hLd]; positivity
  have hηp : 0 < min 1 (ε / (L + 1)) := lt_min one_pos (by positivity)
  refine ⟨min 1 (ε / (L + 1)), hηp, fun B hB hsub h1 h2 => ?_⟩
  obtain ⟨η, hηd⟩ : ∃ η, η = min 1 (ε / (L + 1)) := ⟨_, rfl⟩
  rw [← hηd] at h1 h2 hηp
  have hη1 : η ≤ 1 := hηd ▸ min_le_left _ _
  have hηε : L * η ≤ ε := by
    have h3 : η ≤ ε / (L + 1) := hηd ▸ min_le_right _ _
    calc L * η ≤ (L + 1) * η := by nlinarith
      _ ≤ (L + 1) * (ε / (L + 1)) := mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = ε := by field_simp
  have hBwL : ℬ.wL ≤ B.wL := hsub.2.2.1
  have hwgB := wg_ge hB hsub
  have hρb : rb B ≤ η := by unfold rb; linarith [hB.1]
  have hρw : rw B ≤ η := by unfold rw; linarith [hB.2.2]
  have hbg := abs_le_Bmx hsub (bg_in hB).1 (bg_in hB).2
  have hdb : ∀ b, B.bL ≤ b → b ≤ B.bH → |b - bg B| ≤ rb B := fun b h1 h2 => by
    unfold rb bg; rw [abs_le]; constructor <;> linarith
  have hdw : ∀ w, B.wL ≤ w → w ≤ B.wH → |w - wg B| ≤ rw B := fun w h1 h2 => by
    unfold rw wg; rw [abs_le]; constructor <;> linarith
  have hc1 : c1 B ≤ rb B / ℬ.wL + Bmx ℬ * rw B / ℬ.wL ^ 2 := by
    have hcor : ∀ b' w', B.bL ≤ b' → b' ≤ B.bH → B.wL ≤ w' → w' ≤ B.wH →
        |b' / w' - bg B / wg B| ≤ rb B / ℬ.wL + Bmx ℬ * rw B / ℬ.wL ^ 2 :=
      fun b' w' h1 h2 h3 h4 =>
        corner_bound hW (hBwL.trans h3) hwgB (hdb b' h1 h2) (hdw w' h3 h4) hbg
    unfold c1
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · exact hcor _ _ le_rfl hB.1 le_rfl hB.2.2
    · exact hcor _ _ le_rfl hB.1 hB.2.2 le_rfl
    · exact hcor _ _ hB.1 le_rfl le_rfl hB.2.2
    · exact hcor _ _ hB.1 le_rfl hB.2.2 le_rfl
  have hc2 : c2 B ≤ rw B / (2 * ℬ.wL ^ 2) := by
    unfold c2
    rw [← max_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
    exact max_le (inv_bound hW hBwL hwgB (hdw _ le_rfl hB.2.2))
      (inv_bound hW (hBwL.trans hB.2.2) hwgB (hdw _ hB.2.2 le_rfl))
  have hTE := TE_le_lin (R := R) (Δ := evl Δ) hvE hℬ hB hsub hη1 hρb hρw
  have e : etaC δ s Δ v B u y = c1 B * X1 + c2 B * X2 + TE (evl Δ) (evl v) R B := by
    rw [hX1d, hX2d]; unfold etaC; ring
  have k1 : c1 B * X1 ≤ (η / ℬ.wL + Bmx ℬ * η / ℬ.wL ^ 2) * X1 := by
    refine mul_le_mul_of_nonneg_right (hc1.trans ?_) hX1
    have a1 : rb B / ℬ.wL ≤ η / ℬ.wL := div_le_div_of_nonneg_right hρb hW.le
    have a2 : Bmx ℬ * rw B / ℬ.wL ^ 2 ≤ Bmx ℬ * η / ℬ.wL ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hρw hBm) (by positivity)
    linarith
  have k2 : c2 B * X2 ≤ η / (2 * ℬ.wL ^ 2) * X2 :=
    mul_le_mul_of_nonneg_right (hc2.trans (div_le_div_of_nonneg_right hρw (by positivity))) hX2
  have e2 : (η / ℬ.wL + Bmx ℬ * η / ℬ.wL ^ 2) * X1 + η / (2 * ℬ.wL ^ 2) * X2 +
      (G1f (evl Δ) (evl v) R ℬ + G2f (evl Δ) (evl v) R ℬ + 2 * G3f (evl Δ) (evl v) R ℬ) * η =
      L * η := by
    rw [hLd]; field_simp
  rw [e]
  linarith

theorem shrink_holds : Standalone.D19CondSensitivity.shrink := by
  refine ⟨shrink_eta, ?_⟩
  intro δ s K n Δ 𝒱 ℬ u y hδ hs hΔ h𝒱 hv hℬ hz ε hε
  obtain ⟨η, hη, M₀, h⟩ := limits_holds δ s K n Δ 𝒱 ℬ u y hδ hs hΔ h𝒱 hv hℬ hz ε hε
  refine ⟨η, hη, max M₀ 1, fun C M hC hw hM => ?_⟩
  have hM0 : 0 < M := lt_of_lt_of_le one_pos (le_of_max_le_right hM)
  have hc := certified_holds δ s M K n Δ 𝒱 ℬ C hδ hs hM0 hΔ h𝒱 hv hℬ hC
  have hD := hc.2.1 u y
  exact ⟨hD.1, hD.2.1.trans (h C M hC hw (le_of_max_le_left hM)).1⟩

end Novel.D19CondSensitivity
