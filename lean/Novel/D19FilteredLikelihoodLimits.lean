import Novel.D19FilteredLikelihoodCover

/-!
# Claim 036, part 4: both cover bounds tend to `D_filter`

On a fixed all-positive record, for a subbox `B ⊆ ℬ` and `M` subcells:
* `ε` scales as `1/M` (`epsQ_scale`) and is at most `ℬ`'s value at `M = 1` over `M`;
* `η` is at most `(L_b(ℬ) + L_w(ℬ))` times half the box width (the factors only decrease on
  subboxes).
Each cover term is then at most `exp(2(ε_N + ε_k) + η_N + η_k) D_filter`, and the lower term of a box
containing a maximizer at least `exp(−(2(ε_N + ε_k) + η_N + η_k)) D_filter`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick Standalone.D17ClockCells

variable {δ s : ℝ}

theorem hP_scale {m M : ℕ} (z : Fin m → ℕ) (k : Fin (m + 1)) :
    hP δ M z k = hP δ 1 z k / M := by
  unfold hP
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp [Fin.cons_succ]

theorem epsQ_scale {m M : ℕ} (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) :
    epsQ δ s M Δ v B z = epsQ δ s 1 Δ v B z / M := by
  unfold epsQ
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hP_scale, hP_scale (M := M)]; ring

theorem hP_nonneg (hδ : 0 < δ) {m M : ℕ} {z : Fin m → ℕ} (hz : ∀ j, 1 ≤ z j) (k : Fin (m + 1)) :
    0 ≤ hP δ M z k := by
  unfold hP
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · rw [Fin.cons_succ]; exact div_nonneg (sub_nonneg.2 (lA_lt_lD hδ (hz j)).le) (Nat.cast_nonneg _)

theorem Bmax_mono {B ℬ : Box} (hB : B.Valid) (hsub : B.Sub ℬ) : Bmax B ≤ Bmax ℬ :=
  max_le (abs_le_max_of_mem hsub.1 (hB.1.trans hsub.2.1))
    (abs_le_max_of_mem (hsub.1.trans hB.1) hsub.2.1)

theorem Cj_mono {m : ℕ} {Δ v : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B ℬ : Box}
    (hB : B.Valid) (hℬ : ℬ.Valid) (hsub : B.Sub ℬ) (z : Fin m → ℕ) (j : Fin m) :
    Cj δ s Δ v B z j ≤ Cj δ s Δ v ℬ z j := by
  unfold Cj
  have hR : 0 ≤ Rmax δ s z j := le_max_of_le_left (abs_nonneg _)
  have hBm := Bmax_mono hB hsub
  have hB0 : 0 ≤ Bmax B := le_max_of_le_left (abs_nonneg _)
  have h1 : 0 ≤ Rmax δ s z j + Bmax ℬ * Δ j + ℬ.wH * v j / 2 := by
    have := hB0.trans hBm; have := hΔ j; have := hv j
    have := (hB.2.1.trans_le hB.2.2).trans_le hsub.2.2.2; positivity
  calc (Rmax δ s z j + Bmax B * Δ j + B.wH * v j / 2) / (B.wL * v j)
      ≤ (Rmax δ s z j + Bmax ℬ * Δ j + ℬ.wH * v j / 2) / (B.wL * v j) := by
        refine div_le_div_of_nonneg_right ?_ (mul_pos hB.2.1 (hv j)).le
        have := mul_le_mul_of_nonneg_right hBm (hΔ j).le
        have := mul_le_mul_of_nonneg_right hsub.2.2.2 (hv j).le
        linarith
    _ ≤ _ := div_le_div_of_nonneg_left h1 (mul_pos hℬ.2.1 (hv j))
        (mul_le_mul_of_nonneg_right hsub.2.2.1 (hv j).le)

theorem epsQ_mono (hδ : 0 < δ) {m : ℕ} {Δ v : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j)
    {B ℬ : Box} (hB : B.Valid) (hℬ : ℬ.Valid) (hsub : B.Sub ℬ) {z : Fin m → ℕ} (hz : ∀ j, 1 ≤ z j) :
    epsQ δ s 1 Δ v B z ≤ epsQ δ s 1 Δ v ℬ z :=
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (Cj_mono hΔ hv hB hℬ hsub z j)
    (by have := hP_nonneg (M := 1) hδ hz j.castSucc; have := hP_nonneg (M := 1) hδ hz j.succ
        positivity)

theorem epsQ_nonneg (hδ : 0 < δ) {m M : ℕ} {Δ v : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j)
    (hv : ∀ j, 0 < v j) {B : Box} (hB : B.Valid) {z : Fin m → ℕ} (hz : ∀ j, 1 ≤ z j) :
    0 ≤ epsQ δ s M Δ v B z :=
  Finset.sum_nonneg fun j _ => mul_nonneg (Cj_nonneg hB hΔ hv z j)
    (by have := hP_nonneg (M := M) hδ hz j.castSucc; have := hP_nonneg (M := M) hδ hz j.succ
        positivity)

theorem Lb_nonneg {m : ℕ} {Δ v : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B : Box}
    (hB : B.Valid) (z : Fin m → ℕ) : 0 ≤ Lb δ s Δ v B z :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hΔ j).le (Cj_nonneg hB hΔ hv z j)

theorem Lw_nonneg {m : ℕ} {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) (Δ : Fin m → ℝ) {B : Box}
    (hB : B.Valid) (z : Fin m → ℕ) : 0 ≤ Lw δ s Δ v B z := by
  unfold Lw
  have := hB.2.1
  have h1 : 0 ≤ ∑ j, (Rmax δ s z j + Bmax B * Δ j) ^ 2 / (2 * B.wL ^ 2 * v j) :=
    Finset.sum_nonneg fun j _ => by have := hv j; positivity
  have h2 : 0 ≤ ∑ j, v j / 8 := Finset.sum_nonneg fun j _ => by have := hv j; positivity
  positivity

theorem Lb_mono {m : ℕ} {Δ v : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B ℬ : Box}
    (hB : B.Valid) (hℬ : ℬ.Valid) (hsub : B.Sub ℬ) (z : Fin m → ℕ) :
    Lb δ s Δ v B z ≤ Lb δ s Δ v ℬ z :=
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (Cj_mono hΔ hv hB hℬ hsub z j) (hΔ j).le

theorem Lw_mono {m : ℕ} {Δ v : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B ℬ : Box}
    (hB : B.Valid) (hℬ : ℬ.Valid) (hsub : B.Sub ℬ) (z : Fin m → ℕ) :
    Lw δ s Δ v B z ≤ Lw δ s Δ v ℬ z := by
  unfold Lw
  have hBm := Bmax_mono hB hsub
  have hB0 : 0 ≤ Bmax B := le_max_of_le_left (abs_nonneg _)
  have hw := hsub.2.2.1
  have hwL := hℬ.2.1
  have h1 : (m : ℝ) / (2 * B.wL) ≤ m / (2 * ℬ.wL) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
  have h2 : ∑ j, (Rmax δ s z j + Bmax B * Δ j) ^ 2 / (2 * B.wL ^ 2 * v j) ≤
      ∑ j, (Rmax δ s z j + Bmax ℬ * Δ j) ^ 2 / (2 * ℬ.wL ^ 2 * v j) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hΔj := hΔ j
    have hvj := hv j
    have hR : 0 ≤ Rmax δ s z j := le_max_of_le_left (abs_nonneg _)
    have hn : (Rmax δ s z j + Bmax B * Δ j) ^ 2 ≤ (Rmax δ s z j + Bmax ℬ * Δ j) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) 2
    have hd : 2 * ℬ.wL ^ 2 * v j ≤ 2 * B.wL ^ 2 * v j := by
      have : ℬ.wL ^ 2 ≤ B.wL ^ 2 := pow_le_pow_left₀ hwL.le hw 2
      nlinarith
    calc (Rmax δ s z j + Bmax B * Δ j) ^ 2 / (2 * B.wL ^ 2 * v j)
        ≤ (Rmax δ s z j + Bmax ℬ * Δ j) ^ 2 / (2 * B.wL ^ 2 * v j) :=
          div_le_div_of_nonneg_right hn (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hd
  linarith

theorem etaQ_le {m : ℕ} {Δ v : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B ℬ : Box}
    (hB : B.Valid) (hℬ : ℬ.Valid) (hsub : B.Sub ℬ) (z : Fin m → ℕ) {η : ℝ}
    (hη : B.bH - B.bL ≤ η ∧ B.wH - B.wL ≤ η) :
    etaQ δ s Δ v B z ≤ (Lb δ s Δ v ℬ z + Lw δ s Δ v ℬ z) * (η / 2) := by
  unfold etaQ
  have h1 := Lb_mono (δ := δ) (s := s) hΔ hv hB hℬ hsub z
  have h2 := Lw_mono (δ := δ) (s := s) hΔ hv hB hℬ hsub z
  have h3 := Lb_nonneg (δ := δ) (s := s) hΔ hv hB z
  have h4 := Lw_nonneg (δ := δ) (s := s) hv Δ hB z
  have hb : 0 ≤ (B.bH - B.bL) / 2 := by linarith [hB.1]
  have hw : 0 ≤ (B.wH - B.wL) / 2 := by linarith [hB.2.2]
  have hb' : (B.bH - B.bL) / 2 ≤ η / 2 := by linarith [hη.1]
  have hw' : (B.wH - B.wL) / 2 ≤ η / 2 := by linarith [hη.2]
  calc Lb δ s Δ v B z * ((B.bH - B.bL) / 2) + Lw δ s Δ v B z * ((B.wH - B.wL) / 2)
      ≤ Lb δ s Δ v ℬ z * (η / 2) + Lw δ s Δ v ℬ z * (η / 2) := by
        gcongr
        · linarith
        · linarith
    _ = _ := by ring

theorem le_exp_of_neg {Q L a : ℝ} (h : Real.exp (-a) * Q ≤ L) : Q ≤ Real.exp a * L := by
  calc Q = Real.exp a * (Real.exp (-a) * Q) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

theorem neg_le_of_exp {Q L a : ℝ} (h : L ≤ Real.exp a * Q) : Real.exp (-a) * L ≤ Q := by
  calc Real.exp (-a) * L ≤ Real.exp (-a) * (Real.exp a * Q) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Q := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- `Q_N/Q_k ≤ e^{a + b} L_N/L_k` from `Q_N ≤ e^a L_N` and `L_k ≤ e^b Q_k`. -/
theorem ratio_up {QN Qk LN Lk a b : ℝ} (hQk : 0 < Qk) (hLk : 0 < Lk) (hLN : 0 ≤ LN)
    (h1 : QN ≤ Real.exp a * LN) (h2 : Lk ≤ Real.exp b * Qk) :
    QN / Qk ≤ Real.exp (a + b) * (LN / Lk) := by
  rw [div_le_iff₀ hQk]
  have hr : 1 ≤ Real.exp b * Qk / Lk := (one_le_div hLk).2 h2
  calc QN ≤ Real.exp a * LN * 1 := by rw [mul_one]; exact h1
    _ ≤ Real.exp a * LN * (Real.exp b * Qk / Lk) :=
        mul_le_mul_of_nonneg_left hr (mul_nonneg (Real.exp_pos _).le hLN)
    _ = _ := by rw [Real.exp_add]; field_simp

/-- `e^{−(a + b)} L_N/L_k ≤ Q_N/Q_k` from `e^{−a} L_N ≤ Q_N` and `Q_k ≤ e^b L_k`. -/
theorem ratio_down {QN Qk LN Lk a b : ℝ} (hQk : 0 < Qk) (hLk : 0 < Lk) (hLN : 0 ≤ LN)
    (h1 : Real.exp (-a) * LN ≤ QN) (h2 : Qk ≤ Real.exp b * Lk) :
    Real.exp (-(a + b)) * (LN / Lk) ≤ QN / Qk := by
  rw [le_div_iff₀ hQk]
  have h0 : 0 ≤ Real.exp (-(a + b)) * (LN / Lk) := by have := Real.exp_pos (-(a + b)); positivity
  calc Real.exp (-(a + b)) * (LN / Lk) * Qk ≤ Real.exp (-(a + b)) * (LN / Lk) * (Real.exp b * Lk) :=
        mul_le_mul_of_nonneg_left h2 h0
    _ = Real.exp (-a) * LN := by
        rw [neg_add, Real.exp_add]
        have hb : Real.exp (-b) * Real.exp b = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        field_simp
        linear_combination LN * hb
    _ ≤ QN := h1

/-- The total exponent of one box and clock. -/
noncomputable def Xexp (δ s : ℝ) (M : ℕ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box) (u : Fin K → ℕ)
    (y : Fin n → ℕ) : ℝ :=
  2 * (epsQ δ s M Δ v B (Fin.append u y) + epsQ δ s M (trn Δ) (trn v) B u) +
    (etaQ δ s Δ v B (Fin.append u y) + etaQ δ s (trn Δ) (trn v) B u)

/-- Each cover term is within `e^X` of the likelihood ratio at its center, and each lower term is
at least `e^{−X}` times the ratio anywhere in its box. -/
theorem box_exp (hδ : 0 < δ) (hs : 0 < s) {M : ℕ} (hM : 0 < M) {K n : ℕ} (Δ v : Fin (K + n) → ℝ)
    (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B : Box} (hB : B.Valid) (u : Fin K → ℕ) (y : Fin n → ℕ)
    (hz : ∀ j, 1 ≤ Fin.append u y j) :
    term δ s M Δ v B u y ≤ Real.exp (Xexp δ s M Δ v B u y) * gF δ s Δ v (ctr B).1 (ctr B).2 u y ∧
      ∀ p, B.Mem p → Real.exp (-Xexp δ s M Δ v B u y) * gF δ s Δ v p.1 p.2 u y ≤
        termLow δ s M Δ v B u y := by
  have hc := ctr_mem hB
  have hu := all_pos_left hz
  have hwc : 0 < (ctr B).2 := hB.2.1.trans_le hc.2.1
  set z := Fin.append u y
  set εN := epsQ δ s M Δ v B z
  set εk := epsQ δ s M (trn Δ) (trn v) B u
  set ηN := etaQ δ s Δ v B z
  set ηk := etaQ δ s (trn Δ) (trn v) B u
  have qN := quad_holds δ s (K + n) M Δ v B (ctr B).1 (ctr B).2 z hδ hs hM hΔ hv hB hc hz
  have qk := quad_holds δ s K M (trn Δ) (trn v) B (ctr B).1 (ctr B).2 u hδ hs hM (fun j => hΔ _)
    (fun j => hv _) hB hc hu
  have hLkc := Lz_pos hδ hs (muF (trn Δ) (trn v) (ctr B).1 (ctr B).2) (sdF (trn v) (ctr B).2)
    (fun j => sdF_pos (fun j => hv _) hwc j) u
  have hLNc := Lz_pos hδ hs (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (fun j => sdF_pos hv hwc j) z
  set LNc := Lz δ s (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) z
  set Lkc := Lz δ s (muF (trn Δ) (trn v) (ctr B).1 (ctr B).2) (sdF (trn v) (ctr B).2) u
  set QN := Qs δ s M (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) z
  set Qk := Qs δ s M (muF (trn Δ) (trn v) (ctr B).1 (ctr B).2) (sdF (trn v) (ctr B).2) u
  have hgc : gF δ s Δ v (ctr B).1 (ctr B).2 u y = LNc / Lkc := rfl
  have hX : Xexp δ s M Δ v B u y = 2 * (εN + εk) + (ηN + ηk) := rfl
  constructor
  · have hup := ratio_up qk.1 hLkc hLNc.le (le_exp_of_neg qN.2.1) qk.2.2
    have ht : term δ s M Δ v B u y ≤ Real.exp (εN + εk + ηN + ηk) * (QN / Qk) := by
      refine (min_le_right _ _).trans (le_of_eq ?_)
      show Real.exp (εN + εk + ηN + ηk) * QN / Qk = _
      rw [mul_div_assoc]
    calc term δ s M Δ v B u y ≤ Real.exp (εN + εk + ηN + ηk) * (QN / Qk) := ht
      _ ≤ Real.exp (εN + εk + ηN + ηk) * (Real.exp (εN + εk) * (LNc / Lkc)) :=
          mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le
      _ = _ := by
          rw [hX, hgc, ← mul_assoc, ← Real.exp_add]; ring_nf
  · intro p hp
    obtain ⟨hp1, hp2⟩ := near_ctr hp
    have hcp1 : |(ctr B).1 - p.1| ≤ (B.bH - B.bL) / 2 := by rw [abs_sub_comm]; exact hp1
    have hcp2 : |(ctr B).2 - p.2| ≤ (B.wH - B.wL) / 2 := by rw [abs_sub_comm]; exact hp2
    have hwp : 0 < p.2 := hB.2.1.trans_le hp.2.1
    have pN := Lz_param hδ hs hM hB hp hc hp1 hp2 Δ v z hΔ hv hz
    have pk := Lz_param hδ hs hM hB hc hp hcp1 hcp2 (trn Δ) (trn v) u (fun j => hΔ _) (fun j => hv _) hu
    have hLkp := Lz_pos hδ hs (muF (trn Δ) (trn v) p.1 p.2) (sdF (trn v) p.2)
      (fun j => sdF_pos (fun j => hv _) hwp j) u
    have hLNp := Lz_pos hδ hs (muF Δ v p.1 p.2) (sdF v p.2) (fun j => sdF_pos hv hwp j) z
    have hgp : gF δ s Δ v p.1 p.2 u y =
        Lz δ s (muF Δ v p.1 p.2) (sdF v p.2) z / Lz δ s (muF (trn Δ) (trn v) p.1 p.2) (sdF (trn v) p.2) u :=
      rfl
    have hg0 : 0 ≤ gF δ s Δ v p.1 p.2 u y := gF_nonneg δ s Δ v p.1 p.2 u y
    have hcg := ratio_down hLkc hLkp hLNp.le (neg_le_of_exp pN) pk
    rw [← hgp, ← hgc] at hcg
    have hdown := ratio_down qk.1 hLkc hLNc.le (neg_le_of_exp qN.2.2) (le_exp_of_neg qk.2.1)
    rw [← hgc] at hdown
    have ht : termLow δ s M Δ v B u y = Real.exp (-(εN + εk)) * (QN / Qk) := by
      show Real.exp (-(εN + εk)) * QN / Qk = _
      rw [mul_div_assoc]
    rw [ht]
    calc Real.exp (-Xexp δ s M Δ v B u y) * gF δ s Δ v p.1 p.2 u y
        = Real.exp (-(εN + εk)) * (Real.exp (-(εN + εk)) *
            (Real.exp (-(ηN + ηk)) * gF δ s Δ v p.1 p.2 u y)) := by
          rw [hX, ← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(εN + εk)) * (Real.exp (-(εN + εk)) * gF δ s Δ v (ctr B).1 (ctr B).2 u y) := by
          gcongr
      _ ≤ Real.exp (-(εN + εk)) * (QN / Qk) := by gcongr

/-- The exponent of a subbox of `ℬ` of width at most `η`, uniformly in the subbox and `M`. -/
theorem Xexp_le (hδ : 0 < δ) {M : ℕ} {K n : ℕ} {Δ v : Fin (K + n) → ℝ} (hΔ : ∀ j, 0 < Δ j)
    (hv : ∀ j, 0 < v j) {B ℬ : Box} (hB : B.Valid) (hℬ : ℬ.Valid) (hsub : B.Sub ℬ) {u : Fin K → ℕ}
    {y : Fin n → ℕ} (hz : ∀ j, 1 ≤ Fin.append u y j) {η : ℝ}
    (hη : B.bH - B.bL ≤ η ∧ B.wH - B.wL ≤ η) :
    Xexp δ s M Δ v B u y ≤
      2 * (epsQ δ s 1 Δ v ℬ (Fin.append u y) + epsQ δ s 1 (trn Δ) (trn v) ℬ u) / M +
      (Lb δ s Δ v ℬ (Fin.append u y) + Lw δ s Δ v ℬ (Fin.append u y) +
        (Lb δ s (trn Δ) (trn v) ℬ u + Lw δ s (trn Δ) (trn v) ℬ u)) * (η / 2) := by
  have hu := all_pos_left hz
  have hΔ' : ∀ j, 0 < trn Δ j := fun j => hΔ _
  have hv' : ∀ j, 0 < trn v j := fun j => hv _
  unfold Xexp
  rw [epsQ_scale, epsQ_scale (M := M) (trn Δ)]
  have e1 := epsQ_mono (s := s) hδ hΔ hv hB hℬ hsub hz
  have e2 := epsQ_mono (s := s) hδ hΔ' hv' hB hℬ hsub hu
  have h1 := etaQ_le (δ := δ) (s := s) hΔ hv hB hℬ hsub (Fin.append u y) hη
  have h2 := etaQ_le (δ := δ) (s := s) hΔ' hv' hB hℬ hsub u hη
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hd : 2 * (epsQ δ s 1 Δ v B (Fin.append u y) / M + epsQ δ s 1 (trn Δ) (trn v) B u / M) ≤
      2 * (epsQ δ s 1 Δ v ℬ (Fin.append u y) + epsQ δ s 1 (trn Δ) (trn v) ℬ u) / M := by
    rw [← add_div, mul_div_assoc]
    gcongr
  linarith

/-- Part 4: both cover bounds tend to `D_filter`. -/
theorem limits_holds : Standalone.D19FilteredLikelihood.limits := by
  intro δ s K n Δ 𝒱 ℬ u y hδ hs hΔ h𝒱 hv hℬ hz ε hε
  obtain ⟨⟨θ, hθ, hθe⟩, hmax, hDpos, -⟩ :=
    exact_holds.2.2.2.2.2 δ s K n Δ 𝒱 ℬ u y hδ hs hΔ h𝒱 hv hℬ
  have hu := all_pos_left hz
  have hΔ' : ∀ j, 0 < trn Δ j := fun j => hΔ _
  have hvt : ∀ v ∈ 𝒱, ∀ j, 0 < trn v j := fun v hvv j => hv v hvv _
  set A : (Fin (K + n) → ℝ) → ℝ := fun v =>
    2 * (epsQ δ s 1 Δ v ℬ (Fin.append u y) + epsQ δ s 1 (trn Δ) (trn v) ℬ u)
  set L : (Fin (K + n) → ℝ) → ℝ := fun v =>
    Lb δ s Δ v ℬ (Fin.append u y) + Lw δ s Δ v ℬ (Fin.append u y) +
      (Lb δ s (trn Δ) (trn v) ℬ u + Lw δ s (trn Δ) (trn v) ℬ u)
  have hA0 : ∀ v ∈ 𝒱, 0 ≤ A v := fun v hvv => by
    have := epsQ_nonneg (s := s) (M := 1) hδ hΔ (hv v hvv) hℬ hz
    have := epsQ_nonneg (s := s) (M := 1) hδ hΔ' (hvt v hvv) hℬ hu
    simp only [A]; positivity
  have hL0 : ∀ v ∈ 𝒱, 0 ≤ L v := fun v hvv => by
    have := Lb_nonneg (δ := δ) (s := s) hΔ (hv v hvv) hℬ (Fin.append u y)
    have := Lw_nonneg (δ := δ) (s := s) (hv v hvv) Δ hℬ (Fin.append u y)
    have := Lb_nonneg (δ := δ) (s := s) hΔ' (hvt v hvv) hℬ u
    have := Lw_nonneg (δ := δ) (s := s) (hvt v hvv) (trn Δ) hℬ u
    simp only [L]; positivity
  set S₁ := ∑ v ∈ 𝒱, A v
  set S₂ := ∑ v ∈ 𝒱, L v
  have hS₂ : 0 ≤ S₂ := Finset.sum_nonneg hL0
  refine ⟨ε / (S₂ + 1), div_pos hε (by linarith), ⌈2 * S₁ / ε⌉₊ + 1, fun C M hC hη hM₀ => ?_⟩
  have hMpos : 0 < M := lt_of_lt_of_le (Nat.succ_pos _) hM₀
  have hMR : 2 * S₁ / ε < M := by
    have := Nat.le_ceil (2 * S₁ / ε)
    have : ((⌈2 * S₁ / ε⌉₊ + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hM₀
    push_cast at this; linarith
  have hS₁M : S₁ / M ≤ ε / 2 := by
    have hM' : (0 : ℝ) < M := by exact_mod_cast hMpos
    rw [div_lt_iff₀ hε] at hMR
    rw [div_le_iff₀ hM']; linarith
  have hS₂η : S₂ * (ε / (S₂ + 1) / 2) ≤ ε / 2 := by
    rw [mul_div_assoc', mul_div_assoc', div_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  -- Every box and clock has exponent at most `ε`.
  have hXε : ∀ B ∈ C, ∀ v ∈ 𝒱, Xexp δ s M Δ v B u y ≤ ε := fun B hB v hvv => by
    have hX := Xexp_le (s := s) (M := M) hδ hΔ (hv v hvv) (hC.1 B hB).1 hℬ (hC.1 B hB).2 hz (hη B hB)
    have h1 : A v / M ≤ S₁ / M :=
      div_le_div_of_nonneg_right (Finset.single_le_sum hA0 hvv) (Nat.cast_nonneg _)
    have h2 : L v * (ε / (S₂ + 1) / 2) ≤ S₂ * (ε / (S₂ + 1) / 2) :=
      mul_le_mul_of_nonneg_right (Finset.single_le_sum hL0 hvv) (by positivity)
    have : Xexp δ s M Δ v B u y ≤ A v / M + L v * (ε / (S₂ + 1) / 2) := hX
    linarith
  constructor
  · unfold Dcert
    rw [ite_eq_left_of_eq_true _ _ (eq_true hz)]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity)
      (iSup₂_le fun B hB => iSup₂_le fun v hvv => ENNReal.ofReal_le_ofReal ?_)
    have hcB := ctr_mem (hC.1 B hB).1
    have hsub := (hC.1 B hB).2
    have hgc := hmax (v, ctr B) ⟨hvv, ⟨hsub.1.trans hcB.1.1, hcB.1.2.trans hsub.2.1⟩,
      ⟨hsub.2.2.1.trans hcB.2.1, hcB.2.2.trans hsub.2.2.2⟩⟩
    have hg0 := gF_nonneg δ s Δ v (ctr B).1 (ctr B).2 u y
    calc term δ s M Δ v B u y
        ≤ Real.exp (Xexp δ s M Δ v B u y) * gF δ s Δ v (ctr B).1 (ctr B).2 u y :=
          (box_exp hδ hs hMpos Δ v hΔ (hv v hvv) (hC.1 B hB).1 u y hz).1
      _ ≤ Real.exp ε * gF δ s Δ v (ctr B).1 (ctr B).2 u y :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hXε B hB v hvv)) hg0
      _ ≤ _ := mul_le_mul_of_nonneg_left hgc (Real.exp_pos _).le
  · obtain ⟨B, hB, hθB⟩ := hC.2 θ.2 hθ.2
    have hfin : (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (termLow δ s M Δ v B u y)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top
        (iSup₂_le fun B hB => iSup₂_le fun v hvv => ENNReal.ofReal_le_one.2 ?_)
      have hwc : 0 < (ctr B).2 := (hC.1 B hB).1.2.1.trans_le (ctr_mem (hC.1 B hB).1).2.1
      exact (box_bounds hδ hs hMpos Δ v hΔ (hv v hvv) (hC.1 B hB).1 u y hz
        (ctr_mem (hC.1 B hB).1)).2.trans (gF_le_one hδ hs Δ v (hv v hvv) _ hwc u y)
    have hlow := (box_exp hδ hs hMpos Δ θ.1 hΔ (hv _ hθ.1) (hC.1 B hB).1 u y hz).2 θ.2 hθB
    rw [hθe] at hlow
    unfold Dlow
    calc Real.exp (-ε) * Dfilter δ s Δ 𝒱 ℬ u y
        ≤ Real.exp (-Xexp δ s M Δ θ.1 B u y) * Dfilter δ s Δ 𝒱 ℬ u y :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (neg_le_neg (hXε B hB θ.1 hθ.1))) hDpos.le
      _ ≤ termLow δ s M Δ θ.1 B u y := hlow
      _ ≤ _ := (ENNReal.ofReal_le_iff_le_toReal hfin).1
          (le_iSup₂_of_le B hB (le_iSup₂_of_le θ.1 hθ.1 le_rfl))

end Novel.D19FilteredLikelihood
