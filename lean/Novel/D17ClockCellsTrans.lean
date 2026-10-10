import Novel.D17ClockCellsScale

/-!
# Claim 034, part 1: the transition bound

From `x ∈ [a, d_S)` and `(b, w) ∈ B`, the next log price is `Normal(log x + bΔ − wv/2, wv)`. Its mean
lies in `[M₋, M₊]` (unbounded below when `a = 0`) and its standard deviation in `[s₋, s₊]` (2).
* **The mean.** At every scale, the target mass is maximized over the means at the clipped
  midpoint `m*` (claim 029's `cellP_le_clip`).
* **The scale.** If the log target straddles `m*`, both endpoint terms decrease in the scale, so
  `s₋` is best. Otherwise, after reflection, the mass is `Φ(r/s) − Φ(l/s)` with `0 < l < r`,
  maximized at the clipped (3) (`scale_le`).
* **The zero target** `[0, d_T)` has mass `Φ((log d_T − m)/s)`, decreasing in `m`, and monotone in
  `s` with the sign of `log d_T − M₋`.
* **The trapped state** gives mass one to a zero target (where `W = 1`) and zero otherwise.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D17ClockCells

open Standalone.D17ClockCells Standalone.D14FixedTick Novel.D14FixedTick Novel.GaussianCell

section

variable {B : Box} {a dS c dT Δ v : ℝ}

theorem sdLo_pos (hB : B.Valid) (hv : 0 < v) : 0 < sdLo B v :=
  Real.sqrt_pos.2 (mul_pos hB.2.1 hv)

theorem sdLo_le_sdHi (hB : B.Valid) (hv : 0 < v) : sdLo B v ≤ sdHi B v :=
  Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hB.2.2 hv.le)

theorem sd_mem (hv : 0 < v) {p : ℝ × ℝ} (hp : B.Mem p) :
    Real.sqrt (p.2 * v) ∈ Icc (sdLo B v) (sdHi B v) :=
  ⟨Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hp.2.1 hv.le),
   Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hp.2.2 hv.le)⟩

theorem clip_mem {sL sH x : ℝ} (h : sL ≤ sH) : min sH (max sL x) ∈ Icc sL sH :=
  ⟨le_min h (le_max_left _ _), min_le_left _ _⟩

theorem sstar_mem (hB : B.Valid) (hv : 0 < v) (m : ℝ) :
    sstarC B c dT v m ∈ Icc (sdLo B v) (sdHi B v) := by
  unfold sstarC; dsimp only
  split_ifs
  · exact ⟨le_rfl, sdLo_le_sdHi hB hv⟩
  · exact clip_mem (sdLo_le_sdHi hB hv)

theorem gmass_pos_eq (hc : c ≠ 0) (m s : ℝ) :
    gmass c dT m s = cellP s (Real.log c) (Real.log dT) m := by
  simp [gmass, hc, cellP, Phi_eq]

theorem gmass_zero (m s : ℝ) : gmass 0 dT m s = Φ ((Real.log dT - m) / s) := by
  simp [gmass, Phi_eq]

/-- After reflection the mass is `Φ(r/s) − Φ(l/s)`. -/
theorem cellP_refl_lo {L R m s : ℝ} : cellP s L R m = Φ ((R - m) / s) - Φ ((L - m) / s) := rfl

theorem cellP_refl_hi {L R m s : ℝ} :
    cellP s L R m = Φ ((m - L) / s) - Φ ((m - R) / s) := by
  rw [cellP, show (R - m) / s = -((m - R) / s) by ring, show (L - m) / s = -((m - L) / s) by ring,
    Φ_neg, Φ_neg]
  ring

/-- The scale step at a fixed mean `m`. -/
theorem scale_step (hB : B.Valid) (hv : 0 < v) (hc : 0 < c) (hcd : c < dT) (m : ℝ) {s : ℝ}
    (hs : s ∈ Icc (sdLo B v) (sdHi B v)) :
    cellP s (Real.log c) (Real.log dT) m ≤ gmass c dT m (sstarC B c dT v m) := by
  rw [gmass_pos_eq hc.ne']
  have hLR : Real.log c < Real.log dT := Real.log_lt_log hc hcd
  have hsL := sdLo_pos hB hv
  have hs0 : 0 < s := hsL.trans_le hs.1
  unfold sstarC; dsimp only
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    rw [cellP_refl_lo, cellP_refl_lo]
    have e1 : (Real.log dT - m) / s ≤ (Real.log dT - m) / sdLo B v :=
      div_le_div_of_nonneg_left h2 hsL hs.1
    have e2 : (Real.log c - m) / sdLo B v ≤ (Real.log c - m) / s := by
      rw [show Real.log c - m = -(m - Real.log c) by ring, neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (by linarith) hsL hs.1
    linarith [Φ_mono e1, Φ_mono e2]
  · rw [not_and_or, not_le, not_le] at h
    rcases h with h | h
    · -- `m < L`: `l = L − m`, `r = R − m`.
      have hle : Real.log c - m ≤ Real.log dT - m := by linarith
      rw [abs_of_pos h, abs_of_pos (by linarith : 0 < Real.log dT - m), min_eq_left hle,
        max_eq_right hle, cellP_refl_lo, cellP_refl_lo]
      exact scale_le h (by linarith) hsL (sdLo_le_sdHi hB hv) hs
    · -- `m > R`: `l = m − R`, `r = m − L`.
      have hle : m - Real.log dT ≤ m - Real.log c := by linarith
      rw [abs_of_neg (by linarith : Real.log c - m < 0), abs_of_neg h, neg_sub, neg_sub,
        min_eq_right hle, max_eq_left hle, cellP_refl_hi, cellP_refl_hi]
      exact scale_le (by linarith) (by linarith) hsL (sdLo_le_sdHi hB hv) hs

theorem meanLo_le_meanHi (hB : B.Valid) (ha : 0 < a) (hadS : a < dS) (hΔ : 0 < Δ) (hv : 0 < v) :
    meanLo B a Δ v ≤ meanHi B dS Δ v := by
  unfold meanLo meanHi
  have := Real.log_lt_log ha hadS
  have := mul_le_mul_of_nonneg_right hB.1 hΔ.le
  have := mul_le_mul_of_nonneg_right (hB.2.1.le.trans hB.2.2) hv.le
  nlinarith [mul_le_mul_of_nonneg_right hB.2.2 hv.le]

/-- The positive-target bound over the mean/scale rectangle. -/
theorem rect_le (hB : B.Valid) (hv : 0 < v) (hc : 0 < c) (hcd : c < dT) {m : ℝ}
    (hm1 : a ≠ 0 → meanLo B a Δ v ≤ m) (hm2 : m ≤ meanHi B dS Δ v) {s : ℝ}
    (hs : s ∈ Icc (sdLo B v) (sdHi B v)) :
    cellP s (Real.log c) (Real.log dT) m ≤ Wclock B a dS c dT Δ v := by
  have hLR : Real.log c ≤ Real.log dT := (Real.log_lt_log hc hcd).le
  have hs0 : 0 < s := (sdLo_pos hB hv).trans_le hs.1
  have hmean : cellP s (Real.log c) (Real.log dT) m ≤
      cellP s (Real.log c) (Real.log dT) (mstarC B a dS c dT Δ v) := by
    unfold mstarC; dsimp only
    split_ifs with ha
    · have := cellP_le_clip hs0 hLR (A := min m ((Real.log c + Real.log dT) / 2))
        (B := meanHi B dS Δ v) ((min_le_left _ _).trans hm2) (m := m) ⟨min_le_left _ _, hm2⟩
      rwa [max_eq_right (min_le_right _ _)] at this
    · exact cellP_le_clip hs0 hLR ((hm1 ha).trans hm2) ⟨hm1 ha, hm2⟩
  refine hmean.trans ((scale_step hB hv hc hcd _ hs).trans (le_of_eq ?_))
  unfold Wclock; dsimp only; rw [ite_eq_right hc.ne']

/-- The zero-target bound over the rectangle, from a positive source. -/
theorem zero_le (hB : B.Valid) (hv : 0 < v) (ha : a ≠ 0) {m : ℝ} (hm : meanLo B a Δ v ≤ m) {s : ℝ}
    (hs : s ∈ Icc (sdLo B v) (sdHi B v)) :
    Φ ((Real.log dT - m) / s) ≤ Wclock B a dS 0 dT Δ v := by
  have hsL := sdLo_pos hB hv
  have hs0 : 0 < s := hsL.trans_le hs.1
  unfold Wclock; dsimp only
  simp only [ite_true, ha, ite_false, Phi_eq]
  set t := Real.log dT - meanLo B a Δ v
  have h1 : Φ ((Real.log dT - m) / s) ≤ Φ (t / s) :=
    Φ_mono (div_le_div_of_nonneg_right (by simp only [t]; linarith) hs0.le)
  split_ifs with ht
  · exact h1.trans (Φ_mono (div_le_div_of_nonneg_left ht hsL hs.1))
  · have ht' : t < 0 := not_le.1 ht
    refine h1.trans (Φ_mono ?_)
    rw [div_le_div_iff₀ hs0 (hs0.trans_le hs.2)]
    nlinarith [hs.2]

end

/-- Part 1. -/
theorem transition_holds : transition := by
  intro B a dS c dT Δ v hB ha hadS hc hcd hΔ hv
  have hsL := sdLo_pos hB hv
  have hdT : 0 < dT := hc.trans_lt hcd
  have hdS : 0 < dS := ha.trans_lt hadS
  -- Bounds.
  have hbounds : 0 < Wclock B a dS c dT Δ v ∧ Wclock B a dS c dT Δ v ≤ 1 := by
    unfold Wclock; dsimp only
    split_ifs with h0 h1 h2
    · exact ⟨one_pos, le_rfl⟩
    · rw [Phi_eq]; exact ⟨Φ_pos _, Φ_le_one _⟩
    · rw [Phi_eq]; exact ⟨Φ_pos _, Φ_le_one _⟩
    · have hs := sstar_mem (c := c) (dT := dT) hB hv (mstarC B a dS c dT Δ v)
      rw [gmass_pos_eq h0]
      exact ⟨cellP_pos (hsL.trans_le hs.1) (Real.log_lt_log (lt_of_le_of_ne hc (Ne.symm h0)) hcd) _,
        cellP_le_one _ _ _ _⟩
  refine ⟨hbounds.1, hbounds.2, fun x hx p hp => ?_, fun ha0 => ?_, fun hb hw => ?_⟩
  · -- Domination of the one-step probability.
    have hs := sd_mem hv hp
    have hσ : 0 < Real.sqrt (p.2 * v) := hsL.trans_le hs.1
    set μ := p.1 * Δ - p.2 * v / 2
    rcases (ha.trans hx.1).lt_or_eq with hx0 | hx0
    · have hmHi : Real.log x + μ ≤ meanHi B dS Δ v := by
        unfold meanHi
        have := Real.log_lt_log hx0 hx.2
        have := mul_le_mul_of_nonneg_right hp.1.2 hΔ.le
        have := mul_le_mul_of_nonneg_right hp.2.1 hv.le
        simp only [μ]; linarith
      have hmLo : a ≠ 0 → meanLo B a Δ v ≤ Real.log x + μ := fun ha' => by
        unfold meanLo
        have := Real.log_le_log (lt_of_le_of_ne ha (Ne.symm ha')) hx.1
        have := mul_le_mul_of_nonneg_right hp.1.1 hΔ.le
        have := mul_le_mul_of_nonneg_right hp.2.2 hv.le
        simp only [μ]; linarith
      rcases hc.lt_or_eq with hc0 | hc0
      · rw [stepP_pos hσ hx0 hc0 hcd]
        exact ENNReal.ofReal_le_ofReal (rect_le hB hv hc0 hcd hmLo hmHi hs)
      · subst hc0
        rw [stepP_zero_target hσ hx0 hdT]
        refine ENNReal.ofReal_le_ofReal ?_
        by_cases ha' : a = 0
        · unfold Wclock; dsimp only; simp only [ite_true, ha']; exact Φ_le_one _
        · rw [show Real.log dT - Real.log x - μ = Real.log dT - (Real.log x + μ) by ring]
          exact zero_le hB hv ha' (hmLo ha') hs
    · -- The trapped state.
      rw [← hx0]
      classical
      rcases hc.lt_or_eq with hc0 | hc0
      · rw [(trap_holds c dT _ _).1 hc0]; exact bot_le
      · subst hc0
        have ha0 : a = 0 := le_antisymm (hx0 ▸ hx.1) ha
        rw [(trap_holds 0 dT _ _).2 hdT]
        unfold Wclock; dsimp only; simp [ha0]
  · -- The rectangle maximum on positive sources.
    have ha' : a ≠ 0 := ha0.ne'
    have hMM := meanLo_le_meanHi hB ha0 hadS hΔ hv
    rcases hc.lt_or_eq with hc0 | hc0
    · refine ⟨fun m hm s hs => ?_, mstarC B a dS c dT Δ v, ?_, sstarC B c dT v
        (mstarC B a dS c dT Δ v), sstar_mem hB hv _, ?_⟩
      · rw [gmass_pos_eq hc0.ne']; exact rect_le hB hv hc0 hcd (fun _ => hm.1) hm.2 hs
      · unfold mstarC; dsimp only; rw [ite_eq_right ha']
        exact ⟨le_min hMM (le_max_left _ _), min_le_left _ _⟩
      · unfold Wclock; dsimp only; rw [ite_eq_right hc0.ne']
    · subst hc0
      refine ⟨fun m hm s hs => by rw [gmass_zero]; exact zero_le hB hv ha' hm.1 hs, ?_⟩
      unfold Wclock; dsimp only
      simp only [ite_true, ha', ite_false]
      split_ifs
      · exact ⟨meanLo B a Δ v, ⟨le_rfl, hMM⟩, sdLo B v, ⟨le_rfl, sdLo_le_sdHi hB hv⟩, by
          rw [gmass_zero]; rfl⟩
      · exact ⟨meanLo B a Δ v, ⟨le_rfl, hMM⟩, sdHi B v, ⟨sdLo_le_sdHi hB hv, le_rfl⟩, by
          rw [gmass_zero]; rfl⟩
  · -- The singleton box.
    have hsS : ∀ x, min (sdHi B v) (max (sdLo B v) x) = Real.sqrt (B.wL * v) := fun x => by
      unfold sdHi sdLo; rw [← hw]; exact le_antisymm (min_le_left _ _) (le_min le_rfl (le_max_left _ _))
    have hsstar : ∀ m, sstarC B c dT v m = Real.sqrt (B.wL * v) := fun m => by
      unfold sstarC; dsimp only; split_ifs
      · rfl
      · exact hsS _
    have hlo : ∀ a', meanLo B a' Δ v = Real.log a' + (B.bL * Δ - B.wL * v / 2) := fun a' => by
      unfold meanLo; rw [hw]; ring
    have hhi : meanHi B dS Δ v = Real.log dS + (B.bL * Δ - B.wL * v / 2) := by
      unfold meanHi; rw [hb]; ring
    unfold Wclock; dsimp only
    by_cases hc0 : c = 0
    · subst hc0
      by_cases ha0 : a = 0
      · subst ha0; simp [Wm_c0_a0]
      · simp only [ite_true, ha0, ite_false]
        rw [Wm_c0 ha0, hlo, Phi_eq]
        split_ifs
        · unfold sdLo; congr 2; ring
        · unfold sdHi; rw [← hw]; congr 2; ring
    · rw [ite_eq_right hc0, hsstar, gmass_pos_eq hc0]
      unfold mstarC; dsimp only
      by_cases ha0 : a = 0
      · subst ha0; rw [ite_eq_left rfl, Wm_a0 hc0, hhi]
      · rw [ite_eq_right ha0, Wm_pos_pos ha0 hc0, hhi, hlo]

end Novel.D17ClockCells
