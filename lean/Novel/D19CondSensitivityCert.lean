import Novel.D19CondSensitivityCond

/-!
# Claim 037, (7)–(8): the certified bound with the new allowance

* At each box's center, claim 036's relative integration bound gives
  `g_c ≤ exp(ε_N + ε_k) Q_N/Q_k` (`gF_ctr_le`).
* Claim 036's box bound uses the allowance `η_N + η_k`; (6) gives `g_θ ≤ exp(η_cond) g_c`. Both
  hold, so their minimum does, and `term_cond ≤ term`.
* Hence `D_filter ≤ D_cond ≤ D_cert ≤ 1`, the score `q/D_cond` is at least `q/D_cert`, and claim
  036's validity for any denominator in `[D_filter, 1]` gives its conclusions.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal

namespace Novel.D19CondSensitivity

open Standalone.D19CondSensitivity Standalone.D19FilteredLikelihood Standalone.D14FixedTick
  Standalone.D17ClockCells Novel.D19FilteredLikelihood

variable {δ s : ℝ}

/-- At the center, the conditional mass is at most the center's quadrature ratio. -/
theorem gF_ctr_le (hδ : 0 < δ) (hs : 0 < s) {M : ℕ} (hM : 0 < M) {K n : ℕ} (Δ v : Fin (K + n) → ℝ)
    (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B : Box} (hB : B.Valid) (u : Fin K → ℕ)
    (y : Fin n → ℕ) (hz : ∀ j, 1 ≤ Fin.append u y j) :
    gF δ s Δ v (ctr B).1 (ctr B).2 u y ≤
      Real.exp (epsQ δ s M Δ v B (Fin.append u y) + epsQ δ s M (trn Δ) (trn v) B u) *
        Qs δ s M (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (Fin.append u y) /
          Qs δ s M (trn (muF Δ v (ctr B).1 (ctr B).2)) (trn (sdF v (ctr B).2)) u := by
  have hc := ctr_mem hB
  have hu := all_pos_left hz
  have qN := quad_holds δ s (K + n) M Δ v B (ctr B).1 (ctr B).2 _ hδ hs hM hΔ hv hB hc hz
  have qk := quad_holds δ s K M (trn Δ) (trn v) B (ctr B).1 (ctr B).2 u hδ hs hM (fun j => hΔ _)
    (fun j => hv _) hB hc hu
  have hwc : 0 < (ctr B).2 := hB.2.1.trans_le hc.2.1
  have hLkc := Lz_pos hδ hs (muF (trn Δ) (trn v) (ctr B).1 (ctr B).2) (sdF (trn v) (ctr B).2)
    (fun j => sdF_pos (fun j => hv _) hwc j) u
  show _ / _ ≤ _
  simp only [trn_muF, trn_sdF]
  rw [div_le_div_iff₀ hLkc qk.1]
  set QN := Qs δ s M (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (Fin.append u y)
  set Qk := Qs δ s M (muF (trn Δ) (trn v) (ctr B).1 (ctr B).2) (sdF (trn v) (ctr B).2) u
  set Lkc := Lz δ s (muF (trn Δ) (trn v) (ctr B).1 (ctr B).2) (sdF (trn v) (ctr B).2) u
  have b1 := qN.2.2
  have b2 : Real.exp (-epsQ δ s M (trn Δ) (trn v) B u) * Qk ≤ Lkc := qk.2.1
  have hQk : Qk ≤ Real.exp (epsQ δ s M (trn Δ) (trn v) B u) * Lkc := by
    have := mul_le_mul_of_nonneg_left b2 (Real.exp_pos (epsQ δ s M (trn Δ) (trn v) B u)).le
    rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
  calc Lz δ s (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (Fin.append u y) * Qk
      ≤ (Real.exp (epsQ δ s M Δ v B (Fin.append u y)) * QN) *
          (Real.exp (epsQ δ s M (trn Δ) (trn v) B u) * Lkc) :=
        mul_le_mul b1 hQk qk.1.le (mul_nonneg (Real.exp_pos _).le qN.1.le)
    _ = _ := by rw [Real.exp_add]; ring

theorem termC_bounds (hδ : 0 < δ) (hs : 0 < s) {M : ℕ} (hM : 0 < M) {K n : ℕ}
    (Δ v : Fin (K + n) → ℝ) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B : Box} (hB : B.Valid)
    (u : Fin K → ℕ) (y : Fin n → ℕ) (hz : ∀ j, 1 ≤ Fin.append u y j) :
    (∀ p, B.Mem p → gF δ s Δ v p.1 p.2 u y ≤ termC δ s M Δ v B u y) ∧
      termC δ s M Δ v B u y ≤ term δ s M Δ v B u y := by
  have hc := ctr_mem hB
  have hu := all_pos_left hz
  have qN := quad_holds δ s (K + n) M Δ v B (ctr B).1 (ctr B).2 _ hδ hs hM hΔ hv hB hc hz
  have qk := quad_holds δ s K M (trn Δ) (trn v) B (ctr B).1 (ctr B).2 u hδ hs hM (fun j => hΔ _)
    (fun j => hv _) hB hc hu
  simp only [← trn_muF, ← trn_sdF] at qk
  have hQ : 0 ≤ Qs δ s M (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (Fin.append u y) /
      Qs δ s M (trn (muF Δ v (ctr B).1 (ctr B).2)) (trn (sdF v (ctr B).2)) u :=
    div_nonneg qN.1.le qk.1.le
  have hterm : term δ s M Δ v B u y = min 1 (Real.exp (epsQ δ s M Δ v B (Fin.append u y) +
      epsQ δ s M (trn Δ) (trn v) B u + (etaQ δ s Δ v B (Fin.append u y) +
        etaQ δ s (trn Δ) (trn v) B u)) *
      Qs δ s M (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (Fin.append u y) /
      Qs δ s M (trn (muF Δ v (ctr B).1 (ctr B).2)) (trn (sdF v (ctr B).2)) u) := by
    unfold term; rw [← add_assoc]
  refine ⟨fun p hp => ?_, ?_⟩
  · have hwp : 0 < p.2 := hB.2.1.trans_le hp.2.1
    refine le_min (gF_le_one hδ hs Δ v hv p.1 hwp u y) ?_
    rcases min_choice (etaQ δ s Δ v B (Fin.append u y) + etaQ δ s (trn Δ) (trn v) B u)
      (etaC δ s Δ v B u y) with h | h
    · rw [h]
      have := (box_bounds hδ hs hM Δ v hΔ hv hB u y hz hp).1
      rw [hterm] at this
      exact this.trans (min_le_right _ _)
    · rw [h]
      have h6 := cond_holds δ s K n Δ v B u y p.1 p.2 hδ hs hΔ hv hB hp hz
      have hcl := gF_ctr_le hδ hs hM Δ v hΔ hv hB u y hz (M := M)
      calc gF δ s Δ v p.1 p.2 u y ≤ Real.exp (etaC δ s Δ v B u y) * gF δ s Δ v (bg B) (wg B) u y := h6
        _ ≤ Real.exp (etaC δ s Δ v B u y) * (Real.exp (epsQ δ s M Δ v B (Fin.append u y) +
              epsQ δ s M (trn Δ) (trn v) B u) *
              Qs δ s M (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (Fin.append u y) /
              Qs δ s M (trn (muF Δ v (ctr B).1 (ctr B).2)) (trn (sdF v (ctr B).2)) u) :=
            mul_le_mul_of_nonneg_left hcl (Real.exp_pos _).le
        _ = _ := by rw [Real.exp_add (_ + _)]; ring
  · rw [hterm]
    unfold termC
    refine min_le_min le_rfl ?_
    rw [mul_div_assoc, mul_div_assoc]
    have hmin := min_le_left (etaQ δ s Δ v B (Fin.append u y) + etaQ δ s (trn Δ) (trn v) B u)
      (etaC δ s Δ v B u y)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hQ

theorem termC_le_one (δ s : ℝ) (M : ℕ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box) (u : Fin K → ℕ)
    (y : Fin n → ℕ) : termC δ s M Δ v B u y ≤ 1 := min_le_left _ _

theorem certified_holds : Standalone.D19CondSensitivity.certified := by
  intro δ s M K n Δ 𝒱 ℬ C hδ hs hM hΔ h𝒱 hv hℬ hC
  have hbox : ∀ (u : Fin K → ℕ) (y : Fin n → ℕ), (∀ j, 1 ≤ Fin.append u y j) → ∀ B ∈ C, ∀ v ∈ 𝒱,
      (∀ p, B.Mem p → gF δ s Δ v p.1 p.2 u y ≤ termC δ s M Δ v B u y) ∧
      termC δ s M Δ v B u y ≤ term δ s M Δ v B u y := fun u y hz B hB v hvv =>
    termC_bounds hδ hs hM Δ v hΔ (hv v hvv) (hC.1 B hB).1 u y hz
  have hD : ∀ (u : Fin K → ℕ) (y : Fin n → ℕ),
      Dfilter δ s Δ 𝒱 ℬ u y ≤ Dcond δ s M Δ C 𝒱 u y ∧
      Dcond δ s M Δ C 𝒱 u y ≤ Dcert δ s M Δ C 𝒱 u y ∧ Dcert δ s M Δ C 𝒱 u y ≤ 1 := by
    intro u y
    have hcov := cover_holds δ s M K n Δ 𝒱 ℬ C u y hδ hs hM hΔ h𝒱 hv hℬ hC
    obtain ⟨⟨θ, hθ, hθe⟩, -, -, hDle⟩ := exact_holds.2.2.2.2.2 δ s K n Δ 𝒱 ℬ u y hδ hs hΔ h𝒱 hv hℬ
    have hsup1 : (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (termC δ s M Δ v B u y)) ≤ 1 :=
      iSup₂_le fun B _ => iSup₂_le fun v _ => ENNReal.ofReal_le_one.2 (termC_le_one δ s M Δ v B u y)
    have hsupT : (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (termC δ s M Δ v B u y)) ≠ ⊤ :=
      (hsup1.trans_lt ENNReal.one_lt_top).ne
    have hsupT' : (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (term δ s M Δ v B u y)) ≠ ⊤ :=
      ((iSup₂_le fun B _ => iSup₂_le fun v _ => ENNReal.ofReal_le_one.2
        (term_le_one δ s M Δ v B u y)).trans_lt ENNReal.one_lt_top).ne
    refine ⟨?_, ?_, hcov.2.2.1⟩
    · unfold Dcond
      split_ifs with hz
      · rw [← hθe]
        obtain ⟨B, hB, hθB⟩ := hC.2 θ.2 hθ.2
        have h1 := (hbox u y hz B hB θ.1 hθ.1).1 θ.2 hθB
        have h0 : 0 ≤ termC δ s M Δ θ.1 B u y :=
          (gF_nonneg δ s Δ θ.1 θ.2.1 θ.2.2 u y).trans h1
        refine h1.trans ?_
        rw [← ENNReal.toReal_ofReal h0]
        exact ENNReal.toReal_mono hsupT (le_iSup₂_of_le B hB (le_iSup₂_of_le θ.1 hθ.1 le_rfl))
      · exact hDle
    · unfold Dcond Dcert
      split_ifs with hz
      · refine ENNReal.toReal_mono hsupT' (iSup₂_mono fun B hB => iSup₂_mono fun v hvv => ?_)
        exact ENNReal.ofReal_le_ofReal (hbox u y hz B hB v hvv).2
      · exact le_rfl
  refine ⟨hbox, fun u y => ⟨(hD u y).1, (hD u y).2.1, (hD u y).2.2, fun q =>
    ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal (hD u y).2.1) _⟩, ?_⟩
  intro Ω _ P _ Z ν _ q hZ hν hlaw hq0 hq1
  have h := validity_holds P K n δ s Δ 𝒱 ℬ Z ν q (Dcond δ s M Δ C 𝒱) hδ hs hΔ h𝒱 hv hℬ hZ hν hlaw
    hq0 hq1 fun u y => ⟨(hD u y).1, (hD u y).2.1.trans (hD u y).2.2⟩
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end Novel.D19CondSensitivity
