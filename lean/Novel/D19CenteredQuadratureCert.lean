import Novel.D19CenteredQuadratureMain

/-!
# Claim 038, part 2: the conditional bound and the certificate

* (4). Dividing (2)–(3) for the joint mass by the opposite side for the training mass gives
  `e^(−ε̂_N^− − ε̂_k^+) R_g ≤ g_(θ_g) ≤ e^(ε̂_N^+ + ε̂_k^−) R_g`. Every parameter of the box is within
  `e^η` of the center: `η_N + η_k` by claim 036's parameter step (`Lz_param`), `η_cond` by claim
  037's (6) (`cond_holds`), hence their minimum.
* (5). The new upper term is at most claim 037's (each hatted allowance is at most claim 036's `ε`)
  and the new lower term at least claim 036's; with claim 037's certificate this gives the chain.
* The scores: claim 036's validity for any denominator in `[D_filter, 1]`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D19CenteredQuadrature

open Standalone.D19CenteredQuadrature Standalone.D19FilteredLikelihood Standalone.D19CondSensitivity
  Standalone.D17ClockCells Standalone.D14FixedTick Novel.D19FilteredLikelihood
  Novel.D19CondSensitivity

variable {δ s : ℝ}

/-- Every parameter of the box against its center, with `η(B)`. -/
theorem gF_le_eta (hδ : 0 < δ) (hs : 0 < s) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (hΔ : ∀ j, 0 < Δ j)
    (hv : ∀ j, 0 < v j) {B : Box} (hB : B.Valid) (u : Fin K → ℕ) (y : Fin n → ℕ)
    (hz : ∀ j, 1 ≤ Fin.append u y j) {p : ℝ × ℝ} (hp : B.Mem p) :
    gF δ s Δ v p.1 p.2 u y ≤ Real.exp (etaB δ s Δ v B u y) * gF δ s Δ v (ctr B).1 (ctr B).2 u y := by
  unfold etaB
  rcases min_choice (etaQ δ s Δ v B (Fin.append u y) + etaQ δ s (trn Δ) (trn v) B u)
    (etaC δ s Δ v B u y) with h | h <;> rw [h]
  · have hc := ctr_mem hB
    have hu := all_pos_left hz
    obtain ⟨hp1, hp2⟩ := near_ctr hp
    have hcp1 : |(ctr B).1 - p.1| ≤ (B.bH - B.bL) / 2 := by rw [abs_sub_comm]; exact hp1
    have hcp2 : |(ctr B).2 - p.2| ≤ (B.wH - B.wL) / 2 := by rw [abs_sub_comm]; exact hp2
    have hwp : 0 < p.2 := hB.2.1.trans_le hp.2.1
    have hwc : 0 < (ctr B).2 := hB.2.1.trans_le hc.2.1
    have pN := Lz_param hδ hs one_pos hB hp hc hp1 hp2 Δ v _ hΔ hv hz
    have pk := Lz_param hδ hs one_pos hB hc hp hcp1 hcp2 (trn Δ) (trn v) u (fun j => hΔ _)
      (fun j => hv _) hu
    have hLkp := Lz_pos hδ hs (muF (trn Δ) (trn v) p.1 p.2) (sdF (trn v) p.2)
      (fun j => sdF_pos (fun j => hv _) hwp j) u
    have hLkc := Lz_pos hδ hs (muF (trn Δ) (trn v) (ctr B).1 (ctr B).2) (sdF (trn v) (ctr B).2)
      (fun j => sdF_pos (fun j => hv _) hwc j) u
    have hLNp := Lz_pos hδ hs (muF Δ v p.1 p.2) (sdF v p.2) (fun j => sdF_pos hv hwp j) (Fin.append u y)
    have hcg := ratio_down hLkc hLkp hLNp.le (neg_le_of_exp pN) pk
    exact le_exp_of_neg hcg
  · exact cond_holds δ s K n Δ v B u y p.1 p.2 hδ hs hΔ hv hB hp hz

/-- (4) at the center: both sides, from (2)–(3). -/
theorem center_ratio (hδ : 0 < δ) (hs : 0 < s) {M : ℕ} (hM : 0 < M) {K n : ℕ}
    (Δ v : Fin (K + n) → ℝ) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B : Box} (hB : B.Valid)
    (u : Fin K → ℕ) (y : Fin n → ℕ) (hz : ∀ j, 1 ≤ Fin.append u y j) :
    0 < Rg δ s M Δ v B u y ∧ termCenLow δ s M Δ v B u y ≤ gF δ s Δ v (ctr B).1 (ctr B).2 u y ∧
      gF δ s Δ v (ctr B).1 (ctr B).2 u y ≤ Real.exp (epsPlusH δ s M Δ v B (Fin.append u y) +
        epsMinusH δ s M (trn Δ) (trn v) B u) * Rg δ s M Δ v B u y := by
  have hc := ctr_mem hB
  have hu := all_pos_left hz
  have hwc : 0 < (ctr B).2 := hB.2.1.trans_le hc.2.1
  have cN := centered_holds δ s (K + n) M Δ v B (ctr B).1 (ctr B).2 _ hδ hs hM hΔ hv hB hc hz
  have ck := centered_holds δ s K M (trn Δ) (trn v) B (ctr B).1 (ctr B).2 u hδ hs hM
    (fun j => hΔ _) (fun j => hv _) hB hc hu
  have qN := quad_holds δ s (K + n) M Δ v B (ctr B).1 (ctr B).2 _ hδ hs hM hΔ hv hB hc hz
  have qk := quad_holds δ s K M (trn Δ) (trn v) B (ctr B).1 (ctr B).2 u hδ hs hM (fun j => hΔ _)
    (fun j => hv _) hB hc hu
  have hLkc := Lz_pos hδ hs (muF (trn Δ) (trn v) (ctr B).1 (ctr B).2) (sdF (trn v) (ctr B).2)
    (fun j => sdF_pos (fun j => hv _) hwc j) u
  set QN := Qs δ s M (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (Fin.append u y)
  set Qk := Qs δ s M (muF (trn Δ) (trn v) (ctr B).1 (ctr B).2) (sdF (trn v) (ctr B).2) u
  have hR : Rg δ s M Δ v B u y = QN / Qk := rfl
  have hg : gF δ s Δ v (ctr B).1 (ctr B).2 u y =
      Lz δ s (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (Fin.append u y) /
        Lz δ s (muF (trn Δ) (trn v) (ctr B).1 (ctr B).2) (sdF (trn v) (ctr B).2) u := rfl
  refine ⟨by rw [hR]; exact div_pos qN.1 qk.1, ?_, ?_⟩
  · show Real.exp (-(epsMinusH δ s M Δ v B (Fin.append u y) + epsPlusH δ s M (trn Δ) (trn v) B u)) *
      (QN / Qk) ≤ _
    rw [hg]
    exact ratio_down hLkc qk.1 qN.1.le cN.2.2.2.2.1 ck.2.2.2.2.2
  · rw [hg, hR]
    exact ratio_up hLkc qk.1 qN.1.le cN.2.2.2.2.2 (le_exp_of_neg ck.2.2.2.2.1)

theorem center_holds : Standalone.D19CenteredQuadrature.center := by
  intro δ s M K n Δ v B u y hδ hs hM hΔ hv hB hz
  obtain ⟨hR, hlo, hup⟩ := center_ratio hδ hs hM Δ v hΔ hv hB u y hz
  refine ⟨hR, hlo, fun p hp => ?_⟩
  calc gF δ s Δ v p.1 p.2 u y ≤ Real.exp (etaB δ s Δ v B u y) * gF δ s Δ v (ctr B).1 (ctr B).2 u y :=
        gF_le_eta hδ hs Δ v hΔ hv hB u y hz hp
    _ ≤ Real.exp (etaB δ s Δ v B u y) * (Real.exp (epsPlusH δ s M Δ v B (Fin.append u y) +
          epsMinusH δ s M (trn Δ) (trn v) B u) * Rg δ s M Δ v B u y) :=
        mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add, ← add_assoc]

/-! ## (5) -/

theorem termCen_le_one (δ s : ℝ) (M : ℕ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box)
    (u : Fin K → ℕ) (y : Fin n → ℕ) : termCen δ s M Δ v B u y ≤ 1 := min_le_left _ _

theorem Rg_nonneg (hδ : 0 < δ) (M : ℕ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box) (u : Fin K → ℕ)
    (y : Fin n → ℕ) (hz : ∀ j, 1 ≤ Fin.append u y j) : 0 ≤ Rg δ s M Δ v B u y :=
  div_nonneg (Finset.sum_nonneg fun l _ => msg_nonneg M _ _ _ _ hz hδ l)
    (Finset.sum_nonneg fun l _ => msg_nonneg M _ _ _ _ (all_pos_left hz) hδ l)

/-- The new upper term is at most claim 037's. -/
theorem termCen_le_termC (hδ : 0 < δ) (M : ℕ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box)
    (u : Fin K → ℕ) (y : Fin n → ℕ) (hz : ∀ j, 1 ≤ Fin.append u y j) :
    termCen δ s M Δ v B u y ≤ termC δ s M Δ v B u y := by
  unfold termCen termC
  refine min_le_min le_rfl ?_
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Rg_nonneg hδ M Δ v B u y hz)
  have h1 := min_le_left (epsQ δ s M Δ v B (Fin.append u y)) (epsPlus δ s M Δ v B (Fin.append u y))
  have h2 := min_le_left (epsQ δ s M (trn Δ) (trn v) B u) (epsMinus δ M (trn v) B u)
  unfold epsPlusH epsMinusH etaB
  linarith

/-- The new lower term is at least claim 036's. -/
theorem termLow_le_termCenLow (hδ : 0 < δ) (M : ℕ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box)
    (u : Fin K → ℕ) (y : Fin n → ℕ) (hz : ∀ j, 1 ≤ Fin.append u y j) :
    termLow δ s M Δ v B u y ≤ termCenLow δ s M Δ v B u y := by
  unfold termLow termCenLow
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Rg_nonneg hδ M Δ v B u y hz)
  have h1 := min_le_left (epsQ δ s M Δ v B (Fin.append u y)) (epsMinus δ M v B (Fin.append u y))
  have h2 := min_le_left (epsQ δ s M (trn Δ) (trn v) B u) (epsPlus δ s M (trn Δ) (trn v) B u)
  unfold epsPlusH epsMinusH
  linarith

theorem chain_holds : Standalone.D19CenteredQuadrature.chain := by
  intro δ s Mb K n Δ 𝒱 ℬ C u y hδ hs hMb hΔ h𝒱 hv hℬ hC
  obtain ⟨⟨θ, hθ, hθe⟩, hmax, hDpos, hDle⟩ :=
    exact_holds.2.2.2.2.2 δ s K n Δ 𝒱 ℬ u y hδ hs hΔ h𝒱 hv hℬ
  have hsup1 : (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (termCen δ s (Mb B) Δ v B u y)) ≤ 1 :=
    iSup₂_le fun B _ => iSup₂_le fun v _ => ENNReal.ofReal_le_one.2 (termCen_le_one _ _ _ _ _ _ _ _)
  have hsupT : (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (termCen δ s (Mb B) Δ v B u y)) ≠ ⊤ :=
    (hsup1.trans_lt ENNReal.one_lt_top).ne
  -- Each lower term is at most the center's mass, hence at most `D_filter`.
  have hlowg : (∀ j, 1 ≤ Fin.append u y j) → ∀ B ∈ C, ∀ v ∈ 𝒱,
      termCenLow δ s (Mb B) Δ v B u y ≤ Dfilter δ s Δ 𝒱 ℬ u y := fun hz B hB v hvv => by
    have hcB := ctr_mem (hC.1 B hB).1
    have hsub := (hC.1 B hB).2
    exact (center_ratio hδ hs (hMb B hB) Δ v hΔ (hv v hvv) (hC.1 B hB).1 u y hz).2.1.trans
      (hmax (v, ctr B) ⟨hvv, ⟨hsub.1.trans hcB.1.1, hcB.1.2.trans hsub.2.1⟩,
        ⟨hsub.2.2.1.trans hcB.2.1, hcB.2.2.trans hsub.2.2.2⟩⟩)
  have hlowT : (∀ j, 1 ≤ Fin.append u y j) →
      (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (termCenLow δ s (Mb B) Δ v B u y)) ≠ ⊤ := fun hz =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup₂_le fun B hB => iSup₂_le fun v hvv =>
      ENNReal.ofReal_le_ofReal (hlowg hz B hB v hvv))
  have hDcen : Dfilter δ s Δ 𝒱 ℬ u y ≤ Dcen δ s Mb Δ C 𝒱 u y := by
    unfold Dcen
    split_ifs with hz
    · rw [← hθe]
      obtain ⟨B, hB, hθB⟩ := hC.2 θ.2 hθ.2
      have hwθ : 0 < θ.2.2 := (hC.1 B hB).1.2.1.trans_le hθB.2.1
      have h1 : gF δ s Δ θ.1 θ.2.1 θ.2.2 u y ≤ termCen δ s (Mb B) Δ θ.1 B u y :=
        le_min (gF_le_one hδ hs Δ θ.1 (hv _ hθ.1) _ hwθ u y)
          ((center_holds δ s (Mb B) K n Δ θ.1 B u y hδ hs (hMb B hB) hΔ (hv _ hθ.1)
            (hC.1 B hB).1 hz).2.2 θ.2 hθB)
      have h0 : 0 ≤ termCen δ s (Mb B) Δ θ.1 B u y := (gF_nonneg δ s Δ _ _ _ u y).trans h1
      refine h1.trans ?_
      rw [← ENNReal.toReal_ofReal h0]
      exact ENNReal.toReal_mono hsupT (le_iSup₂_of_le B hB (le_iSup₂_of_le θ.1 hθ.1 le_rfl))
    · exact hDle
  have hDcen1 : Dcen δ s Mb Δ C 𝒱 u y ≤ 1 := by
    unfold Dcen
    split_ifs
    · exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hsup1)
    · exact le_rfl
  refine ⟨hDcen, hDcen1, fun hz => ⟨?_, ?_⟩, fun M hM => ?_⟩
  · -- Positivity: any box and clock.
    obtain ⟨B, hB, -⟩ := hC.2 (ℬ.bL, ℬ.wL) ⟨⟨le_rfl, hℬ.1⟩, ⟨le_rfl, hℬ.2.2⟩⟩
    obtain ⟨v, hvv⟩ := h𝒱
    have hpos : 0 < termCenLow δ s (Mb B) Δ v B u y :=
      mul_pos (Real.exp_pos _) (center_ratio hδ hs (hMb B hB) Δ v hΔ (hv v hvv) (hC.1 B hB).1 u y hz).1
    unfold DcenLow
    exact hpos.trans_le ((ENNReal.ofReal_le_iff_le_toReal (hlowT hz)).1
      (le_iSup₂_of_le B hB (le_iSup₂_of_le v hvv le_rfl)))
  · unfold DcenLow
    exact ENNReal.toReal_le_of_le_ofReal hDpos.le (iSup₂_le fun B hB => iSup₂_le fun v hvv =>
      ENNReal.ofReal_le_ofReal (hlowg hz B hB v hvv))
  · have hM0 : 0 < M := by
      obtain ⟨B, hB, -⟩ := hC.2 (ℬ.bL, ℬ.wL) ⟨⟨le_rfl, hℬ.1⟩, ⟨le_rfl, hℬ.2.2⟩⟩
      rw [← hM B hB]; exact hMb B hB
    have hcert := (certified_holds δ s M K n Δ 𝒱 ℬ C hδ hs hM0 hΔ h𝒱 hv hℬ hC).2.1 u y
    have hcond : Dcen δ s Mb Δ C 𝒱 u y ≤ Dcond δ s M Δ C 𝒱 u y := by
      unfold Dcen Dcond
      split_ifs with hz
      · have hsupC : (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (termC δ s M Δ v B u y)) ≠ ⊤ :=
          ((iSup₂_le fun B _ => iSup₂_le fun v _ => ENNReal.ofReal_le_one.2
            (termC_le_one δ s M Δ v B u y)).trans_lt ENNReal.one_lt_top).ne
        refine ENNReal.toReal_mono hsupC (iSup₂_mono fun B hB => iSup₂_mono fun v _ => ?_)
        rw [hM B hB]
        exact ENNReal.ofReal_le_ofReal (termCen_le_termC hδ M Δ v B u y hz)
      · exact le_rfl
    refine ⟨hcond, hcert.2.1, hcert.2.2.1, fun hz => ?_, fun q =>
      ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal hcond) _⟩
    unfold Dlow DcenLow
    refine ENNReal.toReal_mono (hlowT hz) (iSup₂_mono fun B hB => iSup₂_mono fun v _ => ?_)
    rw [hM B hB]
    exact ENNReal.ofReal_le_ofReal (termLow_le_termCenLow hδ M Δ v B u y hz)

theorem scores_holds : Standalone.D19CenteredQuadrature.scores := by
  intro Ω _ P _ δ s Mb K n Δ 𝒱 ℬ C Z ν _ q hδ hs hMb hΔ h𝒱 hv hℬ hC hZ hν hlaw hq0 hq1
  have hch := fun u y => chain_holds δ s Mb K n Δ 𝒱 ℬ C u y hδ hs hMb hΔ h𝒱 hv hℬ hC
  have h := validity_holds P K n δ s Δ 𝒱 ℬ Z ν q (Dcen δ s Mb Δ C 𝒱) hδ hs hΔ h𝒱 hv hℬ hZ hν hlaw
    hq0 hq1 fun u y => ⟨(hch u y).1, (hch u y).2.1⟩
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end Novel.D19CenteredQuadrature
