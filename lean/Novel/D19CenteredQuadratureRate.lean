import Novel.D19CenteredQuadratureCert

/-!
# Claim 038, part 3: the rate

* Every `r_j` is its `M = 1` value over `M`, so `ε^±` are their `M = 1` values over `M²`
  (`epsMinus_scale`, `epsPlus_scale`). On a subbox of `ℬ`, `w_−` is larger and each `C_j` smaller
  (claim 036's `Cj_mono`), so the `M = 1` values are at most `ℬ`'s (`rate_uniform`).
* Convergence: the new upper term is at most claim 036's box term and the new lower term at least
  claim 036's lower term. With every box's `M ≥ M₀` and widths `≤ η`, claim 036's exponent bound
  (`Xexp_le`) holds uniformly over the boxes and clocks, which gives both limits.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D19CenteredQuadrature

open Standalone.D19CenteredQuadrature Standalone.D19FilteredLikelihood Standalone.D19CondSensitivity
  Standalone.D17ClockCells Standalone.D14FixedTick Novel.D19FilteredLikelihood
  Novel.D19CondSensitivity

variable {δ s : ℝ} {m : ℕ}

theorem epsMinus_scale (M : ℕ) (v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) :
    epsMinus δ M v B z = epsMinus δ 1 v B z / M ^ 2 := by
  unfold epsMinus
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hP_scale (M := M), hP_scale (M := M) z j.succ]
  ring

theorem epsPlus_scale (M : ℕ) (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) :
    epsPlus δ s M Δ v B z = epsPlus δ s 1 Δ v B z / M ^ 2 := by
  unfold epsPlus
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hP_scale (M := M) z i.succ]
  ring

theorem Cpad_nonneg {Δ v : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B : Box}
    (hB : B.Valid) (z : Fin m → ℕ) (k : Fin (m + 1)) : 0 ≤ Cpad δ s Δ v B z k := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp [Cpad]
  · unfold Cpad; rw [Fin.snoc_castSucc]; exact Cj_nonneg hB hΔ hv z j

theorem Cpad_mono {Δ v : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B ℬ : Box}
    (hB : B.Valid) (hℬ : ℬ.Valid) (hsub : B.Sub ℬ) (z : Fin m → ℕ) (k : Fin (m + 1)) :
    Cpad δ s Δ v B z k ≤ Cpad δ s Δ v ℬ z k := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp [Cpad]
  · unfold Cpad; rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; exact Cj_mono hΔ hv hB hℬ hsub z j

theorem rate_uniform (M : ℕ) {Δ v : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j)
    (hv : ∀ j, 0 < v j) (z : Fin m → ℕ) {B ℬ : Box} (hB : B.Valid)
    (hℬ : ℬ.Valid) (hsub : B.Sub ℬ) :
    epsMinus δ M v B z ≤ epsMinus δ 1 v ℬ z / M ^ 2 ∧
      epsPlus δ s M Δ v B z ≤ epsPlus δ s 1 Δ v ℬ z / M ^ 2 := by
  rw [epsMinus_scale, epsPlus_scale]
  have hM2 : (0 : ℝ) ≤ (M : ℝ) ^ 2 := sq_nonneg _
  constructor
  · refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) hM2
    have hvj := hv j
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by have := hℬ.2.1; positivity)
      (by nlinarith [hsub.2.2.1])
  · refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => ?_) hM2
    have h1 := Cpad_mono (δ := δ) (s := s) hΔ hv hB hℬ hsub z i.castSucc
    have h2 := Cpad_mono (δ := δ) (s := s) hΔ hv hB hℬ hsub z i.succ
    have h3 := Cpad_nonneg (δ := δ) (s := s) hΔ hv hB z i.castSucc
    have h4 := Cpad_nonneg (δ := δ) (s := s) hΔ hv hB z i.succ
    have hsq : (Cpad δ s Δ v B z i.castSucc + Cpad δ s Δ v B z i.succ) ^ 2 ≤
        (Cpad δ s Δ v ℬ z i.castSucc + Cpad δ s Δ v ℬ z i.succ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have := sq_nonneg (hP δ 1 z i.succ / 2)
    nlinarith

/-- The new upper term is at most claim 036's box term. -/
theorem termCen_le_term (hδ : 0 < δ) (hs : 0 < s) {M : ℕ} (hM : 0 < M) {K n : ℕ}
    (Δ v : Fin (K + n) → ℝ) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B : Box} (hB : B.Valid)
    (u : Fin K → ℕ) (y : Fin n → ℕ) (hz : ∀ j, 1 ≤ Fin.append u y j) :
    termCen δ s M Δ v B u y ≤ term δ s M Δ v B u y :=
  (termCen_le_termC hδ M Δ v B u y hz).trans (termC_bounds hδ hs hM Δ v hΔ hv hB u y hz).2

theorem rate_holds : Standalone.D19CenteredQuadrature.rate := by
  refine ⟨fun δ s M m Δ v B z => ⟨epsMinus_scale M v B z, epsPlus_scale M Δ v B z⟩,
    fun δ s M m Δ v B ℬ z _ hΔ hv _ hB hℬ hsub => rate_uniform M hΔ hv z hB hℬ hsub, ?_⟩
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
  refine ⟨ε / (S₂ + 1), div_pos hε (by linarith), ⌈2 * S₁ / ε⌉₊ + 1, Nat.succ_pos _,
    fun C Mb hC hη hM₀ => ?_⟩
  have hS₂η : S₂ * (ε / (S₂ + 1) / 2) ≤ ε / 2 := by
    rw [mul_div_assoc', mul_div_assoc', div_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  have hMpos : ∀ B ∈ C, 0 < Mb B := fun B hB => lt_of_lt_of_le (Nat.succ_pos _) (hM₀ B hB)
  -- Every box and clock has exponent at most `ε`.
  have hXε : ∀ B ∈ C, ∀ v ∈ 𝒱, Xexp δ s (Mb B) Δ v B u y ≤ ε := fun B hB v hvv => by
    have hMR : 2 * S₁ / ε < Mb B := by
      have := Nat.le_ceil (2 * S₁ / ε)
      have : ((⌈2 * S₁ / ε⌉₊ + 1 : ℕ) : ℝ) ≤ Mb B := by exact_mod_cast hM₀ B hB
      push_cast at this; linarith
    have hS₁M : S₁ / Mb B ≤ ε / 2 := by
      have hM' : (0 : ℝ) < Mb B := by exact_mod_cast hMpos B hB
      rw [div_lt_iff₀ hε] at hMR
      rw [div_le_iff₀ hM']; linarith
    have hX := Xexp_le (s := s) (M := Mb B) hδ hΔ (hv v hvv) (hC.1 B hB).1 hℬ (hC.1 B hB).2 hz
      (hη B hB)
    have h1 : A v / Mb B ≤ S₁ / Mb B :=
      div_le_div_of_nonneg_right (Finset.single_le_sum hA0 hvv) (Nat.cast_nonneg _)
    have h2 : L v * (ε / (S₂ + 1) / 2) ≤ S₂ * (ε / (S₂ + 1) / 2) :=
      mul_le_mul_of_nonneg_right (Finset.single_le_sum hL0 hvv) (by positivity)
    have : Xexp δ s (Mb B) Δ v B u y ≤ A v / Mb B + L v * (ε / (S₂ + 1) / 2) := hX
    linarith
  constructor
  · unfold Dcen
    rw [ite_eq_left_of_eq_true _ _ (eq_true hz)]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity)
      (iSup₂_le fun B hB => iSup₂_le fun v hvv => ENNReal.ofReal_le_ofReal ?_)
    have hcB := ctr_mem (hC.1 B hB).1
    have hsub := (hC.1 B hB).2
    have hgc := hmax (v, ctr B) ⟨hvv, ⟨hsub.1.trans hcB.1.1, hcB.1.2.trans hsub.2.1⟩,
      ⟨hsub.2.2.1.trans hcB.2.1, hcB.2.2.trans hsub.2.2.2⟩⟩
    have hg0 := gF_nonneg δ s Δ v (ctr B).1 (ctr B).2 u y
    calc termCen δ s (Mb B) Δ v B u y ≤ term δ s (Mb B) Δ v B u y :=
          termCen_le_term hδ hs (hMpos B hB) Δ v hΔ (hv v hvv) (hC.1 B hB).1 u y hz
      _ ≤ Real.exp (Xexp δ s (Mb B) Δ v B u y) * gF δ s Δ v (ctr B).1 (ctr B).2 u y :=
          (box_exp hδ hs (hMpos B hB) Δ v hΔ (hv v hvv) (hC.1 B hB).1 u y hz).1
      _ ≤ Real.exp ε * gF δ s Δ v (ctr B).1 (ctr B).2 u y :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hXε B hB v hvv)) hg0
      _ ≤ _ := mul_le_mul_of_nonneg_left hgc (Real.exp_pos _).le
  · obtain ⟨B, hB, hθB⟩ := hC.2 θ.2 hθ.2
    have hch := chain_holds δ s Mb K n Δ 𝒱 ℬ C u y hδ hs hMpos hΔ h𝒱 hv hℬ hC
    have hfin : (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (termCenLow δ s (Mb B) Δ v B u y)) ≠ ⊤ := by
      intro h
      have := (hch.2.2.1 hz).1
      unfold DcenLow at this
      rw [h, ENNReal.toReal_top] at this
      exact lt_irrefl 0 this
    have hlow := (box_exp hδ hs (hMpos B hB) Δ θ.1 hΔ (hv _ hθ.1) (hC.1 B hB).1 u y hz).2 θ.2 hθB
    rw [hθe] at hlow
    unfold DcenLow
    calc Real.exp (-ε) * Dfilter δ s Δ 𝒱 ℬ u y
        ≤ Real.exp (-Xexp δ s (Mb B) Δ θ.1 B u y) * Dfilter δ s Δ 𝒱 ℬ u y :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (neg_le_neg (hXε B hB θ.1 hθ.1))) hDpos.le
      _ ≤ termLow δ s (Mb B) Δ θ.1 B u y := hlow
      _ ≤ termCenLow δ s (Mb B) Δ θ.1 B u y := termLow_le_termCenLow hδ _ Δ θ.1 B u y hz
      _ ≤ _ := (ENNReal.ofReal_le_iff_le_toReal hfin).1
          (le_iSup₂_of_le B hB (le_iSup₂_of_le θ.1 hθ.1 le_rfl))

end Novel.D19CenteredQuadrature
