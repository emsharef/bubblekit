import Novel.D19FilteredLikelihoodCont

/-!
# Claim 036, part 1: the exact likelihood

Assembly of part 1 from the forward measures (`alpha_univ`, `walk_append`, `walk_pos`,
`tsum_append`) and continuity (`walk_contOn`). The maximum over `𝒱 × ℬ` is attained: each clock's
conditional mass is continuous on the compact rectangle, and `𝒱` is finite.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick Standalone.D17ClockCells

theorem walk_ne_top {δ : ℝ} {m : ℕ} (μ σ : Fin m → ℝ) (x : ℝ) (z : Fin m → ℕ) :
    walkM δ μ σ x {z} ≠ ⊤ := by
  have := walk_prob (δ := δ) μ σ x; exact measure_ne_top _ _

theorem Lz_pos {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 < s) {m : ℕ} (μ σ : Fin m → ℝ)
    (hσ : ∀ j, 0 < σ j) (z : Fin m → ℕ) : 0 < Lz δ s μ σ z :=
  ENNReal.toReal_pos (walk_pos hδ hs m μ σ z hσ).ne' (walk_ne_top μ σ s z)

theorem sdF_pos {m : ℕ} {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) {w : ℝ} (hw : 0 < w) (j : Fin m) :
    0 < sdF v w j := Real.sqrt_pos.2 (mul_pos hw (hv j))

theorem gF_hasSum {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 < s) {K n : ℕ} (Δ v : Fin (K + n) → ℝ)
    (hv : ∀ j, 0 < v j) (b : ℝ) {w : ℝ} (hw : 0 < w) (u : Fin K → ℕ) :
    HasSum (gF δ s Δ v b w u) 1 := by
  have hL := Lz_pos hδ hs (trn (muF Δ v b w)) (trn (sdF v w)) (fun j => sdF_pos hv hw _) u
  have ht := tsum_append hδ hs.le (muF Δ v b w) (sdF v w) u
  have h1 := ENNReal.hasSum_toReal (ht.symm ▸ walk_ne_top _ _ s u)
  rw [← ENNReal.tsum_toReal_eq (fun y => walk_ne_top _ _ s _), ht] at h1
  have := h1.div_const (Lz δ s (trn (muF Δ v b w)) (trn (sdF v w)) u)
  rwa [show ((walkM δ (trn (muF Δ v b w)) (trn (sdF v w)) s) {u}).toReal =
    Lz δ s (trn (muF Δ v b w)) (trn (sdF v w)) u from rfl, div_self hL.ne'] at this

theorem gF_nonneg (δ s : ℝ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (b w : ℝ) (u : Fin K → ℕ)
    (y : Fin n → ℕ) : 0 ≤ gF δ s Δ v b w u y :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem gF_le_one {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 < s) {K n : ℕ} (Δ v : Fin (K + n) → ℝ)
    (hv : ∀ j, 0 < v j) (b : ℝ) {w : ℝ} (hw : 0 < w) (u : Fin K → ℕ) (y : Fin n → ℕ) :
    gF δ s Δ v b w u y ≤ 1 :=
  le_hasSum (gF_hasSum hδ hs Δ v hv b hw u) y fun y' _ => gF_nonneg δ s Δ v b w u y'

theorem gF_pos {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 < s) {K n : ℕ} (Δ v : Fin (K + n) → ℝ)
    (hv : ∀ j, 0 < v j) (b : ℝ) {w : ℝ} (hw : 0 < w) (u : Fin K → ℕ) (y : Fin n → ℕ) :
    0 < gF δ s Δ v b w u y :=
  div_pos (Lz_pos hδ hs _ _ (fun _ => sdF_pos hv hw _) _)
    (Lz_pos hδ hs _ _ (fun _ => sdF_pos hv hw _) _)

theorem continuous_muF {m : ℕ} (Δ v : Fin m → ℝ) :
    Continuous fun bw : ℝ × ℝ => muF Δ v bw.1 bw.2 :=
  continuous_pi fun _ => (continuous_fst.mul continuous_const).sub
    ((continuous_snd.mul continuous_const).div_const _)

theorem continuous_sdF {m : ℕ} (v : Fin m → ℝ) : Continuous fun bw : ℝ × ℝ => sdF v bw.2 :=
  continuous_pi fun _ => Real.continuous_sqrt.comp (continuous_snd.mul continuous_const)

theorem Lz_contOn {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 < s) {m : ℕ} (Δ v : Fin m → ℝ)
    (hv : ∀ j, 0 < v j) (z : Fin m → ℕ) :
    ContinuousOn (fun bw : ℝ × ℝ => Lz δ s (muF Δ v bw.1 bw.2) (sdF v bw.2) z) {bw | 0 < bw.2} := by
  have h := walk_contOn (X := ℝ × ℝ) hδ hs (Pm := fun bw => (muF Δ v bw.1 bw.2, sdF v bw.2))
    ((continuous_muF Δ v).prodMk (continuous_sdF v)).continuousOn
    (fun bw hbw j => sdF_pos hv hbw j) z
  exact fun x hx => ContinuousAt.comp_continuousWithinAt (g := ENNReal.toReal)
    (f := fun bw : ℝ × ℝ => walkM δ (muF Δ v bw.1 bw.2) (sdF v bw.2) s {z})
    (ENNReal.continuousAt_toReal (walk_ne_top (δ := δ) (muF Δ v x.1 x.2) (sdF v x.2) s z)) (h x hx)

theorem gF_contOn {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 < s) {K n : ℕ} (Δ v : Fin (K + n) → ℝ)
    (hv : ∀ j, 0 < v j) (u : Fin K → ℕ) (y : Fin n → ℕ) :
    ContinuousOn (fun bw : ℝ × ℝ => gF δ s Δ v bw.1 bw.2 u y) {bw | 0 < bw.2} := by
  have h1 := Lz_contOn hδ hs Δ v hv (Fin.append u y)
  have h2 := Lz_contOn hδ hs (trn Δ) (trn v) (fun j => hv _) u
  exact h1.div h2 fun bw hbw => (Lz_pos hδ hs _ _ (fun j => sdF_pos (fun j => hv _) hbw j) u).ne'

/-- The maximum over `𝒱 × ℬ` is attained. -/
theorem gF_max {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 < s) {K n : ℕ} (Δ : Fin (K + n) → ℝ)
    {𝒱 : Finset (Fin (K + n) → ℝ)} (h𝒱 : 𝒱.Nonempty) (hv : ∀ v ∈ 𝒱, ∀ j, 0 < v j) {ℬ : Box}
    (hℬ : ℬ.Valid) (u : Fin K → ℕ) (y : Fin n → ℕ) :
    ∃ θ ∈ Θset 𝒱 ℬ, ∀ θ' ∈ Θset 𝒱 ℬ, gF δ s Δ θ'.1 θ'.2.1 θ'.2.2 u y ≤ gF δ s Δ θ.1 θ.2.1 θ.2.2 u y := by
  set Rr : Set (ℝ × ℝ) := Icc ℬ.bL ℬ.bH ×ˢ Icc ℬ.wL ℬ.wH
  have hRc : IsCompact Rr := isCompact_Icc.prod isCompact_Icc
  have hRn : Rr.Nonempty := ⟨(ℬ.bL, ℬ.wL), ⟨le_rfl, hℬ.1⟩, ⟨le_rfl, hℬ.2.2⟩⟩
  have hRsub : Rr ⊆ {bw | 0 < bw.2} := fun bw hbw => hℬ.2.1.trans_le hbw.2.1
  have hper : ∀ v ∈ 𝒱, ∃ bw ∈ Rr, ∀ bw' ∈ Rr, gF δ s Δ v bw'.1 bw'.2 u y ≤ gF δ s Δ v bw.1 bw.2 u y :=
    fun v hvv => by
      obtain ⟨bw, hbw, hmax⟩ := hRc.exists_isMaxOn hRn ((gF_contOn hδ hs Δ v (hv v hvv) u y).mono hRsub)
      exact ⟨bw, hbw, fun bw' hbw' => hmax hbw'⟩
  choose! bwv hbwv hmaxv using hper
  obtain ⟨v₀, hv₀, hbest⟩ := 𝒱.exists_max_image (fun v => gF δ s Δ v (bwv v).1 (bwv v).2 u y) h𝒱
  refine ⟨(v₀, bwv v₀), ⟨hv₀, hbwv v₀ hv₀⟩, fun θ' hθ' => ?_⟩
  exact (hmaxv θ'.1 hθ'.1 θ'.2 hθ'.2).trans (hbest θ'.1 hθ'.1)

theorem exact_holds : Standalone.D19FilteredLikelihood.exact := by
  refine ⟨fun δ s m μ σ z hδ hs hσ => Lz_pos hδ hs μ σ hσ z,
    fun δ s m μ σ z hδ hs _ => alpha_univ hδ hs.le μ σ z,
    fun δ s K n μ σ u y hδ hs _ => walk_append hδ hs.le μ σ u y,
    fun δ s K n Δ v b w u hδ hs _ hv hw => gF_hasSum hδ hs Δ v hv b hw u,
    fun δ s K n Δ v u y hδ hs _ hv => gF_contOn hδ hs Δ v hv u y,
    fun δ s K n Δ 𝒱 ℬ u y hδ hs _ h𝒱 hv hℬ => ?_⟩
  obtain ⟨θ, hθ, hmax⟩ := gF_max hδ hs Δ h𝒱 hv hℬ u y
  have hw : ∀ θ' ∈ Θset 𝒱 ℬ, 0 < θ'.2.2 := fun θ' h => hℬ.2.1.trans_le h.2.2.1
  have hG : IsGreatest ((fun θ : (Fin (K + n) → ℝ) × ℝ × ℝ => gF δ s Δ θ.1 θ.2.1 θ.2.2 u y) ''
      Θset 𝒱 ℬ) (gF δ s Δ θ.1 θ.2.1 θ.2.2 u y) :=
    ⟨⟨θ, hθ, rfl⟩, by rintro _ ⟨θ', hθ', rfl⟩; exact hmax θ' hθ'⟩
  have hD : Dfilter δ s Δ 𝒱 ℬ u y = gF δ s Δ θ.1 θ.2.1 θ.2.2 u y := hG.csSup_eq
  refine ⟨⟨θ, hθ, hD.symm⟩, fun θ' hθ' => hD ▸ hmax θ' hθ', ?_, ?_⟩
  · rw [hD]; exact gF_pos hδ hs Δ θ.1 (hv _ hθ.1) _ (hw θ hθ) u y
  · rw [hD]; exact gF_le_one hδ hs Δ θ.1 (hv _ hθ.1) _ (hw θ hθ) u y

end Novel.D19FilteredLikelihood
