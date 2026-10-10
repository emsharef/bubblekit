import Novel.D19FilteredLikelihoodValid
import Novel.D17ClockCellsProof

/-!
# Claim 036, part 4: the comparison (9)

* `D_filter ≤ D_endpoint`: the conditional mass is the evaluation walk averaged over the training
  endpoint law `α_K/L_K`, which lives on the last training cell (`walk_append`); so it is at most
  the largest walk from an exact endpoint in that cell.
* `D_endpoint ≤ D_clock^(h,ℓ)`: claim 034 bounds the walk from every endpoint in the cell and every
  parameter in a covering dyadic box (`walk_le_Bc`).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick Standalone.D17ClockCells
  Novel.D17ClockCells

theorem endpoint_bdd (δ : ℝ) {K n : ℕ} (Δ : Fin (K + 1 + n) → ℝ) (𝒱 : Finset (Fin (K + 1 + n) → ℝ))
    (ℬ : Box) (u : Fin (K + 1) → ℕ) (y : Fin n → ℕ) :
    BddAbove {r | ∃ θ ∈ Θset 𝒱 ℬ, ∃ x ∈ mcell δ (u (Fin.last K)),
      r = (walkM δ (evl (muF Δ θ.1 θ.2.1 θ.2.2)) (evl (sdF θ.1 θ.2.2)) x {y}).toReal} := by
  refine ⟨1, ?_⟩
  rintro r ⟨θ, -, x, -, rfl⟩
  have := walk_prob (δ := δ) (evl (muF Δ θ.1 θ.2.1 θ.2.2)) (evl (sdF θ.1 θ.2.2)) x
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

theorem comparison_holds : Standalone.D19FilteredLikelihood.comparison := by
  intro δ s K n h ℓ Δ 𝒱 ℬ u y hδ hs hΔ h𝒱 hv hℬ
  have hbdd := endpoint_bdd δ Δ 𝒱 ℬ u y
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨θ, hθ, hθe⟩, -, -, -⟩ := exact_holds.2.2.2.2.2 δ s (K + 1) n Δ 𝒱 ℬ u y hδ hs hΔ h𝒱 hv hℬ
    rw [← hθe]
    have hw : 0 < θ.2.2 := hℬ.2.1.trans_le hθ.2.2.1
    have hLk := Lz_pos hδ hs (trn (muF Δ θ.1 θ.2.1 θ.2.2)) (trn (sdF θ.1 θ.2.2))
      (fun j => sdF_pos (hv _ hθ.1) hw _) u
    set Dend := Dendpoint δ Δ 𝒱 ℬ u y
    have hDend0 : 0 ≤ Dend := by
      refine le_csSup_of_le hbdd ⟨θ, hθ, mlo δ (u (Fin.last K)), ⟨le_rfl,
        Novel.D14FixedTick.mlo_lt_mhi hδ _⟩, rfl⟩ ENNReal.toReal_nonneg
    -- The joint mass is at most `D_endpoint` times the training mass.
    have hj : walkM δ (muF Δ θ.1 θ.2.1 θ.2.2) (sdF θ.1 θ.2.2) s {Fin.append u y} ≤
        ENNReal.ofReal Dend * walkM δ (trn (muF Δ θ.1 θ.2.1 θ.2.2)) (trn (sdF θ.1 θ.2.2)) s {u} := by
      rw [walk_append hδ hs.le, ← alpha_univ hδ hs.le, ← lintegral_const]
      show ∫⁻ x, _ ∂(((alphaF δ s K _ _ (Fin.init u)).bind _).restrict (mcell δ (u (Fin.last K)))) ≤
        ∫⁻ _, _ ∂(((alphaF δ s K _ _ (Fin.init u)).bind _).restrict (mcell δ (u (Fin.last K))))
      refine setLIntegral_mono measurable_const fun x hx => ?_
      rw [← ENNReal.ofReal_toReal (walk_ne_top _ _ x y)]
      exact ENNReal.ofReal_le_ofReal (le_csSup hbdd ⟨θ, hθ, x, hx, rfl⟩)
    unfold gF
    rw [div_le_iff₀ hLk]
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (walk_ne_top _ _ s u)) hj
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hDend0] at this
  · have hDc := Dclock_bounds hδ hℬ (Δ := evl Δ) (𝒱 := 𝒱.image evl) (fun j => hΔ _)
      (h𝒱.image _) (fun vc hvc j => by
        obtain ⟨v, hv', rfl⟩ := Finset.mem_image.1 hvc; exact hv v hv' _) h ℓ (u (Fin.last K)) y
    rw [← ENNReal.ofReal_toReal (hDc.2.trans_lt ENNReal.one_lt_top).ne]
    refine ENNReal.ofReal_le_ofReal (Real.sSup_le (fun r hr => ?_) ENNReal.toReal_nonneg)
    obtain ⟨θ, hθ, x, hx, rfl⟩ := hr
    obtain ⟨i, hi, k, hk, hpb⟩ := pbox_cover h hθ.2
    have hbd := walk_le_Bc hδ (pbox_valid hℬ h i k) ℓ (Δ := evl Δ) (vc := evl θ.1) (fun j => hΔ _)
      (fun j => hv _ hθ.1 _) y hpb hx
    have hle : walkM δ (evl (muF Δ θ.1 θ.2.1 θ.2.2)) (evl (sdF θ.1 θ.2.2)) x {y} ≤
        Dclock δ ℬ h ℓ (evl Δ) (𝒱.image evl) (u (Fin.last K)) y :=
      hbd.trans (le_iSup₂_of_le i (Finset.mem_range.2 hi) (le_iSup₂_of_le k (Finset.mem_range.2 hk)
        (le_iSup₂_of_le (evl θ.1) (Finset.mem_image_of_mem _ hθ.1) le_rfl)))
    exact ENNReal.toReal_mono (hDc.2.trans_lt ENNReal.one_lt_top).ne hle

end Novel.D19FilteredLikelihood
