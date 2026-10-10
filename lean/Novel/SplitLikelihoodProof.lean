import Standalone.D3CatalogueCalibration

/-!
# AX-52's moment form, proved from Mathlib

Proves claim 051's restated input `Standalone.D3CatalogueCalibration.AX52` (`ax52_holds`): for a
correctly specified finite catalogue, the split likelihood ratio at the true parameter has mean at
most one. No hypothesis structure is needed. The steps apply existing Mathlib results to the
premises:
* the disintegration `P∘(U,V)⁻¹ = (P∘U⁻¹) ⊗ condDistrib V U P` (`compProd_map_condDistrib`) and
  Tonelli for the composition product (`Measure.lintegral_compProd`);
* correct specification (`IsCondDensity`) replaces `condDistrib V U P u` by
  `μ.withDensity g_ϑ(u, ·)` for almost every `u`, and integration against a density
  (`lintegral_withDensity_eq_lintegral_mul`);
* positivity cancels `g_ϑ`, and normalization of `g_{ϑ̂(u)}(u, ·)` makes the inner integral one.
In fact the mean is exactly one. The source's bound (Wasserman–Ramdas–Balakrishnan (6), §6) is used
only in this specialization, with finite strictly positive common-support densities.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.SplitLikelihood

open Standalone.D3CatalogueCalibration

/-- `(u, v) ↦ g_{sel u}(u, v)` is measurable. -/
theorem measurable_selected {𝒰 𝒱 Θ : Type} [MeasurableSpace 𝒰] [MeasurableSpace 𝒱] [Countable Θ]
    {g : Θ → 𝒰 → 𝒱 → ℝ} {sel : 𝒰 → Θ} (hg : ∀ θ, Measurable (Function.uncurry (g θ)))
    (hsel : ∀ θ, MeasurableSet (sel ⁻¹' {θ})) :
    Measurable fun p : 𝒰 × 𝒱 => g (sel p.1) p.1 p.2 := fun s hs => by
  have : (fun p : 𝒰 × 𝒱 => g (sel p.1) p.1 p.2) ⁻¹' s =
      ⋃ θ, ((sel ⁻¹' {θ}) ×ˢ (univ : Set 𝒱)) ∩ (Function.uncurry (g θ)) ⁻¹' s := by
    ext ⟨u, v⟩
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_prod, mem_singleton_iff, mem_univ,
      and_true, Function.uncurry_apply_pair]
    exact ⟨fun h => ⟨sel u, rfl, h⟩, fun ⟨θ, hθ, h⟩ => hθ ▸ h⟩
  rw [this]
  exact MeasurableSet.iUnion fun θ => ((hsel θ).prod MeasurableSet.univ).inter (hg θ hs)

/-- AX-52's moment form holds. -/
theorem ax52_holds : AX52 := by
  intro Ω 𝒰 𝒱 Θ _ _ _ _ _ _ _ P _ U V μ g sel ϑ hM hc
  have := Fintype.ofFinite Θ
  have hμ := hM.sfinite
  set F : 𝒰 × 𝒱 → ℝ≥0∞ := fun p => ENNReal.ofReal (g (sel p.1) p.1 p.2 / g ϑ p.1 p.2) with hFdef
  have hF : Measurable F :=
    ENNReal.measurable_ofReal.comp ((measurable_selected hM.measg hM.measSel).div (hM.measg ϑ))
  have hUV : Measurable fun ω => (U ω, V ω) := hM.measU.prodMk hM.measV
  calc ∫⁻ ω, ENNReal.ofReal (Tstat U V g sel ϑ ω) ∂P
      = ∫⁻ p, F p ∂(P.map fun ω => (U ω, V ω)) := by
        rw [lintegral_map hF hUV]; rfl
    _ = ∫⁻ u, ∫⁻ v, F (u, v) ∂(condDistrib V U P u) ∂(P.map U) := by
        rw [← compProd_map_condDistrib hM.measU.aemeasurable hM.measV.aemeasurable,
          Measure.lintegral_compProd hF]
    _ = ∫⁻ _, 1 ∂(P.map U) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hc] with u hu
        have h1 : Measurable fun v => ENNReal.ofReal (g ϑ u v) :=
          ENNReal.measurable_ofReal.comp ((hM.measg ϑ).comp measurable_prodMk_left)
        have h2 : Measurable fun v => F (u, v) := hF.comp measurable_prodMk_left
        rw [hu, lintegral_withDensity_eq_lintegral_mul _ h1 h2]
        rw [← hM.norm (sel u) u]
        refine lintegral_congr fun v => ?_
        simp only [Pi.mul_apply, hFdef]
        rw [← ENNReal.ofReal_mul (hM.pos ϑ u v).le, mul_div_cancel₀ _ (hM.pos ϑ u v).ne']
    _ ≤ 1 := by
        rw [lintegral_const, one_mul]
        exact prob_le_one

end Novel.SplitLikelihood
