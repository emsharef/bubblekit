import Standalone.D15SharedJump
import Novel.D15SharedJumpBox

/-!
# Claim 061 (D15): proof

Proves `Standalone.D15SharedJump.statement` (`statement_holds`).
* `envelope`: `Novel/D15SharedJumpEnvelope.lean` (`V_J`) and `Novel/D15SharedJumpBox.lean` (`V_J^P`).
* `score`: claim 060's `score_gen` applied to the envelopes `V_J` and `V_J^P`. Each is measurable,
  finite, dominates every jump law in `Θ_J`, and takes `D_G`'s values off the positive stratum. The
  orderings (3) and (8), and the cap, floor and refinement comparisons, follow from the envelope
  comparisons and the monotonicity of `Edrift` in its denominator (`Edrift_anti`).
* Parts 2 and 3 in return coordinates: `Novel/D15JumpProfileSearchProof.lean`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D15SharedJump

open Standalone.D15SharedJump Standalone.D13DriftNull Standalone.D15JumpEnvelope
  Standalone.CEVSupport Standalone.D13CEVCatalogue Novel.D15JumpEnvelopeBound
  Novel.D13DriftRectScore Standalone.SplitLikelihoodDominated

theorem envelope_holds : Standalone.D15SharedJump.envelope := by
  intro n Δ σmin Λ hn hΔ hs
  refine ⟨fun θ hθ y0 y => gJ_le_VJ hn hΔ hs hθ y0 y, VJ_le_UJ hn hΔ hs, VJ_lt_top hn hΔ hs,
    measurable_VJ hΔ hs, fun y0 y hp => VJ_off hp, fun hΛ y0 y hp => ?_,
    fun hΛ y0 y hp => VJ_top hp hΛ, fun Λ' h y0 y => VJ_mono_cap hn hΔ hs h y0 y,
    fun σ' hs' hσ y0 y => VJ_mono_floor hΔ hs' hσ y0 y, fun h0 => VJ_cap_zero hn hΔ hs h0,
    fun Nb bx hR => ⟨fun y0 y => ⟨VJ_le_VP hn hΔ hs hR y0 y, VP_le_UJ y0 y⟩, VP_lt_top hΔ hs,
      measurable_VP hR, fun y0 y hp => VP_off hp⟩,
    fun Nb bx Nb' bx' hR hf y0 y => VP_refine hΔ hR hf y0 y⟩
  obtain ⟨p, hp', hV, -⟩ := VJ_attain hn hΔ hs hΛ hp
  exact ⟨p, hp', hV⟩

theorem score_holds : Standalone.D15SharedJump.score := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN σmin Λ hm2 hs g sel Δe y0 yv ED EJ
    DP EP E
  have hΔ : ∀ j, 0 < Δe j := fun j => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  have hm : 0 < m := by omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := Novel.D15JumpEnvelopeScore.score_gen P' 𝓕 Wb
    Solves h55 h56 hW s R k m c t pw κ hN σmin Λ hm2 (fun y0 y => VJ σmin Λ Δe y0 y)
    (measurable_VJ hΔ hs) (VJ_lt_top hm hΔ hs) (fun θ hθ y0 y => gJ_le_VJ hm hΔ hs hθ y0 y)
    (fun y0 y hp => VJ_off hp)
  have hVU : Λ = ⊤ → ∀ y0' y', VJ σmin Λ Δe y0' y' = UJ σmin Λ Δe y0' y' := fun hΛ y0' y' => by
    by_cases hp : PosPath y0' y'
    · rw [VJ_top hp hΛ, hΛ, UJ_top_pos hs hΔ hp]
    · rw [VJ_off hp, UJ_off hp]
  refine ⟨⟨h1, h2, h3, h4, h5, h6⟩,
    fun u v => ⟨Edrift_anti (max_le_max le_rfl (VJ_le_UJ hm hΔ hs _ _)), (h7 u v).1, (h7 u v).2⟩,
    fun Λ' hΛ u v => Edrift_anti (max_le_max le_rfl (VJ_mono_cap hm hΔ hs hΛ _ _)),
    fun σ' hs' hσ u v => Edrift_anti (max_le_max le_rfl (VJ_mono_floor hΔ hs' hσ _ _)),
    fun h0 u v => ?_, fun htop u v => ?_, h8, h9, fun Nb bx hR => ?_,
    fun Nb bx Nb' bx' hR hf u v => Edrift_anti (max_le_max le_rfl (VP_refine hΔ hR hf _ _))⟩
  · show Edrift _ (max _ _) = Edrift _ _
    have hle : VJ σmin Λ Δe (y0 u) (yv v) ≤ Dmax Δe pw g u v :=
      (VJ_cap_zero hm hΔ hs h0 _ _).trans (le_max_right _ _)
    rw [max_eq_left hle]
  · show Edrift _ (max _ _) = Edrift _ (max _ _)
    rw [hVU htop]
  · obtain ⟨b1, b2, b3, b4, b5, b6, -, -, -⟩ := Novel.D15JumpEnvelopeScore.score_gen P' 𝓕 Wb
      Solves h55 h56 hW s R k m c t pw κ hN σmin Λ hm2 (fun y0 y => VP σmin Λ Δe Nb bx y0 y)
      (measurable_VP hR) (VP_lt_top hΔ hs)
      (fun θ hθ y0 y => (gJ_le_VJ hm hΔ hs hθ y0 y).trans (VJ_le_VP hm hΔ hs hR y0 y))
      (fun y0 y hp => VP_off hp)
    exact ⟨⟨b1, b2, b3, b4, b5, b6⟩, fun u v =>
      ⟨Edrift_anti (max_le_max le_rfl (VP_le_UJ _ _)),
        Edrift_anti (max_le_max le_rfl (VJ_le_VP hm hΔ hs hR _ _))⟩⟩

theorem statement_holds : Standalone.D15SharedJump.statement :=
  ⟨envelope_holds, score_holds, Novel.D15JumpProfileSearch.statement_holds⟩

end Novel.D15SharedJump
