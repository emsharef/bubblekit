import Standalone.SplitLikelihoodDominated
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# AX-58's moment form, proved from Mathlib

Proves `Standalone.SplitLikelihoodDominated.AX58` (`ax58_holds`), by the AX-57 route of
`Novel/SplitLikelihoodSupportProof.lean`:
* `mul_Edrift_le`: `g · E^drift ≤ Ĝ` whenever `g ≤ D`. On `0 < D < ∞` this is `g/D ≤ 1`; at `D = 0`
  the null density vanishes (`0 · ∞ = 0`); and the score is zero otherwise.
* At each `u` where the conditional law is `g λ(u, ·) μ`, `∫ E^drift dH = ∫ g E^drift dμ ≤ ∫ Ĝ dμ = 1`
  (`lintegral_withDensity_eq_lintegral_mul`).
* Disintegration (`compProd_map_condDistrib`, `Measure.lintegral_compProd`) integrates over the
  actual training law, and Markov (`mul_meas_ge_le_lintegral₀`) gives the test.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.SplitLikelihoodDominated

open Standalone.D3CatalogueCalibration Standalone.SplitLikelihoodDominated

theorem Edrift_meas : Measurable fun p : ℝ × ℝ≥0∞ => Edrift p.1 p.2 := by
  classical
  unfold Edrift
  refine Measurable.ite ((measurableSet_eq_fun measurable_fst measurable_const).union
    (measurableSet_eq_fun measurable_snd measurable_const)) measurable_const ?_
  exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
    ((ENNReal.measurable_ofReal.comp measurable_fst).div measurable_snd)

theorem mul_Edrift_le {a b : ℝ} {d : ℝ≥0∞} (hbd : ENNReal.ofReal b ≤ d) :
    ENNReal.ofReal b * Edrift a d ≤ ENNReal.ofReal a := by
  classical
  unfold Edrift
  split_ifs with h1 h2
  · rw [mul_zero]; exact bot_le
  · rw [h2, nonpos_iff_eq_zero] at hbd
    rw [hbd, zero_mul]; exact bot_le
  · push Not at h1
    calc ENNReal.ofReal b * (ENNReal.ofReal a / d) ≤ d * (ENNReal.ofReal a / d) :=
          mul_le_mul_left hbd _
      _ = ENNReal.ofReal a := ENNReal.mul_div_cancel h2 h1.2

/-- AX-58's conditional, moment and test form holds. -/
theorem ax58_holds : AX58 := by
  intro Ω 𝒰 𝒱 Λ _ _ _ _ _ _ P _ U V μ Gh g D l hM hc
  have hμ := hM.sfinite
  have hEm : Measurable fun p : 𝒰 × 𝒱 => Edrift (Gh p.1 p.2) (D p.1 p.2) :=
    Edrift_meas.comp (hM.measGh.prodMk hM.measD)
  -- The conditional bound at every `u` where the actual law is the null density.
  have hcond : ∀ᵐ u ∂(P.map U),
      ∫⁻ v, Edrift (Gh u v) (D u v) ∂(condDistrib V U P u) ≤ 1 := by
    filter_upwards [hc] with u hu
    have h1 : Measurable fun v => ENNReal.ofReal (g l u v) :=
      ENNReal.measurable_ofReal.comp ((hM.measg l).comp measurable_prodMk_left)
    have h2 : Measurable fun v => Edrift (Gh u v) (D u v) := hEm.comp measurable_prodMk_left
    rw [hu, lintegral_withDensity_eq_lintegral_mul _ h1 h2]
    calc ∫⁻ v, ((fun v => ENNReal.ofReal (g l u v)) * fun v => Edrift (Gh u v) (D u v)) v ∂μ
        ≤ ∫⁻ v, ENNReal.ofReal (Gh u v) ∂μ :=
          lintegral_mono fun v => mul_Edrift_le (hM.dom l u v)
      _ = 1 := hM.normGh u
  have hmom : ∫⁻ ω, Edrift (Gh (U ω) (V ω)) (D (U ω) (V ω)) ∂P ≤ 1 := by
    have hUV : Measurable fun ω => (U ω, V ω) := hM.measU.prodMk hM.measV
    calc ∫⁻ ω, Edrift (Gh (U ω) (V ω)) (D (U ω) (V ω)) ∂P
        = ∫⁻ p, Edrift (Gh p.1 p.2) (D p.1 p.2) ∂(P.map fun ω => (U ω, V ω)) := by
          rw [lintegral_map hEm hUV]
      _ = ∫⁻ u, ∫⁻ v, Edrift (Gh u v) (D u v) ∂(condDistrib V U P u) ∂(P.map U) := by
          rw [← compProd_map_condDistrib hM.measU.aemeasurable hM.measV.aemeasurable,
            Measure.lintegral_compProd hEm]
      _ ≤ ∫⁻ _, 1 ∂(P.map U) := lintegral_mono_ae hcond
      _ ≤ 1 := by
          rw [lintegral_const, one_mul]
          exact prob_le_one
  refine ⟨hcond, hmom, fun α hα hα1 => ?_⟩
  have hT : Measurable fun ω => Edrift (Gh (U ω) (V ω)) (D (U ω) (V ω)) :=
    hEm.comp (hM.measU.prodMk hM.measV)
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hT.aemeasurable (ENNReal.ofReal (1 / α))
  have hsub : {ω | ENNReal.ofReal (1 / α) < Edrift (Gh (U ω) (V ω)) (D (U ω) (V ω))} ⊆
      {ω | ENNReal.ofReal (1 / α) ≤ Edrift (Gh (U ω) (V ω)) (D (U ω) (V ω))} := fun _ h => by
    simp only [mem_ofPred_eq] at h ⊢; exact h.le
  have hle : ENNReal.ofReal (1 / α) *
      P {ω | ENNReal.ofReal (1 / α) < Edrift (Gh (U ω) (V ω)) (D (U ω) (V ω))} ≤ 1 :=
    (mul_le_mul_right (measure_mono hsub) _).trans (hmk.trans hmom)
  have hinv : (ENNReal.ofReal (1 / α))⁻¹ = ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
  rw [← hinv, ENNReal.le_inv_iff_mul_le, mul_comm]
  exact hle

theorem proof : Standalone.SplitLikelihoodDominated.statement := ax58_holds

end Novel.SplitLikelihoodDominated
