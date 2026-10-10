import Standalone.SplitLikelihoodSupport
import Novel.SplitLikelihoodProof

/-!
# AX-57's moment form, proved from Mathlib

Proves `Standalone.SplitLikelihoodSupport.AX57` (`ax57_holds`). It is the AX-52 argument of
`Novel/SplitLikelihoodProof.lean`, with nonnegative densities and the extended ratio `R₊`:
* `transfer`: disintegration (`compProd_map_condDistrib`, `Measure.lintegral_compProd`) and
  correct specification turn `∫⁻ h(U,V) dP` into `∫⁻ ∫⁻ g_ϑ(u,v) h(u,v) μ(dv) (P∘U⁻¹)(du)`;
* `mul_Rplus_le`: `b · R₊(a, b) ≤ a`, which replaces positive-density cancellation (`0 · ∞ = 0`);
* the zero set of the true density has `P`-measure zero, because `g_ϑ · 1{g_ϑ = 0} = 0`;
* coverage by Markov's inequality (`mul_meas_ge_le_lintegral₀`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.SplitLikelihoodSupport

open Standalone.D3CatalogueCalibration Standalone.SplitLikelihoodSupport

theorem Rplus_meas : Measurable fun p : ℝ × ℝ => Rplus p.1 p.2 := by
  classical
  unfold Rplus
  refine Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    (ENNReal.measurable_ofReal.comp (measurable_fst.div measurable_snd)) ?_
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const
    measurable_const

theorem mul_Rplus_le {a b : ℝ} (hb : 0 ≤ b) :
    ENNReal.ofReal b * Rplus a b ≤ ENNReal.ofReal a := by
  classical
  unfold Rplus
  split_ifs with h1 h2
  · rw [← ENNReal.ofReal_mul hb, mul_div_cancel₀ _ h1.ne']
  · rw [mul_zero]; exact zero_le
  · have : b = 0 := le_antisymm (not_lt.1 h1) hb
    simp [this]

/-- Integrals of functions of `(U, V)` against the true conditional density. -/
theorem transfer {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒰] [StandardBorelSpace 𝒱] [Nonempty 𝒱] {P : Measure Ω}
    [IsProbabilityMeasure P] {U : Ω → 𝒰} {V : Ω → 𝒱} {μ : Measure 𝒱} {g : Θ → 𝒰 → 𝒱 → ℝ}
    {sel : 𝒰 → Θ} {ϑ : Θ} (hM : SupportModel U V μ g sel) (hc : IsCondDensity P U V μ (g ϑ))
    {h : 𝒰 × 𝒱 → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ ω, h (U ω, V ω) ∂P =
      ∫⁻ u, ∫⁻ v, ENNReal.ofReal (g ϑ u v) * h (u, v) ∂μ ∂(P.map U) := by
  have hμ := hM.sfinite
  have hUV : Measurable fun ω => (U ω, V ω) := hM.measU.prodMk hM.measV
  calc ∫⁻ ω, h (U ω, V ω) ∂P = ∫⁻ p, h p ∂(P.map fun ω => (U ω, V ω)) := by
        rw [lintegral_map hh hUV]
    _ = ∫⁻ u, ∫⁻ v, h (u, v) ∂(condDistrib V U P u) ∂(P.map U) := by
        rw [← compProd_map_condDistrib hM.measU.aemeasurable hM.measV.aemeasurable,
          Measure.lintegral_compProd hh]
    _ = _ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hc] with u hu
        have h1 : Measurable fun v => ENNReal.ofReal (g ϑ u v) :=
          ENNReal.measurable_ofReal.comp ((hM.measg ϑ).comp measurable_prodMk_left)
        have h2 : Measurable fun v => h (u, v) := hh.comp measurable_prodMk_left
        rw [hu, lintegral_withDensity_eq_lintegral_mul _ h1 h2]
        rfl

/-- AX-57's moment, null-support and coverage form holds. -/
theorem ax57_holds : AX57 := by
  intro Ω 𝒰 𝒱 Θ _ _ _ _ _ _ _ P _ U V μ g sel ϑ hM hc
  classical
  have := Fintype.ofFinite Θ
  have hsel := Novel.SplitLikelihood.measurable_selected hM.measg hM.measSel
  have hTm : Measurable fun p : 𝒰 × 𝒱 => Rplus (g (sel p.1) p.1 p.2) (g ϑ p.1 p.2) :=
    Rplus_meas.comp (hsel.prodMk (hM.measg ϑ))
  have hmom : ∫⁻ ω, TplusE U V g sel ϑ ω ∂P ≤ 1 := by
    rw [show (∫⁻ ω, TplusE U V g sel ϑ ω ∂P) =
        ∫⁻ ω, (fun p : 𝒰 × 𝒱 => Rplus (g (sel p.1) p.1 p.2) (g ϑ p.1 p.2)) (U ω, V ω) ∂P from rfl,
      transfer hM hc hTm]
    calc ∫⁻ u, ∫⁻ v, ENNReal.ofReal (g ϑ u v) * Rplus (g (sel u) u v) (g ϑ u v) ∂μ ∂(P.map U)
        ≤ ∫⁻ u, ∫⁻ v, ENNReal.ofReal (g (sel u) u v) ∂μ ∂(P.map U) :=
          lintegral_mono fun u => lintegral_mono fun v =>
            mul_Rplus_le (hM.nonneg _ _ _)
      _ = ∫⁻ _, 1 ∂(P.map U) := by
          congr 1; funext u; exact hM.norm (sel u) u
      _ ≤ 1 := by
          rw [lintegral_const, one_mul]
          exact prob_le_one
  refine ⟨?_, hmom, fun α hα hα1 => ?_⟩
  · -- The true density vanishes with probability zero.
    have hZ : MeasurableSet {p : 𝒰 × 𝒱 | g ϑ p.1 p.2 = 0} :=
      measurableSet_eq_fun (hM.measg ϑ) measurable_const
    have hind : Measurable ({p : 𝒰 × 𝒱 | g ϑ p.1 p.2 = 0}.indicator fun _ => (1 : ℝ≥0∞)) :=
      measurable_const.indicator hZ
    have h0 := transfer hM hc hind
    have hzero : ∀ u v, ENNReal.ofReal (g ϑ u v) *
        {p : 𝒰 × 𝒱 | g ϑ p.1 p.2 = 0}.indicator (fun _ => (1 : ℝ≥0∞)) (u, v) = 0 := fun u v => by
      by_cases h : g ϑ u v = 0
      · simp [h]
      · simp [Set.indicator, h]
    simp only [hzero, lintegral_zero] at h0
    have hset : {ω | g ϑ (U ω) (V ω) = 0} =
        (fun ω => (U ω, V ω)) ⁻¹' {p : 𝒰 × 𝒱 | g ϑ p.1 p.2 = 0} := rfl
    rw [hset, ← lintegral_indicator_one ((hM.measU.prodMk hM.measV) hZ)]
    rw [← h0]
    rfl
  · -- Coverage by Markov's inequality.
    have hT : Measurable (TplusE U V g sel ϑ) := hTm.comp (hM.measU.prodMk hM.measV)
    have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hT.aemeasurable (ENNReal.ofReal (1 / α))
    have hsub : {ω | ENNReal.ofReal (1 / α) < TplusE U V g sel ϑ ω} ⊆
        {ω | ENNReal.ofReal (1 / α) ≤ TplusE U V g sel ϑ ω} := fun _ h => by
      simp only [mem_ofPred_eq] at h ⊢; exact h.le
    have hle : ENNReal.ofReal (1 / α) * P {ω | ENNReal.ofReal (1 / α) < TplusE U V g sel ϑ ω} ≤ 1 :=
      (mul_le_mul_right (measure_mono hsub) _).trans (hmk.trans hmom)
    have hinv : (ENNReal.ofReal (1 / α))⁻¹ = ENNReal.ofReal α := by
      rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
    rw [← hinv, ENNReal.le_inv_iff_mul_le, mul_comm]
    exact hle

theorem proof : Standalone.SplitLikelihoodSupport.statement := ax57_holds

end Novel.SplitLikelihoodSupport
