import Novel.D30VariationProfileProfile
import Novel.SplitLikelihoodDominatedProof
import Novel.D18SignNoiseValid

/-!
# Claim 072, part 3: the fixed-horizon test (9)

Under (1) for `z ∈ Z_V`, or a mixture of such laws, the observation law has a density `g ≤ P_V`.
AX-58's proved pointwise bound (`mul_Edrift_le`: `g · E^drift(q, D) ≤ q` whenever `g ≤ D`) gives
`∫ E_V dP = ∫ g E_V ≤ ∫ q = 1`; Markov gives the size. Any score below `E_V` inherits both, which
covers the certified score and zero on uncertified records.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

namespace Novel.D30VariationProfile

open Standalone.D30VariationProfile Standalone.SplitLikelihoodDominated

variable {m : ℕ} {Δ : Fin (m + 1) → ℝ}

theorem continuous_ell_prod (Δ : Fin (m + 1) → ℝ) :
    Continuous fun p : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) => ell Δ p.1 p.2 := by
  unfold ell cR fj Aco; fun_prop

/-- `g · E^drift(q, D) ≤ q` for an extended-real `g ≤ D`. -/
theorem mul_Edrift_le' {a : ℝ} {g d : ℝ≥0∞} (hgd : g ≤ d) : g * Edrift a d ≤ ENNReal.ofReal a := by
  classical
  by_cases hg : g = ⊤
  · have : d = ⊤ := top_le_iff.1 (hg ▸ hgd)
    simp [Edrift, this]
  · rw [← ENNReal.ofReal_toReal hg] at hgd ⊢
    exact Novel.SplitLikelihoodDominated.mul_Edrift_le hgd

/-- The observation law has a density below `P_V`. -/
theorem density_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (hΔ : ∀ j, 0 < Δ j) {V : ℝ}
    {R : Ω → Fin (m + 1) → ℝ} (hnull : NullLaw P Δ V R) :
    ∃ g : (Fin (m + 1) → ℝ) → ℝ≥0∞, Measurable g ∧ (∀ r, g r ≤ PV Δ V r) ∧
      P.map R = volume.withDensity g := by
  rcases hnull with ⟨z, hz, hlaw⟩ | ⟨ν, hν, hνZ, hmap⟩
  · refine ⟨fun r => ENNReal.ofReal (Real.exp (ell Δ r z)),
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (continuous_ell_R Δ z).measurable),
      fun r => le_PV hz r, ?_⟩
    rw [hlaw.map_eq, nullLaw_eq hΔ]
  · refine ⟨fun r => ∫⁻ z, ENNReal.ofReal (Real.exp (ell Δ r z)) ∂ν, ?_, fun r => ?_, hmap⟩
    · exact Measurable.lintegral_prod_right' (ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp (continuous_ell_prod Δ).measurable))
    · have hae : ∀ᵐ z ∂ν, z ∈ ZV V := ae_iff.2 (by rw [← hνZ]; rfl)
      calc ∫⁻ z, ENNReal.ofReal (Real.exp (ell Δ r z)) ∂ν ≤ ∫⁻ _z, PV Δ V r ∂ν :=
            lintegral_mono_ae (hae.mono fun z hz => le_PV hz r)
        _ = PV Δ V r := by simp

theorem test_holds : Standalone.D30VariationProfile.test := by
  intro m Δ V hΔ hV Ω _ P _ R q hR hq hq0 hq1 hnull E' hE'
  obtain ⟨g, hg, hgP, hmap⟩ := density_le hΔ hnull
  have hEm : Measurable fun r => Edrift (q r) (PV Δ V r) :=
    Novel.SplitLikelihoodDominated.Edrift_meas.comp (hq.prodMk (measurable_PV V))
  have hmean : ∫⁻ ω, Edrift (q (R ω)) (PV Δ V (R ω)) ∂P ≤ 1 := by
    rw [← lintegral_map hEm hR, hmap, lintegral_withDensity_eq_lintegral_mul _ hg hEm, ← hq1]
    exact lintegral_mono fun r => mul_Edrift_le' (hgP r)
  refine ⟨(lintegral_mono hE').trans hmean, fun α hα _ => ?_⟩
  refine le_trans (measure_mono fun ω hω => ?_)
    (Novel.D18SignNoise.size_ge (hEm.comp hR) hmean hα)
  exact (show ENNReal.ofReal (1 / α) < E' ω from hω).le.trans (hE' ω)

end Novel.D30VariationProfile
