import Standalone.D14CellSubdivision
import Novel.D14CellSubdivisionBoundProof
import Novel.D14RoundedStartProof

/-!
# Claim 030 (D14): proof

Proves `Standalone.D14CellSubdivision.statement` (`statement_holds`). The interval maximum is
`Novel/D14CellIntervalProof.lean`; the subcell bounds, level zero and monotonicity are
`Novel/D14CellSubdivisionBoundProof.lean`.
* **(5).** Claim 028's mixture (`Novel.D14RoundedStart.mix`): the conditional law of the labels given
  `U` is the mixture of the path probabilities from the latent endpoint `x` over its conditional law.
  That law lives on the last training cell. At each such `x` the log state lies in some level-`ℓ`
  subcell `a`, where the path probability is at most `U_a ≤ B^ℓ` (`dom`). No posterior is
  approximated, and the bound holds for every level and label array on the same set of training
  values.
* **Validity at any level choice.** For each `v` the denominator at level `L(u, v)` dominates the
  conditional mass of `v`, so `Σ_v (q/D) P(v | u) ≤ Σ_v q = 1` (AX-58's domination, with counting
  measure). Disintegration, Markov and monotonicity give the rest.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14CellSubdivision

open Standalone.RoundedCells Standalone.D14Misspecification Standalone.D14RoundedStart
  Standalone.D14CellSubdivision Novel.D14RoundedStartCells Novel.D14CellSubdivisionBound
  Novel.D14RoundedStart

theorem lab_of_Qh {h x : ℝ} (hh : 0 < h) {z : ℤ} (hq : Qh h x = rep h z) : lab h x = z := by
  have h1 : h * (lab h x : ℝ) = h * z := Real.exp_injective hq
  exact_mod_cast mul_left_cancel₀ hh.ne' h1

theorem validity_holds : validity := by
  intro Ω 𝒰 _ _ P _ n Δ h b κ U X R z Γ hΓ q Lv hΔ hh hbκ hΓκ hU hX hR hz hq hq0 hq1 hL hXc hRc
    V E
  have hκ : 0 < κ := hΓκ _ hbκ
  have hF := labF_meas (n := n) h
  have hV : Measurable V := hF.comp (hX.prodMk hR)
  have hmix := mix (F := fun p : ℝ × (Fin n → ℝ) => labF h p.1 p.2) hU hX hR hF hRc
  have hW : Measurable fun ω => (U ω, X ω) := hU.prodMk hX
  set C : Set (𝒰 × ℝ) := {p | 0 < p.2 ∧ Qh h p.2 = rep h (z p.1)}
  have hC : MeasurableSet C := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_eq_fun ((Novel.RoundedCells.Qh_meas h).comp measurable_snd)
      ((measurable_from_top (f := rep h)).comp (hz.comp measurable_fst)))
  have hcell : ∀ᵐ u ∂(P.map U), ∀ᵐ x ∂(condDistrib X U P u), (u, x) ∈ C := by
    have h1 : ∀ᵐ w ∂(P.map fun ω => (U ω, X ω)), w ∈ C := (ae_map_iff hW.aemeasurable hC).2 hXc
    rw [← compProd_map_condDistrib hU.aemeasurable hX.aemeasurable] at h1
    exact Measure.ae_ae_of_ae_compProd h1
  have hD := fun ℓ z0 v => Dl_bounds (n := n) hΓ hΓκ hh hΔ ℓ z0 v
  have hBD : ∀ ℓ z0 v, Bθ h b κ ℓ n Δ z0 v ≤ Dl Γ hΓ h ℓ n Δ z0 v := fun ℓ z0 v =>
    Finset.le_sup' (f := fun θ : ℝ × ℝ => Bθ h θ.1 θ.2 ℓ n Δ z0 v) hbκ
  -- (5), in `[0, ∞]`.
  have h5 : ∀ᵐ u ∂(P.map U), ∀ (v : Fin n → ℤ) (ℓ : ℕ),
      condDistrib V U P u {v} ≤ ENNReal.ofReal (Bθ h b κ ℓ n Δ (z u) v) := by
    filter_upwards [hmix, hcell] with u hu hcu v ℓ
    rw [hu, Kernel.comp_apply' _ _ _ (measurableSet_singleton v)]
    have hx : ∀ᵐ x ∂(condDistrib X U P u), (Lk hF (lawR Δ b κ)) x {v} ≤
        ENNReal.ofReal (Bθ h b κ ℓ n Δ (z u) v) := by
      filter_upwards [hcu] with x hx
      obtain ⟨hx0, hqx⟩ := hx
      have hmem : Real.log x ∈ Icell h (z u) := by
        rw [← lab_exp_iff hh, Real.exp_log hx0]; exact lab_of_Qh hh hqx
      obtain ⟨ha, hsub⟩ := floor_sub (ℓ := ℓ) hh hmem
      have hd := dom (b := b) hh hκ n Δ ℓ (z u) v _ hΔ ha _ hsub
      rw [Real.exp_log hx0] at hd
      exact hd.trans (ENNReal.ofReal_le_ofReal (Ub_le_Bθ h b κ Δ (z u) v ha))
    calc ∫⁻ x, (Lk hF (lawR Δ b κ)) x {v} ∂(condDistrib X U P u)
        ≤ ∫⁻ _, ENNReal.ofReal (Bθ h b κ ℓ n Δ (z u) v) ∂(condDistrib X U P u) := lintegral_mono_ae hx
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  -- The score.
  have hEv : ∀ v, Measurable fun u => E u v := fun v => by
    have h1 : Measurable fun u => Dl Γ hΓ h (Lv u v) n Δ (z u) v :=
      Measurable.comp (g := fun p : ℕ × ℤ => Dl Γ hΓ h p.1 n Δ p.2 v)
        (f := fun u => (Lv u v, z u)) (measurable_of_countable _) ((hL v).prodMk hz)
    exact Measurable.div (f := fun u => q u v) (g := fun u => Dl Γ hΓ h (Lv u v) n Δ (z u) v)
      (hq v) h1
  have hEm : Measurable (Function.uncurry E) := measurable_from_prod_countable_left hEv
  have hE0 : ∀ u v, 0 ≤ E u v := fun u v => div_nonneg (hq0 u v) (hD _ _ v).1.le
  have hcm : ∀ᵐ u ∂(P.map U), ∫⁻ v, ENNReal.ofReal (E u v) ∂(condDistrib V U P u) ≤ 1 := by
    filter_upwards [h5] with u hu
    rw [lintegral_countable']
    calc ∑' v, ENNReal.ofReal (E u v) * condDistrib V U P u {v}
        ≤ ∑' v, ENNReal.ofReal (q u v) := ENNReal.tsum_le_tsum fun v => by
          have hDp := (hD (Lv u v) (z u) v).1
          calc ENNReal.ofReal (E u v) * condDistrib V U P u {v}
              ≤ ENNReal.ofReal (E u v) * ENNReal.ofReal (Dl Γ hΓ h (Lv u v) n Δ (z u) v) :=
                mul_le_mul_right ((hu v (Lv u v)).trans
                  (ENNReal.ofReal_le_ofReal (hBD _ _ v))) _
            _ = ENNReal.ofReal (q u v) := by
                rw [← ENNReal.ofReal_mul (hE0 u v)]
                congr 1
                exact div_mul_cancel₀ _ hDp.ne'
      _ = 1 := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (hq0 u) (hq1 u).summable, (hq1 u).tsum_eq,
            ENNReal.ofReal_one]
  have hum : ∫⁻ ω, ENNReal.ofReal (E (U ω) (V ω)) ∂P ≤ 1 := by
    have := Novel.D14SupportRobustness.disint (P := P) hU hV
      (F := fun p => ENNReal.ofReal (Function.uncurry E p)) (ENNReal.measurable_ofReal.comp hEm)
    refine (le_of_eq this).trans ?_
    have : IsProbabilityMeasure (P.map U) := (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
    calc ∫⁻ u, ∫⁻ v, ENNReal.ofReal (Function.uncurry E (u, v)) ∂(condDistrib V U P u) ∂(P.map U)
        ≤ ∫⁻ _, 1 ∂(P.map U) := lintegral_mono_ae hcm
      _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
  have hEω : Measurable fun ω => E (U ω) (V ω) := hEm.comp (hU.prodMk hV)
  refine ⟨?_, hD, hEm, hE0, hcm, hum, fun α hα => ?_, fun α hα => ?_, fun F hFm hF' => ?_⟩
  · filter_upwards [h5] with u hu v ℓ
    exact ⟨ENNReal.toReal_le_of_le_ofReal (Bθ_bounds hh hκ hΔ ℓ (z u) v).1.le (hu v ℓ), hBD ℓ _ v⟩
  · filter_upwards [hcm] with u hu
    exact Novel.D14SupportRobustness.markov_one (measurable_of_countable _) hu hα
  · exact ENNReal.toReal_le_of_le_ofReal hα.le (Novel.D14SupportRobustness.markov_one hEω hum hα)
  · exact (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hF' ω).2).trans hum

theorem statement_holds : Standalone.D14CellSubdivision.statement :=
  ⟨Novel.D14CellInterval.interval_holds, bounds_holds, level0_holds, monotone_holds, validity_holds,
    Novel.D14JumpRobustness.panel_holds⟩

end Novel.D14CellSubdivision
