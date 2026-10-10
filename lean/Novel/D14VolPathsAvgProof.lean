import Standalone.D14VolPaths
import Novel.D14SupportRobustnessProof

/-!
# Claim 027 (D14): proof of part 2 for an abstract latent mixture

Proves `Standalone.D14VolPaths.averaging` (`averaging_holds`).

* **One component** at `(u, z)`.
  - Markov under the reference (claim 025's `markov_one`, from the reference moment) and the
    eventwise budget (claim 023's `ofReal_le_add`) give `H{E > 1/α} ≤ α + ε`.
  - The bounded-function comparison (claim 023's `lintegral_le_tv`) gives
    `∫ min(E, c) dH ≤ 1 + c ε`.
* **Averaging.** The actual conditional law is the latent mixture (`Measure.bind_apply`,
  `Measure.lintegral_bind`), so integrating over `ν(u, ·)` replaces `ε` by `ε̄(u)`. Disintegration
  then integrates over the actual training law.
* **Zero budgets.** Each component equals its reference, so the raw reference moment applies.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14VolPathsAvg

open Standalone.D14VolPaths

section Avg

variable {Ω 𝒰 𝒱 𝒵 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
  [MeasurableSpace 𝒵] {ν : Kernel 𝒰 𝒵} [IsMarkovKernel ν] {H G : Kernel (𝒰 × 𝒵) 𝒱}
  [IsMarkovKernel H] [IsMarkovKernel G] {ε : 𝒰 × 𝒵 → ℝ}

omit [MeasurableSpace Ω] [IsMarkovKernel H] [IsMarkovKernel G] in
theorem eps_int (hε : Measurable ε) (h01 : ∀ p, 0 ≤ ε p ∧ ε p ≤ 1) (u : 𝒰) :
    Integrable (fun z => ε (u, z)) (ν u) :=
  Integrable.of_bound (C := 1) (hε.comp measurable_prodMk_left).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h01 _).1]; exact (h01 _).2)

omit [MeasurableSpace Ω] [IsMarkovKernel H] [IsMarkovKernel G] in
theorem lint_eps (hε : Measurable ε) (h01 : ∀ p, 0 ≤ ε p ∧ ε p ≤ 1) (u : 𝒰) :
    ∫⁻ z, ENNReal.ofReal (ε (u, z)) ∂(ν u) = ENNReal.ofReal (∫ z, ε (u, z) ∂(ν u)) :=
  (ofReal_integral_eq_lintegral_ofReal (eps_int hε h01 u)
    (Eventually.of_forall fun _ => (h01 _).1)).symm

omit [MeasurableSpace Ω] [IsMarkovKernel H] [IsMarkovKernel G] in
theorem epsbar_meas (hε : Measurable ε) (h01 : ∀ p, 0 ≤ ε p ∧ ε p ≤ 1) :
    Measurable fun u => ∫ z, ε (u, z) ∂(ν u) := by
  have : (fun u => ∫ z, ε (u, z) ∂(ν u)) =
      fun u => (∫⁻ z, ENNReal.ofReal (ε (u, z)) ∂(ν u)).toReal := funext fun u => by
    rw [lint_eps hε h01 u, ENNReal.toReal_ofReal (integral_nonneg fun z => (h01 _).1)]
  rw [this]
  exact (Measurable.lintegral_kernel_prod_right'
    (ENNReal.measurable_ofReal.comp hε)).ennreal_toReal

omit [MeasurableSpace Ω] [IsMarkovKernel H] [IsMarkovKernel G] in
theorem epsbar_bounds (hε : Measurable ε) (h01 : ∀ p, 0 ≤ ε p ∧ ε p ≤ 1) (u : 𝒰) :
    0 ≤ ∫ z, ε (u, z) ∂(ν u) ∧ ∫ z, ε (u, z) ∂(ν u) ≤ 1 := by
  refine ⟨integral_nonneg fun z => (h01 _).1, ?_⟩
  calc ∫ z, ε (u, z) ∂(ν u) ≤ ∫ _z, (1 : ℝ) ∂(ν u) :=
        integral_mono (eps_int hε h01 u) (integrable_const _) fun z => (h01 _).2
    _ = 1 := by simp

end Avg

open Standalone.D12CatalogueFDR in
theorem averaging_holds : Standalone.D14VolPaths.averaging := by
  refine ⟨?_, Novel.D14SupportRobustness.general_holds.2⟩
  intro Ω 𝒰 𝒱 𝒵 _ _ _ _ _ _ P _ U V ν _ H G _ _ E ε hU hV hE hE0 hε h01 hmom htv hmix εbar
  have hHz : ∀ u, Measurable fun z => H (u, z) := fun u => H.measurable.comp measurable_prodMk_left
  have hEu : ∀ u, Measurable (E u) := fun u => hE.comp measurable_prodMk_left
  have hεbar_m : Measurable εbar := epsbar_meas hε h01
  have hεbar := epsbar_bounds (ν := ν) hε h01
  have hεbar_int : Integrable (fun ω => εbar (U ω)) P :=
    Integrable.of_bound (C := 1) (hεbar_m.comp hU).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hεbar _).1]; exact (hεbar _).2)
  -- One component: the event bound.
  have hcomp_ev : ∀ α : ℝ, 0 < α → ∀ u z, H (u, z) {v | 1 / α < E u v} ≤
      ENNReal.ofReal α + ENNReal.ofReal (ε (u, z)) := fun α hα u z => by
    have hS : MeasurableSet {v | 1 / α < E u v} := measurableSet_lt measurable_const (hEu u)
    have h1 := Novel.D14Misspecification.ofReal_le_add (h01 (u, z)).1
      (by linarith [(abs_le.1 (htv u z _ hS)).2] :
        (H (u, z)).real {v | 1 / α < E u v} ≤ (G (u, z)).real {v | 1 / α < E u v} + ε (u, z))
    exact h1.trans (add_le_add (Novel.D14SupportRobustness.markov_one (hEu u) (hmom u z) hα) le_rfl)
  -- (5), conditional.
  have hcond5 : ∀ α : ℝ, 0 < α → ∀ᵐ u ∂(P.map U),
      condDistrib V U P u {v | 1 / α < E u v} ≤ ENNReal.ofReal (α + εbar u) := fun α hα => by
    filter_upwards [hmix] with u hu
    have hS : MeasurableSet {v | 1 / α < E u v} := measurableSet_lt measurable_const (hEu u)
    rw [hu, Measure.bind_apply hS (hHz u).aemeasurable]
    calc ∫⁻ z, H (u, z) {v | 1 / α < E u v} ∂(ν u)
        ≤ ∫⁻ z, (ENNReal.ofReal α + ENNReal.ofReal (ε (u, z))) ∂(ν u) :=
          lintegral_mono fun z => hcomp_ev α hα u z
      _ = ENNReal.ofReal (α + εbar u) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lint_eps hε h01 u, ← ENNReal.ofReal_add hα.le (hεbar u).1]
  -- (5), unconditional.
  have huncond5 : ∀ α : ℝ, 0 < α →
      P.real {ω | 1 / α < E (U ω) (V ω)} ≤ α + ∫ ω, εbar (U ω) ∂P := fun α hα => by
    set S : Set (𝒰 × 𝒱) := {x | 1 / α < E x.1 x.2}
    have hS : MeasurableSet S := measurableSet_lt measurable_const hE
    have hmeas : MeasurableSet {ω | 1 / α < E (U ω) (V ω)} :=
      measurableSet_lt measurable_const (hE.comp (hU.prodMk hV))
    have hP : P {ω | 1 / α < E (U ω) (V ω)} =
        ∫⁻ u, condDistrib V U P u (Prod.mk u ⁻¹' S) ∂(P.map U) := by
      have h := Novel.D14SupportRobustness.disint (P := P) hU hV
        (measurable_const.indicator hS : Measurable (S.indicator 1))
      rw [← lintegral_indicator_one hmeas]
      refine (Eq.trans (by rfl) h).trans (lintegral_congr fun u => ?_)
      show ∫⁻ v, (Prod.mk u ⁻¹' S).indicator 1 v ∂_ = _
      rw [lintegral_indicator_one (measurable_prodMk_left hS)]
    have hlin : ∫⁻ u, ENNReal.ofReal (α + εbar u) ∂(P.map U) =
        ENNReal.ofReal (α + ∫ ω, εbar (U ω) ∂P) := by
      have := (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 ‹_›
      have hint : Integrable εbar (P.map U) := Integrable.of_bound (C := 1)
        hεbar_m.aestronglyMeasurable (Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hεbar _).1]; exact (hεbar _).2)
      rw [← ofReal_integral_eq_lintegral_ofReal (f := fun u => α + εbar u)
        ((integrable_const α).add hint)
        (Eventually.of_forall fun u => add_nonneg hα.le (hεbar u).1),
        integral_add (integrable_const α) hint, integral_const,
        integral_map hU.aemeasurable hεbar_m.aestronglyMeasurable]
      simp
    rw [measureReal_def, hP]
    refine ENNReal.toReal_le_of_le_ofReal
      (add_nonneg hα.le (integral_nonneg fun ω => (hεbar _).1)) ?_
    rw [← hlin]
    exact lintegral_mono_ae (hcond5 α hα)
  -- (6), conditional.
  have hcond6 : ∀ (c : ℝ) (eb : 𝒰 → ℝ), 0 < c → (∀ u, εbar u ≤ eb u) →
      ∀ᵐ u ∂(P.map U), ∫⁻ v, ENNReal.ofReal (min (E u v) c / (1 + c * eb u))
        ∂(condDistrib V U P u) ≤ 1 := fun c eb hc heb => by
    filter_upwards [hmix] with u hu
    have hden : 0 < 1 + c * eb u := by nlinarith [(hεbar u).1, heb u]
    have hY : Measurable fun v => min (E u v) c := (hEu u).min measurable_const
    have hfm : Measurable fun v => ENNReal.ofReal (min (E u v) c / (1 + c * eb u)) :=
      ENNReal.measurable_ofReal.comp (hY.div_const _)
    rw [hu, Measure.lintegral_bind (hHz u).aemeasurable hfm.aemeasurable]
    have hsplit : ∀ v, ENNReal.ofReal (min (E u v) c / (1 + c * eb u)) =
        ENNReal.ofReal (1 / (1 + c * eb u)) * ENNReal.ofReal (min (E u v) c) := fun v => by
      rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    have hinner : ∀ z, ∫⁻ v, ENNReal.ofReal (min (E u v) c / (1 + c * eb u)) ∂(H (u, z)) ≤
        ENNReal.ofReal (1 / (1 + c * eb u)) * (1 + ENNReal.ofReal (c * ε (u, z))) := fun z => by
      simp_rw [hsplit]
      rw [lintegral_const_mul (ENNReal.ofReal (1 / (1 + c * eb u)))
        (f := fun v => ENNReal.ofReal (min (E u v) c)) (ENNReal.measurable_ofReal.comp hY)]
      refine mul_le_mul_right ?_ _
      have htv' := Novel.D14Misspecification.lintegral_le_tv hY
        (fun v => le_min (hE0 u v) hc.le) (fun v => min_le_right _ _) hc.le (h01 _).1 (htv u z)
      have hG : ∫⁻ v, ENNReal.ofReal (min (E u v) c) ∂(G (u, z)) ≤ 1 :=
        (lintegral_mono fun v => ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (hmom u z)
      exact htv'.trans (add_le_add hG le_rfl)
    calc ∫⁻ z, ∫⁻ v, ENNReal.ofReal (min (E u v) c / (1 + c * eb u)) ∂(H (u, z)) ∂(ν u)
        ≤ ∫⁻ z, ENNReal.ofReal (1 / (1 + c * eb u)) * (1 + ENNReal.ofReal (c * ε (u, z))) ∂(ν u) :=
          lintegral_mono hinner
      _ = ENNReal.ofReal (1 / (1 + c * eb u)) * (1 + ENNReal.ofReal (c * εbar u)) := by
          rw [lintegral_const_mul (ENNReal.ofReal (1 / (1 + c * eb u)))
            (f := fun z => 1 + ENNReal.ofReal (c * ε (u, z)))
            (measurable_const.add (ENNReal.measurable_ofReal.comp
              (measurable_const.mul (hε.comp measurable_prodMk_left)))),
            lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
          congr 2
          · simp_rw [ENNReal.ofReal_mul hc.le]
            rw [lintegral_const_mul (ENNReal.ofReal c) (f := fun z => ENNReal.ofReal (ε (u, z)))
              (ENNReal.measurable_ofReal.comp (hε.comp measurable_prodMk_left)),
              lint_eps hε h01 u]
      _ ≤ ENNReal.ofReal (1 / (1 + c * eb u)) * ENNReal.ofReal (1 + c * eb u) := by
          refine mul_le_mul_right ?_ _
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
            (mul_nonneg hc.le (hεbar u).1)]
          exact ENNReal.ofReal_le_ofReal (by nlinarith [heb u])
      _ = 1 := by
          rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hden.ne',
            ENNReal.ofReal_one]
  refine ⟨hcond5, fun α hα => le_min measureReal_le_one (huncond5 α hα),
    fun α e he0 he heα => ?_, fun c eb hc hebm heb => ⟨hcond6 c eb hc heb, ?_⟩, fun h0 => ?_⟩
  · -- The shifted threshold.
    have hb := huncond5 (α - e) (by linarith)
    have hint : ∫ ω, εbar (U ω) ∂P ≤ e := by
      calc ∫ ω, εbar (U ω) ∂P ≤ ∫ _ω, e ∂P := integral_mono hεbar_int (integrable_const e)
            fun ω => he _
        _ = e := by simp
    linarith
  · -- (6), unconditional.
    have hF : Measurable fun x : 𝒰 × 𝒱 =>
        ENNReal.ofReal (min (E x.1 x.2) c / (1 + c * eb x.1)) :=
      ENNReal.measurable_ofReal.comp ((hE.min measurable_const).div
        (measurable_const.add (measurable_const.mul (hebm.comp measurable_fst))))
    rw [show (∫⁻ ω, ENNReal.ofReal (min (E (U ω) (V ω)) c / (1 + c * eb (U ω))) ∂P) =
        ∫⁻ ω, (fun x : 𝒰 × 𝒱 => ENNReal.ofReal (min (E x.1 x.2) c / (1 + c * eb x.1)))
          (U ω, V ω) ∂P from rfl, Novel.D14SupportRobustness.disint hU hV hF]
    have := (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 ‹_›
    calc ∫⁻ u, ∫⁻ v, ENNReal.ofReal (min (E u v) c / (1 + c * eb u)) ∂(condDistrib V U P u)
          ∂(P.map U) ≤ ∫⁻ _u, 1 ∂(P.map U) := lintegral_mono_ae (hcond6 c eb hc heb)
      _ = 1 := by simp
  · -- Zero budgets.
    have heq : ∀ u z, H (u, z) = G (u, z) := fun u z => by
      ext A hA
      have h := htv u z A hA
      rw [h0, abs_nonpos_iff, sub_eq_zero, measureReal_def, measureReal_def] at h
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h
    have hcondr : ∀ᵐ u ∂(P.map U), ∫⁻ v, ENNReal.ofReal (E u v) ∂(condDistrib V U P u) ≤ 1 := by
      filter_upwards [hmix] with u hu
      rw [hu, Measure.lintegral_bind (f := fun v => ENNReal.ofReal (E u v)) (hHz u).aemeasurable
        (ENNReal.measurable_ofReal.comp (hEu u)).aemeasurable]
      calc ∫⁻ z, ∫⁻ v, ENNReal.ofReal (E u v) ∂(H (u, z)) ∂(ν u) ≤ ∫⁻ _z, 1 ∂(ν u) :=
            lintegral_mono fun z => by rw [heq u z]; exact hmom u z
        _ = 1 := by simp
    refine ⟨hcondr, ?_⟩
    have hF : Measurable fun x : 𝒰 × 𝒱 => ENNReal.ofReal (E x.1 x.2) :=
      ENNReal.measurable_ofReal.comp hE
    rw [show (∫⁻ ω, ENNReal.ofReal (E (U ω) (V ω)) ∂P) =
        ∫⁻ ω, (fun x : 𝒰 × 𝒱 => ENNReal.ofReal (E x.1 x.2)) (U ω, V ω) ∂P from rfl,
      Novel.D14SupportRobustness.disint hU hV hF]
    have := (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 ‹_›
    calc ∫⁻ u, ∫⁻ v, ENNReal.ofReal (E u v) ∂(condDistrib V U P u) ∂(P.map U)
        ≤ ∫⁻ _u, 1 ∂(P.map U) := lintegral_mono_ae hcondr
      _ = 1 := by simp

end Novel.D14VolPathsAvg
