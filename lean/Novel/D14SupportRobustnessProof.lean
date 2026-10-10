import Standalone.D14SupportRobustness
import Novel.SplitLikelihoodSupportProof
import Novel.D14MisspecificationProof
import Novel.D13CEVCatalogueProof

/-!
# Claim 025 (D14): proof

Proves `Standalone.D14SupportRobustness.statement` (`statement_holds`): `general_holds` and
`cev_holds`.

* **The score.** `E0` is a finite infimum of measurable `R₊` values (`Rplus_meas`,
  `measurable_selected`), and (1) is a piecewise combination on `J ×ˢ W`.
* **(3)** (`ref_moment`). At any `u`, `Gemb ϑ u` integrates `v ↦ Ebar(u, ι v)` against
  `g_ϑ(du u, ·) μ`, and `dv ∘ ι = id`. At a null `ϑ`, `E0 ≤ R₊(q, g_ϑ)` and
  `g_ϑ · R₊(q, g_ϑ) ≤ q` (`mul_Rplus_le`, AX-57's support-restricted step). So the integral is at
  most `∫ q dμ = 1`; this is not positive-density cancellation.
* **(4)** (`size`). At valid `u`, Markov under `Gemb` and the TV envelope give
  `H u {Ebar > 1/α} ≤ α + ε u`. At invalid `u` the event is empty. Disintegration
  (`compProd_map_condDistrib`) integrates `1_J (α + ε)` over the actual training law.
* **(6)** (`clipped`). At valid `u`, claim 023's layer-cake comparison (`lintegral_le_tv`) gives
  `∫ min(Ebar, c) dH ≤ 1 + c ε u`. Division by the training-measurable denominator gives a value at
  most `1_J(u)`, and the mask and lower score only decrease it.
* **Claim 054's objects** (`cev_holds`).
  - `Design` comes from claim 054's `supportModel`: chain normalization from the cited AX-55/56
    one-step facts, kernel measurability, and measurable selector fibres.
  - Finiteness of the composite score on every array is `CEVSupport.score` with claim 054's
    `support`.
  - The band rule: a null in the confidence set has `b₁ ≤ r^{2−2p} b₁`, so the band excludes every
    null, and the attained minimum (`Ecomp_attained`) exceeds `1/α`.
  - Absorption: from a zero endpoint every chain is the same trapped value (`chain_from_zero`). From
    a positive endpoint with a zero coordinate, a `p ≥ 1` selection has numerator zero
    (`first_zero`), and a `p < 1` selection is itself null. Either way `E ≤ R₊(q, q) ≤ 1` or
    `E = 0`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14SupportRobustness

open Standalone.SplitLikelihoodSupport Standalone.D12CatalogueFDR Standalone.D14SupportRobustness
  Novel.SplitLikelihoodSupport

/-- Markov's inequality for a nonnegative real function with integral at most one. -/
theorem markov_one {X : Type*} [MeasurableSpace X] {G : Measure X} {f : X → ℝ} (hf : Measurable f)
    (h1 : ∫⁻ x, ENNReal.ofReal (f x) ∂G ≤ 1) {α : ℝ} (hα : 0 < α) :
    G {x | 1 / α < f x} ≤ ENNReal.ofReal α := by
  have hmk := mul_meas_ge_le_lintegral₀ (μ := G) (ENNReal.measurable_ofReal.comp hf).aemeasurable
    (ENNReal.ofReal (1 / α))
  have hsub : {x | 1 / α < f x} ⊆ {x | ENNReal.ofReal (1 / α) ≤ ENNReal.ofReal (f x)} :=
    fun x hx => ENNReal.ofReal_le_ofReal (le_of_lt hx)
  have hle : ENNReal.ofReal (1 / α) * G {x | 1 / α < f x} ≤ 1 :=
    (mul_le_mul_right (measure_mono hsub) _).trans (hmk.trans h1)
  have hinv : (ENNReal.ofReal (1 / α))⁻¹ = ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
  rw [← hinv, ENNReal.le_inv_iff_mul_le, mul_comm]
  exact hle

theorem disint {Ω 𝒰 𝒱 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒱] [Nonempty 𝒱] {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → 𝒰}
    {V : Ω → 𝒱} (hU : Measurable U) (hV : Measurable V) {F : 𝒰 × 𝒱 → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (U ω, V ω) ∂P = ∫⁻ u, ∫⁻ v, F (u, v) ∂(condDistrib V U P u) ∂(P.map U) := by
  rw [← lintegral_map hF (hU.prodMk hV), ← compProd_map_condDistrib hU.aemeasurable
    hV.aemeasurable, Measure.lintegral_compProd hF]

theorem lin_bound {Ω 𝒰 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] {P : Measure Ω}
    [IsProbabilityMeasure P] {U : Ω → 𝒰} {J : Set 𝒰} {ε : 𝒰 → ℝ} (hU : Measurable U) (hJ : MeasurableSet J) (hε : Measurable ε)
    (h0 : ∀ u, 0 ≤ ε u) (h1 : ∀ u, ε u ≤ 1) {α : ℝ} (hα : 0 < α) :
    ∫⁻ u, ENNReal.ofReal (J.indicator (fun u => α + ε u) u) ∂(P.map U) =
      ENNReal.ofReal (α * P.real (U ⁻¹' J) + ∫ ω, J.indicator ε (U ω) ∂P) := by
  have := (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 ‹_›
  have hεi : Integrable ε (P.map U) := Integrable.of_bound (C := 1) hε.aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 u)]; exact h1 u)
  have hsplit : (fun u => J.indicator (fun u => α + ε u) u) =
      fun u => J.indicator (fun _ => α) u + J.indicator ε u := funext fun u => by
    by_cases h : u ∈ J <;> simp [h]
  have hi1 : Integrable (fun u => J.indicator (fun _ => α) u) (P.map U) :=
    (integrable_const α).indicator hJ
  have hi2 : Integrable (fun u => J.indicator ε u) (P.map U) := hεi.indicator hJ
  have hint : Integrable (fun u => J.indicator (fun u => α + ε u) u) (P.map U) :=
    ((integrable_const α).add hεi).indicator hJ
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun u => indicator_nonneg (fun u _ => add_nonneg hα.le (h0 u)) u),
    hsplit, integral_add hi1 hi2, integral_indicator_const α hJ, smul_eq_mul,
    integral_map hU.aemeasurable (hεi.indicator hJ).aestronglyMeasurable,
    map_measureReal_apply hU hJ, mul_comm]

section Name

variable {Ω 𝒰 𝒱 𝒰₀ 𝒱₀ Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
  [MeasurableSpace 𝒰₀] [MeasurableSpace 𝒱₀] [Fintype Θ]
  {μ : Measure 𝒱₀} {g : Θ → 𝒰₀ → 𝒱₀ → ℝ} {sel : 𝒰₀ → Θ} {pw : Θ → ℝ} {J : Set 𝒰}
  {du : 𝒰 → 𝒰₀} {W : Set 𝒱} {dv : 𝒱 → 𝒱₀} {ι : 𝒱₀ → 𝒱}

theorem measurable_E0 (hD : Design μ g sel pw J du W dv ι) :
    Measurable fun p : 𝒰₀ × 𝒱₀ => E0 pw g sel p.1 p.2 := by
  have hsel := Novel.SplitLikelihood.measurable_selected hD.measg hD.measSel
  unfold E0
  refine Measurable.iInf fun ϑ => Measurable.iInf fun _ => ?_
  exact Rplus_meas.comp (hsel.prodMk (hD.measg ϑ))

theorem measurable_Ebar (hD : Design μ g sel pw J du W dv ι) :
    Measurable (Function.uncurry (Ebar pw g sel J du W dv)) := by
  classical
  have h := (measurable_E0 hD).comp ((hD.measdu.comp measurable_fst).prodMk
    (hD.measdv.comp measurable_snd))
  exact Measurable.ite (hD.measJ.prod hD.measW) h.ennreal_toReal measurable_const

omit [MeasurableSpace 𝒰] [MeasurableSpace 𝒱] [MeasurableSpace 𝒰₀] [MeasurableSpace 𝒱₀]
  [Fintype Θ] in
theorem Ebar_nonneg (u : 𝒰) (v : 𝒱) : 0 ≤ Ebar pw g sel J du W dv u v := by
  unfold Ebar; split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

omit [MeasurableSpace 𝒰] [MeasurableSpace 𝒱] [MeasurableSpace 𝒰₀] [MeasurableSpace 𝒱₀]
  [Fintype Θ] in
theorem Ebar_valid {u : 𝒰} {v : 𝒱} (h : 0 < Ebar pw g sel J du W dv u v) : u ∈ J ∧ v ∈ W := by
  unfold Ebar at h; split_ifs at h with hv
  · exact hv
  · exact absurd h (lt_irrefl 0)

omit [MeasurableSpace 𝒰] [MeasurableSpace 𝒱] [MeasurableSpace 𝒰₀] [MeasurableSpace 𝒱₀]
  [Fintype Θ] in
theorem Ebar_invalid {u : 𝒰} (hu : u ∉ J) (v : 𝒱) : Ebar pw g sel J du W dv u v = 0 := by
  unfold Ebar; simp only [hu, false_and, ↓reduceIte]

omit [Fintype Θ] in
theorem gemb_prob (hD : Design μ g sel pw J du W dv ι) (ϑ : Θ) (u : 𝒰) :
    IsProbabilityMeasure (Gemb μ g du ι ϑ u) :=
  ⟨by rw [Gemb, Measure.map_apply hD.measι MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hD.norm]⟩

/-- (3): the reference moment at every training value. -/
theorem ref_moment (hD : Design μ g sel pw J du W dv ι) (u : 𝒰) {ϑ : Θ} (hϑ : pw ϑ ≤ 1) :
    ∫⁻ v, ENNReal.ofReal (Ebar pw g sel J du W dv u v) ∂(Gemb μ g du ι ϑ u) ≤ 1 := by
  have hEu : Measurable fun v => ENNReal.ofReal (Ebar pw g sel J du W dv u v) :=
    ENNReal.measurable_ofReal.comp ((measurable_Ebar hD).comp measurable_prodMk_left)
  have hgm : Measurable fun v => ENNReal.ofReal (g ϑ (du u) v) :=
    ENNReal.measurable_ofReal.comp ((hD.measg ϑ).comp measurable_prodMk_left)
  unfold Gemb
  have key := lintegral_withDensity_eq_lintegral_mul μ hgm (hEu.comp hD.measι)
  simp only [Function.comp_def] at key
  rw [lintegral_map hEu hD.measι, key]
  calc _ ≤ ∫⁻ v, ENNReal.ofReal (g (sel (du u)) (du u) v) ∂μ := lintegral_mono fun v => by
        simp only [Pi.mul_apply]
        unfold Ebar
        split_ifs with h
        · rw [hD.dvι, ENNReal.ofReal_toReal (hD.fin _ _)]
          exact (mul_le_mul_right (iInf₂_le ϑ hϑ) _).trans (mul_Rplus_le (hD.nonneg _ _ _))
        · simp
    _ = 1 := hD.norm _ _

variable [StandardBorelSpace 𝒱] [Nonempty 𝒱] {P : Measure Ω} [IsProbabilityMeasure P]
  {U : Ω → 𝒰} {V : Ω → 𝒱} {ref : 𝒰 → Θ} {ε : 𝒰 → ℝ}

/-- (4) for one name. -/
theorem size (hU : Measurable U) (hV : Measurable V) (hD : Design μ g sel pw J du W dv ι)
    (hN : NullEnv P U V μ g pw J du ι ref ε) {α : ℝ} (hα : 0 < α) :
    P.real {ω | 1 / α < Ebar pw g sel J du W dv (U ω) (V ω)} ≤
      α * P.real (U ⁻¹' J) + ∫ ω, J.indicator ε (U ω) ∂P := by
  set S : Set (𝒰 × 𝒱) := {x | 1 / α < Ebar pw g sel J du W dv x.1 x.2}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (measurable_Ebar hD)
  have hP : P {ω | 1 / α < Ebar pw g sel J du W dv (U ω) (V ω)} =
      ∫⁻ u, condDistrib V U P u (Prod.mk u ⁻¹' S) ∂(P.map U) := by
    have h := disint (P := P) hU hV (measurable_const.indicator hS : Measurable (S.indicator 1))
    have hmeas : MeasurableSet {ω | 1 / α < Ebar pw g sel J du W dv (U ω) (V ω)} :=
      measurableSet_lt measurable_const ((measurable_Ebar hD).comp (hU.prodMk hV))
    rw [← lintegral_indicator_one hmeas]
    refine (Eq.trans (by rfl) h).trans (lintegral_congr fun u => ?_)
    show ∫⁻ v, (Prod.mk u ⁻¹' S).indicator 1 v ∂_ = _
    rw [lintegral_indicator_one (measurable_prodMk_left hS)]
  have hbound : ∀ᵐ u ∂(P.map U), condDistrib V U P u (Prod.mk u ⁻¹' S) ≤
      ENNReal.ofReal (J.indicator (fun u => α + ε u) u) := by
    filter_upwards [hN.env] with u hu
    by_cases hJ : u ∈ J
    · have := gemb_prob hD (ref u) u
      have hSu : MeasurableSet (Prod.mk u ⁻¹' S) := measurable_prodMk_left hS
      have hu' := hu hJ _ hSu
      have h1 := Novel.D14Misspecification.ofReal_le_add (hN.ε_nonneg u)
        (by linarith [(abs_le.1 hu').2] : (condDistrib V U P u).real (Prod.mk u ⁻¹' S) ≤
          (Gemb μ g du ι (ref u) u).real (Prod.mk u ⁻¹' S) + ε u)
      refine h1.trans ?_
      rw [indicator_of_mem hJ, ENNReal.ofReal_add hα.le (hN.ε_nonneg u)]
      exact add_le_add (markov_one ((measurable_Ebar hD).comp measurable_prodMk_left)
        (ref_moment hD u (hN.null u)) hα) le_rfl
    · have : Prod.mk u ⁻¹' S = ∅ := by
        ext v
        simp only [S, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt,
          Ebar_invalid hJ]
        positivity
      rw [this, measure_empty]; exact bot_le
  rw [measureReal_def, hP]
  have hnn : 0 ≤ α * P.real (U ⁻¹' J) + ∫ ω, J.indicator ε (U ω) ∂P :=
    add_nonneg (mul_nonneg hα.le measureReal_nonneg)
      (integral_nonneg fun ω => indicator_nonneg (fun u _ => hN.ε_nonneg u) _)
  refine ENNReal.toReal_le_of_le_ofReal hnn ?_
  rw [← lin_bound hU hD.measJ hN.measε hN.ε_nonneg hN.ε_le_one hα]
  exact lintegral_mono_ae hbound

/-- (6) for one name. -/
theorem clipped (hU : Measurable U) (hV : Measurable V) (hD : Design μ g sel pw J du W dv ι)
    (hN : NullEnv P U V μ g pw J du ι ref ε) {c : ℝ} (hc : 0 < c) {M Elow : Ω → ℝ}
    (hM : ∀ ω, 0 ≤ M ω ∧ M ω ≤ 1) (hl0 : ∀ ω, 0 ≤ Elow ω)
    (hl : ∀ᵐ ω ∂P, Elow ω ≤ Ebar pw g sel J du W dv (U ω) (V ω)) :
    ∫⁻ ω, ENNReal.ofReal (M ω * min (Elow ω) c / (1 + c * ε (U ω))) ∂P ≤ P (U ⁻¹' J) := by
  set F : 𝒰 × 𝒱 → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (min (Ebar pw g sel J du W dv x.1 x.2) c / (1 + c * ε x.1))
  have hden : ∀ u, 0 < 1 + c * ε u := fun u => by
    have := mul_nonneg hc.le (hN.ε_nonneg u); linarith
  have hF : Measurable F := ENNReal.measurable_ofReal.comp
    (((measurable_Ebar hD).min measurable_const).div
      (measurable_const.add (measurable_const.mul (hN.measε.comp measurable_fst))))
  have hstep : ∫⁻ ω, ENNReal.ofReal (M ω * min (Elow ω) c / (1 + c * ε (U ω))) ∂P ≤
      ∫⁻ ω, F (U ω, V ω) ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hl] with ω hω
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (hden _).le)
    calc M ω * min (Elow ω) c ≤ 1 * min (Elow ω) c :=
          mul_le_mul_of_nonneg_right (hM ω).2 (le_min (hl0 ω) hc.le)
      _ ≤ min (Ebar pw g sel J du W dv (U ω) (V ω)) c := by
          rw [one_mul]; exact min_le_min_right _ hω
  refine hstep.trans ?_
  rw [disint hU hV hF]
  have hin : ∀ᵐ u ∂(P.map U), ∫⁻ v, F (u, v) ∂(condDistrib V U P u) ≤
      J.indicator (fun _ => (1 : ℝ≥0∞)) u := by
    filter_upwards [hN.env] with u hu
    by_cases hJ : u ∈ J
    · rw [indicator_of_mem hJ]
      have := gemb_prob hD (ref u) u
      set Y : 𝒱 → ℝ := fun v => min (Ebar pw g sel J du W dv u v) c
      have hY : Measurable Y := ((measurable_Ebar hD).comp measurable_prodMk_left).min
        measurable_const
      have hY0 : ∀ v, 0 ≤ Y v := fun v => le_min (Ebar_nonneg u v) hc.le
      have htv := Novel.D14Misspecification.lintegral_le_tv hY hY0 (fun v => min_le_right _ _)
        hc.le (hN.ε_nonneg u) (hu hJ)
      have hG : ∫⁻ v, ENNReal.ofReal (Y v) ∂(Gemb μ g du ι (ref u) u) ≤ 1 :=
        (lintegral_mono fun v => ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans
          (ref_moment hD u (hN.null u))
      have hsplit : ∀ v, F (u, v) =
          ENNReal.ofReal (1 / (1 + c * ε u)) * ENNReal.ofReal (Y v) := fun v => by
        simp only [F, Y]
        rw [← ENNReal.ofReal_mul (by have := hden u; positivity)]
        congr 1; ring
      simp_rw [hsplit]
      rw [lintegral_const_mul (ENNReal.ofReal (1 / (1 + c * ε u)))
        (f := fun v => ENNReal.ofReal (Y v)) (ENNReal.measurable_ofReal.comp hY)]
      calc ENNReal.ofReal (1 / (1 + c * ε u)) * ∫⁻ v, ENNReal.ofReal (Y v) ∂(condDistrib V U P u)
          ≤ ENNReal.ofReal (1 / (1 + c * ε u)) * (1 + ENNReal.ofReal (c * ε u)) :=
            mul_le_mul_right (htv.trans (add_le_add hG le_rfl)) _
        _ = 1 := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
              (mul_nonneg hc.le (hN.ε_nonneg u)), ← ENNReal.ofReal_mul (by have := hden u; positivity),
              one_div, inv_mul_cancel₀ (hden u).ne']
    · rw [indicator_of_notMem hJ]
      refine le_of_eq (lintegral_eq_zero_of_ae_eq_zero ?_) |>.trans le_rfl
      refine Eventually.of_forall fun v => ?_
      simp only [F, Ebar_invalid hJ, min_eq_left hc.le, zero_div, ENNReal.ofReal_zero, Pi.zero_apply]
  calc ∫⁻ u, ∫⁻ v, F (u, v) ∂(condDistrib V U P u) ∂(P.map U)
      ≤ ∫⁻ u, J.indicator (fun _ => (1 : ℝ≥0∞)) u ∂(P.map U) := lintegral_mono_ae hin
    _ = P (U ⁻¹' J) := by
        rw [lintegral_indicator_const hD.measJ, one_mul, Measure.map_apply hU hD.measJ]

end Name

open Classical in
theorem general_holds : Standalone.D14SupportRobustness.general := by
  refine ⟨?_, fun P _ Rj b N₀ hb => le_min measureReal_le_one
      ((measureReal_biUnion_finset_le N₀ Rj).trans (Finset.sum_le_sum hb)),
    fun h53 _ _ _ _ _ P _ Er N₀ q hq hq1 hm hnn hnull => ⟨h53 P Er N₀ q hq hq1 hm hnn hnull,
      fun S hS => h53 P (fun i ω => if i ∈ S ω then Er i ω else 0) N₀ q hq hq1
        (fun i => Measurable.ite (hS i) (hm i) measurable_const)
        (fun i ω => by split_ifs; exacts [hnn i ω, le_rfl])
        fun i hi => (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (by
          split_ifs; exacts [le_rfl, hnn i ω])).trans (hnull i hi)⟩, ?_⟩
  · intro Ω 𝒰 𝒱 𝒰₀ 𝒱₀ Θ _ _ _ _ _ _ _ _ P _ U V μ g sel pw J du W dv ι hU hV hD
    refine ⟨⟨measurable_Ebar hD, Ebar_nonneg, fun u v h => Ebar_valid h⟩,
      fun u ϑ hϑ => ref_moment hD u hϑ, fun ref ε hN α hα hα1 => ?_,
      fun ref ε hN c M Elow hc hMm hM hlm hl0 hl => ?_⟩
    · have hB := size hU hV hD hN hα
      have h1 := le_min measureReal_le_one hB
      refine ⟨h1, fun R hR => (measureReal_mono hR).trans h1, fun e he heα => ?_,
        fun Elow hlm hl => ?_⟩
      · have hb := size hU hV hD hN (α := α - e) (by linarith)
        have hint : ∫ ω, J.indicator ε (U ω) ∂P ≤ ∫ ω, J.indicator (fun _ => e) (U ω) ∂P := by
          refine integral_mono_of_nonneg
            (Eventually.of_forall fun ω => indicator_nonneg (fun u _ => hN.ε_nonneg u) _)
            ((integrable_const e).indicator (hU hD.measJ) |>.congr ?_) ?_
          · exact Eventually.of_forall fun ω => by
              by_cases h : U ω ∈ J <;> simp [h, Set.indicator]
          · exact Eventually.of_forall fun ω => by
              by_cases h : U ω ∈ J
              · simp only [indicator_of_mem h]; exact he _ h
              · simp only [indicator_of_notMem h]; exact le_rfl
        have hJe : ∫ ω, J.indicator (fun _ => e) (U ω) ∂P = e * P.real (U ⁻¹' J) := by
          rw [show (fun ω => J.indicator (fun _ => e) (U ω)) = (U ⁻¹' J).indicator (fun _ => e)
            from funext fun ω => by by_cases h : U ω ∈ J <;> simp [h, Set.indicator],
            integral_indicator_const e (hU hD.measJ), smul_eq_mul, mul_comm]
        have hPJ : P.real (U ⁻¹' J) ≤ 1 := measureReal_le_one
        calc P.real {ω | 1 / (α - e) < Ebar pw g sel J du W dv (U ω) (V ω)}
            ≤ (α - e) * P.real (U ⁻¹' J) + ∫ ω, J.indicator ε (U ω) ∂P := hb
          _ ≤ (α - e) * P.real (U ⁻¹' J) + e * P.real (U ⁻¹' J) := by linarith
          _ = α * P.real (U ⁻¹' J) := by ring
          _ ≤ α := by nlinarith [measureReal_nonneg (μ := P) (s := U ⁻¹' J)]
      · refine le_trans ?_ h1
        rw [measureReal_def, measureReal_def]
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
        filter_upwards [hl] with ω hω h
        exact lt_of_lt_of_le h hω
    · have hden : ∀ u, 0 < 1 + c * ε u := fun u => by
        have := mul_nonneg hc.le (hN.ε_nonneg u); linarith
      have hMmin : ∀ ω, M ω * min (Elow ω) c ≤ min (Elow ω) c := fun ω =>
        mul_le_of_le_one_left (le_min (hl0 ω) hc.le) (hM ω).2
      refine ⟨(hMm.mul (hlm.min measurable_const)).div
          (measurable_const.add (measurable_const.mul (hN.measε.comp hU))),
        fun ω => div_nonneg (mul_nonneg (hM ω).1 (le_min (hl0 ω) hc.le)) (hden _).le,
        fun ω => ?_, clipped hU hV hD hN hc hM hl0 hl, prob_le_one, fun α hα ω h => ?_⟩
      · calc M ω * min (Elow ω) c / (1 + c * ε (U ω)) ≤ M ω * min (Elow ω) c :=
              div_le_self (mul_nonneg (hM ω).1 (le_min (hl0 ω) hc.le))
                (by have := mul_nonneg hc.le (hN.ε_nonneg (U ω)); linarith)
          _ ≤ Elow ω := (hMmin ω).trans (min_le_left _ _)
      · have hd := hden (U ω)
        have hcap : 1 / α < c / (1 + c * ε (U ω)) :=
          h.trans_le (div_le_div_of_nonneg_right ((hMmin ω).trans (min_le_right _ _)) hd.le)
        rw [div_lt_div_iff₀ hα hd, one_mul] at hcap
        have hεα : ε (U ω) < α := by
          by_contra hn; push Not at hn; nlinarith [hN.ε_nonneg (U ω)]
        refine ⟨hεα, ?_⟩
        rw [div_lt_iff₀ (sub_pos.2 hεα)]; nlinarith
  · intro ι _ q x hq hq1 i hi
    by_cases hk : kstar q x = 0
    · rw [Novel.D12CatalogueFDR.rej_zero hk] at hi; simp at hi
    have h := (Novel.D12CatalogueFDR.rej_of_pos hk i).1 hi
    have hkm : (kstar q x : ℝ) ≤ Fintype.card ι := by exact_mod_cast Novel.D12CatalogueFDR.kstar_le
    have hkpos : (0 : ℝ) < kstar q x := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
    have : 1 < (Fintype.card ι : ℝ) / (q * kstar q x) := by
      rw [lt_div_iff₀ (mul_pos hq hkpos)]; nlinarith
    linarith

/-! ## Claim 054's CEV score -/

section CEV

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.D3CatalogueCalibration

/-- From a zero endpoint, every chain is `1` on the all-zero array and `0` otherwise. -/
theorem chain_from_zero {m : ℕ} (Δ : Fin m → ℝ) (p κ : ℝ) (v : Fin m → NNR) :
    chainN (Kc p κ) Δ 0 v = if ∀ l, (v l : ℝ) = 0 then 1 else 0 := by
  classical
  split_ifs with hz
  · have : v = fun _ => zero := funext fun l => Subtype.ext (hz l)
    rw [this]; exact Novel.CEVSupport.chain_absorbed Δ p κ
  · push Not at hz
    have hex : ∃ n, ∃ h : n < m, (v ⟨n, h⟩ : ℝ) ≠ 0 := by
      obtain ⟨l, hl⟩ := hz; exact ⟨l, l.2, hl⟩
    set n := Nat.find hex
    obtain ⟨hn, hvn⟩ := Nat.find_spec hex
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨n, hn⟩) ?_
    have hprev : prevN 0 v ⟨n, hn⟩ = 0 := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exact Novel.CEVSupport.prevN_zero 0 v ⟨n, hn⟩ h0
      · rw [Novel.CEVSupport.prevN_succ 0 v ⟨n, hn⟩ h0.ne']
        by_contra h
        exact Nat.find_min hex (show n - 1 < n by omega) ⟨by omega, h⟩
    show Kc p κ (Δ ⟨n, hn⟩) (prevN 0 v ⟨n, hn⟩) (v ⟨n, hn⟩) = 0
    rw [hprev]
    exact Novel.CEVSupport.Kc_zero_pos hvn

theorem measurable_coord {n : ℕ} (j : Fin n) :
    Measurable fun u : Fin n → Zobs => ((u j : Zobs) : ℝ × Bool) :=
  measurable_subtype_coe.comp (measurable_pi_apply j)

theorem measurableSet_validN (n : ℕ) : MeasurableSet (validN n) := by
  have : validN n = ⋂ j, ({u : Fin n → Zobs | ((u j : Zobs) : ℝ × Bool).2 = true} ∩
      {u | 0 ≤ ((u j : Zobs) : ℝ × Bool).1}) := by
    ext u; simp [validN, Zobs.Valid]
  rw [this]
  exact MeasurableSet.iInter fun j =>
    (measurableSet_eq_fun (measurable_snd.comp (measurable_coord j)) measurable_const).inter
      (measurableSet_le measurable_const (measurable_fst.comp (measurable_coord j)))

theorem measurable_decN (n : ℕ) : Measurable (decN n) :=
  measurable_pi_iff.2 fun j =>
    Novel.D13CEVCatalogue.toNNR_meas.comp (measurable_fst.comp (measurable_coord j))

theorem measurable_embN (n : ℕ) : Measurable (embN n) :=
  measurable_pi_iff.2 fun j => Measurable.subtype_mk
    ((measurable_subtype_coe.comp (measurable_pi_apply j)).prodMk measurable_const)

/-- Claim 054's score is at most one on absorbed arrays: a zero last training price, or a zero
evaluation price. -/
theorem Ecomp_absorbed {s R : ℝ} {k m c : ℕ} {t : Fin (k + 1 + m + 1) → NNReal} {pw κ : Fin c → ℝ}
    (hN : NameC s R t pw κ) (hC : Novel.D13CEVCatalogue.Cited) (u0 : Fin (k + 1) → NNR)
    (v0 : Fin m → NNR) (hcase : (u0 (Fin.last k) : ℝ) = 0 ∨ ∃ l, (v0 l : ℝ) = 0) :
    Ecomp pw (fun ϑ => gC t pw κ ϑ u0 v0) (selC hN.size t s pw κ u0) ≤ 1 := by
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  set sl := selC hN.size t s pw κ u0
  have hq0 : 0 ≤ gC t pw κ sl u0 v0 := hSM.nonneg _ _ _
  obtain ⟨ϑ₀, hϑ₀⟩ := hN.hasNull
  by_cases hx : (u0 (Fin.last k) : ℝ) = 0
  · have heq : gC t pw κ ϑ₀ u0 v0 = gC t pw κ sl u0 v0 := by
      unfold gC; rw [hx, chain_from_zero, chain_from_zero]
    refine (Novel.D13CEVCatalogue.Ecomp_le hϑ₀).trans ?_
    show Rplus (gC t pw κ sl u0 v0) (gC t pw κ ϑ₀ u0 v0) ≤ 1
    rw [heq]; exact Novel.D13CEVCatalogue.Rplus_self _ hq0
  · have hpos : 0 < (u0 (Fin.last k) : ℝ) := lt_of_le_of_ne (u0 (Fin.last k)).2 (Ne.symm hx)
    have hz := hcase.resolve_left hx
    by_cases hsel : 1 ≤ pw sl
    · have h0 : gC t pw κ sl u0 v0 = 0 := Novel.CEVSupport.first_zero hsel hpos hz
      refine (Novel.D13CEVCatalogue.Ecomp_le hϑ₀).trans ?_
      show Rplus (gC t pw κ sl u0 v0) (gC t pw κ ϑ₀ u0 v0) ≤ 1
      rw [h0, Novel.CEVSupport.Rplus_zero_left]; exact zero_le_one
    · exact (Novel.D13CEVCatalogue.Ecomp_le (le_of_lt (not_le.1 hsel))).trans
        (Novel.D13CEVCatalogue.Rplus_self _ hq0)

theorem cev_holds : Standalone.D14SupportRobustness.cev := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW s R r k m c t pw κ hN
  have hC := Novel.D13CEVCatalogue.cited_of h55 h56 hW
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Ω') (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  have hfin : ∀ u v, Ecomp pw (fun ϑ => gC t pw κ ϑ u v) (selC hN.size t s pw κ u) ≠ ⊤ :=
    fun u v => (Novel.CEVSupport.score pw (fun ϑ => gC t pw κ ϑ u v) (selC hN.size t s pw κ u)
      (fun ϑ => hSM.nonneg ϑ u v) hN.hasNull (Novel.D13CEVCatalogue.support hN hC u v)).1.ne
  have hEb : ∀ u v, u ∈ validN (k + 1) → v ∈ validN m →
      Ebar pw (gC t pw κ) (selC hN.size t s pw κ) (validN (k + 1)) (decN (k + 1)) (validN m)
        (decN m) u v =
      (Ecomp pw (fun ϑ => gC t pw κ ϑ (decN _ u) (decN _ v))
        (selC hN.size t s pw κ (decN _ u))).toReal := fun u v hu hv => by
    unfold Ebar; simp only [hu, hv, and_self, ↓reduceIte]; rfl
  refine ⟨⟨hSM.sfinite, hSM.measg, hSM.nonneg, hSM.norm, hSM.measSel, hfin,
      measurableSet_validN _, measurable_decN _, measurableSet_validN _, measurable_decN _,
      measurable_embN _, fun v j => ⟨rfl, (v j).2⟩,
      fun v => funext fun j => Subtype.ext (max_eq_left (v j).2)⟩, ?_, ?_⟩
  · -- The band rule.
    intro α hα hr u v hu hv C hb
    set u0 := decN _ u
    set v0 := decN _ v
    set q := gC t pw κ (selC hN.size t s pw κ u0) u0 v0
    have hall : ∀ ϑ, pw ϑ ≤ 1 → ENNReal.ofReal (1 / α) < Rplus q (gC t pw κ ϑ u0 v0) :=
      fun ϑ hϑ => by
        by_contra hle
        have hc : ϑ ∈ C := not_lt.1 hle
        have h1 := Novel.D3CatalogueCalibration.Lo_le
          (f := fun ϑ => blk1 R r (pw ϑ) (κ ϑ)) hc
        have h2 := Novel.D3CatalogueCalibration.le_Hi
          (f := fun ϑ => r ^ (2 - 2 * pw ϑ) * blk1 R r (pw ϑ) (κ ϑ)) hc
        have hpos := (Novel.CEVSupport.blocks (p := pw ϑ) hN.onset hr (hN.scales ϑ)).2.2
        have hrp : 1 ≤ r ^ (2 - 2 * pw ϑ) := Real.one_le_rpow hr.le (by linarith)
        have h3 : blk1 R r (pw ϑ) (κ ϑ) ≤ r ^ (2 - 2 * pw ϑ) * blk1 R r (pw ϑ) (κ ϑ) :=
          le_mul_of_one_le_left hpos.le hrp
        linarith
    obtain ⟨ϑ, hϑ, he⟩ := Novel.D13CEVCatalogue.Ecomp_attained pw
      (fun ϑ => gC t pw κ ϑ u0 v0) (selC hN.size t s pw κ u0) hN.hasNull
    rw [hEb u v hu hv, ← ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (hfin _ _), he]
    exact hall ϑ hϑ
  · -- Absorbed arrays.
    intro u v hu hv hcase
    rw [hEb u v hu hv]
    set u0 := decN _ u
    set v0 := decN _ v
    have hE := Ecomp_absorbed hN hC u0 v0 hcase
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])

end CEV

theorem statement_holds : Standalone.D14SupportRobustness.statement := ⟨general_holds, cev_holds⟩

end Novel.D14SupportRobustness
