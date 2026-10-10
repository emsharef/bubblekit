import Standalone.D14JumpRobustness
import Novel.D13DriftNullProof
import Novel.D14MisspecificationProof

/-!
# Claim 026: proof

Proves `Standalone.D14JumpRobustness.statement` (`proof`).
* **`reference`.**
  - Claim 055's domination `g_G ≤ D` and AX-58's pointwise bound `g · E^drift ≤ Ĝ`
    (`mul_Edrift_le`) give `∫ E^drift dG(u) = ∫ g_G E^drift dμ ≤ ∫ Ĝ dμ = 1` at every `u`.
  - `Ĝ` is normalized by claim 054's chain normalization, and `G(u)` by claim 055's.
* **`oneName`.**
  - Under (1), `H(A) = (1 − p)G(A) + pJ(A)` (`Measure.add_apply`, `Measure.smul_apply`). The
    reference Markov bound gives `G(E > 1/α) ≤ α`.
  - For bounded `f`, `∫ f dH = (1 − p)∫ f dG + p∫ f dJ` (`lintegral_add_measure`,
    `lintegral_smul_measure`).
  - Disintegration (`compProd_map_condDistrib`) integrates the conditional bounds over the actual
    training law.
* **`cap`.** Scalar inequalities, and claim 053's rank characterization of `rej`.
* **`panel`.** Claim 055's union bound, and AX-53 applied to the dominated scores (claim 053's
  masking argument).
* **`jumpLaw`.**
  - The no-jump law is computed by induction on the number of evaluation prices: split the last
    coordinate (`measurePreserving_piFinSuccAbove`), and integrate the last return against the
    log-normal step by the substitution `y = x eʳ`. This is claim 055's chain `gG_chain`.
  - With independent `L`, split `νL` on `{0}` and its complement. `ν.prod (c • δ₀)` is `c` times
    the no-jump law.
* **`dependent`.**
  - The price maps agree off `{L ≠ 0}`.
  - Claim 023's `lintegral_le_tv` gives the clipped moment, and its `ofReal_le_add` the raw size.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace Novel.D14JumpRobustness

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.D13DriftNull
  Standalone.SplitLikelihoodDominated Standalone.D3CatalogueCalibration Standalone.D12CatalogueFDR
  Standalone.D14JumpRobustness

/-! ## One name -/

section OneName

variable {Ω 𝒰 𝒱 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]

theorem mix_apply {H G J : Measure 𝒱} {p : ℝ}
    (h : H = ENNReal.ofReal (1 - p) • G + ENNReal.ofReal p • J) (A : Set 𝒱) :
    H A = ENNReal.ofReal (1 - p) * G A + ENNReal.ofReal p * J A := by
  rw [h, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]

theorem mix_lintegral {H G J : Measure 𝒱} {p : ℝ}
    (h : H = ENNReal.ofReal (1 - p) • G + ENNReal.ofReal p • J) (f : 𝒱 → ℝ≥0∞) :
    ∫⁻ v, f v ∂H = ENNReal.ofReal (1 - p) * ∫⁻ v, f v ∂G + ENNReal.ofReal p * ∫⁻ v, f v ∂J := by
  rw [h, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul,
    smul_eq_mul]

/-- The reference Markov bound. -/
theorem ref_markov {G : Measure 𝒱} {e : 𝒱 → ℝ≥0∞} (he : Measurable e) (hmom : ∫⁻ v, e v ∂G ≤ 1)
    {α : ℝ} (hα : 0 < α) : G {v | ENNReal.ofReal (1 / α) < e v} ≤ ENNReal.ofReal α := by
  have hε : ENNReal.ofReal (1 / α) ≠ 0 := (ENNReal.ofReal_pos.2 (one_div_pos.2 hα)).ne'
  calc G {v | ENNReal.ofReal (1 / α) < e v}
      ≤ G {v | ENNReal.ofReal (1 / α) ≤ e v} := measure_mono fun v (hv : ENNReal.ofReal (1 / α) < e v) =>
        (le_of_lt hv : ENNReal.ofReal (1 / α) ≤ e v)
    _ ≤ (∫⁻ v, e v ∂G) / ENNReal.ofReal (1 / α) :=
        meas_ge_le_lintegral_div he.aemeasurable hε ENNReal.ofReal_ne_top
    _ ≤ 1 / ENNReal.ofReal (1 / α) := ENNReal.div_le_div_right hmom _
    _ = ENNReal.ofReal α := by
        rw [one_div, ← ENNReal.ofReal_inv_of_pos (one_div_pos.2 hα), one_div, inv_inv]

/-- The conditional size bound under (1). -/
theorem cond_size {H G J : Measure 𝒱} [IsProbabilityMeasure J] {p ρ : ℝ} (hp0 : 0 ≤ p)
    (hpρ : p ≤ ρ) (hρ1 : ρ ≤ 1) (h : H = ENNReal.ofReal (1 - p) • G + ENNReal.ofReal p • J) {e : 𝒱 → ℝ≥0∞}
    (he : Measurable e) (hmom : ∫⁻ v, e v ∂G ≤ 1) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    H {v | ENNReal.ofReal (1 / α) < e v} ≤ ENNReal.ofReal (α + (1 - α) * ρ) := by
  rw [mix_apply h]
  calc ENNReal.ofReal (1 - p) * G {v | ENNReal.ofReal (1 / α) < e v} +
        ENNReal.ofReal p * J {v | ENNReal.ofReal (1 / α) < e v}
      ≤ ENNReal.ofReal (1 - p) * ENNReal.ofReal α + ENNReal.ofReal p * 1 :=
        add_le_add (mul_le_mul_right (ref_markov he hmom hα) _) (mul_le_mul_right prob_le_one _)
    _ ≤ ENNReal.ofReal (α + (1 - α) * ρ) := by
        rw [← ENNReal.ofReal_mul (by linarith), mul_one, ← ENNReal.ofReal_add
          (mul_nonneg (by linarith) hα.le) hp0]
        exact ENNReal.ofReal_le_ofReal (by nlinarith)

/-- Disintegration of the actual joint law. -/
theorem disint {P : Measure Ω} [IsProbabilityMeasure P] [StandardBorelSpace 𝒱] [Nonempty 𝒱]
    {U : Ω → 𝒰} {V : Ω → 𝒱} (hU : Measurable U) (hV : Measurable V) {F : 𝒰 × 𝒱 → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, F (U ω, V ω) ∂P = ∫⁻ u, ∫⁻ v, F (u, v) ∂(condDistrib V U P u) ∂(P.map U) := by
  rw [← lintegral_map hF (hU.prodMk hV), ← compProd_map_condDistrib hU.aemeasurable
    hV.aemeasurable, Measure.lintegral_compProd hF]

theorem disint_set {P : Measure Ω} [IsProbabilityMeasure P] [StandardBorelSpace 𝒱] [Nonempty 𝒱]
    {U : Ω → 𝒰} {V : Ω → 𝒱} (hU : Measurable U) (hV : Measurable V) {S : Set (𝒰 × 𝒱)}
    (hS : MeasurableSet S) :
    P {ω | (U ω, V ω) ∈ S} = ∫⁻ u, condDistrib V U P u (Prod.mk u ⁻¹' S) ∂(P.map U) := by
  have e1 : {ω | (U ω, V ω) ∈ S} = (fun ω => (U ω, V ω)) ⁻¹' S := rfl
  rw [e1, ← Measure.map_apply (hU.prodMk hV) hS, ← compProd_map_condDistrib hU.aemeasurable
    hV.aemeasurable, Measure.compProd_apply hS]


theorem real_le_one' (μ : Measure 𝒱) [IsProbabilityMeasure μ] (A : Set 𝒱) : μ.real A ≤ 1 := by
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

theorem lint_affine {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → 𝒰} (hU : Measurable U)
    {ρ : 𝒰 → ℝ} (hρm : Measurable ρ) (hρ : ∀ u, 0 ≤ ρ u ∧ ρ u ≤ 1) {a c : ℝ} (ha : 0 ≤ a)
    (hc : 0 ≤ c) :
    ∫⁻ u, ENNReal.ofReal (a + c * ρ u) ∂(P.map U) = ENNReal.ofReal (a + c * ∫ ω, ρ (U ω) ∂P) := by
  have hρi : Integrable ρ (P.map U) := Integrable.of_bound hρm.aestronglyMeasurable 1
    (ae_of_all _ fun u => by rw [Real.norm_eq_abs, abs_of_nonneg (hρ u).1]; exact (hρ u).2)
  have hint : Integrable (fun u => a + c * ρ u) (P.map U) :=
    (integrable_const a).add (hρi.const_mul c)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun u => by
      have := (hρ u).1; positivity),
    integral_add (integrable_const a) (hρi.const_mul c), integral_const, integral_const_mul,
    integral_map hU.aemeasurable hρm.aestronglyMeasurable, probReal_univ, one_smul]

/-- Parts 1–2 for one name. -/
theorem oneName_holds : oneName := by
  intro Ω 𝒰 𝒱 _ _ _ _ _ P _ U V E G ρ hU hV hE hρm hρ hG hmom hmix
  have hEu : ∀ u, Measurable (E u) := fun u => hE.comp measurable_prodMk_left
  have hsizeC : ∀ α : ℝ, 0 < α → α < 1 → ∀ᵐ u ∂(P.map U),
      condDistrib V U P u {v | ENNReal.ofReal (1 / α) < E u v} ≤
        ENNReal.ofReal (α + (1 - α) * ρ u) := fun α hα hα1 => by
    filter_upwards [hmix] with u hu
    obtain ⟨p, J, hJ, hp0, hpρ, h⟩ := hu
    exact cond_size hp0 hpρ (hρ u).2 h (hEu u) (hmom u) hα hα1
  have hset : ∀ a : ℝ≥0∞, P {ω | a < E (U ω) (V ω)} =
      ∫⁻ u, condDistrib V U P u {v | a < E u v} ∂(P.map U) := fun a =>
    disint_set (S := {x : 𝒰 × 𝒱 | a < E x.1 x.2}) hU hV (measurableSet_lt measurable_const hE)
  refine ⟨?_, fun α hα hα1 => ⟨hsizeC α hα hα1, ?_⟩, ?_, fun c hc => ?_⟩
  · -- TV.
    filter_upwards with u
    intro p J hJ hp0 hp1 h A _
    have := hG u
    have hr : (condDistrib V U P u).real A = (1 - p) * (G u).real A + p * J.real A := by
      rw [measureReal_def, mix_apply h, ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
        ENNReal.toReal_ofReal hp0]
      rfl
    have g0 : 0 ≤ (G u).real A := measureReal_nonneg
    have g1 := real_le_one' (G u) A
    have j0 : 0 ≤ J.real A := measureReal_nonneg
    have j1 := real_le_one' J A
    rw [hr]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  · -- (2), unconditional.
    rw [hset]
    exact (lintegral_mono_ae (hsizeC α hα hα1)).trans_eq
      (lint_affine hU hρm hρ hα.le (by linarith))
  · -- The adjusted threshold.
    intro α e he0 heα hα1 hρe
    set β := (α - e) / (1 - e) with hβ
    have hβ0 : 0 < β := div_pos (by linarith) (by linarith)
    have hβ1 : β < 1 := (div_lt_one (by linarith)).2 (by linarith)
    have h1β : (1 - e) / (α - e) = 1 / β := by rw [hβ, one_div_div]
    rw [h1β, hset]
    calc ∫⁻ u, condDistrib V U P u {v | ENNReal.ofReal (1 / β) < E u v} ∂(P.map U)
        ≤ ∫⁻ _, ENNReal.ofReal α ∂(P.map U) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hsizeC β hβ0 hβ1, hρe] with u hu hue
          refine hu.trans (ENNReal.ofReal_le_ofReal ?_)
          have hb : β * (1 - e) = α - e := div_mul_cancel₀ _ (by linarith)
          have : β + (1 - β) * e = α := by linear_combination hb
          nlinarith
      _ = ENNReal.ofReal α := by rw [lintegral_const, measure_univ, mul_one]
  · -- (3).
    have hDpos : ∀ u, 1 ≤ 1 + (c - 1) * ρ u := fun u => by nlinarith [(hρ u).1]
    have hmin_ne : ∀ u v, min (E u v) (ENNReal.ofReal c) ≠ ⊤ := fun u v =>
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
    have hmeas : Measurable (fun x : 𝒰 × 𝒱 => Ejump c (ρ x.1) (E x.1 x.2)) :=
      (ENNReal.measurable_toReal.comp (hE.min measurable_const)).div
        (measurable_const.add (measurable_const.mul (hρm.comp measurable_fst)))
    have hofReal : ∀ u v, ENNReal.ofReal (Ejump c (ρ u) (E u v)) =
        min (E u v) (ENNReal.ofReal c) * ENNReal.ofReal (1 / (1 + (c - 1) * ρ u)) := fun u v => by
      rw [Ejump, div_eq_mul_one_div, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (hmin_ne u v)]
    have hcm : ∀ᵐ u ∂(P.map U),
        ∫⁻ v, ENNReal.ofReal (Ejump c (ρ u) (E u v)) ∂(condDistrib V U P u) ≤ 1 := by
      filter_upwards [hmix] with u hu
      obtain ⟨p, J, hJ, hp0, hpρ, h⟩ := hu
      have hD := hDpos u
      simp_rw [hofReal u]
      rw [lintegral_mul_const _ ((hEu u).min measurable_const), mix_lintegral h]
      have hG1 : ∫⁻ v, min (E u v) (ENNReal.ofReal c) ∂(G u) ≤ 1 :=
        (lintegral_mono fun v => min_le_left _ _).trans (hmom u)
      have hJ1 : ∫⁻ v, min (E u v) (ENNReal.ofReal c) ∂J ≤ ENNReal.ofReal c :=
        (lintegral_mono fun v => min_le_right _ _).trans_eq (by rw [lintegral_const, measure_univ, mul_one])
      have hp1 : p ≤ 1 := hpρ.trans (hρ u).2
      calc (ENNReal.ofReal (1 - p) * ∫⁻ v, min (E u v) (ENNReal.ofReal c) ∂(G u) +
            ENNReal.ofReal p * ∫⁻ v, min (E u v) (ENNReal.ofReal c) ∂J) *
            ENNReal.ofReal (1 / (1 + (c - 1) * ρ u))
          ≤ (ENNReal.ofReal (1 - p) * 1 + ENNReal.ofReal p * ENNReal.ofReal c) *
            ENNReal.ofReal (1 / (1 + (c - 1) * ρ u)) :=
            mul_le_mul_left (add_le_add (mul_le_mul_right hG1 _) (mul_le_mul_right hJ1 _)) _
        _ ≤ ENNReal.ofReal (1 + (c - 1) * ρ u) * ENNReal.ofReal (1 / (1 + (c - 1) * ρ u)) := by
            refine mul_le_mul_left ?_ _
            rw [mul_one, ← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_add (by linarith)
              (mul_nonneg hp0 (by linarith))]
            exact ENNReal.ofReal_le_ofReal (by nlinarith)
        _ = 1 := by
            rw [← ENNReal.ofReal_mul (by linarith), mul_one_div_cancel (by linarith),
              ENNReal.ofReal_one]
    refine ⟨hmeas, fun u v => ⟨div_nonneg ENNReal.toReal_nonneg (by linarith [hDpos u]), ?_⟩,
      hcm, fun F hF hFb => ?_⟩
    · have h1 : (min (E u v) (ENNReal.ofReal c)).toReal ≤ c :=
        ENNReal.toReal_le_of_le_ofReal (by linarith) (min_le_right _ _)
      exact (div_le_self ENNReal.toReal_nonneg (hDpos u)).trans h1
    · calc ∫⁻ ω, ENNReal.ofReal (F ω) ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal (Ejump c (ρ (U ω)) (E (U ω) (V ω))) ∂P :=
            lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hFb ω).2
        _ = ∫⁻ u, ∫⁻ v, ENNReal.ofReal (Ejump c (ρ u) (E u v)) ∂(condDistrib V U P u) ∂(P.map U) :=
            disint (F := fun x => ENNReal.ofReal (Ejump c (ρ x.1) (E x.1 x.2))) hU hV
              (ENNReal.measurable_ofReal.comp hmeas)
        _ ≤ ∫⁻ _, 1 ∂(P.map U) := lintegral_mono_ae hcm
        _ = 1 := by rw [lintegral_const, measure_univ, one_mul]


/-- Claim 023's consequences under a TV contract. -/
theorem dependent_tv : ∀ {Ω 𝒰 𝒱 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒱] [Nonempty 𝒱] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → 𝒰) (V : Ω → 𝒱) (E : 𝒰 → 𝒱 → ℝ≥0∞) (G : 𝒰 → Measure 𝒱) (ρ : 𝒰 → ℝ),
    Measurable U → Measurable V → Measurable (Function.uncurry E) → Measurable ρ →
    (∀ u, 0 ≤ ρ u ∧ ρ u ≤ 1) → (∀ u, IsProbabilityMeasure (G u)) →
    (∀ u, ∫⁻ v, E u v ∂(G u) ≤ 1) →
    (∀ᵐ u ∂(P.map U), ∀ A, MeasurableSet A →
      |(condDistrib V U P u).real A - (G u).real A| ≤ ρ u) →
    (∀ α : ℝ, 0 < α → α < 1 →
      P.real {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ min 1 (α + ∫ ω, ρ (U ω) ∂P)) ∧
    ∀ c : ℝ, 0 < c → ∫⁻ ω, ENNReal.ofReal (Edep c (ρ (U ω)) (E (U ω) (V ω))) ∂P ≤ 1 := by
  intro Ω 𝒰 𝒱 _ _ _ _ _ P _ U V E G ρ hU hV hE hρm hρ hG hmom htv
  have hEu : ∀ u, Measurable (E u) := fun u => hE.comp measurable_prodMk_left
  refine ⟨fun α hα hα1 => ?_, fun c hc => ?_⟩
  · have hS : MeasurableSet {x : 𝒰 × 𝒱 | ENNReal.ofReal (1 / α) < E x.1 x.2} :=
      measurableSet_lt measurable_const hE
    have hle : P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤
        ENNReal.ofReal (α + 1 * ∫ ω, ρ (U ω) ∂P) := by
      have hset : P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} =
          ∫⁻ u, condDistrib V U P u {v | ENNReal.ofReal (1 / α) < E u v} ∂(P.map U) :=
        disint_set (S := {x : 𝒰 × 𝒱 | ENNReal.ofReal (1 / α) < E x.1 x.2}) hU hV hS
      rw [hset, ← lint_affine hU hρm hρ hα.le zero_le_one]
      refine lintegral_mono_ae ?_
      filter_upwards [htv] with u hu
      have := hG u
      have hA : MeasurableSet {v | ENNReal.ofReal (1 / α) < E u v} :=
        measurableSet_lt measurable_const (hEu u)
      have h1 := Novel.D14Misspecification.ofReal_le_add (hρ u).1
        (by linarith [(abs_le.1 (hu _ hA)).2] :
          (condDistrib V U P u).real {v | ENNReal.ofReal (1 / α) < E u v} ≤
            (G u).real {v | ENNReal.ofReal (1 / α) < E u v} + ρ u)
      refine h1.trans ?_
      rw [one_mul, ENNReal.ofReal_add hα.le (hρ u).1]
      exact add_le_add (ref_markov (hEu u) (hmom u) hα) le_rfl
    have hr := ENNReal.toReal_le_of_le_ofReal (by
      have : 0 ≤ ∫ ω, ρ (U ω) ∂P := integral_nonneg fun ω => (hρ _).1
      positivity) hle
    rw [one_mul] at hr
    exact le_min (real_le_one' P _) hr
  · have hcm : ∀ᵐ u ∂(P.map U),
        ∫⁻ v, ENNReal.ofReal (Edep c (ρ u) (E u v)) ∂(condDistrib V U P u) ≤ 1 := by
      filter_upwards [htv] with u hu
      have := hG u
      have hD : 0 < 1 + c * ρ u := by nlinarith [(hρ u).1]
      have hmin_ne : ∀ v, min (E u v) (ENNReal.ofReal c) ≠ ⊤ := fun v =>
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
      have hY : Measurable fun v => (min (E u v) (ENNReal.ofReal c)).toReal :=
        ENNReal.measurable_toReal.comp ((hEu u).min measurable_const)
      have hof : ∀ v, ENNReal.ofReal (Edep c (ρ u) (E u v)) =
          ENNReal.ofReal ((min (E u v) (ENNReal.ofReal c)).toReal) *
            ENNReal.ofReal (1 / (1 + c * ρ u)) := fun v => by
        rw [Edep, div_eq_mul_one_div, ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      simp_rw [hof]
      rw [lintegral_mul_const (f := fun v => ENNReal.ofReal ((min (E u v) (ENNReal.ofReal c)).toReal))
        _ (ENNReal.measurable_ofReal.comp hY)]
      have htvb := Novel.D14Misspecification.lintegral_le_tv (H := condDistrib V U P u) (G := G u)
        hY (fun v => ENNReal.toReal_nonneg)
        (fun v => ENNReal.toReal_le_of_le_ofReal hc.le (min_le_right _ _)) hc.le (hρ u).1 hu
      have hG1 : ∫⁻ v, ENNReal.ofReal ((min (E u v) (ENNReal.ofReal c)).toReal) ∂(G u) ≤ 1 := by
        simp_rw [ENNReal.ofReal_toReal (hmin_ne _)]
        exact (lintegral_mono fun v => min_le_left _ _).trans (hmom u)
      calc (∫⁻ v, ENNReal.ofReal ((min (E u v) (ENNReal.ofReal c)).toReal) ∂(condDistrib V U P u)) *
            ENNReal.ofReal (1 / (1 + c * ρ u))
          ≤ (1 + ENNReal.ofReal (c * ρ u)) * ENNReal.ofReal (1 / (1 + c * ρ u)) :=
            mul_le_mul_left (htvb.trans (add_le_add hG1 le_rfl)) _
        _ = 1 := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by nlinarith [(hρ u).1]),
              ← ENNReal.ofReal_mul (by linarith), mul_one_div_cancel (by linarith)]
    have hmeas : Measurable (fun x : 𝒰 × 𝒱 => ENNReal.ofReal (Edep c (ρ x.1) (E x.1 x.2))) :=
      ENNReal.measurable_ofReal.comp ((ENNReal.measurable_toReal.comp (hE.min measurable_const)).div
        (measurable_const.add (measurable_const.mul (hρm.comp measurable_fst))))
    calc ∫⁻ ω, ENNReal.ofReal (Edep c (ρ (U ω)) (E (U ω) (V ω))) ∂P
        = ∫⁻ u, ∫⁻ v, ENNReal.ofReal (Edep c (ρ u) (E u v)) ∂(condDistrib V U P u) ∂(P.map U) :=
          disint hU hV hmeas
      _ ≤ ∫⁻ _, 1 ∂(P.map U) := lintegral_mono_ae hcm
      _ = 1 := by rw [lintegral_const, measure_univ, one_mul]

end OneName

/-! ## (4) -/

theorem Ejump_le {c ρ : ℝ} {e : ℝ≥0∞} (hc : 1 ≤ c) (hρ0 : 0 ≤ ρ) :
    Ejump c ρ e ≤ c / (1 + (c - 1) * ρ) :=
  div_le_div_of_nonneg_right (ENNReal.toReal_le_of_le_ofReal (by linarith) (min_le_right _ _))
    (by nlinarith)

theorem cap_one {c ρ α : ℝ} {e : ℝ≥0∞} (hc : 1 ≤ c) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hα : 0 < α)
    (hα1 : α < 1) :
    (1 / α < Ejump c ρ e → ρ < α ∧ (1 - ρ) / (α - ρ) < c) ∧
    (1 / α ≤ Ejump c ρ e → ρ < α ∧ (1 - ρ) / (α - ρ) ≤ c) := by
  have hD : 0 < 1 + (c - 1) * ρ := by nlinarith
  have hle := Ejump_le (e := e) hc hρ0
  constructor
  · intro h
    have h2 : 1 / α < c / (1 + (c - 1) * ρ) := h.trans_le hle
    rw [div_lt_div_iff₀ hα hD] at h2
    have hρα : ρ < α := by
      by_contra hcon; push Not at hcon
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c) (sub_nonneg.2 hcon)]
    exact ⟨hρα, by rw [div_lt_iff₀ (by linarith)]; nlinarith⟩
  · intro h
    have h2 : 1 / α ≤ c / (1 + (c - 1) * ρ) := h.trans hle
    rw [div_le_div_iff₀ hα hD] at h2
    have hρα : ρ < α := by
      by_contra hcon; push Not at hcon
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c) (sub_nonneg.2 hcon),
        mul_pos (by linarith : (0 : ℝ) < c) (by linarith : (0 : ℝ) < 1 - α)]
    exact ⟨hρα, by rw [div_le_iff₀ (by linarith)]; nlinarith⟩

theorem cap_holds : cap := by
  refine ⟨fun c ρ α e hc hρ0 hρ1 hα hα1 => cap_one hc hρ0 hρ1 hα hα1, ?_⟩
  intro ι _ q c ρ e hq hq1 hb i hi a
  set x := fun j => Ejump (c j) (ρ j) (e j) with hx
  have hk : kstar q x ≠ 0 := fun h0 => by
    rw [Novel.D12CatalogueFDR.rej_zero h0] at hi; simp at hi
  have hth := (Novel.D12CatalogueFDR.rej_of_pos hk i).1 hi
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.2 ⟨i⟩
  have hk0 : (0 : ℝ) < kstar q x := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkm : (kstar q x : ℝ) ≤ Fintype.card ι := by exact_mod_cast Novel.D12CatalogueFDR.kstar_le
  have ha0 : 0 < a := by positivity
  have ha1 : a < 1 := by
    show q * kstar q x / Fintype.card ι < 1
    rw [div_lt_one hm]; nlinarith
  have h1a : 1 / a ≤ x i := by
    show 1 / (q * kstar q x / Fintype.card ι) ≤ x i
    rwa [one_div_div]
  exact (cap_one (hb i).1 (hb i).2.1 (hb i).2.2 ha0 ha1).2 h1a

/-! ## The panel -/

theorem panel_holds : panel := by
  classical
  refine ⟨Novel.D13DriftScore.drift_holds.2.1, ?_⟩
  intro h53 ι _ _ Ω _ P _ Er Ej N₀ q hq hq1 hEr hnn hdom hEj
  have hnull : ∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (Er i ω) ∂P ≤ 1 := fun i hi =>
    (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hdom i hi ω)).trans (hEj i hi)
  refine ⟨h53 P Er N₀ q hq hq1 hEr hnn hnull, fun S hS => ?_⟩
  set E' : ι → Ω → ℝ := fun i ω => if i ∈ S ω then Er i ω else 0 with hE'
  have hm : ∀ i, Measurable (E' i) := fun i => Measurable.ite (hS i) (hEr i) measurable_const
  have hnn' : ∀ i ω, 0 ≤ E' i ω := fun i ω => by
    simp only [hE']; split_ifs; exacts [hnn i ω, le_rfl]
  have hle : ∀ i ω, E' i ω ≤ Er i ω := fun i ω => by
    simp only [hE']; split_ifs; exacts [le_rfl, hnn i ω]
  have hnull' : ∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (E' i ω) ∂P ≤ 1 := fun i hi =>
    (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hle i ω)).trans (hnull i hi)
  refine ⟨fun ω i hi => ?_, h53 P E' N₀ q hq hq1 hm hnn' hnull'⟩
  by_contra hiS
  exact Novel.D12CatalogueFDR.not_rej_of_zero hq (x := fun i => E' i ω) (by simp [hE', hiS]) hi


/-! ## The reference moment for claim 055's score -/

theorem reference_holds : reference := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN b κg hκg g sel Δe E G
  obtain ⟨hnorm, -, hdomG, -, hEm, hEfin, -⟩ :=
    Novel.D13DriftScore.drift_holds.1 P' 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN
  have hΔ : ∀ l, 0 < Δe l := fun l => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  have hC := Novel.D13CEVCatalogue.cited_of h55 h56 hW
  have hgnorm : ∀ u, ∫⁻ v, ENNReal.ofReal (g (sel u) u v) ∂(Measure.pi fun _ : Fin m => muCEV) = 1 :=
    fun u => Novel.D13CEVCatalogue.chainN_norm m _ (fun _ => Novel.D13CEVCatalogue.Kc_meas _ _ _)
      (fun _ _ _ hx hy => Novel.D13CEVCatalogue.Kc_nonneg (hN.powers _) (hN.scales _)
        (Novel.D13CEVCatalogue.incrC_pos hN.gridMono _) hx hy)
      (fun _ _ hx => Novel.D13CEVCatalogue.Kc_norm' hC (hN.powers _) (hN.scales _)
        (Novel.D13CEVCatalogue.incrC_pos hN.gridMono _) hx) _ (u (Fin.last k)).2
  have hgG := (Novel.D13DriftNull.profile_holds m Δe (by have := hN.evals; omega) hΔ).2.1 b κg
  have hGm : ∀ u : Fin (k + 1) → NNR, Measurable fun v : Fin m → NNR =>
      ENNReal.ofReal (gGN Δe b κg u v) := fun u =>
    ENNReal.measurable_ofReal.comp (hgG.comp (measurable_const.prodMk
      (measurable_pi_iff.2 fun l => measurable_subtype_coe.comp (measurable_pi_apply l))))
  refine ⟨hEm, hEfin, fun u => ⟨?_⟩, fun u => ?_⟩
  · show ((Measure.pi fun _ : Fin m => muCEV).withDensity
      fun v => ENNReal.ofReal (gGN Δe b κg u v)) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hnorm b κg u hκg
  · show ∫⁻ v, E u v ∂(Measure.pi fun _ : Fin m => muCEV).withDensity
      (fun v => ENNReal.ofReal (gGN Δe b κg u v)) ≤ 1
    have hEv : Measurable (E u) :=
      Measurable.comp (g := Function.uncurry E) (f := Prod.mk u) hEm measurable_prodMk_left
    rw [lintegral_withDensity_eq_lintegral_mul _ (hGm u) hEv, ← hgnorm u]
    exact lintegral_mono fun v =>
      Novel.SplitLikelihoodDominated.mul_Edrift_le (hdomG b κg u v hκg)


/-! ## Part 3: the price map -/

section Price

variable {m : ℕ}

theorem toNNR_coe (y : NNR) : toNNR (y : ℝ) = y := Subtype.ext (max_eq_left y.2)

theorem toNNR_pos {x : ℝ} (hx : 0 < x) : ((toNNR x : NNR) : ℝ) = x := max_eq_left hx.le

theorem priceMap_meas (x0 : ℝ) : Measurable (priceMap (m := m) x0) :=
  measurable_pi_iff.2 fun _ => Novel.D13CEVCatalogue.toNNR_meas.comp (measurable_const.mul
    (Real.measurable_exp.comp (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)))

theorem Iic_eq_filter {n : ℕ} (j : Fin n) : Finset.Iic j = Finset.univ.filter (· ≤ j) := by
  ext k; simp

theorem sum_snoc_castSucc (z : Fin m → ℝ) (a : ℝ) (i : Fin m) :
    ∑ k ∈ Finset.Iic i.castSucc, (Fin.snoc z a : Fin (m + 1) → ℝ) k = ∑ k ∈ Finset.Iic i, z k := by
  rw [Iic_eq_filter, Iic_eq_filter, Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_le_castSucc_iff, Fin.snoc_castSucc]
  have : ¬ Fin.last m ≤ i.castSucc := not_le.2 (Fin.castSucc_lt_last i)
  simp [this]

theorem sum_snoc_last (z : Fin m → ℝ) (a : ℝ) :
    ∑ k ∈ Finset.Iic (Fin.last m), (Fin.snoc z a : Fin (m + 1) → ℝ) k = ∑ k, z k + a := by
  rw [Iic_eq_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
  simp [Fin.le_last]

theorem lastOrN_priceMap {x0 : ℝ} (hx0 : 0 < x0) (z : Fin m → ℝ) :
    Novel.D13CEVCatalogue.lastOrN x0 (priceMap x0 z) = x0 * Real.exp (∑ k, z k) := by
  unfold Novel.D13CEVCatalogue.lastOrN
  split_ifs with h
  · subst h; simp
  · have hI : Finset.Iic (⟨m - 1, by omega⟩ : Fin m) = Finset.univ := by
      ext k; simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
      exact Fin.mk_le_mk.2 (by omega) |>.trans_eq' rfl
    rw [priceMap, hI, toNNR_pos (by positivity)]

theorem priceMap_snoc {x0 : ℝ} (hx0 : 0 < x0) (z : Fin m → ℝ) (a : ℝ) :
    priceMap x0 (Fin.snoc z a : Fin (m + 1) → ℝ) =
      Fin.snoc (priceMap x0 z) (toNNR (Novel.D13CEVCatalogue.lastOrN x0 (priceMap x0 z) *
        Real.exp a)) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last, priceMap, sum_snoc_last, lastOrN_priceMap hx0, Real.exp_add, mul_assoc]
  · rw [Fin.snoc_castSucc, priceMap, priceMap, sum_snoc_castSucc]

theorem lastOrN_priceMap_pos {x0 : ℝ} (hx0 : 0 < x0) (z : Fin m → ℝ) :
    0 < Novel.D13CEVCatalogue.lastOrN x0 (priceMap x0 z) := by
  rw [lastOrN_priceMap hx0]; positivity

end Price


/-! ## Part 3: the no-jump law is claim 055's Gaussian law -/

section NoJump

open Novel.D13DriftScore (KG KG_meas KG_nonneg gG_chain)

variable {b κ : ℝ}

theorem var_ne {κ Δ : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ) : (κ ^ 2 * Δ).toNNReal ≠ 0 := by
  intro h
  have : (0 : ℝ) < ((κ ^ 2 * Δ).toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ (by positivity)]; positivity
  rw [h, NNReal.coe_zero] at this
  exact lt_irrefl _ this

/-- One Gaussian log return from a positive price is one step of (1). -/
theorem gauss_step (hκ : 0 < κ) {Δ L : ℝ} (hΔ : 0 < Δ) (hL : 0 < L) {f : NNR → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ r, f (toNNR (L * Real.exp r)) ∂gaussianReal ((b - κ ^ 2 / 2) * Δ) (κ ^ 2 * Δ).toNNReal =
      ∫⁻ y, ENNReal.ofReal (KG b κ Δ L y) * f y ∂muCEV := by
  have hv := var_ne hκ hΔ
  have h0 : KG b κ Δ L 0 = 0 := by unfold KG; simp [hL.ne']
  have hcoe : ∀ y : NNR, ENNReal.ofReal (KG b κ Δ L y) * f y =
      (fun r : ℝ => ENNReal.ofReal (KG b κ Δ L r) * f (toNNR r)) y := fun y => by
    simp only [toNNR_coe]
  rw [muCEV, lintegral_add_measure, lintegral_dirac, Novel.D13DriftScore.coe_zero, h0,
    ENNReal.ofReal_zero, zero_mul, add_zero]
  simp_rw [hcoe]
  rw [Novel.D13CEVCatalogue.lebNN_lintegral (fun r => ENNReal.ofReal (KG b κ Δ L r) * f (toNNR r)),
    gaussianReal_of_var_ne_zero _ hv,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _)
      (g := fun r => f (toNNR (L * Real.exp r)))
      (hf.comp (Novel.D13CEVCatalogue.toNNR_meas.comp (measurable_const.mul Real.measurable_exp)))]
  have himg : (fun r => L * Real.exp r) '' univ = Ioi 0 := by
    ext y
    simp only [image_univ, mem_range, mem_Ioi]
    constructor
    · rintro ⟨r, rfl⟩; positivity
    · intro hy
      exact ⟨Real.log (y / L), by rw [Real.exp_log (div_pos hy hL)]; field_simp⟩
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (f := fun r => L * Real.exp r) (f' := fun r => L * Real.exp r)
    (fun r _ => ((Real.hasDerivAt_exp r).const_mul L).hasDerivWithinAt)
    (fun r1 _ r2 _ h => Real.exp_injective (mul_left_cancel₀ hL.ne' h)), Measure.restrict_univ]
  refine lintegral_congr fun r => ?_
  have hpos : 0 < L * Real.exp r := by positivity
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← mul_assoc, abs_of_pos hpos, ← ENNReal.ofReal_mul hpos.le]
  congr 2
  unfold KG
  simp only [hL.ne', hpos.ne', ↓reduceIte]
  rw [show L * Real.exp r / L = Real.exp r by field_simp, Real.log_exp]
  field_simp

theorem snoc_meas {α : Type*} [MeasurableSpace α] {m : ℕ} :
    Measurable fun q : (Fin m → α) × α => (Fin.snoc q.1 q.2 : Fin (m + 1) → α) := by
  refine measurable_pi_iff.2 fun j => ?_
  induction j using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; exact measurable_snd
  | cast i => simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply i).comp measurable_fst

/-- The no-jump price law integrates like (1), by induction on the number of returns. -/
theorem push_chain (hκ : 0 < κ) : ∀ (m : ℕ) (Δ : Fin m → ℝ) (x0 : ℝ), (∀ j, 0 < Δ j) → 0 < x0 →
    ∀ F : (Fin m → NNR) → ℝ≥0∞, Measurable F →
      ∫⁻ z, F (priceMap x0 z) ∂lawZ Δ b κ =
        ∫⁻ y, ENNReal.ofReal (chainN (fun Δj => KG b κ Δj) Δ x0 y) * F y
          ∂(Measure.pi fun _ : Fin m => muCEV)
  | 0, Δ, x0, _, _, F, _ => by
    have hs : ∀ y y' : Fin 0 → NNR, y = y' := fun y y' => funext fun i => i.elim0
    rw [lawZ, Measure.pi_of_empty, Measure.pi_of_empty, lintegral_dirac, lintegral_dirac]
    simp only [chainN, Finset.univ_eq_empty, Finset.prod_empty, ENNReal.ofReal_one, one_mul]
    exact congrArg F (hs _ _)
  | m + 1, Δ, x0, hΔ, hx0, F, hF => by
    set γ : Fin (m + 1) → Measure ℝ := fun j =>
      gaussianReal ((b - κ ^ 2 / 2) * Δ j) (κ ^ 2 * Δ j).toNNReal
    have hmp := (measurePreserving_piFinSuccAbove γ (Fin.last m)).symm
    have hmpN := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => muCEV) (Fin.last m)
    set Δ' : Fin m → ℝ := fun i => Δ i.castSucc
    -- The inner integral, against the last return.
    set Φ : (Fin m → NNR) → ℝ≥0∞ := fun y' => ∫⁻ y, ENNReal.ofReal
      (KG b κ (Δ (Fin.last m)) (Novel.D13CEVCatalogue.lastOrN x0 y') y) * F (Fin.snoc y' y) ∂muCEV
      with hΦ
    have hG2 : Measurable fun q : (Fin m → NNR) × NNR => ENNReal.ofReal
        (KG b κ (Δ (Fin.last m)) (Novel.D13CEVCatalogue.lastOrN x0 q.1) q.2) * F (Fin.snoc q.1 q.2) := by
      refine (ENNReal.measurable_ofReal.comp ((KG_meas b κ _).comp
        ((Novel.D13CEVCatalogue.lastOrN_meas.comp (measurable_const.prodMk measurable_fst)).prodMk
          (measurable_subtype_coe.comp measurable_snd)))).mul (hF.comp ?_)
      exact snoc_meas
    have hΦm : Measurable Φ := hG2.lintegral_prod_right'
    have ih := push_chain hκ m Δ' x0 (fun i => hΔ _) hx0 Φ hΦm
    -- Left side.
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
    set eN := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => NNR) (Fin.last m)
    have he : ∀ q : ℝ × (Fin m → ℝ), e.symm q = Fin.snoc q.2 q.1 := fun q => by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply] <;> rfl
    have heN : ∀ q : NNR × (Fin m → NNR), eN.symm q = Fin.snoc q.2 q.1 := fun q => by
      simp [eN, MeasurableEquiv.piFinSuccAbove_symm_apply] <;> rfl
    have hγ' : (Measure.pi fun i : Fin m => γ ((Fin.last m).succAbove i)) = lawZ Δ' b κ := by
      simp only [Fin.succAbove_last, γ, lawZ, Δ']
    -- Left side.
    have hL : ∫⁻ z, F (priceMap x0 z) ∂lawZ Δ b κ = ∫⁻ z', Φ (priceMap x0 z') ∂lawZ Δ' b κ := by
      have hFm : Measurable fun q : ℝ × (Fin m → ℝ) => F (priceMap x0 (e.symm q)) :=
        hF.comp ((priceMap_meas x0).comp e.symm.measurable)
      rw [show lawZ Δ b κ = Measure.pi γ from rfl,
        ← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
        lintegral_prod_symm _ hFm.aemeasurable, hγ']
      refine lintegral_congr fun z' => ?_
      simp only [he]
      rw [hΦ]
      simp only
      simp_rw [priceMap_snoc hx0]
      exact gauss_step (b := b) hκ (hΔ (Fin.last m)) (lastOrN_priceMap_pos hx0 z')
        (f := fun y => F (Fin.snoc (priceMap x0 z') y))
        (hF.comp (show Measurable fun y : NNR => (Fin.snoc (priceMap x0 z') y : Fin (m + 1) → NNR)
          from snoc_meas.comp ((measurable_const (a := priceMap x0 z')).prodMk measurable_id)))
    -- Right side.
    have hR : ∫⁻ y, ENNReal.ofReal (chainN (fun Δj => KG b κ Δj) Δ x0 y) * F y
        ∂(Measure.pi fun _ : Fin (m + 1) => muCEV) =
        ∫⁻ y', ENNReal.ofReal (chainN (fun Δj => KG b κ Δj) Δ' x0 y') * Φ y'
          ∂(Measure.pi fun _ : Fin m => muCEV) := by
      have hc := Novel.D13CEVCatalogue.chainN_meas (f := fun Δj => KG b κ Δj) (Δ := Δ)
        (fun j => KG_meas b κ _)
      have hGm : Measurable fun q : NNR × (Fin m → NNR) =>
          ENNReal.ofReal (chainN (fun Δj => KG b κ Δj) Δ x0 (eN.symm q)) * F (eN.symm q) :=
        (ENNReal.measurable_ofReal.comp (hc.comp (measurable_const.prodMk eN.symm.measurable))).mul
          (hF.comp eN.symm.measurable)
      rw [← hmpN.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
        lintegral_prod_symm _ hGm.aemeasurable]
      refine lintegral_congr fun y' => ?_
      simp only [heN]
      have hc' : 0 ≤ chainN (fun Δj => KG b κ Δj) Δ' x0 y' :=
        Novel.D13CEVCatalogue.chainN_nonneg (fun j x y _ hy => KG_nonneg b κ _ hy) hx0.le y'
      have hsplit : ∀ x : NNR, chainN (fun Δj => KG b κ Δj) Δ x0 (Fin.snoc y' x) =
          chainN (fun Δj => KG b κ Δj) Δ' x0 y' *
            KG b κ (Δ (Fin.last m)) (Novel.D13CEVCatalogue.lastOrN x0 y') x := fun x => by
        rw [Novel.D13CEVCatalogue.chainN_succ]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rfl
      have hx : Measurable fun x : NNR => ENNReal.ofReal
          (KG b κ (Δ (Fin.last m)) (Novel.D13CEVCatalogue.lastOrN x0 y') x) * F (Fin.snoc y' x) :=
        hG2.comp ((measurable_const (a := y')).prodMk measurable_id)
      simp_rw [hsplit, ENNReal.ofReal_mul hc', mul_assoc]
      rw [lintegral_const_mul _ hx]
    rw [hL, ih, hR]

theorem noJump (hκ : 0 < κ) {m : ℕ} {Δ : Fin m → ℝ} {x0 : ℝ} (hΔ : ∀ j, 0 < Δ j) (hx0 : 0 < x0) :
    (lawZ Δ b κ).map (priceMap x0) = Gref Δ b κ x0 := by
  ext B hB
  rw [Measure.map_apply (priceMap_meas x0) hB, Gref, withDensity_apply _ hB]
  have hl : lawZ Δ b κ (priceMap x0 ⁻¹' B) = ∫⁻ z, B.indicator 1 (priceMap x0 z) ∂lawZ Δ b κ := by
    rw [← lintegral_indicator_one ((priceMap_meas x0) hB)]; rfl
  have hr : ∫⁻ y in B, ENNReal.ofReal (gG Δ b κ x0 fun l => (y l : ℝ))
      ∂(Measure.pi fun _ : Fin m => muCEV) =
      ∫⁻ y, ENNReal.ofReal (chainN (fun Δj => KG b κ Δj) Δ x0 y) * B.indicator 1 y
        ∂(Measure.pi fun _ : Fin m => muCEV) := by
    rw [← lintegral_indicator hB]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ B <;> simp [hy, gG_chain hΔ b κ hx0.le]
  rw [hl, hr]
  exact push_chain hκ m Δ x0 hΔ hx0 _ (measurable_one.indicator hB)

theorem lawZ_prob {m : ℕ} (Δ : Fin m → ℝ) : IsProbabilityMeasure (lawZ Δ b κ) := by
  unfold lawZ; infer_instance

theorem indep (hκ : 0 < κ) {m : ℕ} {Δ : Fin m → ℝ} {x0 : ℝ} (hΔ : ∀ j, 0 < Δ j) (hx0 : 0 < x0)
    (νL : Measure (Fin m → ℝ)) [IsProbabilityMeasure νL] :
    ∃ J : Measure (Fin m → NNR), IsProbabilityMeasure J ∧
      ((lawZ Δ b κ).prod νL).map (fun x => priceMap x0 (x.1 + x.2)) =
        ENNReal.ofReal (1 - (νL {l | l ≠ 0}).toReal) • Gref Δ b κ x0 +
          ENNReal.ofReal (νL {l | l ≠ 0}).toReal • J := by
  have := lawZ_prob (b := b) (κ := κ) Δ
  set π : (Fin m → ℝ) × (Fin m → ℝ) → (Fin m → NNR) := fun x => priceMap x0 (x.1 + x.2) with hπdef
  have hπ : Measurable π := (priceMap_meas x0).comp (measurable_fst.add measurable_snd)
  have hne : {l : Fin m → ℝ | l ≠ 0} = {0}ᶜ := by ext; simp
  rw [hne]
  have h0part : ((lawZ Δ b κ).prod (νL.restrict {0})).map π = νL {0} • Gref Δ b κ x0 := by
    rw [Measure.restrict_singleton]
    ext B hB
    rw [Measure.map_apply hπ hB, Measure.prod_apply (hπ hB), Measure.smul_apply, ← noJump hκ hΔ hx0,
      Measure.map_apply (priceMap_meas x0) hB, smul_eq_mul, ← lintegral_indicator_one
        ((priceMap_meas x0) hB), ← lintegral_const_mul _ (measurable_one.indicator
        ((priceMap_meas x0) hB))]
    refine lintegral_congr fun z => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurable_prodMk_left (hπ hB))]
    congr 1
    have : (0 : Fin m → ℝ) ∈ Prod.mk z ⁻¹' π ⁻¹' B ↔ z ∈ priceMap x0 ⁻¹' B := by
      simp only [mem_preimage, hπdef, add_zero]
    by_cases hz : z ∈ priceMap x0 ⁻¹' B
    · rw [indicator_of_mem hz, indicator_of_mem (this.2 hz)]; rfl
    · rw [indicator_of_notMem hz, indicator_of_notMem (mt this.1 hz)]
  have hsplit : νL = νL.restrict {0} + νL.restrict {0}ᶜ :=
    (Measure.restrict_add_restrict_compl (measurableSet_singleton 0)).symm
  set M := ((lawZ Δ b κ).prod (νL.restrict {0}ᶜ)).map π with hM
  have hmain : ((lawZ Δ b κ).prod νL).map π = νL {0} • Gref Δ b κ x0 + M := by
    conv_lhs => rw [hsplit]
    rw [Measure.prod_add, Measure.map_add _ _ hπ, h0part]
  have hq1 : νL {0} + νL {0}ᶜ = 1 := by
    rw [measure_add_measure_compl (measurableSet_singleton 0), measure_univ]
  have h1p : ENNReal.ofReal (1 - (νL {0}ᶜ).toReal) = νL {0} := by
    have := congrArg ENNReal.toReal hq1
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at this
    rw [show 1 - (νL {0}ᶜ).toReal = (νL {0}).toReal by linarith, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hmain, h1p]
  have hGp : IsProbabilityMeasure (Gref Δ b κ x0) := by rw [← noJump hκ hΔ hx0]; infer_instance
  by_cases hq : νL {0}ᶜ = 0
  · refine ⟨Gref Δ b κ x0, hGp, ?_⟩
    have hM0 : M = 0 := by rw [hM, Measure.restrict_eq_zero.2 hq, Measure.prod_zero, Measure.map_zero]
    rw [hM0, hq, ENNReal.toReal_zero, ENNReal.ofReal_zero, zero_smul, add_zero]
  · have hqt : νL {0}ᶜ ≠ ⊤ := measure_ne_top _ _
    refine ⟨(νL {0}ᶜ)⁻¹ • M, ⟨?_⟩, ?_⟩
    · rw [Measure.smul_apply, hM, Measure.map_apply hπ MeasurableSet.univ, preimage_univ,
        ← univ_prod_univ, Measure.prod_prod, measure_univ, one_mul, Measure.restrict_apply_univ,
        smul_eq_mul, ENNReal.inv_mul_cancel hq hqt]
    · rw [ENNReal.ofReal_toReal hqt, smul_smul, ENNReal.mul_inv_cancel hq hqt, one_smul]

theorem bernoulli {m : ℕ} (p : ℝ) (w : Fin m → ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hw : w ≠ 0) :
    let νL := ENNReal.ofReal (1 - p) • Measure.dirac (0 : Fin m → ℝ) +
      ENNReal.ofReal p • Measure.dirac w
    IsProbabilityMeasure νL ∧ (νL {l | l ≠ 0}).toReal = p := by
  intro νL
  have hne : MeasurableSet {l : Fin m → ℝ | l ≠ 0} := (measurableSet_singleton 0).compl
  refine ⟨⟨?_⟩, ?_⟩
  · simp only [νL, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by linarith) hp0.le]; simp
  · simp only [νL, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hne]
    simp [indicator, hw, hp0.le]

theorem survival {m : ℕ} (νL : Measure (Fin m → ℝ)) [IsProbabilityMeasure νL] (lam τ : ℝ)
    (h : ENNReal.ofReal (Real.exp (-(lam * τ))) ≤ νL {0}) :
    (νL {l | l ≠ 0}).toReal ≤ 1 - Real.exp (-(lam * τ)) := by
  have hne : {l : Fin m → ℝ | l ≠ 0} = {0}ᶜ := by ext; simp
  have hc := probReal_compl_eq_one_sub (μ := νL) (measurableSet_singleton (0 : Fin m → ℝ))
  have h2 := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h
  rw [hne, ← measureReal_def, hc, measureReal_def]
  linarith

theorem jumpLaw_holds : jumpLaw := by
  intro m Δ b κ x0 hΔ hκ hx0
  exact ⟨noJump hκ hΔ hx0, fun νL hνL => indep hκ hΔ hx0 νL,
    fun p w hp0 hp1 hw => bernoulli p w hp0 hp1 hw,
    fun νL lam τ hνL _ _ h => survival νL lam τ h⟩

theorem coupling : ∀ (m : ℕ) (Δ : Fin m → ℝ) (b κ x0 : ℝ), (∀ j, 0 < Δ j) → 0 < κ → 0 < x0 →
    ∀ ν : Measure ((Fin m → ℝ) × (Fin m → ℝ)), IsProbabilityMeasure ν →
      ν.map Prod.fst = lawZ Δ b κ →
      ∀ A, MeasurableSet A → |(ν.map fun x => priceMap x0 (x.1 + x.2)).real A -
        (Gref Δ b κ x0).real A| ≤ (ν {x | x.2 ≠ 0}).toReal := by
  intro m Δ b κ x0 hΔ hκ hx0 ν hν hfst A hA
  set f : (Fin m → ℝ) × (Fin m → ℝ) → (Fin m → NNR) := fun x => priceMap x0 (x.1 + x.2)
  set g : (Fin m → ℝ) × (Fin m → ℝ) → (Fin m → NNR) := fun x => priceMap x0 x.1
  have hf : Measurable f := (priceMap_meas x0).comp (measurable_fst.add measurable_snd)
  have hg : Measurable g := (priceMap_meas x0).comp measurable_fst
  have hG : Gref Δ b κ x0 = ν.map g := by
    rw [← noJump hκ hΔ hx0, ← hfst, Measure.map_map (priceMap_meas x0) measurable_fst]; rfl
  set N := {x : (Fin m → ℝ) × (Fin m → ℝ) | x.2 ≠ 0}
  have hfg : ∀ x, x ∉ N → f x = g x := fun x hx => by
    have : x.2 = 0 := not_not.1 hx
    simp [f, g, this]
  have h1 : ν (f ⁻¹' A) ≤ ν (g ⁻¹' A) + ν N := by
    refine (measure_mono fun x hx => ?_).trans (measure_union_le _ _)
    by_cases hxN : x ∈ N
    · exact Or.inr hxN
    · exact Or.inl (show g x ∈ A by rw [← hfg x hxN]; exact hx)
  have h2 : ν (g ⁻¹' A) ≤ ν (f ⁻¹' A) + ν N := by
    refine (measure_mono fun x hx => ?_).trans (measure_union_le _ _)
    by_cases hxN : x ∈ N
    · exact Or.inr hxN
    · exact Or.inl (show f x ∈ A by rw [hfg x hxN]; exact hx)
  rw [hG, measureReal_def, measureReal_def, Measure.map_apply hf hA, Measure.map_apply hg hA]
  have t1 := ENNReal.toReal_mono (by finiteness) h1
  have t2 := ENNReal.toReal_mono (by finiteness) h2
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at t1 t2
  exact abs_le.2 ⟨by linarith, by linarith⟩

end NoJump

/-- Claim 026. -/
theorem proof : Standalone.D14JumpRobustness.statement :=
  ⟨reference_holds, oneName_holds, cap_holds, panel_holds, jumpLaw_holds, coupling, dependent_tv⟩

end Novel.D14JumpRobustness
