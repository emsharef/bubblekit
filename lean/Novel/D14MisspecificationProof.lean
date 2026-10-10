import Standalone.D14Misspecification
import Novel.D12CatalogueFDRProof
import Novel.SplitLikelihoodProof
import Novel.D14GaussianProof

/-!
# Claim 023 (D14): proof

Proves `Standalone.D14Misspecification.statement` (`statement_holds`).

* **Scores on the observation space.** `Esc u v = min_{ϑ null} g_{ϑ̂(u)}(u,v)/g_ϑ(u,v)`, so
  `E = Esc(U, V)`. It is measurable (a finite `inf'`) and at most the ratio at `ref u`.
* **Under the reference** (`ref_moment`): `∫ g_{ϑ̂(u)}/g_{ref u} dG u = 1`. This is the
  split-density cancellation of `Novel.SplitLikelihood.ax52_holds`, at one fixed `u`. Markov gives
  `G u {E > 1/α} ≤ α`.
* **Under the actual law.** The eventwise TV envelope gives `H u {E > 1/α} ≤ α + ε u`. The
  disintegration `P∘(U,V)⁻¹ = P∘U⁻¹ ⊗ condDistrib V U P` (`compProd_map_condDistrib`,
  `Measure.compProd_apply`, `Measure.lintegral_compProd`) integrates this over the actual training
  law.
* **Bounded scores** (`lintegral_le_tv`): layer cake (`lintegral_eq_lintegral_meas_lt`) gives
  `∫ Y dH ≤ ∫ Y dG + c ε` for `0 ≤ Y ≤ c`. With the reference moment this bounds the clipped score's
  mean, by `1`.
* **Claim 051's band rule** (`band_sub`): a null in the confidence set has `B₁ ≤ B₂` (claim 051's
  `null_order`), so the band event excludes every null, for any truth.
* Part 3 is `Novel.D14Gaussian.part3_holds`.
* Part 4 is finite algebra and a limit.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Novel.D14Misspecification

open Standalone.D3PowerTail Standalone.D3CatalogueCalibration Standalone.D12CatalogueFDR
  Standalone.D14Misspecification

/-! ## Layer cake under a TV envelope -/

theorem ofReal_le_add {𝒱 : Type} [MeasurableSpace 𝒱] {H G : Measure 𝒱} [IsFiniteMeasure H]
    [IsFiniteMeasure G] {A : Set 𝒱} {ε : ℝ} (hε : 0 ≤ ε) (h : H.real A ≤ G.real A + ε) :
    H A ≤ G A + ENNReal.ofReal ε := by
  rw [← ofReal_measureReal (measure_ne_top H _), ← ofReal_measureReal (measure_ne_top G _),
    ← ENNReal.ofReal_add measureReal_nonneg hε]
  exact ENNReal.ofReal_le_ofReal h

theorem lintegral_le_tv {𝒱 : Type} [MeasurableSpace 𝒱] {H G : Measure 𝒱} [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] {Y : 𝒱 → ℝ} {c ε : ℝ} (hY : Measurable Y) (h0 : ∀ v, 0 ≤ Y v)
    (hc : ∀ v, Y v ≤ c) (_hc0 : 0 ≤ c) (hε : 0 ≤ ε)
    (henv : ∀ A, MeasurableSet A → |H.real A - G.real A| ≤ ε) :
    ∫⁻ v, ENNReal.ofReal (Y v) ∂H ≤ ∫⁻ v, ENNReal.ofReal (Y v) ∂G + ENNReal.ofReal (c * ε) := by
  rw [lintegral_eq_lintegral_meas_lt H (Eventually.of_forall h0) hY.aemeasurable,
    lintegral_eq_lintegral_meas_lt G (Eventually.of_forall h0) hY.aemeasurable]
  have hpt : ∀ t : ℝ, H {a | t < Y a} ≤ G {a | t < Y a} + (Iio c).indicator
      (fun _ => ENNReal.ofReal ε) t := fun t => by
    by_cases ht : t < c
    · rw [indicator_of_mem (show t ∈ Iio c from ht)]
      have hm : MeasurableSet {a | t < Y a} := measurableSet_lt measurable_const hY
      exact ofReal_le_add hε (by linarith [(abs_le.1 (henv _ hm)).2])
    · have : {a | t < Y a} = ∅ := by
        ext a; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (hc a).trans (not_lt.1 ht)
      rw [this, measure_empty]; exact bot_le
  have hind : ∫⁻ t in Ioi 0, (Iio c).indicator (fun _ => ENNReal.ofReal ε) t =
      ENNReal.ofReal (c * ε) := by
    rw [lintegral_indicator measurableSet_Iio, setLIntegral_const,
      Measure.restrict_apply measurableSet_Iio, Iio_inter_Ioi, Real.volume_Ioo, sub_zero,
      ← ENNReal.ofReal_mul hε, mul_comm]
  calc ∫⁻ t in Ioi 0, H {a | t < Y a}
      ≤ ∫⁻ t in Ioi 0, (G {a | t < Y a} + (Iio c).indicator (fun _ => ENNReal.ofReal ε) t) :=
        lintegral_mono fun t => hpt t
    _ = (∫⁻ t in Ioi 0, G {a | t < Y a}) +
          ∫⁻ t in Ioi 0, (Iio c).indicator (fun _ => ENNReal.ofReal ε) t :=
        by rw [lintegral_add_right _ (measurable_const.indicator measurableSet_Iio)]
    _ = (∫⁻ t in Ioi 0, G {a | t < Y a}) + ENNReal.ofReal (c * ε) := by rw [hind]

/-! ## One name -/

section Name

variable {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
  [StandardBorelSpace 𝒱] [Nonempty 𝒱] [Fintype Θ] {P : Measure Ω} [IsProbabilityMeasure P]
  {U : Ω → 𝒰} {V : Ω → 𝒱} {μ : Measure 𝒱} {g : Θ → 𝒰 → 𝒱 → ℝ} {sel : 𝒰 → Θ} {p : Θ → ℝ}
  {ref : 𝒰 → Θ} {ε : 𝒰 → ℝ}

/-- The score as a function of `(u, v)`. -/
noncomputable def Esc (g : Θ → 𝒰 → 𝒱 → ℝ) (sel : 𝒰 → Θ) (p : Θ → ℝ) (u : 𝒰) (v : 𝒱) : ℝ :=
  sInf ((fun ϑ => g (sel u) u v / g ϑ u v) '' {ϑ | p ϑ ≤ 1})

omit [StandardBorelSpace 𝒱] [Nonempty 𝒱] [Fintype Θ] [IsProbabilityMeasure P] [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱] in
theorem eval_eq (ω : Ω) : Eval U V g sel p ω = Esc g sel p (U ω) (V ω) := rfl

/-- The reference conditional law `G u`. -/
noncomputable def Gref (μ : Measure 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ) (ref : 𝒰 → Θ) (u : 𝒰) : Measure 𝒱 :=
  μ.withDensity fun v => ENNReal.ofReal (g (ref u) u v)

omit [StandardBorelSpace 𝒱] [Nonempty 𝒱] [Fintype Θ] [IsProbabilityMeasure P] in
theorem gref_prob (hM : CatalogueModel U V μ g sel) (u : 𝒰) :
    IsProbabilityMeasure (Gref μ g ref u) :=
  ⟨by rw [Gref, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hM.norm]⟩

omit [StandardBorelSpace 𝒱] [Nonempty 𝒱] [IsProbabilityMeasure P] in
theorem esc_facts (hM : CatalogueModel U V μ g sel) (hnull : ∀ u, p (ref u) ≤ 1) :
    Measurable (Function.uncurry (Esc g sel p)) ∧ (∀ u v, 0 < Esc g sel p u v) ∧
      ∀ u v, Esc g sel p u v ≤ g (sel u) u v / g (ref u) u v := by
  classical
  set N : Finset Θ := Finset.univ.filter fun ϑ => p ϑ ≤ 1
  have hNset : (N : Set Θ) = {ϑ | p ϑ ≤ 1} := by ext; simp [N]
  have hmem : ∀ u, ref u ∈ N := fun u => by simp [N, hnull u]
  have hEq : ∀ u v (hne : N.Nonempty), Esc g sel p u v =
      N.inf' hne fun ϑ => g (sel u) u v / g ϑ u v := fun u v hne => by
    simp only [Esc]; rw [Finset.inf'_eq_csInf_image, hNset]
  have hrat : ∀ ϑ, Measurable fun x : 𝒰 × 𝒱 => g (sel x.1) x.1 x.2 / g ϑ x.1 x.2 := fun ϑ =>
    (Novel.SplitLikelihood.measurable_selected hM.measg hM.measSel).div (hM.measg ϑ)
  refine ⟨?_, fun u v => ?_, fun u v => ?_⟩
  · rcases isEmpty_or_nonempty 𝒰 with h | ⟨⟨u0⟩⟩
    · exact fun s _ => by
        have : (Function.uncurry (Esc g sel p)) ⁻¹' s = ∅ := by
          ext ⟨u, _⟩; exact (h.false u).elim
        rw [this]; exact MeasurableSet.empty
    · have hne : N.Nonempty := ⟨_, hmem u0⟩
      have : Function.uncurry (Esc g sel p) = N.inf' hne fun ϑ x => g (sel x.1) x.1 x.2 / g ϑ x.1 x.2 := by
        funext x
        show Esc g sel p x.1 x.2 = _
        rw [hEq x.1 x.2 hne, Finset.inf'_apply]
      rw [this]
      exact Finset.inf'_induction hne _ (fun _ hf _ hg => hf.inf hg) fun ϑ _ => hrat ϑ
  · have hne : N.Nonempty := ⟨_, hmem u⟩
    obtain ⟨ϑ, -, he⟩ := Finset.exists_mem_eq_inf' hne fun ϑ => g (sel u) u v / g ϑ u v
    rw [hEq u v hne, he]; exact div_pos (hM.pos _ _ _) (hM.pos _ _ _)
  · have hne : N.Nonempty := ⟨_, hmem u⟩
    rw [hEq u v hne]; exact Finset.inf'_le _ (hmem u)

omit [StandardBorelSpace 𝒱] [Nonempty 𝒱] [Fintype Θ] [IsProbabilityMeasure P] in
/-- The split-density cancellation under the reference at one `u`. -/
theorem ref_moment (hM : CatalogueModel U V μ g sel) (u : 𝒰) :
    ∫⁻ v, ENNReal.ofReal (g (sel u) u v / g (ref u) u v) ∂(Gref μ g ref u) = 1 := by
  have h1 : Measurable fun v => ENNReal.ofReal (g (ref u) u v) :=
    ENNReal.measurable_ofReal.comp ((hM.measg _).comp measurable_prodMk_left)
  have h2 : Measurable fun v => ENNReal.ofReal (g (sel u) u v / g (ref u) u v) :=
    ENNReal.measurable_ofReal.comp (((hM.measg _).comp measurable_prodMk_left).div
      ((hM.measg _).comp measurable_prodMk_left))
  rw [Gref, lintegral_withDensity_eq_lintegral_mul _ h1 h2, ← hM.norm (sel u) u]
  refine lintegral_congr fun v => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (hM.pos _ u v).le, mul_div_cancel₀ _ (hM.pos _ u v).ne']

omit [StandardBorelSpace 𝒱] [Nonempty 𝒱] in
/-- Markov under the reference: `G u {E > 1/α} ≤ α`. -/
theorem ref_markov (hM : CatalogueModel U V μ g sel) (hnull : ∀ u, p (ref u) ≤ 1) (u : 𝒰)
    {α : ℝ} (hα : 0 < α) : Gref μ g ref u {v | 1 / α < Esc g sel p u v} ≤ ENNReal.ofReal α := by
  have hE := esc_facts hM hnull
  have hm : Measurable fun v => ENNReal.ofReal (Esc g sel p u v) :=
    ENNReal.measurable_ofReal.comp (hE.1.comp measurable_prodMk_left)
  have hpos : (0 : ℝ) < 1 / α := one_div_pos.2 hα
  have hsub : {v | 1 / α < Esc g sel p u v} ⊆
      {v | ENNReal.ofReal (1 / α) ≤ ENNReal.ofReal (Esc g sel p u v)} := fun v hv =>
    ENNReal.ofReal_le_ofReal (le_of_lt hv)
  have hmom : ∫⁻ v, ENNReal.ofReal (Esc g sel p u v) ∂(Gref μ g ref u) ≤ 1 :=
    (lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hE.2.2 u v)).trans (ref_moment hM u).le
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div hm.aemeasurable
    (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top).trans ?_)
  refine (ENNReal.div_le_div_right hmom _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos hpos]
  congr 1; field_simp

omit [Fintype Θ] in
/-- Disintegration of the actual law, for a jointly measurable nonnegative function. -/
theorem disint (hM : CatalogueModel U V μ g sel) {F : 𝒰 × 𝒱 → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (U ω, V ω) ∂P = ∫⁻ u, ∫⁻ v, F (u, v) ∂(condDistrib V U P u) ∂(P.map U) := by
  have hUV : Measurable fun ω => (U ω, V ω) := hM.measU.prodMk hM.measV
  rw [← lintegral_map hF hUV, ← compProd_map_condDistrib hM.measU.aemeasurable
    hM.measV.aemeasurable, Measure.lintegral_compProd hF]

/-- (2) for one name. -/
theorem part1_one (hM : CatalogueModel U V μ g sel) (hR : NullRef P U V μ g p ref ε) {α : ℝ}
    (hα : 0 < α) :
    P.real {ω | 1 / α < Eval U V g sel p ω} ≤ α + ∫ ω, ε (U ω) ∂P := by
  have hE := esc_facts hM hR.null
  set S : Set (𝒰 × 𝒱) := {x | 1 / α < Esc g sel p x.1 x.2}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hE.1
  have hP : P {ω | 1 / α < Eval U V g sel p ω} = ∫⁻ u, condDistrib V U P u (Prod.mk u ⁻¹' S)
      ∂(P.map U) := by
    have h := disint (P := P) hM (measurable_const.indicator hS : Measurable (S.indicator 1))
    have h2 : ∫⁻ ω, S.indicator (1 : 𝒰 × 𝒱 → ℝ≥0∞) (U ω, V ω) ∂P =
        P {ω | 1 / α < Eval U V g sel p ω} := by
      have hmeas : MeasurableSet {ω | 1 / α < Eval U V g sel p ω} :=
        measurableSet_lt measurable_const (hE.1.comp (hM.measU.prodMk hM.measV))
      rw [← lintegral_indicator_one hmeas]
      rfl
    rw [← h2, h]
    refine lintegral_congr fun u => ?_
    show ∫⁻ v, (Prod.mk u ⁻¹' S).indicator 1 v ∂_ = _
    rw [lintegral_indicator_one (measurable_prodMk_left hS)]
  have hεi : Integrable (fun u => ε u) (P.map U) :=
    Integrable.of_bound (C := 1) hR.measε.aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hR.ε_nonneg u)]; exact hR.ε_le_one u)
  have hbound : ∀ᵐ u ∂(P.map U), condDistrib V U P u (Prod.mk u ⁻¹' S) ≤
      ENNReal.ofReal (α + ε u) := by
    filter_upwards [hR.env] with u hu
    have := gref_prob (ref := ref) hM u
    have hSu : MeasurableSet (Prod.mk u ⁻¹' S) := measurable_prodMk_left hS
    have hu' : |(condDistrib V U P u).real (Prod.mk u ⁻¹' S) -
        (Gref μ g ref u).real (Prod.mk u ⁻¹' S)| ≤ ε u := hu _ hSu
    have h1 := ofReal_le_add (hR.ε_nonneg u) (by linarith [(abs_le.1 hu').2] :
      (condDistrib V U P u).real (Prod.mk u ⁻¹' S) ≤ (Gref μ g ref u).real (Prod.mk u ⁻¹' S) +
        ε u)
    refine h1.trans ?_
    rw [ENNReal.ofReal_add hα.le (hR.ε_nonneg u)]
    exact add_le_add (ref_markov hM hR.null u hα) le_rfl
  have hlin : ∫⁻ u, ENNReal.ofReal (α + ε u) ∂(P.map U) =
      ENNReal.ofReal (α + ∫ ω, ε (U ω) ∂P) := by
    have hmU : Measurable U := hM.measU
    have := (Measure.isProbabilityMeasure_map_iff hmU.aemeasurable).2 ‹_›
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun u => α + ε u)
      ((integrable_const α).add hεi)
      (Eventually.of_forall fun u => add_nonneg hα.le (hR.ε_nonneg u)),
      integral_add (integrable_const α) hεi, integral_const, integral_map hmU.aemeasurable
      hR.measε.aestronglyMeasurable]
    simp
  rw [measureReal_def, hP]
  refine ENNReal.toReal_le_of_le_ofReal
    (add_nonneg hα.le (integral_nonneg fun ω => hR.ε_nonneg _)) ?_
  rw [← hlin]
  exact lintegral_mono_ae hbound

omit [StandardBorelSpace 𝒱] [Nonempty 𝒱] [Fintype Θ] [IsProbabilityMeasure P] [MeasurableSpace Ω]
  [MeasurableSpace 𝒰] [MeasurableSpace 𝒱] in
/-- Claim 051's band rule implies null exclusion, with no premise on the truth. -/
theorem band_sub [Finite Θ] (hnull : ∀ u, p (ref u) ≤ 1) {α R r : ℝ} {σ : Θ → ℝ → ℝ} (hR : 0 < R)
    (hr : 1 < r) (hσ : ∀ ϑ, ∃ κ : ℝ, 0 < κ ∧ ∀ x, R ≤ x → σ ϑ x = κ * x ^ p ϑ) (ω : Ω)
    (hb : Hi (Cset U V g sel α ω) (fun ϑ => B2 R r (σ ϑ)) <
      Lo (Cset U V g sel α ω) (fun ϑ => B1 R r (σ ϑ))) :
    1 / α < Eval U V g sel p ω := by
  have hall : ∀ ϑ, p ϑ ≤ 1 → 1 / α < Tstat U V g sel ϑ ω := fun ϑ hϑ => by
    by_contra hle
    have hc : ϑ ∈ Cset U V g sel α ω := not_lt.1 hle
    have h0 := Novel.D3CatalogueCalibration.null_order hR hr (hσ ϑ) hϑ
    have h1 := Novel.D3CatalogueCalibration.Lo_le (f := fun ϑ => B1 R r (σ ϑ)) hc
    have h2 := Novel.D3CatalogueCalibration.le_Hi (f := fun ϑ => B2 R r (σ ϑ)) hc
    linarith
  obtain ⟨ϑ, hϑ, he⟩ := Novel.D3CatalogueCalibration.Lo_mem
    (f := fun ϑ => Tstat U V g sel ϑ ω) (C := {ϑ | p ϑ ≤ 1}) ⟨ref (U ω), hnull _⟩
  have : Eval U V g sel p ω = Tstat U V g sel ϑ ω := he.symm
  rw [this]; exact hall ϑ hϑ

theorem part1 (hM : CatalogueModel U V μ g sel) (hR : NullRef P U V μ g p ref ε) {α : ℝ}
    (hα : 0 < α) (_hα1 : α < 1) :
    P.real {ω | 1 / α < Eval U V g sel p ω} ≤ min 1 (α + ∫ ω, ε (U ω) ∂P) ∧
    (∀ R : Set Ω, R ⊆ {ω | 1 / α < Eval U V g sel p ω} →
      P.real R ≤ min 1 (α + ∫ ω, ε (U ω) ∂P)) ∧
    (∀ e : ℝ, (∀ u, ε u ≤ e) → e < α →
      P.real {ω | 1 / (α - e) < Eval U V g sel p ω} ≤ α) := by
  have h1 := le_min measureReal_le_one (part1_one hM hR hα)
  refine ⟨h1, fun R hR' => (measureReal_mono hR').trans h1, fun e he heα => ?_⟩
  have hb := part1_one hM hR (α := α - e) (by linarith)
  have hint : ∫ ω, ε (U ω) ∂P ≤ e := by
    calc ∫ ω, ε (U ω) ∂P ≤ ∫ _ω, e ∂P := integral_mono_of_nonneg
          (Eventually.of_forall fun ω => hR.ε_nonneg _) (integrable_const e)
          (Eventually.of_forall fun ω => he _)
      _ = e := by simp
  linarith

omit [StandardBorelSpace 𝒱] [Nonempty 𝒱] [Fintype Θ] [IsProbabilityMeasure P] [MeasurableSpace Ω]
  [MeasurableSpace 𝒰] [MeasurableSpace 𝒱] in
theorem erob_eq (c : ℝ) (ω : Ω) : Erob U V g sel p ε c ω =
    min (Esc g sel p (U ω) (V ω)) c / (1 + c * ε (U ω)) := rfl

theorem part2 (hM : CatalogueModel U V μ g sel) (hR : NullRef P U V μ g p ref ε) {c : ℝ}
    (hc : 0 < c) :
    Measurable (Erob U V g sel p ε c) ∧ (∀ ω, 0 ≤ Erob U V g sel p ε c ω) ∧
    (∀ ω, Erob U V g sel p ε c ω ≤ Eval U V g sel p ω) ∧
    ∫⁻ ω, ENNReal.ofReal (Erob U V g sel p ε c ω) ∂P ≤ 1 ∧
    ∀ α : ℝ, 0 < α → ∀ ω, 1 / α < Erob U V g sel p ε c ω →
      ε (U ω) < α ∧ 1 / (α - ε (U ω)) < c := by
  have hE := esc_facts hM hR.null
  have hden : ∀ u, 1 ≤ 1 + c * ε u := fun u => by nlinarith [hR.ε_nonneg u]
  set F : 𝒰 × 𝒱 → ℝ := fun x => min (Esc g sel p x.1 x.2) c / (1 + c * ε x.1)
  have hF : Measurable F :=
    (hE.1.min measurable_const).div (measurable_const.add (measurable_const.mul
      (hR.measε.comp measurable_fst)))
  have hF0 : ∀ x, 0 ≤ F x := fun x =>
    div_nonneg (le_min (hE.2.1 _ _).le hc.le) (zero_le_one.trans (hden _))
  have hErob : Erob U V g sel p ε c = fun ω => F (U ω, V ω) := rfl
  refine ⟨by rw [hErob]; exact hF.comp (hM.measU.prodMk hM.measV), fun ω => hF0 (U ω, V ω),
    fun ω => ?_, ?_, fun α hα ω h => ?_⟩
  · rw [erob_eq, eval_eq]
    exact (div_le_self (le_min (hE.2.1 _ _).le hc.le) (hden _)).trans (min_le_left _ _)
  · show ∫⁻ ω, ENNReal.ofReal (F (U ω, V ω)) ∂P ≤ 1
    rw [disint (P := P) (F := fun x => ENNReal.ofReal (F x)) hM (ENNReal.measurable_ofReal.comp hF)]
    have hmU := (Measure.isProbabilityMeasure_map_iff hM.measU.aemeasurable).2 ‹IsProbabilityMeasure P›
    calc ∫⁻ u, ∫⁻ v, ENNReal.ofReal (F (u, v)) ∂(condDistrib V U P u) ∂(P.map U)
        ≤ ∫⁻ _u, 1 ∂(P.map U) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hR.env] with u hu
          have := gref_prob (ref := ref) hM u
          set Y : 𝒱 → ℝ := fun v => min (Esc g sel p u v) c
          have hY : Measurable Y := (hE.1.comp measurable_prodMk_left).min measurable_const
          have hYG : ∫⁻ v, ENNReal.ofReal (Y v) ∂(Gref μ g ref u) ≤ 1 :=
            (lintegral_mono fun v => ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans
              (hE.2.2 u v))).trans (ref_moment hM u).le
          have htv := lintegral_le_tv (H := condDistrib V U P u) (G := Gref μ g ref u) hY
            (fun v => le_min (hE.2.1 _ _).le hc.le) (fun v => min_le_right _ _) hc.le
            (hR.ε_nonneg u) (fun A hA => hu A hA)
          have hd : 0 < 1 + c * ε u := zero_lt_one.trans_le (hden u)
          have hsplit : ∀ v, ENNReal.ofReal (F (u, v)) =
              ENNReal.ofReal (1 / (1 + c * ε u)) * ENNReal.ofReal (Y v) := fun v => by
            rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; simp only [F, Y]; ring
          simp_rw [hsplit]
          rw [lintegral_const_mul (ENNReal.ofReal (1 / (1 + c * ε u)))
            (f := fun v => ENNReal.ofReal (Y v)) (ENNReal.measurable_ofReal.comp hY)]
          calc ENNReal.ofReal (1 / (1 + c * ε u)) * ∫⁻ v, ENNReal.ofReal (Y v) ∂condDistrib V U P u
              ≤ ENNReal.ofReal (1 / (1 + c * ε u)) * ENNReal.ofReal (1 + c * ε u) := by
                gcongr
                refine htv.trans ?_
                rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hc.le (hR.ε_nonneg u)),
                  ENNReal.ofReal_one]
                gcongr
            _ = 1 := by
                rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hd.ne',
                  ENNReal.ofReal_one]
      _ = 1 := by rw [lintegral_const, one_mul]; exact measure_univ
  · -- The cap condition (5).
    rw [erob_eq] at h
    have hd : 0 < 1 + c * ε (U ω) := zero_lt_one.trans_le (hden _)
    have hcap : 1 / α < c / (1 + c * ε (U ω)) :=
      h.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) hd.le)
    rw [div_lt_div_iff₀ hα hd, one_mul] at hcap
    have hεα : ε (U ω) < α := by
      by_contra hn; push Not at hn; nlinarith [hR.ε_nonneg (U ω)]
    refine ⟨hεα, ?_⟩
    rw [div_lt_iff₀ (sub_pos.2 hεα)]; nlinarith

end Name

/-! ## The statement -/

open Classical in
theorem statement_holds : Standalone.D14Misspecification.statement := by
  refine ⟨fun P _ U V μ g sel p ref ε α hM hR hα hα1 => part1 hM hR hα hα1,
    fun P _ U V μ g sel p ref ε α R r σ hM hR hα hα1 hR0 hr hσ =>
      ⟨fun ω hb => band_sub hR.null hR0 hr hσ ω hb,
        (part1 hM hR hα hα1).2.1 _ fun ω hb => band_sub hR.null hR0 hr hσ ω hb⟩, ?_,
    fun P _ U V μ g sel p ref ε c hM hR hc => part2 hM hR hc,
    fun h53 _ _ _ _ _ P _ Er N₀ q hq hq1 hm hnn hnull => ⟨h53 P Er N₀ q hq hq1 hm hnn hnull,
      fun S hS => h53 P (fun i ω => if i ∈ S ω then Er i ω else 0) N₀ q hq hq1
        (fun i => Measurable.ite (hS i) (hm i) measurable_const)
        (fun i ω => by split_ifs; exacts [hnn i ω, le_rfl])
        fun i hi => (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (by
          split_ifs; exacts [le_rfl, hnn i ω])).trans (hnull i hi)⟩,
    fun p e hp he hpe => ?_, fun e he he1 => ?_, fun α e hα hα1 he hemin => ?_,
    fun P Pref _ _ η R _ h => ?_, Novel.D14Gaussian.part3_holds⟩
  · -- The union bound.
    intro ι Ω _ _ P _ Rj b N₀ hb
    exact le_min measureReal_le_one ((measureReal_biUnion_finset_le N₀ Rj).trans
      (Finset.sum_le_sum hb))
  · have h1 : 1 - p ≠ 0 := by linarith
    field_simp; ring
  · -- Unboundedness as `p ↓ 0`.
    have hinv : Tendsto (fun p : ℝ => e * (1 / (2 * p))) (𝓝[>] 0) atTop := by
      have : Tendsto (fun p : ℝ => p⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
      have h2 := (this.const_mul_atTop (by positivity : (0 : ℝ) < e / 2))
      refine h2.congr fun p => ?_
      field_simp
    have hcont : Tendsto (fun p : ℝ => 1 - e * (1 / (2 * (1 - p)))) (𝓝[>] 0)
        (𝓝 (1 - e * (1 / (2 * (1 - 0))))) := by
      have hca : ContinuousAt (fun p : ℝ => 1 - e * (1 / (2 * (1 - p)))) 0 :=
        continuousAt_const.sub (continuousAt_const.mul (continuousAt_const.div
          (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)) (by norm_num)))
      exact hca.tendsto.mono_left nhdsWithin_le_nhds
    exact (hcont.add_atTop hinv).congr fun p => by ring
  · -- The size example.
    have hea : e < α := lt_of_lt_of_le hemin (min_le_left _ _)
    have he1 : e < 1 - α := lt_of_lt_of_le hemin (min_le_right _ _)
    simp only
    refine ⟨by linarith, by linarith, ?_, ?_, by linarith, by ring⟩
    · rw [div_lt_div_iff₀ hα (by linarith)]
      have : (1 - e / (4 * α)) * α = α - e / 4 := by field_simp
      linarith
    · rw [div_lt_div_iff₀ (by linarith) hα]
      have : e / (4 * α) * α = e / 4 := by field_simp
      linarith
  · -- (10).
    obtain ⟨h1, h2⟩ := abs_le.1 h
    exact ⟨max_le measureReal_nonneg (by linarith), le_min measureReal_le_one (by linarith)⟩

end Novel.D14Misspecification
