import Standalone.D3CatalogueCalibration
import Novel.D3PowerTailProof
import Novel.SplitLikelihoodProof

/-!
# Claim 051 (D3): proof

Proves `Standalone.D3CatalogueCalibration.statement` (`statement_holds`), conditional on the
restated AX-52 (moment form), and `core_holds` with that premise discharged by formalizer's
`Novel.SplitLikelihood.ax52_holds` (AX-52's moment form proved from Mathlib).

* `markov`: from `E[T(ϑ*)] ≤ 1` (AX-52), Mathlib's Markov inequality (`meas_ge_le_lintegral_div`)
  gives `P(ϑ* ∉ C) ≤ α`.
* `sel_mem`: `T(ϑ̂(U)) = 1 ≤ 1/α`, so every confidence set is nonempty.
* `Lo`/`Hi` of a finite nonempty image are attained (`Set.Nonempty.csInf_mem`), hence positive by
  claim 013's `B1_pos` and `B2_eq`.
* Simultaneous coverage and the compatibility test: the finite union bound
  `measureReal_iUnion_fintype_le`, with no independence across names.
* The null ordering `B₁ ≤ B₂` for `p ≤ 1` is claim 013's `B₂ = r^{2−2p} B₁`.
* `E` is a finite minimum (`Finset.inf'`), so measurable and attained. Markov again gives the
  p-value bound.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D3CatalogueCalibration

open Standalone.D3PowerTail Standalone.D3CatalogueCalibration
open Novel.D3PowerTail (B1_pos B2_eq)

section Name

variable {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
  {U : Ω → 𝒰} {V : Ω → 𝒱} {μ : Measure 𝒱} {g : Θ → 𝒰 → 𝒱 → ℝ} {sel : 𝒰 → Θ}

theorem T_pos (hM : CatalogueModel U V μ g sel) (ϑ : Θ) (ω : Ω) : 0 < Tstat U V g sel ϑ ω :=
  div_pos (hM.pos _ _ _) (hM.pos _ _ _)

theorem sel_mem (hM : CatalogueModel U V μ g sel) {α : ℝ} (hα : 0 < α ∧ α < 1) (ω : Ω) :
    sel (U ω) ∈ Cset U V g sel α ω := by
  show Tstat U V g sel (sel (U ω)) ω ≤ 1 / α
  rw [Tstat, div_self (hM.pos _ _ _).ne']
  rw [le_div_iff₀ hα.1]; linarith

theorem measurable_T [Fintype Θ] (hM : CatalogueModel U V μ g sel) (ϑ : Θ) :
    Measurable (Tstat U V g sel ϑ) := by
  have hnum : Measurable fun ω => g (sel (U ω)) (U ω) (V ω) := by
    have heq : (fun ω => g (sel (U ω)) (U ω) (V ω)) = fun ω =>
        ∑ ϑ' : Θ, (sel ⁻¹' {ϑ'}).indicator (fun _ => (1 : ℝ)) (U ω) * g ϑ' (U ω) (V ω) := by
      funext ω
      rw [Finset.sum_eq_single (sel (U ω))]
      · simp
      · intro b _ hb
        simp [indicator, Ne.symm hb]
      · simp
    rw [heq]
    exact Finset.measurable_sum _ fun ϑ' _ =>
      ((measurable_const.indicator (hM.measSel ϑ')).comp hM.measU).mul
        ((hM.measg ϑ').comp (hM.measU.prodMk hM.measV))
  exact hnum.div ((hM.measg ϑ).comp (hM.measU.prodMk hM.measV))

/-- Markov from the AX-52 moment bound: `P(ϑ ∉ C) ≤ α`. -/
theorem markov [Fintype Θ] {P : Measure Ω} [IsProbabilityMeasure P]
    (hM : CatalogueModel U V μ g sel) {ϑ : Θ} {α : ℝ} (hα : 0 < α ∧ α < 1)
    (hmom : ∫⁻ ω, ENNReal.ofReal (Tstat U V g sel ϑ ω) ∂P ≤ 1) :
    P.real {ω | ϑ ∉ Cset U V g sel α ω} ≤ α := by
  have hm := measurable_T hM ϑ
  have h1 : {ω | ϑ ∉ Cset U V g sel α ω} ⊆
      {ω | ENNReal.ofReal (1 / α) ≤ ENNReal.ofReal (Tstat U V g sel ϑ ω)} := fun ω hω =>
    ENNReal.ofReal_le_ofReal (le_of_lt (not_le.1 hω))
  have hpos : (0 : ℝ) < 1 / α := one_div_pos.2 hα.1
  have h2 := meas_ge_le_lintegral_div (μ := P) (ENNReal.measurable_ofReal.comp hm).aemeasurable
    (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top
  have h3 : P {ω | ϑ ∉ Cset U V g sel α ω} ≤ ENNReal.ofReal α := by
    refine (measure_mono h1).trans (h2.trans ?_)
    refine (ENNReal.div_le_div_right hmom _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos hpos]
    congr 1; field_simp
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hα.1.le h3

theorem measurableSet_mem [Fintype Θ] (hM : CatalogueModel U V μ g sel) (ϑ : Θ) (α : ℝ) :
    MeasurableSet {ω | ϑ ∈ Cset U V g sel α ω} :=
  measurableSet_le (measurable_T hM ϑ) measurable_const

end Name

/-! ## Finite extrema -/

section Extrema

variable {Θ : Type} [Finite Θ] {C : Set Θ} {f : Θ → ℝ}

theorem Lo_mem (hC : C.Nonempty) : Lo C f ∈ f '' C :=
  Set.Nonempty.csInf_mem (hC.image f) ((Set.toFinite C).image f)

theorem Hi_mem (hC : C.Nonempty) : Hi C f ∈ f '' C :=
  Set.Nonempty.csSup_mem (hC.image f) ((Set.toFinite C).image f)

theorem Lo_le {ϑ : Θ} (h : ϑ ∈ C) : Lo C f ≤ f ϑ :=
  csInf_le ((Set.toFinite C).image f).bddBelow ⟨ϑ, h, rfl⟩

theorem le_Hi {ϑ : Θ} (h : ϑ ∈ C) : f ϑ ≤ Hi C f :=
  le_csSup ((Set.toFinite C).image f).bddAbove ⟨ϑ, h, rfl⟩

end Extrema

/-- Under a null (`p ≤ 1`), `B₁ ≤ B₂` (claim 013). -/
theorem null_order {R r p : ℝ} {σ : ℝ → ℝ} (hR : 0 < R) (hr : 1 < r)
    (h : ∃ κ : ℝ, 0 < κ ∧ ∀ x, R ≤ x → σ x = κ * x ^ p) (hp : p ≤ 1) :
    B1 R r σ ≤ B2 R r σ := by
  obtain ⟨κ, hκ, ht⟩ := h
  rw [B2_eq hκ ht hR hr]
  have h1 := B1_pos hκ ht hR hr
  have h2 : 1 ≤ r ^ (2 - 2 * p) := Real.one_le_rpow hr.le (by linarith)
  nlinarith

theorem blocks_pos {R r p : ℝ} {σ : ℝ → ℝ} (hR : 0 < R) (hr : 1 < r)
    (h : ∃ κ : ℝ, 0 < κ ∧ ∀ x, R ≤ x → σ x = κ * x ^ p) : 0 < B1 R r σ ∧ 0 < B2 R r σ := by
  obtain ⟨κ, hκ, ht⟩ := h
  have h1 := B1_pos hκ ht hR hr
  refine ⟨h1, ?_⟩
  rw [B2_eq hκ ht hR hr]
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) h1

/-! ## The statement -/

theorem statement_holds : Standalone.D3CatalogueCalibration.statement := by
  intro h52 ι _ R r Θ _ _ σ p 𝒰 𝒱 _ _ _ _ _ Ω _ P _ U V μ g sel θs α αt hR hr hσ hM hD hα hsum C b1 b2
  -- Per-name coverage from AX-52.
  have hmom : ∀ i, ∫⁻ ω, ENNReal.ofReal (Tstat (U i) (V i) (g i) (sel i) (θs i) ω) ∂P ≤ 1 :=
    fun i => h52 P (U i) (V i) (μ i) (g i) (sel i) (θs i) (hM i) (hD i)
  have hmiss : ∀ i, P.real {ω | θs i ∉ C i ω} ≤ α i := fun i => markov (hM i) (hα i) (hmom i)
  have hne : ∀ i ω, (C i ω).Nonempty := fun i ω => ⟨_, sel_mem (hM i) (hα i) ω⟩
  -- The union of the non-coverage events.
  set Miss : Set Ω := ⋃ i, {ω | θs i ∉ C i ω}
  have hMiss : P.real Miss ≤ αt :=
    (measureReal_iUnion_fintype_le _).trans ((Finset.sum_le_sum fun i _ => hmiss i).trans hsum)
  have hMissm : MeasurableSet Miss :=
    MeasurableSet.iUnion fun i => (measurableSet_mem (hM i) (θs i) (α i)).compl
  have hcov_of : ∀ S : Set Ω, Missᶜ ⊆ S → 1 - αt ≤ P.real S := fun S hS => by
    have h1 : P.real Missᶜ ≤ P.real S := measureReal_mono hS
    rw [probReal_compl_eq_one_sub hMissm] at h1
    linarith
  have hbad_of : ∀ S : Set Ω, S ⊆ Miss → P.real S ≤ αt := fun S hS =>
    (measureReal_mono hS).trans hMiss
  refine ⟨⟨fun i ω => ?_, hcov_of _ fun ω hω => ?_, fun i hnull => ?_⟩, fun q hq => ?_,
    fun i hN => ?_⟩
  · -- Nonempty sets and positive bands.
    obtain ⟨ϑ1, -, e1⟩ := Lo_mem (f := b1 i) (hne i ω)
    obtain ⟨ϑ2, -, e2⟩ := Lo_mem (f := b2 i) (hne i ω)
    obtain ⟨ϑ0, h0⟩ := hne i ω
    refine ⟨hne i ω, ?_, (Lo_le h0).trans (le_Hi h0), ?_, (Lo_le h0).trans (le_Hi h0)⟩
    · rw [← e1]; exact (blocks_pos (hR i) hr (hσ i ϑ1).2).1
    · rw [← e2]; exact (blocks_pos (hR i) hr (hσ i ϑ2).2).2
  · -- Simultaneous coverage.
    simp only [Miss, mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hω
    exact fun i => ⟨⟨Lo_le (hω i), le_Hi (hω i)⟩, ⟨Lo_le (hω i), le_Hi (hω i)⟩⟩
  · -- The per-name band rule.
    refine (measureReal_mono (s₂ := {ω | θs i ∉ C i ω})
      fun ω (hω : Hi (C i ω) (b2 i) < Lo (C i ω) (b1 i)) hin => ?_).trans (hmiss i)
    have := null_order (hR i) hr (hσ i (θs i)).2 hnull
    have h1 := Lo_le (f := b1 i) hin
    have h2 := le_Hi (f := b2 i) hin
    exact absurd hω (not_lt.2 (by simp only [b1, b2] at *; linarith))
  · -- The compatibility test.
    refine hbad_of _ fun ω hω => ?_
    by_contra hno
    simp only [Miss, mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hno
    exact hω ⟨q, fun i => ⟨θs i, hno i, hq i⟩⟩
  · -- e-values and p-values.
    intro E
    set N : Finset (Θ i) := Finset.univ.filter fun ϑ => p i ϑ ≤ 1
    have hNne : N.Nonempty := by
      obtain ⟨ϑ, hϑ⟩ := hN; exact ⟨ϑ, by simp [N, hϑ]⟩
    have hNset : (N : Set (Θ i)) = {ϑ | p i ϑ ≤ 1} := by ext; simp [N]
    have hEq : ∀ ω, E ω = N.inf' hNne fun ϑ => Tstat (U i) (V i) (g i) (sel i) ϑ ω := fun ω => by
      simp only [E, Eval]
      rw [Finset.inf'_eq_csInf_image, hNset]
    have hEmem : ∀ ω, ∃ ϑ, p i ϑ ≤ 1 ∧ E ω = Tstat (U i) (V i) (g i) (sel i) ϑ ω := fun ω => by
      obtain ⟨ϑ, hϑ, he⟩ := Finset.exists_mem_eq_inf' hNne
        (fun ϑ => Tstat (U i) (V i) (g i) (sel i) ϑ ω)
      exact ⟨ϑ, by simpa [N] using hϑ, by rw [hEq, he]⟩
    have hEle : ∀ ω ϑ, p i ϑ ≤ 1 → E ω ≤ Tstat (U i) (V i) (g i) (sel i) ϑ ω := fun ω ϑ hϑ => by
      rw [hEq]; exact Finset.inf'_le _ (by simp [N, hϑ])
    have hEpos : ∀ ω, 0 < E ω := fun ω => by
      obtain ⟨ϑ, -, he⟩ := hEmem ω; rw [he]; exact T_pos (hM i) ϑ ω
    have hEm : Measurable E := by
      have : E = N.inf' hNne fun ϑ => Tstat (U i) (V i) (g i) (sel i) ϑ := by
        funext ω; rw [hEq, Finset.inf'_apply]
      rw [this]
      exact Finset.inf'_induction hNne _ (fun _ hf _ hg => hf.inf hg)
        fun ϑ _ => measurable_T (hM i) ϑ
    have hexcl : ∀ ω, C i ω ∩ {ϑ | p i ϑ ≤ 1} = ∅ ↔ 1 / α i < E ω := fun ω => by
      constructor
      · intro h
        obtain ⟨ϑ, hϑ, he⟩ := hEmem ω
        rw [he]
        by_contra hle
        have : ϑ ∈ C i ω ∩ {ϑ | p i ϑ ≤ 1} := ⟨not_lt.1 hle, hϑ⟩
        rw [h] at this; exact this
      · intro h
        ext ϑ
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        intro hc hϑ
        exact absurd ((hEle ω ϑ hϑ).trans hc) (not_le.2 h)
    refine ⟨hEpos, hEm, fun hnull => ⟨?_, fun a ha0 ha1 => ?_⟩, fun ω => ⟨hexcl ω, ?_⟩,
      fun ω hband => ?_⟩
    · exact (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hEle ω _ hnull)).trans (hmom i)
    · -- The p-value.
      rcases ha1.lt_or_eq with ha1 | rfl
      · rcases ha0.lt_or_eq with ha0 | rfl
        · have hsub : {ω | min 1 (1 / E ω) ≤ a} ⊆
              {ω | ENNReal.ofReal (1 / a) ≤ ENNReal.ofReal (E ω)} := fun ω hω => by
            have hω' : min 1 (1 / E ω) ≤ a := hω
            have h1 : 1 / E ω ≤ a := by
              rcases min_le_iff.1 hω' with h | h
              · linarith
              · exact h
            refine ENNReal.ofReal_le_ofReal ?_
            rw [div_le_iff₀ (hEpos ω)] at h1
            rw [div_le_iff₀ ha0]; linarith
          have hpos : (0 : ℝ) < 1 / a := one_div_pos.2 ha0
          have hmk := meas_ge_le_lintegral_div (μ := P)
            (ENNReal.measurable_ofReal.comp hEm).aemeasurable
            (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top
          have hE1 : ∫⁻ ω, ENNReal.ofReal (E ω) ∂P ≤ 1 :=
            (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hEle ω _ hnull)).trans (hmom i)
          have h3 : P {ω | min 1 (1 / E ω) ≤ a} ≤ ENNReal.ofReal a := by
            refine (measure_mono hsub).trans (hmk.trans ?_)
            refine (ENNReal.div_le_div_right hE1 _).trans (le_of_eq ?_)
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos hpos]
            congr 1; field_simp
          rw [measureReal_def]
          exact ENNReal.toReal_le_of_le_ofReal ha0.le h3
        · have hempty : {ω | min 1 (1 / E ω) ≤ 0} = ∅ := by
            ext ω
            simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
            exact lt_min one_pos (one_div_pos.2 (hEpos ω))
          rw [hempty, measureReal_empty]
      · exact measureReal_le_one
    · -- `1/α < E ↔ min(1, 1/E) < α`.
      have hαi := hα i
      have hE := hEpos ω
      constructor
      · intro h
        refine min_lt_iff.2 (Or.inr ?_)
        rw [div_lt_iff₀ hE]
        rw [div_lt_iff₀ hαi.1] at h
        linarith
      · intro h
        rcases min_lt_iff.1 h with h | h
        · linarith [hαi.2]
        · rw [div_lt_iff₀ hE] at h
          rw [div_lt_iff₀ hαi.1]
          linarith
    · -- The band rule implies exclusion.
      ext ϑ
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hc hϑ
      have := null_order (hR i) hr (hσ i ϑ).2 hϑ
      have h1 := Lo_le (f := b1 i) hc
      have h2 := le_Hi (f := b2 i) hc
      exact absurd hband (not_lt.2 (by simp only [b1, b2] at *; linarith))

/-- Claim 051's conclusions, with AX-52's moment form proved (`ax52_holds`). -/
theorem core_holds : Standalone.D3CatalogueCalibration.core :=
  statement_holds Novel.SplitLikelihood.ax52_holds

end Novel.D3CatalogueCalibration
