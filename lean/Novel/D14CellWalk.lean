import Novel.D14CellEnvelope

/-!
# Claim 029: the path envelope (3)

From any start `x₀ ∈ I_{z₀}`, the label law of the Gaussian walk gives each label vector at most
`∏_j K_j`. The proof is by induction on `n`, peeling off the first increment with
`measurePreserving_piFinSuccAbove` at `0`.
* The first increment lands the walk in `I_{v₁}` with probability at most the one-step envelope.
* Conditionally on that, the rest of the walk starts in `I_{v₁}`, so the induction hypothesis
  applies whatever the exact position.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14CellWalk

open Standalone.D14Cell Novel.GaussianCell Novel.D14CellEnvelope

theorem measurable_label (h : ℝ) : Measurable (label h) :=
  Int.measurable_floor.comp ((measurable_id.div_const h).add_const _)

theorem measurable_labelsW (h : ℝ) : ∀ n : ℕ,
    Measurable fun q : ℝ × (Fin n → ℝ) => labelsW h n q.1 q.2
  | 0 => measurable_of_subsingleton_codomain _
  | n + 1 => by
    have hfirst : Measurable fun q : ℝ × (Fin (n + 1) → ℝ) => q.1 + q.2 0 :=
      measurable_fst.add ((measurable_pi_apply 0).comp measurable_snd)
    have htail : Measurable fun q : ℝ × (Fin (n + 1) → ℝ) => Fin.tail q.2 :=
      measurable_pi_iff.2 fun j => (measurable_pi_apply j.succ).comp measurable_snd
    refine measurable_pi_iff.2 fun j => ?_
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [labelsW, Fin.cons_zero]
      exact (measurable_label h).comp hfirst
    · simp only [labelsW, Fin.cons_succ]
      exact (measurable_pi_apply i).comp ((measurable_labelsW h n).comp (hfirst.prodMk htail))

theorem cons_eq_iff {n : ℕ} (a : ℤ) (v : Fin (n + 1) → ℤ) (c : Fin n → ℤ) :
    (Fin.cons a c : Fin (n + 1) → ℤ) = v ↔ a = v 0 ∧ c = Fin.tail v := by
  constructor
  · rintro rfl; simp
  · rintro ⟨rfl, rfl⟩; exact Fin.cons_self_tail v

theorem Bcell_succ (h : ℝ) {n : ℕ} (μ s : Fin (n + 1) → ℝ) (z₀ : ℤ) (v : Fin (n + 1) → ℤ) :
    Bcell h μ s z₀ v = Kcell h (μ 0) (s 0) z₀ (v 0) *
      Bcell h (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) := by
  unfold Bcell
  rw [Fin.prod_univ_succ]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have e1 : (Fin.cons z₀ v : Fin (n + 2) → ℤ) j.succ.castSucc = v j.castSucc := by
    rw [← Fin.succ_castSucc, Fin.cons_succ]
  have e2 : (Fin.cons (v 0) (Fin.tail v) : Fin (n + 1) → ℤ) j.castSucc = v j.castSucc := by
    rw [Fin.cons_self_tail]
  rw [e1, e2]
  rfl

instance walk_prob (h : ℝ) {n : ℕ} (μ s : Fin n → ℝ) (x₀ : ℝ) :
    IsProbabilityMeasure (walkLaw h μ s x₀) :=
  (Measure.isProbabilityMeasure_map_iff ((measurable_labelsW h n).comp
    (measurable_const.prodMk measurable_id)).aemeasurable).2 inferInstance

/-- (3) along a path, from every exact start in `I_{z₀}`. -/
theorem path_bound {h : ℝ} (hh : 0 < h) : ∀ (n : ℕ) (μ s : Fin n → ℝ), (∀ j, 0 < s j) →
    ∀ (x₀ : ℝ) (z₀ : ℤ) (v : Fin n → ℤ), x₀ ∈ cell h z₀ →
      walkLaw h μ s x₀ {v} ≤ ENNReal.ofReal (Bcell h μ s z₀ v)
  | 0, μ, s, _, x₀, z₀, v, _ => by
    unfold Bcell
    simp only [Finset.univ_eq_empty, Finset.prod_empty, ENNReal.ofReal_one]
    exact prob_le_one
  | n + 1, μ, s, hs, x₀, z₀, v, hx => by
    set g : Fin (n + 1) → Measure ℝ := fun j => gaussianReal (μ j) (s j ^ 2).toNNReal
    have hmeasW : Measurable (labelsW h (n + 1) x₀) :=
      (measurable_labelsW h (n + 1)).comp (measurable_const.prodMk measurable_id)
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hmp := measurePreserving_piFinSuccAbove g 0
    simp only [Fin.succAbove_zero] at hmp
    set T : Set (ℝ × (Fin n → ℝ)) := {p | label h (x₀ + p.1) = v 0 ∧
      labelsW h n (x₀ + p.1) p.2 = Fin.tail v} with hTdef
    have hT : MeasurableSet T := by
      refine (measurableSet_eq_fun ((measurable_label h).comp ((measurable_const (a := x₀)).add measurable_fst))
        measurable_const).inter (measurableSet_eq_fun ?_ measurable_const)
      exact (measurable_labelsW h n).comp (((measurable_const (a := x₀)).add measurable_fst).prodMk measurable_snd)
    have hpre : labelsW h (n + 1) x₀ ⁻¹' {v} = e ⁻¹' T := by
      ext ξ
      simp only [mem_preimage, mem_singleton_iff]
      rw [show labelsW h (n + 1) x₀ ξ = Fin.cons (label h (x₀ + ξ 0))
        (labelsW h n (x₀ + ξ 0) (Fin.tail ξ)) from rfl, cons_eq_iff]
      simp [e, hTdef]
    unfold walkLaw
    rw [Measure.map_apply hmeasW (measurableSet_singleton v), hpre,
      hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply hT]
    -- The tail laws are the walk from the new position.
    set A : Set ℝ := {a : ℝ | label h (x₀ + a) = v 0} with hAdef
    have hA : MeasurableSet A :=
      measurableSet_eq_fun ((measurable_label h).comp ((measurable_const (a := x₀)).add measurable_id))
        measurable_const
    have hsect : ∀ a : ℝ, (Measure.pi fun j : Fin n => g j.succ) (Prod.mk a ⁻¹' T) =
        A.indicator (fun a => walkLaw h (Fin.tail μ) (Fin.tail s) (x₀ + a) {Fin.tail v}) a :=
      fun a => by
        by_cases ha : label h (x₀ + a) = v 0
        · have hset : Prod.mk a ⁻¹' T = labelsW h n (x₀ + a) ⁻¹' {Fin.tail v} := by
            ext w; simp [hTdef, ha]
          rw [hset, indicator_of_mem (show a ∈ A from ha)]
          show _ = ((Measure.pi fun j : Fin n => g j.succ).map (labelsW h n (x₀ + a))) {Fin.tail v}
          have hmW : Measurable (labelsW h n (x₀ + a)) :=
            (measurable_labelsW h n).comp (measurable_const.prodMk measurable_id)
          rw [Measure.map_apply hmW (measurableSet_singleton _)]
        · have hset : Prod.mk a ⁻¹' T = ∅ := by ext w; simp [hTdef, ha]
          rw [hset, measure_empty, indicator_of_notMem (show a ∉ A from ha)]
    simp_rw [hsect]
    have hstep : ∀ a : ℝ, A.indicator (fun a => walkLaw h (Fin.tail μ) (Fin.tail s) (x₀ + a)
        {Fin.tail v}) a ≤
        A.indicator (fun _ => ENNReal.ofReal (Bcell h (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v))) a :=
      fun a => by
        by_cases ha : a ∈ A
        · rw [indicator_of_mem ha, indicator_of_mem ha]
          exact path_bound hh n _ _ (fun j => hs _) (x₀ + a) (v 0) (Fin.tail v)
            ((label_eq_iff hh _ _).1 ha)
        · rw [indicator_of_notMem ha, indicator_of_notMem ha]
    calc ∫⁻ a, A.indicator (fun a => walkLaw h (Fin.tail μ) (Fin.tail s) (x₀ + a) {Fin.tail v}) a
          ∂(g 0)
        ≤ ∫⁻ a, A.indicator
            (fun _ => ENNReal.ofReal (Bcell h (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v))) a
              ∂(g 0) := lintegral_mono hstep
      _ = ENNReal.ofReal (Bcell h (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v)) * g 0 A := by
          rw [lintegral_indicator_const hA]
      _ ≤ ENNReal.ofReal (Bcell h (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v)) *
            ENNReal.ofReal (Kcell h (μ 0) (s 0) z₀ (v 0)) := by
          refine mul_le_mul_right ?_ _
          have hmap : (g 0).map (fun a => x₀ + a) = gaussianReal (x₀ + μ 0) (s 0 ^ 2).toNNReal := by
            simp only [g]; rw [gaussianReal_map_const_add, add_comm]
          have hshift : g 0 A = gaussianReal (x₀ + μ 0) (s 0 ^ 2).toNNReal (cell h (v 0)) := by
            rw [← hmap, cell, Measure.map_apply (measurable_const_add x₀) measurableSet_Ico]
            congr 1
            ext a
            simp only [hAdef, mem_ofPred_eq, mem_preimage]
            exact label_eq_iff hh _ _
          rw [hshift]
          exact one_step_le hh (hs 0) hx
      _ = ENNReal.ofReal (Bcell h μ s z₀ v) := by
          have hB : 0 ≤ Bcell h (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) :=
            Finset.prod_nonneg fun j _ => (Kcell_pos hh (hs _) _ _).le
          rw [← ENNReal.ofReal_mul hB, mul_comm, Bcell_succ]

end Novel.D14CellWalk
