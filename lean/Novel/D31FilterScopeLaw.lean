import Standalone.D31FilterScope

/-!
# Claim 043, part 1: the law of the filtered return

For a Borel set `B`, `H_a⁻¹(B)` is the retained part `B ∩ {|r| ≤ a}` together with the erased tail
`{|r| > a}` when `0 ∈ B`. The retained part differs from `B ∩ {0 < |r| ≤ a}` by at most the
Lebesgue-null point `0`. So `P(Y ∈ B) = ∫_(B ∩ kept) f + 1_(0∈B) ρ_f(a)`, the `ν_a`-integral of
`f_a` over `B` (`map_Ha`). A strictly positive density charges every set of positive length, so
`0 < ρ_p(a) < 1`, and the atom rules out a Lebesgue density.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Novel.D31FilterScope

open Standalone.D31FilterScope

theorem measurable_Ha (a : ℝ) : Measurable (Ha a) := by
  classical
  unfold Ha
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) measurable_id
    measurable_const

theorem measurableSet_kept (a : ℝ) : MeasurableSet (kept a) :=
  (measurableSet_lt measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)

theorem measurableSet_tail (a : ℝ) : MeasurableSet {r : ℝ | a < |r|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

theorem measurable_fa {f : ℝ → ℝ} (hf : Measurable f) (a : ℝ) : Measurable (fa f a) := by
  classical
  unfold fa
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) hf measurable_const)

theorem tail_ne_top {f : ℝ → ℝ} (hf : IsDensity f) (a : ℝ) :
    ∫⁻ r in {r | a < |r|}, ENNReal.ofReal (f r) ≠ ⊤ :=
  ne_top_of_le_ne_top (hf.2.2 ▸ ENNReal.one_ne_top) (setLIntegral_le_lintegral _ _)

theorem ofReal_rho {f : ℝ → ℝ} (hf : IsDensity f) (a : ℝ) :
    ENNReal.ofReal (rho f a) = ∫⁻ r in {r | a < |r|}, ENNReal.ofReal (f r) := by
  unfold rho; rw [ENNReal.ofReal_toReal (tail_ne_top hf a)]

theorem rho_nonneg (f : ℝ → ℝ) (a : ℝ) : 0 ≤ rho f a := ENNReal.toReal_nonneg

theorem fa_nonneg {f : ℝ → ℝ} (hf : IsDensity f) (a y : ℝ) : 0 ≤ fa f a y := by
  unfold fa; split_ifs
  · exact rho_nonneg f a
  · exact hf.2.1 y
  · exact le_rfl

open Classical in
theorem lintegral_dirac_restrict (g : ℝ → ℝ≥0∞) (B : Set ℝ) (hB : MeasurableSet B) :
    ∫⁻ y in B, g y ∂(Measure.dirac 0) = if (0 : ℝ) ∈ B then g 0 else 0 := by
  classical
  rw [restrict_dirac' hB]
  split_ifs <;> simp

/-- Part 1's pushforward identity. -/
theorem map_Ha {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hf : IsDensity f) :
    (lawOf f).map (Ha a) = (nu a).withDensity (fun y => ENNReal.ofReal (fa f a y)) := by
  classical
  ext B hB
  rw [Measure.map_apply (measurable_Ha a) hB, withDensity_apply _ hB, lawOf,
    withDensity_apply _ ((measurable_Ha a) hB), nu, Measure.restrict_add, lintegral_add_measure,
    Measure.restrict_restrict hB, lintegral_dirac_restrict _ B hB]
  -- The retained part.
  have hkept : ∫⁻ y in B ∩ kept a, ENNReal.ofReal (fa f a y) =
      ∫⁻ r in B ∩ kept a, ENNReal.ofReal (f r) := by
    refine setLIntegral_congr_fun (hB.inter (measurableSet_kept a)) fun y hy => ?_
    have hy0 : y ≠ 0 := fun h => by rw [h] at hy; simp [kept] at hy
    simp only [fa, hy0, ↓reduceIte, if_pos hy.2.2]
  have hret : ∫⁻ r in B ∩ {r | |r| ≤ a}, ENNReal.ofReal (f r) =
      ∫⁻ r in B ∩ kept a, ENNReal.ofReal (f r) := by
    have hsplit : B ∩ {r | |r| ≤ a} = (B ∩ kept a) ∪ (B ∩ {0}) := by
      ext r
      simp only [mem_inter_iff, mem_setOf_eq, kept, mem_union, mem_singleton_iff]
      constructor
      · rintro ⟨hr, hra⟩
        by_cases h0 : r = 0
        · exact Or.inr ⟨hr, h0⟩
        · exact Or.inl ⟨hr, abs_pos.2 h0, hra⟩
      · rintro (⟨hr, -, hra⟩ | ⟨hr, rfl⟩)
        · exact ⟨hr, hra⟩
        · exact ⟨hr, by simp [ha.le]⟩
    rw [hsplit, lintegral_union (hB.inter (measurableSet_singleton 0))
      (Set.disjoint_left.2 fun r h1 h2 => by
        rw [h2.2] at h1; simp [kept] at h1),
      setLIntegral_measure_zero _ _ (measure_mono_null inter_subset_right (Real.volume_singleton)),
      add_zero]
  by_cases h0 : (0 : ℝ) ∈ B
  · have hpre : Ha a ⁻¹' B = (B ∩ {r | |r| ≤ a}) ∪ {r | a < |r|} := by
      ext r
      simp only [mem_preimage, Ha, mem_union, mem_inter_iff, mem_setOf_eq]
      split_ifs with hr
      · exact ⟨fun h => Or.inl ⟨h, hr⟩, fun h => h.elim (fun h => h.1) fun h => absurd hr (not_le.2 h)⟩
      · exact ⟨fun _ => Or.inr (not_le.1 hr), fun _ => h0⟩
    rw [hpre, lintegral_union (measurableSet_tail a)
      (Set.disjoint_left.2 fun r h1 h2 => (not_le.2 (show a < |r| from h2)) (show |r| ≤ a from h1.2)),
      hret, hkept, if_pos h0]
    simp only [fa, ↓reduceIte, ofReal_rho hf]
  · have hpre : Ha a ⁻¹' B = B ∩ {r | |r| ≤ a} := by
      ext r
      simp only [mem_preimage, Ha, mem_inter_iff, mem_setOf_eq]
      split_ifs with hr
      · exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩
      · exact ⟨fun h => absurd h h0, fun h => absurd h.2 hr⟩
    rw [hpre, hret, hkept, if_neg h0, add_zero]

theorem mass_fa {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hf : IsDensity f) :
    ∫⁻ y, ENNReal.ofReal (fa f a y) ∂(nu a) = 1 := by
  have h := congrArg (fun m : Measure ℝ => m univ) (map_Ha ha hf)
  simp only [Measure.map_apply (measurable_Ha a) MeasurableSet.univ, preimage_univ, lawOf,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [← h, hf.2.2]

theorem lawOf_apply_pos {p : ℝ → ℝ} (hpm : Measurable p) (hp : ∀ r, 0 < p r) {s : Set ℝ}
    (hs : MeasurableSet s) (hvs : 0 < volume s) : 0 < lawOf p s := by
  rw [lawOf, withDensity_apply _ hs]
  refine (setLIntegral_pos_iff hpm.ennreal_ofReal).2 ?_
  have : Function.support (fun r => ENNReal.ofReal (p r)) = univ :=
    Function.support_eq_univ fun r => (ENNReal.ofReal_pos.2 (hp r)).ne'
  rw [this, univ_inter]; exact hvs

theorem rho_pos_lt {a : ℝ} (ha : 0 < a) {p : ℝ → ℝ} (hp : IsDensity p) (hpos : ∀ r, 0 < p r) :
    0 < rho p a ∧ rho p a < 1 := by
  have hprob : IsProbabilityMeasure (lawOf p) :=
    ⟨by rw [lawOf, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hp.2.2]⟩
  have htail : lawOf p {r | a < |r|} = ENNReal.ofReal (rho p a) := by
    rw [ofReal_rho hp, lawOf, withDensity_apply _ (measurableSet_tail a)]
  have hv1 : 0 < volume {r : ℝ | a < |r|} :=
    lt_of_lt_of_le (by rw [Real.volume_Ioo]; simp) (measure_mono (s := Ioo a (a + 1))
      fun r hr => by simp only [mem_setOf_eq]; rw [abs_of_pos (ha.trans hr.1)]; exact hr.1)
  have hv2 : 0 < volume ({r : ℝ | a < |r|}ᶜ) :=
    lt_of_lt_of_le (by rw [Real.volume_Ioo]; simp [ha]) (measure_mono (s := Ioo 0 a)
      fun r hr => by
        simp only [mem_compl_iff, mem_setOf_eq, not_lt]; rw [abs_of_pos hr.1]; exact hr.2.le)
  have h1 := lawOf_apply_pos hp.1 hpos (measurableSet_tail a) hv1
  have h2 := lawOf_apply_pos hp.1 hpos (measurableSet_tail a).compl hv2
  rw [prob_compl_eq_one_sub (measurableSet_tail a), htail] at h2
  rw [htail] at h1
  refine ⟨ENNReal.ofReal_pos.1 h1, ?_⟩
  have : ENNReal.ofReal (rho p a) < 1 := by
    by_contra hle
    rw [tsub_eq_zero_of_le (not_lt.1 hle)] at h2
    exact lt_irrefl _ h2
  exact (ENNReal.ofReal_lt_one).1 this

theorem rho_update (p : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (c : ℝ) :
    rho (Function.update p 0 c) a = rho p a := by
  unfold rho
  congr 1
  refine setLIntegral_congr_fun (measurableSet_tail a) fun r hr => ?_
  have : r ≠ 0 := fun h => by rw [h] at hr; simp at hr; linarith
  rw [Function.update_of_ne this]

theorem law_holds : Standalone.D31FilterScope.law := by
  intro a ha
  refine ⟨fun f hf => ⟨map_Ha ha hf, mass_fa ha hf⟩,
    fun P _ R p hp hpos hR hlaw => ?_⟩
  have hmap : P.map (fun ω => Ha a (R ω)) = (nu a).withDensity (fun y => ENNReal.ofReal (fa p a y)) := by
    rw [show (fun ω => Ha a (R ω)) = Ha a ∘ R from rfl, ← Measure.map_map (measurable_Ha a) hR, hlaw,
      map_Ha ha hp]
  have hzero : P {ω | Ha a (R ω) = 0} = ENNReal.ofReal (rho p a) := by
    have := congrArg (fun m : Measure ℝ => m {0}) hmap
    rw [Measure.map_apply (show Measurable (fun ω => Ha a (R ω)) from (measurable_Ha a).comp hR)
      (measurableSet_singleton 0)] at this
    rw [show {ω | Ha a (R ω) = 0} = (fun ω => Ha a (R ω)) ⁻¹' {0} from rfl, this,
      withDensity_apply _ (measurableSet_singleton 0), Measure.restrict_singleton, lintegral_smul_measure,
      lintegral_dirac]
    have hnu : nu a {0} = 1 := by
      simp [nu, Measure.restrict_apply (measurableSet_singleton 0), kept]
    simp [hnu, fa]
  obtain ⟨hρ0, hρ1⟩ := rho_pos_lt ha hp hpos
  have hnac : ¬ P.map (fun ω => Ha a (R ω)) ≪ volume := fun hac => by
    have h0 := hac (Real.volume_singleton (a := 0))
    rw [Measure.map_apply (show Measurable (fun ω => Ha a (R ω)) from (measurable_Ha a).comp hR)
      (measurableSet_singleton 0)] at h0
    have : P {ω | Ha a (R ω) = 0} = 0 := h0
    rw [hzero] at this
    exact (ENNReal.ofReal_pos.2 hρ0).ne' this
  refine ⟨hmap, hzero, hρ0, hρ1, hnac, fun μ v hv h => hnac (h ▸
    gaussianReal_absolutelyContinuous μ hv), fun c => rho_update p ha c⟩

end Novel.D31FilterScope
