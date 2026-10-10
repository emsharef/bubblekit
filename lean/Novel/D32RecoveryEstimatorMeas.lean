import Novel.D32RecoveryEstimatorCoverage

/-!
# Claim 044: measurability of the histogram and facts about `η_T`

* The histogram fit is jointly measurable in the training data and `x`: its counts and cell sums are
  finite sums of indicators.
* `η_T` is finite with total mass `p_I ≤ 1`, and integrals against it are `ν_T`-integrals with
  weight `x/I₀`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D32RecoveryEstimator

open Standalone.D32RecoveryEstimator

variable {d J N : ℕ}

/-! ## The histogram -/

theorem count_real (C : Fin J → Set ℝ) (z : Fin N → ℝ × (Fin d → ℝ)) (j : Fin J) :
    (count C z j : ℝ) = ∑ r, (Prod.fst ⁻¹' C j).indicator (fun _ => (1 : ℝ)) (z r) := by
  classical
  rw [count_eq, cellIdx, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Set.indicator_apply, mem_preimage]

theorem cellSum_eq (C : Fin J → Set ℝ) (z : Fin N → ℝ × (Fin d → ℝ)) (j : Fin J) (i : Fin d) :
    ∑ r ∈ cellIdx C z j, (z r).2 i =
      ∑ r, (Prod.fst ⁻¹' C j).indicator (fun p : ℝ × (Fin d → ℝ) => p.2 i) (z r) := by
  classical
  rw [cellIdx, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Set.indicator_apply, mem_preimage]

theorem measurable_count {C : Fin J → Set ℝ} (hC : ∀ j, MeasurableSet (C j)) (j : Fin J) :
    Measurable fun z : Fin N → ℝ × (Fin d → ℝ) => (count C z j : ℝ) := by
  simp_rw [count_real]
  exact Finset.measurable_sum _ fun r _ =>
    (measurable_const.indicator (measurable_fst (hC j))).comp (measurable_pi_apply r)

theorem measurableSet_occ {C : Fin J → Set ℝ} (hC : ∀ j, MeasurableSet (C j)) (j : Fin J) :
    MeasurableSet {z : Fin N → ℝ × (Fin d → ℝ) | 0 < count C z j} := by
  have : {z : Fin N → ℝ × (Fin d → ℝ) | 0 < count C z j} =
      {z | (0 : ℝ) < count C z j} := by ext z; simp
  rw [this]; exact measurableSet_lt measurable_const (measurable_count hC j)

theorem measurable_cellVal {C : Fin J → Set ℝ} (hC : ∀ j, MeasurableSet (C j)) (ω : Fin d → ℝ)
    (j : Fin J) : Measurable fun z : Fin N → ℝ × (Fin d → ℝ) => cellVal C ω z j := by
  classical
  unfold cellVal
  refine Measurable.ite (measurableSet_occ hC j) (measurable_pi_iff.2 fun i => ?_) measurable_const
  have : (fun z : Fin N → ℝ × (Fin d → ℝ) => (∑ r ∈ Finset.univ.filter (fun r => (z r).1 ∈ C j),
      (z r).2 i) / count C z j) = fun z => (∑ r, (Prod.fst ⁻¹' C j).indicator
        (fun p : ℝ × (Fin d → ℝ) => p.2 i) (z r)) /
        (count C z j : ℝ) := by
    funext z; rw [← cellSum_eq]; rfl
  rw [this]
  exact (Finset.measurable_sum _ fun r _ => (((measurable_pi_apply i).comp measurable_snd).indicator
    (measurable_fst (hC j))).comp (measurable_pi_apply r)).div (measurable_count hC j)

theorem measurable_histFit {C : Fin J → Set ℝ} (hC : ∀ j, MeasurableSet (C j)) (ω : Fin d → ℝ) :
    Measurable fun p : (Fin N → ℝ × (Fin d → ℝ)) × ℝ => histFit C ω N p.1 p.2 := by
  classical
  unfold histFit
  refine Measurable.ite (measurable_snd (MeasurableSet.iUnion hC)) ?_ measurable_const
  refine Finset.measurable_sum _ fun j _ => ?_
  have : (fun p : (Fin N → ℝ × (Fin d → ℝ)) × ℝ => (C j).indicator (fun _ => cellVal C ω p.1 j) p.2) =
      fun p => if p.2 ∈ C j then cellVal C ω p.1 j else 0 := by
    funext p; simp only [Set.indicator_apply]
  rw [this]
  exact Measurable.ite (measurable_snd (hC j)) ((measurable_cellVal hC ω j).comp measurable_fst)
    measurable_const

theorem histFit_unit {C : Fin J → Set ℝ} (hdisj : Pairwise (Function.onFun Disjoint C))
    {ω : Fin d → ℝ} (hω : ω ∈ Simplex d) {z : Fin N → ℝ × (Fin d → ℝ)} (hz : z ∉ Zsimp) (x : ℝ)
    (i : Fin d) : 0 ≤ histFit C ω N z x i ∧ histFit C ω N z x i ≤ 1 := by
  by_cases hx : x ∈ ⋃ j, C j
  · obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    rw [histFit_cell hdisj ω z hj]; exact cellVal_unit hω hz j i
  · classical
    unfold histFit; rw [ite_eq_right hx]; exact unit_of_simplex hω i

/-! ## `η_T` -/

variable {H : Measure (ℝ × (Fin d → ℝ))} {ν : Measure ℝ} {I0 : ℝ} {ω : Fin d → ℝ}
  {m : Fin d → ℝ → ℝ}

theorem PI_prob (hc : Contract H ν I0 ω m) : IsProbabilityMeasure (PI H) := by
  have := hc.probH; unfold PI; infer_instance

theorem nu_pos (hc : Contract H ν I0 ω m) : ∀ᵐ x ∂ν, 0 < x := by
  have h : ∀ᵐ x ∂(PI H), 0 < x := by
    unfold PI; exact ae_map_iff measurable_fst.aemeasurable (measurableSet_lt measurable_const
      measurable_id) |>.2 hc.pos
  exact hc.acν.ae_le h

theorem eta_eq_smul (hc : Contract H ν I0 ω m) (g : ℝ → ℝ) :
    ∫ x, g x ∂(eta ν I0) = ∫ x, (x / I0) * g x ∂ν := by
  unfold eta
  have : (fun x => ENNReal.ofReal (x / I0)) = fun x => ((x / I0).toNNReal : ℝ≥0∞) := rfl
  rw [this, integral_withDensity_eq_integral_smul
    (Measurable.real_toNNReal (measurable_id'.div_const I0 : Measurable fun x : ℝ => x / I0))]
  refine integral_congr_ae ((nu_pos hc).mono fun x hx => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (div_pos hx hc.I0pos).le]

theorem eta_univ (hc : Contract H ν I0 ω m) : eta ν I0 univ = ENNReal.ofReal (pI ν I0) := by
  have := hc.probν
  have hI : Integrable (fun x : ℝ => x / I0) ν := hc.integ.div_const I0
  unfold eta pI
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI
      ((nu_pos hc).mono fun x hx => (div_pos hx hc.I0pos).le), integral_div]

theorem eta_finite (hc : Contract H ν I0 ω m) : IsFiniteMeasure (eta ν I0) :=
  ⟨by rw [eta_univ hc]; exact ENNReal.ofReal_lt_top⟩

theorem eta_le_one (hc : Contract H ν I0 ω m) (B : Set ℝ) : (eta ν I0).real B ≤ 1 := by
  have := eta_finite hc
  calc (eta ν I0).real B ≤ (eta ν I0).real univ := measureReal_mono (subset_univ B)
    _ = pI ν I0 := by
        rw [Measure.real, eta_univ hc, ENNReal.toReal_ofReal]
        unfold pI
        exact div_nonneg (integral_nonneg_of_ae ((nu_pos hc).mono fun x hx => hx.le)) hc.I0pos.le
    _ ≤ 1 := hc.mass

end Novel.D32RecoveryEstimator
