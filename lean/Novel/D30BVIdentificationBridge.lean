import Upstream.SemimartingaleQV
import Novel.D30BVIdentificationIdent

/-!
# Claim 071: AX-13 from its Upstream structures

* `qv_fv`: Proposition 6.25 with no martingale part, proved pathwise. A continuous path of bounded
  variation has `Σ (ΔF)² ≤ max |ΔF| · V(F)`, and `max |ΔF| → 0` as the mesh does, by uniform
  continuity on `[0, T]`; almost-sure convergence then gives convergence in measure.
* `ax13_of_upstream`: the restated `AX13` follows from `Upstream.SemimartingaleQV` (the Brownian
  integral plus finite variation) and `qv_fv`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D30BVIdentification

open Standalone.D30BVIdentification

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

theorem part_chain {t : ℝ≥0} {m : ℕ} {p : ℕ → ℝ≥0} (hp : IsPartition t m p) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ m → p i ≤ p j := by
  intro i j hij hjm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => exact le_rfl
  | succ d ih => exact (ih (by omega) (by omega)).trans (hp.2.2 _ (by omega))

theorem part_le {t : ℝ≥0} {m : ℕ} {p : ℕ → ℝ≥0} (hp : IsPartition t m p) {i : ℕ} (hi : i ≤ m) :
    p i ≤ t := hp.2.1 ▸ part_chain hp hi le_rfl

/-- The squared increments of a continuous path of bounded variation tend to zero. -/
theorem sqSum_tendsto_zero {g : ℝ≥0 → ℝ} {T t : ℝ≥0} (ht : t ≤ T) (hg : Continuous g)
    (hbv : BoundedVariationOn g (Icc 0 T)) {m : ℕ → ℕ} {p : ℕ → ℕ → ℝ≥0}
    (hp : ∀ k, IsPartition t (m k) (p k)) (hmesh : Tendsto (fun k => mesh (m k) (p k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∑ i ∈ Finset.range (m k), (g (p k (i + 1)) - g (p k i)) ^ 2) atTop (𝓝 0) := by
  set V := (eVariationOn g (Icc 0 T)).toReal
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hmem : ∀ k i, i ≤ m k → p k i ∈ Icc 0 T := fun k i hi => ⟨zero_le, (part_le (hp k) hi).trans ht⟩
  -- The variation bound on each partition.
  have hsum : ∀ k, ∑ i ∈ Finset.range (m k), |g (p k (i + 1)) - g (p k i)| ≤ V := fun k => by
    set u : ℕ → ℝ≥0 := fun i => p k (min i (m k))
    have hu : Monotone u := fun i j hij => part_chain (hp k) (min_le_min_right _ hij) (min_le_right _ _)
    have hs := eVariationOn.sum_le (f := g) (n := m k) hu fun i => hmem k _ (min_le_right _ _)
    have he : ∑ i ∈ Finset.range (m k), edist (g (u (i + 1))) (g (u i)) =
        ENNReal.ofReal (∑ i ∈ Finset.range (m k), |g (p k (i + 1)) - g (p k i)|) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      simp only [u, min_eq_left (show i + 1 ≤ m k by omega), min_eq_left hi'.le, edist_dist,
        Real.dist_eq]
    rw [he] at hs
    exact (ENNReal.ofReal_le_iff_le_toReal hbv).1 hs
  -- Uniform continuity.
  have huc := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).uniformContinuousOn_of_continuous
    hg.continuousOn
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / (V + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hmesh.eventually (Iio_mem_nhds (Real.toNNReal_pos.2 hδ)))
  refine ⟨N, fun k hk => ?_⟩
  have hstep : ∀ i ∈ Finset.range (m k), |g (p k (i + 1)) - g (p k i)| < η := fun i hi => by
    have hi' := Finset.mem_range.1 hi
    have hle := (hp k).2.2 i hi'
    have hmesh_i : p k (i + 1) - p k i ≤ mesh (m k) (p k) :=
      Finset.le_sup (f := fun i => p k (i + 1) - p k i) hi
    have hlt : p k (i + 1) - p k i < δ.toNNReal := lt_of_le_of_lt hmesh_i (hN k hk)
    have hd : dist (p k (i + 1)) (p k i) < δ := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hle)),
        ← NNReal.coe_sub hle]
      exact (Real.lt_toNNReal_iff_coe_lt).1 hlt
    have := hδc _ (hmem k _ (by omega)) _ (hmem k _ hi'.le) hd
    rwa [Real.dist_eq] at this
  have hnn : 0 ≤ ∑ i ∈ Finset.range (m k), (g (p k (i + 1)) - g (p k i)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  calc ∑ i ∈ Finset.range (m k), (g (p k (i + 1)) - g (p k i)) ^ 2
      ≤ ∑ i ∈ Finset.range (m k), η * |g (p k (i + 1)) - g (p k i)| :=
        Finset.sum_le_sum fun i hi => by
          rw [← sq_abs, sq]
          exact mul_le_mul_of_nonneg_right (hstep i hi).le (abs_nonneg _)
    _ = η * ∑ i ∈ Finset.range (m k), |g (p k (i + 1)) - g (p k i)| := by rw [Finset.mul_sum]
    _ ≤ η * V := mul_le_mul_of_nonneg_left (hsum k) hη.le
    _ < ε := by
        simp only [η]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- Proposition 6.25 with no martingale part: `[c + F] = 0` for continuous adapted `F` of finite
variation on `[0, T]`. -/
theorem qv_fv {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ}
    {F Y : ℝ≥0 → Ω → ℝ} {c : ℝ} {T : ℝ≥0} (hF : FVProc 𝓕 T F)
    (hY : ∀ᵐ ω ∂Q, ∀ t ≤ T, Y t ω = c + F t ω) (t : ℝ≥0) (ht : t ≤ T) :
    QVat Q Y t fun _ => 0 := by
  intro m p hp hmesh
  have hae : ∀ k, sqSum F (m k) (p k) =ᵐ[Q] sqSum Y (m k) (p k) := fun k => hY.mono fun ω h => by
    unfold sqSum
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [h _ ((part_le (hp k) (by omega)).trans ht), h _ ((part_le (hp k) hi'.le).trans ht)]
    ring
  have hFm : ∀ s, Measurable (F s) := fun s => (hF.1 s).mono (𝓕.le s) le_rfl
  have hmeas : ∀ k, AEStronglyMeasurable (sqSum F (m k) (p k)) Q := fun k =>
    (Finset.measurable_sum _ fun i _ => ((hFm _).sub (hFm _)).pow_const 2).aestronglyMeasurable
  have hpt : ∀ ω, Tendsto (fun k => sqSum F (m k) (p k) ω) atTop (𝓝 0) := fun ω =>
    sqSum_tendsto_zero ht (hF.2.1 ω) (hF.2.2.2 ω) hp hmesh
  exact (tendstoInMeasure_of_tendsto_ae hmeas (ae_of_all _ hpt)).congr_left hae

/-- The restated AX-13 from its Upstream structure and `qv_fv`. -/
theorem ax13_of_upstream {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {P : Upstream.StochasticIntegration.Primitives Q 𝓕} (h : Upstream.SemimartingaleQV P) :
    AX13 Q 𝓕 P.Integral :=
  ⟨fun W K I F Y c T hW hU hK hsq hI hF hY t ht =>
    h.qv_integral W K I F Y c T hW hU hK hsq hI hF hY t ht,
    fun F Y c T hQ hF hY t ht => qv_fv hF hY t ht⟩

end Novel.D30BVIdentification
