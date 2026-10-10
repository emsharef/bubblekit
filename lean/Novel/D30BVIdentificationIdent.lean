import Novel.D30BVIdentificationArray

/-!
# Claim 071, part 1: the continuous-record identity (2)

* Realized quadratic variation is unique almost surely (limits in measure are, along one uniform
  partition sequence), and scales by `κ²` when the process is multiplied by `κ`.
* On `[0, T]`, `L = a_time + βX = a_time + β(M + B)`, so `L ± X = a_time + (β ± 1)(M + B)`. For
  `β ± 1 ≠ 0`, `(L ± X)/(β ± 1)` is a constant plus `M` plus a continuous adapted
  finite-variation process, whose quadratic variation AX-13 gives as `∫ v`; for `β ± 1 = 0`,
  `L ± X` is finite variation, with quadratic variation zero. Polarization gives `β Q(T)`.
* `a_time` enters frozen after `T`, which leaves it unchanged on `[0, T]` and makes it continuous.
* Versions: equality at rational times, then everywhere on `[0, T]` by continuity. The fundamental
  theorem of calculus gives the one-sided derivative `v`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D30BVIdentification

open Standalone.D30BVIdentification Standalone.D9HoldingPeriod Standalone.D3VisitedRange

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-! ### Realized quadratic variation -/

/-- The uniform partition of `[0, t]` into `k + 1` pieces, constant after. -/
noncomputable def uPart (t : ℝ≥0) (k i : ℕ) : ℝ≥0 := t * ((min i (k + 1) : ℕ) : ℝ≥0) / ((k : ℝ≥0) + 1)

theorem uPart_isPartition (t : ℝ≥0) (k : ℕ) : IsPartition t (k + 1) (uPart t k) := by
  refine ⟨by simp [uPart], ?_, fun i _ => ?_⟩
  · simp only [uPart, min_self]
    push_cast
    rw [mul_div_assoc, div_self (by positivity), mul_one]
  · unfold uPart
    gcongr
    first | omega | exact_mod_cast min_le_min_right (k + 1) (Nat.le_succ i)

theorem uPart_step (t : ℝ≥0) (k i : ℕ) : uPart t k (i + 1) - uPart t k i ≤ t / ((k : ℝ≥0) + 1) := by
  rw [tsub_le_iff_right]
  unfold uPart
  rw [← add_div, ← mul_one t]
  rw [mul_one]
  have hk : (0 : ℝ≥0) < (k : ℝ≥0) + 1 := by positivity
  rw [div_le_div_iff_of_pos_right hk]
  have : ((min (i + 1) (k + 1) : ℕ) : ℝ≥0) ≤ 1 + ((min i (k + 1) : ℕ) : ℝ≥0) := by
    have h : min (i + 1) (k + 1) ≤ 1 + min i (k + 1) := by omega
    exact_mod_cast h
  calc t * ((min (i + 1) (k + 1) : ℕ) : ℝ≥0) ≤ t * (1 + ((min i (k + 1) : ℕ) : ℝ≥0)) := by gcongr
    _ = t + t * ((min i (k + 1) : ℕ) : ℝ≥0) := by ring

theorem uPart_mesh (t : ℝ≥0) : Tendsto (fun k => mesh (k + 1) (uPart t k)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun k : ℕ => t * (1 / ((k : ℝ≥0) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).const_mul t
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun k => zero_le)
    fun k => Finset.sup_le fun i _ => ?_
  rw [mul_one_div]
  exact uPart_step t k i

theorem QVat_unique {Q : Measure Ω} {Y : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {q q' : Ω → ℝ}
    (h : QVat Q Y t q) (h' : QVat Q Y t q') : q =ᵐ[Q] q' :=
  tendstoInMeasure_ae_unique (h _ _ (fun k => uPart_isPartition t k) (uPart_mesh t))
    (h' _ _ (fun k => uPart_isPartition t k) (uPart_mesh t))

theorem QVat_smul {Q : Measure Ω} {Z : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {q : Ω → ℝ} (h : QVat Q Z t q)
    (κ : ℝ) : QVat Q (fun t ω => κ * Z t ω) t (fun ω => κ ^ 2 * q ω) := by
  intro m p hp hmesh ε hε
  have hs : ∀ k ω, sqSum (fun t ω => κ * Z t ω) (m k) (p k) ω = κ ^ 2 * sqSum Z (m k) (p k) ω :=
    fun k ω => by
      unfold sqSum
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hs]
  by_cases hκ : κ = 0
  · have : ∀ k, {x | ε ≤ edist (κ ^ 2 * sqSum Z (m k) (p k) x) (κ ^ 2 * q x)} = ∅ := fun k => by
      ext x; simp [hκ, not_le.2 hε]
    simp_rw [this, measure_empty]
    exact tendsto_const_nhds
  · have hκ2 : 0 < κ ^ 2 := by positivity
    have hc0 : ENNReal.ofReal (κ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hκ2).ne'
    refine (h m p hp hmesh (ε / ENNReal.ofReal (κ ^ 2))
      (ENNReal.div_pos hε.ne' ENNReal.ofReal_ne_top)).congr fun k => ?_
    congr 1
    ext ω
    simp only [mem_setOf_eq, edist_dist, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hκ2]
    rw [ENNReal.ofReal_mul hκ2.le, ENNReal.div_le_iff hc0 ENNReal.ofReal_ne_top, mul_comm]

/-! ### Finite variation -/

theorem eVar_add_smul {f g : ℝ≥0 → ℝ} {s : Set ℝ≥0} (c d : ℝ) :
    eVariationOn (fun t => f t + c * g t + d) s ≤
      eVariationOn f s + ENNReal.ofReal |c| * eVariationOn g s := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, us⟩
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) + c * g (u (i + 1)) + d) (f (u i) + c * g (u i) + d)
      ≤ ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) +
          ENNReal.ofReal |c| * edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => by
          simp only [edist_dist, Real.dist_eq]
          rw [← ENNReal.ofReal_mul (abs_nonneg c), ← ENNReal.ofReal_add (abs_nonneg _) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← abs_mul]
          calc |f (u (i + 1)) + c * g (u (i + 1)) + d - (f (u i) + c * g (u i) + d)|
              = |(f (u (i + 1)) - f (u i)) + c * (g (u (i + 1)) - g (u i))| := by ring_nf
            _ ≤ _ := abs_add_le _ _
    _ = ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) +
          ENNReal.ofReal |c| * ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu us) (by gcongr; exact eVariationOn.sum_le hu us)

/-- `a_time` frozen after `T`. -/
noncomputable def aT (a : ℝ → ℝ) (T : ℝ≥0) (t : ℝ≥0) : ℝ := a (min (t : ℝ) T)

theorem aT_eq (a : ℝ → ℝ) {T t : ℝ≥0} (h : t ≤ T) : aT a T t = a t := by
  unfold aT; rw [min_eq_left (by exact_mod_cast h)]

theorem aT_cont {a : ℝ → ℝ} {T : ℝ≥0} (ha : ContinuousOn a (Icc 0 T)) : Continuous (aT a T) :=
  ha.comp_continuous (continuous_subtype_val.min continuous_const) fun t =>
    ⟨le_min t.2 T.2, min_le_right _ _⟩

theorem aT_bv {a : ℝ → ℝ} {T : ℝ≥0} (ha : BoundedVariationOn a (Icc 0 T)) :
    BoundedVariationOn (aT a T) (Icc 0 T) := by
  refine ne_top_of_le_ne_top ha (eVariationOn.comp_le_of_monotoneOn a (fun t : ℝ≥0 => min (t : ℝ) T)
    (fun x _ y _ hxy => min_le_min_right _ (by exact_mod_cast hxy)) fun t _ =>
      ⟨le_min t.2 T.2, min_le_right _ _⟩)

theorem FVProc_comb {𝓕 : Filtration ℝ≥0 mΩ} {T : ℝ≥0} {B : ℝ≥0 → Ω → ℝ} (hB : FVProc 𝓕 T B)
    {g : ℝ≥0 → ℝ} (hg : Continuous g) (hgb : BoundedVariationOn g (Icc 0 T)) (c : ℝ) :
    FVProc 𝓕 T fun t ω => B t ω + c * g t + -(c * g 0) := by
  refine ⟨fun i => ((hB.1 i).add measurable_const).add measurable_const,
    fun ω => ((hB.2.1 ω).add (continuous_const.mul hg)).add continuous_const,
    fun ω => by simp [hB.2.2.1 ω], fun ω => ?_⟩
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hB.2.2.2 ω,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgb⟩) (eVar_add_smul c _)

/-! ### The identity -/

section Ident

variable {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {W M B v : ℝ≥0 → Ω → ℝ} {a : ℝ → ℝ} {T : ℝ≥0}
  (hAX : AX13 Q 𝓕 Integral) (hW : IsFBrownian 𝓕 W Q) (hU : UsualConditions 𝓕 Q)
  (ha : ContinuousOn a (Icc 0 T)) (hab : BoundedVariationOn a (Icc 0 T))
  (hv : ∀ t ω, 0 < v t ω) (hvc : ∀ ω, Continuous fun t => v t ω) (hvp : IsStronglyProgressive 𝓕 v)
  (hM : Integral (fun t ω => Real.sqrt (v t ω)) W M) (hB : FVProc 𝓕 T B)
include hAX hW hU ha hab hv hvc hvp hM hB

omit hAX hW hU ha hab hv hvc hM hB in
theorem sqrt_prog : IsStronglyProgressive 𝓕 fun t ω => Real.sqrt (v t ω) := fun i =>
  Real.continuous_sqrt.comp_stronglyMeasurable (hvp i)

omit hAX hW hU ha hab hvp hM hB in
theorem sq_int : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
    IntegrableOn (fun s : ℝ => Real.sqrt (v s.toNNReal ω) ^ 2) (Ioc 0 (t : ℝ)) :=
  ae_of_all _ fun ω t => by
    simp_rw [Real.sq_sqrt (hv _ ω).le]
    exact ((hvc ω).comp continuous_real_toNNReal).integrableOn_Ioc

/-- Any process equal on `[0, T]` to `a_time + κ(M + B)` has quadratic variation `κ² ∫₀ᵀ v` at `T`. -/
theorem QV_comb (κ : ℝ) {Y : ℝ≥0 → Ω → ℝ}
    (hY : ∀ᵐ ω ∂Q, ∀ t ≤ T, Y t ω = aT a T t + κ * (M t ω + B t ω)) :
    QVat Q Y T fun ω => κ ^ 2 * ∫ s in (0 : ℝ)..(T : ℝ), v s.toNNReal ω := by
  have hP : IsProbabilityMeasure Q := hW.1
  by_cases hκ : κ = 0
  · have hz : FVProc 𝓕 T (fun _ _ => (0 : ℝ)) := ⟨fun i => measurable_const,
      fun _ => continuous_const, fun _ => rfl, fun _ => by
        rw [BoundedVariationOn, eVariationOn.constant_on]
        · exact ENNReal.zero_ne_top
        · exact Set.subsingleton_singleton.anti (Set.image_subset_iff.2 fun _ _ => rfl)⟩
    have hF := FVProc_comb hz (aT_cont ha) (aT_bv hab) 1
    have := hAX.2 _ Y (aT a T 0) T hP hF (hY.mono fun ω h t ht => by
      rw [h t ht, hκ]; ring) T le_rfl
    convert this using 2 with ω
    simp [hκ]
  · have hF := FVProc_comb hB (aT_cont ha) (aT_bv hab) (1 / κ)
    have h1 := hAX.1 W (fun t ω => Real.sqrt (v t ω)) M _ (fun t ω => Y t ω / κ) (aT a T 0 / κ) T
      hW hU (sqrt_prog hvp) (sq_int hv hvc) hM hF
      (hY.mono fun ω h t ht => by rw [h t ht]; field_simp; ring) T le_rfl
    have h2 := QVat_smul h1 κ
    have he : (fun t ω => κ * (Y t ω / κ)) = Y := funext fun t => funext fun ω => by field_simp
    rw [he] at h2
    convert h2 using 2 with ω
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [Real.sq_sqrt (hv _ ω).le]

end Ident

theorem identity_holds : Standalone.D30BVIdentification.identity.{u} := by
  intro Ω mΩ Q 𝓕 Integral W X M B v a β T hAX hW hU hT ha hab hXc hXa hX0 hv hvc hvp hM hB hrep
    L Qv
  have hP : IsProbabilityMeasure Q := hW.1
  -- `[X]`.
  have hQX : ∀ t ≤ T, QVat Q X t (Qv t) := fun t ht => by
    have := hAX.1 W (fun t ω => Real.sqrt (v t ω)) M B X 0 T hW hU
      (sqrt_prog hvp) (sq_int hv hvc) hM hB
      (hrep.mono fun ω h t ht => by rw [(h t ht).1, zero_add]) t ht
    convert this using 2 with ω
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [Real.sq_sqrt (hv _ ω).le]
  -- `L ± X = a_time + (β ± 1)(M + B)` on `[0, T]`.
  have hL : ∀ᵐ ω ∂Q, ∀ t ≤ T, L t ω = aT a T t + β * (M t ω + B t ω) := hrep.mono fun ω h t ht => by
    simp only [L]
    rw [(h t ht).2, Real.log_exp, aT_eq a ht, (h t ht).1]
  have hQp := QV_comb hAX hW hU ha hab hv hvc hvp hM hB (β + 1) (Y := fun t ω => L t ω + X t ω)
    ((hL.and hrep).mono fun ω h t ht => by rw [h.1 t ht, (h.2 t ht).1]; ring)
  have hQm := QV_comb hAX hW hU ha hab hv hvc hvp hM hB (β - 1) (Y := fun t ω => L t ω - X t ω)
    ((hL.and hrep).mono fun ω h t ht => by rw [h.1 t ht, (h.2 t ht).1]; ring)
  refine ⟨hQX, hQp, hQm, fun A qp qm hAc hA hqp hqm => ?_⟩
  -- Rational times, then all of `[0, T]` by continuity.
  have hrat : ∀ᵐ ω ∂Q, ∀ r : ℚ, (r : ℝ) ∈ Ioo 0 (T : ℝ) →
      A (r : ℝ).toNNReal ω = Qv (r : ℝ).toNNReal ω := by
    rw [ae_all_iff]
    intro r
    by_cases hr : (r : ℝ) ∈ Ioo 0 (T : ℝ)
    · have hle : (r : ℝ).toNNReal ≤ T := by
        rw [Real.toNNReal_le_iff_le_coe]; exact hr.2.le
      exact (QVat_unique (hA _ hle) (hQX _ hle)).mono fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hr
  have hpT := QVat_unique hqp hQp
  have hmT := QVat_unique hqm hQm
  filter_upwards [hrat, hpT, hmT] with ω hr hp hm
  have hvcR : Continuous fun s : ℝ => v s.toNNReal ω := (hvc ω).comp continuous_real_toNNReal
  have hQc : Continuous fun s : ℝ => Qv s.toNNReal ω := by
    have : (fun s : ℝ => Qv s.toNNReal ω) = fun s =>
        ∫ r in (0 : ℝ)..(max s 0), v r.toNNReal ω := funext fun s => by simp [Qv, Real.coe_toNNReal']
    rw [this]
    exact (intervalIntegral.continuous_primitive (fun _ _ => hvcR.intervalIntegrable _ _) 0).comp
      (continuous_id.max continuous_const)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hEq : EqOn (fun s : ℝ => A s.toNNReal ω) (fun s => Qv s.toNNReal ω) (Icc 0 T) := by
    refine Set.EqOn.of_subset_closure (s := Ioo 0 (T : ℝ) ∩ range ((↑) : ℚ → ℝ))
      (fun s ⟨hs, r, hrs⟩ => by rw [← hrs] at hs ⊢; exact hr r hs)
      ((hAc ω).comp continuous_real_toNNReal).continuousOn hQc.continuousOn
      (fun s hs => Ioo_subset_Icc_self hs.1) ?_
    calc Icc 0 (T : ℝ) = closure (Ioo 0 (T : ℝ)) := (closure_Ioo hTpos.ne).symm
      _ ⊆ closure (closure (Ioo 0 (T : ℝ) ∩ range ((↑) : ℚ → ℝ))) :=
          closure_mono (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
      _ = _ := closure_closure
  have hAt : ∀ t ≤ T, A t ω = Qv t ω := fun t ht => by
    have := hEq ⟨t.2, by exact_mod_cast ht⟩
    simpa using this
  have hQT : 0 < Qv T ω := intervalIntegral.intervalIntegral_pos_of_pos_on
    (hvcR.intervalIntegrable _ _) (fun s _ => hv _ ω) hTpos
  have hAT : 0 < A T ω := (hAt T le_rfl).symm ▸ hQT
  refine ⟨hAt, hAT, fun t ht => ?_, ?_, ?_⟩
  · have hder : HasDerivWithinAt (fun s : ℝ => A s.toNNReal ω) (v t.toNNReal ω) (Icc 0 T) t := by
      have hF := (intervalIntegral.integral_hasDerivAt_right (hvcR.intervalIntegrable 0 t)
        (hvcR.stronglyMeasurableAtFilter _ _) hvcR.continuousAt).hasDerivWithinAt (s := Icc 0 (T : ℝ))
      refine hF.congr (fun s hs => ?_) ?_
      · have := hEq hs
        simp only at this
        rw [this]; simp [Qv, Real.coe_toNNReal _ hs.1]
      · have := hEq ht
        simp only at this
        rw [this]; simp [Qv, Real.coe_toNNReal _ ht.1]
    refine ⟨hder, ?_⟩
    rw [hder.derivWithin ((uniqueDiffOn_Icc hTpos) t ht)]
  · rw [hp, hm, hAt T le_rfl]; ring
  · rw [hp, hm, hAt T le_rfl]; field_simp; ring

end Novel.D30BVIdentification
