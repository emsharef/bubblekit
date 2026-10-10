import Novel.D32RecoveryEstimatorTools

/-!
# Claim 044, part 2: histogram coverage (6) with random cell counts

On the training law `H^N`, fix a cell `j` and a name `i`. For each set `S` of indices, the event
`E_S` that exactly the pairs in `S` fall in cell `j` is a box. Conditioned on it, the pairs are
independent with laws `H(· | C_j)` on `S` (`pi_cond`), so the cell mean of `U_i` deviates from
`m̄_(i,j) = E_H[U_i | Y ∈ C_j]` by more than `√(log(2dJ/δ)/(2|S|))` with conditional probability at
most `δ/(dJ)` (`hoeffding_two`). Summing over `S` bounds the cell failure by `δ/(dJ)`; a union over
cells and names bounds the total by `δ`. Off these events and two null events, the bias
`|m̄_(i,j) − m_i(x)| ≤ L h` (17) gives (6); an empty cell gives radius one.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D32RecoveryEstimator

open Standalone.D32RecoveryEstimator

variable {d J N : ℕ}

/-! ## Cells -/

/-- The indices in cell `j`. -/
noncomputable def cellIdx (C : Fin J → Set ℝ) (z : Fin N → ℝ × (Fin d → ℝ)) (j : Fin J) :
    Finset (Fin N) :=
  open Classical in Finset.univ.filter fun r => (z r).1 ∈ C j

theorem count_eq (C : Fin J → Set ℝ) (z : Fin N → ℝ × (Fin d → ℝ)) (j : Fin J) :
    count C z j = (cellIdx C z j).card := rfl

theorem mem_cellIdx {C : Fin J → Set ℝ} {z : Fin N → ℝ × (Fin d → ℝ)} {j : Fin J} {r : Fin N} :
    r ∈ cellIdx C z j ↔ (z r).1 ∈ C j := by
  unfold cellIdx; simp

/-- The cell mean of name `i`. -/
noncomputable def cellMean (C : Fin J → Set ℝ) (z : Fin N → ℝ × (Fin d → ℝ)) (j : Fin J)
    (i : Fin d) : ℝ :=
  (∑ r ∈ cellIdx C z j, (z r).2 i) / (cellIdx C z j).card

theorem cellVal_pos {C : Fin J → Set ℝ} {ω : Fin d → ℝ} {z : Fin N → ℝ × (Fin d → ℝ)} {j : Fin J}
    (h : 0 < count C z j) : cellVal C ω z j = fun i => cellMean C z j i := by
  unfold cellVal; rw [ite_eq_left h]; rfl

theorem cellVal_zero {C : Fin J → Set ℝ} {ω : Fin d → ℝ} {z : Fin N → ℝ × (Fin d → ℝ)} {j : Fin J}
    (h : count C z j = 0) : cellVal C ω z j = ω := by
  unfold cellVal; rw [ite_eq_right (by omega)]

theorem histFit_cell {C : Fin J → Set ℝ} (hdisj : Pairwise (Function.onFun Disjoint C))
    (ω : Fin d → ℝ) (z : Fin N → ℝ × (Fin d → ℝ)) {x : ℝ} {j : Fin J} (hx : x ∈ C j) :
    histFit C ω N z x = cellVal C ω z j := by
  classical
  unfold histFit
  rw [ite_eq_left (mem_iUnion.2 ⟨j, hx⟩), Finset.sum_eq_single j]
  · exact Set.indicator_of_mem hx _
  · intro k _ hk
    exact Set.indicator_of_notMem (Set.disjoint_left.1 (hdisj hk.symm) hx) _
  · simp

/-! ## The bias (17) -/

/-- The fiber of cell `j` in the pair space. -/
def cellSet (C : Fin J → Set ℝ) (j : Fin J) : Set (ℝ × (Fin d → ℝ)) := Prod.fst ⁻¹' C j

/-- `m̄_(i,j) = E_H[U_i | Y ∈ C_j]`. -/
noncomputable def mbar (H : Measure (ℝ × (Fin d → ℝ))) (C : Fin J → Set ℝ) (j : Fin J) (i : Fin d) :
    ℝ :=
  ∫ p, p.2 i ∂(H[|cellSet C j])

theorem bias {H : Measure (ℝ × (Fin d → ℝ))} {ν : Measure ℝ} {I0 : ℝ} {ω : Fin d → ℝ}
    {m : Fin d → ℝ → ℝ} (hc : Contract H ν I0 ω m) {B : Set ℝ} {C : Fin J → Set ℝ} {h L : ℝ}
    (hP : Partition B C h) (hL : LipOn m B L) (hL0 : 0 ≤ L) {j : Fin J}
    (h0 : H (cellSet C j) ≠ 0) (i : Fin d) {x : ℝ} (hx : x ∈ C j) :
    |mbar H C j i - m i x| ≤ L * h := by
  have := hc.probH
  have : IsProbabilityMeasure (PI H) := by unfold PI; infer_instance
  have hCB : C j ⊆ B := hP.cover ▸ subset_iUnion C j
  have hmeasC : MeasurableSet (cellSet (d := d) C j) := measurable_fst (hP.meas j)
  have hPI : PI H (C j) = H (Prod.fst ⁻¹' C j) := Measure.map_apply measurable_fst (hP.meas j)
  set p := (PI H (C j)).toReal
  have hp0 : 0 < p := ENNReal.toReal_pos (hPI ▸ h0) (measure_ne_top _ _)
  have hmi : ∀ y, 0 ≤ m i y ∧ m i y ≤ 1 := fun y =>
    ⟨(hc.msimplex y).1 i, by
      have h := (hc.msimplex y).2
      have := Finset.single_le_sum (fun k _ => (hc.msimplex y).1 k) (Finset.mem_univ i)
      linarith⟩
  have hint : IntegrableOn (m i) (C j) (PI H) :=
    (Integrable.of_mem_Icc 0 1 (hc.mmeas i).aemeasurable (Eventually.of_forall fun y => hmi y)).integrableOn
  have hmbar : mbar H C j i = (∫ y in C j, m i y ∂(PI H)) / p := by
    unfold mbar
    rw [ProbabilityTheory.cond, integral_smul_measure, show cellSet C j = Prod.fst ⁻¹' C j from rfl,
      hc.mcond i (C j) (hP.meas j), ← hPI, ENNReal.toReal_inv, smul_eq_mul, inv_mul_eq_div]
  have hconst : m i x = (∫ _y in C j, m i x ∂(PI H)) / p := by
    rw [setIntegral_const, smul_eq_mul, show (PI H).real (C j) = p from rfl]
    field_simp
  rw [hmbar, hconst, ← sub_div, ← integral_sub hint (integrable_const _), abs_div,
    abs_of_pos hp0, div_le_iff₀ hp0]
  have hbd : ∀ y ∈ C j, ‖m i y - m i x‖ ≤ L * h := fun y hy => by
    rw [Real.norm_eq_abs]
    exact (hL i y (hCB hy) x (hCB hx)).trans (mul_le_mul_of_nonneg_left (hP.diam j y hy x hx) hL0)
  have := norm_setIntegral_le_of_norm_le_const (measure_lt_top (PI H) (C j)) hbd
  rw [Real.norm_eq_abs] at this
  calc |∫ y in C j, (m i y - m i x) ∂(PI H)| ≤ L * h * (PI H).real (C j) := this
    _ = L * h * p := rfl

/-! ## One cell and one name -/

/-- `√(log(2dJ/δ)/(2n))`. -/
noncomputable def tN (d J : ℕ) (δ : ℝ) (n : ℕ) : ℝ := Real.sqrt (Real.log (2 * d * J / δ) / (2 * n))

/-- The cell failure: occupied, and the cell mean misses `m̄` by more than the radius. -/
def badCell (H : Measure (ℝ × (Fin d → ℝ))) (C : Fin J → Set ℝ) (δ : ℝ) (j : Fin J) (i : Fin d) :
    Set (Fin N → ℝ × (Fin d → ℝ)) :=
  {z | 0 < count C z j ∧ tN d J δ (count C z j) < |cellMean C z j i - mbar H C j i|}

/-- Exactly the indices in `S` fall in cell `j`. -/
def ES (C : Fin J → Set ℝ) (j : Fin J) (S : Finset (Fin N)) : Set (Fin N → ℝ × (Fin d → ℝ)) :=
  {z | cellIdx C z j = S}

theorem ES_eq (C : Fin J → Set ℝ) (j : Fin J) (S : Finset (Fin N)) :
    ES (d := d) C j S = Set.univ.pi fun r => if r ∈ S then cellSet C j else (cellSet C j)ᶜ := by
  ext z
  simp only [ES, mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies]
  constructor
  · rintro rfl r
    by_cases hr : r ∈ cellIdx C z j
    · rw [ite_eq_left hr]; exact mem_cellIdx.1 hr
    · rw [ite_eq_right hr]; exact fun h => hr (mem_cellIdx.2 h)
  · intro h
    ext r
    rw [mem_cellIdx]
    by_cases hr : r ∈ S
    · have := h r; rw [ite_eq_left hr] at this; exact ⟨fun _ => hr, fun _ => this⟩
    · have := h r; rw [ite_eq_right hr] at this; exact ⟨fun h' => absurd h' this, fun h' => absurd h' hr⟩

theorem measurableSet_ES {C : Fin J → Set ℝ} (hC : ∀ j, MeasurableSet (C j)) (j : Fin J)
    (S : Finset (Fin N)) : MeasurableSet (ES (d := d) C j S) := by
  rw [ES_eq]
  exact MeasurableSet.univ_pi fun r => by
    split_ifs
    · exact measurable_fst (hC j)
    · exact (measurable_fst (hC j)).compl

theorem log_pos' {d J : ℕ} (hd : 0 < d) (hJ : 0 < J) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.log (2 * d * J / δ) := by
  apply Real.log_pos
  rw [one_lt_div hδ]
  have : (1 : ℝ) ≤ d := Nat.one_le_cast.2 hd
  have : (1 : ℝ) ≤ J := Nat.one_le_cast.2 hJ
  nlinarith

theorem two_exp_tN {d J : ℕ} (hd : 0 < d) (hJ : 0 < J) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {n : ℕ}
    (hn : 0 < n) : 2 * Real.exp (-2 * n * tN d J δ n ^ 2 / 1 ^ 2) = δ / (d * J) := by
  have hlog := log_pos' hd hJ hδ hδ1
  unfold tN
  rw [Real.sq_sqrt (by positivity)]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [show -2 * (n : ℝ) * (Real.log (2 * d * J / δ) / (2 * n)) / 1 ^ 2 = -Real.log (2 * d * J / δ) by
    field_simp, Real.exp_neg, Real.exp_log (by positivity)]
  have : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have : (0 : ℝ) < J := Nat.cast_pos.2 hJ
  field_simp

theorem cell_bound {H : Measure (ℝ × (Fin d → ℝ))} {ν : Measure ℝ} {I0 : ℝ} {ω : Fin d → ℝ}
    {m : Fin d → ℝ → ℝ} (hc : Contract H ν I0 ω m) {C : Fin J → Set ℝ}
    (hC : ∀ j, MeasurableSet (C j)) (hJ : 0 < J) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (j : Fin J)
    (i : Fin d) (S : Finset (Fin N)) :
    (Measure.pi fun _ : Fin N => H) (badCell H C δ j i ∩ ES C j S) ≤
      ENNReal.ofReal (δ / (d * J)) * (Measure.pi fun _ : Fin N => H) (ES C j S) := by
  have := hc.probH
  have hd : 0 < d := Fin.pos i
  set π := Measure.pi fun _ : Fin N => H
  set D : Fin N → Set (ℝ × (Fin d → ℝ)) := fun r => if r ∈ S then cellSet C j else (cellSet C j)ᶜ
  have hDm : ∀ r, MeasurableSet (D r) := fun r => by
    simp only [D]; split_ifs
    · exact measurable_fst (hC j)
    · exact (measurable_fst (hC j)).compl
  have hES : ES C j S = Set.univ.pi D := ES_eq C j S
  rcases Finset.eq_empty_or_nonempty S with rfl | hS
  · -- An empty cell is never a failure.
    have : badCell H C δ j i ∩ ES C j (∅ : Finset (Fin N)) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun z ⟨⟨h1, _⟩, h2⟩ => ?_
      simp only [ES, mem_ofPred_eq] at h2
      rw [count_eq, h2] at h1
      simp at h1
    rw [this, measure_empty]; exact zero_le
  by_cases h0 : π (ES C j S) = 0
  · rw [h0, mul_zero]; exact le_of_eq (measure_mono_null inter_subset_right h0)
  have hD0 : ∀ r, H (D r) ≠ 0 := by
    intro r hr
    apply h0
    rw [hES, Measure.pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ r) hr
  have : ∀ r, IsProbabilityMeasure (H[|D r]) := fun r => cond_isProbabilityMeasure (hD0 r)
  set π' := Measure.pi fun r => H[|D r]
  have hcond : π[|ES C j S] = π' := by rw [hES]; exact pi_cond _ hDm hD0
  -- The failure inside `E_S`, under the conditional product.
  set n := S.card
  have hn : 0 < n := hS.card_pos
  have hsub : badCell H C δ j i ∩ ES C j S ⊆
      {z | tN d J δ n < |(∑ r ∈ S, (z r).2 i) / S.card - mbar H C j i|} := by
    rintro z ⟨⟨_, h2⟩, h3⟩
    simp only [ES, mem_ofPred_eq] at h3
    simp only [mem_ofPred_eq]
    rw [count_eq, h3] at h2
    unfold cellMean at h2
    rw [h3] at h2
    exact h2
  have hjS : ∀ r ∈ S, D r = cellSet C j := fun r hr => by simp only [D, hr, ↓reduceIte]
  have hevalr : ∀ r, π'.map (fun z => z r) = H[|D r] := fun r =>
    (measurePreserving_eval (fun r => H[|D r]) r).map_eq
  have hsimp : ∀ r, ∀ᵐ z ∂π', (z r).2 i ∈ Icc 0 (0 + 1) := fun r => by
    have hH : ∀ᵐ p ∂(H[|D r]), p.2 i ∈ Icc (0 : ℝ) (0 + 1) := by
      refine (cond_absolutelyContinuous (s := D r)).ae_le (hc.simplex.mono fun p hp => ?_)
      refine ⟨hp.1 i, ?_⟩
      have := Finset.single_le_sum (fun k _ => hp.1 k) (Finset.mem_univ i)
      rw [hp.2] at this; linarith
    rw [← hevalr r] at hH
    exact ae_of_ae_map (measurable_pi_apply r).aemeasurable hH
  have hmean : ∀ r ∈ S, ∫ z, (z r).2 i ∂π' = mbar H C j i := fun r hr => by
    have e := integral_map (μ := π') (φ := fun z : Fin N → ℝ × (Fin d → ℝ) => z r)
      (f := fun p : ℝ × (Fin d → ℝ) => p.2 i) (measurable_pi_apply r).aemeasurable
      ((measurable_pi_apply i).comp measurable_snd).aestronglyMeasurable
    rw [← e, hevalr r, hjS r hr]
    rfl
  have hind : iIndepFun (fun r (z : Fin N → ℝ × (Fin d → ℝ)) => (z r).2 i) π' :=
    iIndepFun_pi (μ := fun r => H[|D r]) (X := fun (_ : Fin N) (p : ℝ × (Fin d → ℝ)) => p.2 i)
      fun r => ((measurable_pi_apply i).comp measurable_snd).aemeasurable
  have hH := hoeffding_two hS hind (fun r => ((measurable_pi_apply i).comp measurable_snd).comp
    (measurable_pi_apply r)) one_pos (fun r _ => hsimp r) hmean (t := tN d J δ n) (Real.sqrt_nonneg _)
  rw [two_exp_tN hd hJ hδ hδ1 hn] at hH
  calc π (badCell H C δ j i ∩ ES C j S)
      ≤ π (ES C j S ∩ {z | tN d J δ n < |(∑ r ∈ S, (z r).2 i) / S.card - mbar H C j i|}) :=
        measure_mono fun z hz => ⟨hz.2, hsub hz⟩
    _ = π[|ES C j S] {z | tN d J δ n < |(∑ r ∈ S, (z r).2 i) / S.card - mbar H C j i|} *
          π (ES C j S) := (cond_mul_eq_inter (measurableSet_ES hC j S) _ π).symm
    _ ≤ ENNReal.ofReal (δ / (d * J)) * π (ES C j S) := by
        rw [hcond]; gcongr

theorem badCell_le {H : Measure (ℝ × (Fin d → ℝ))} {ν : Measure ℝ} {I0 : ℝ} {ω : Fin d → ℝ}
    {m : Fin d → ℝ → ℝ} (hc : Contract H ν I0 ω m) {C : Fin J → Set ℝ}
    (hC : ∀ j, MeasurableSet (C j)) (hJ : 0 < J) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (j : Fin J)
    (i : Fin d) :
    (Measure.pi fun _ : Fin N => H) (badCell H C δ j i) ≤ ENNReal.ofReal (δ / (d * J)) := by
  have := hc.probH
  set π := Measure.pi fun _ : Fin N => H
  have hcov : badCell H C δ j i ⊆ ⋃ S ∈ (Finset.univ : Finset (Finset (Fin N))),
      badCell H C δ j i ∩ ES C j S := fun z hz =>
    mem_iUnion₂.2 ⟨cellIdx C z j, Finset.mem_univ _, hz, rfl⟩
  have hdisj : (↑(Finset.univ : Finset (Finset (Fin N))) : Set (Finset (Fin N))).PairwiseDisjoint
      (ES (d := d) C j) := fun S _ S' _ h => Set.disjoint_left.2 fun z h1 h2 => h (h1.symm.trans h2)
  have htot : ∑ S ∈ (Finset.univ : Finset (Finset (Fin N))), π (ES C j S) = 1 := by
    rw [← measure_biUnion_finset hdisj fun S _ => measurableSet_ES hC j S]
    have : (⋃ S ∈ (Finset.univ : Finset (Finset (Fin N))), ES (d := d) C j S) = univ :=
      eq_univ_of_forall fun z => mem_iUnion₂.2 ⟨cellIdx C z j, Finset.mem_univ _, rfl⟩
    rw [this, measure_univ]
  calc π (badCell H C δ j i)
      ≤ ∑ S ∈ (Finset.univ : Finset (Finset (Fin N))), π (badCell H C δ j i ∩ ES C j S) :=
        (measure_mono hcov).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset (Fin N))), ENNReal.ofReal (δ / (d * J)) * π (ES C j S) :=
        Finset.sum_le_sum fun S _ => cell_bound hc hC hJ hδ hδ1 j i S
    _ = ENNReal.ofReal (δ / (d * J)) := by rw [← Finset.mul_sum, htot, mul_one]

/-! ## Two null events -/

/-- Some pair has weights outside the simplex. -/
def Zsimp : Set (Fin N → ℝ × (Fin d → ℝ)) := {z | ∃ r, (z r).2 ∉ Simplex d}

/-- An occupied cell of probability zero. -/
def Zcell (H : Measure (ℝ × (Fin d → ℝ))) (C : Fin J → Set ℝ) (j : Fin J) :
    Set (Fin N → ℝ × (Fin d → ℝ)) :=
  {z | 0 < count C z j ∧ H (cellSet C j) = 0}

theorem Zsimp_null {H : Measure (ℝ × (Fin d → ℝ))} {ν : Measure ℝ} {I0 : ℝ} {ω : Fin d → ℝ}
    {m : Fin d → ℝ → ℝ} (hc : Contract H ν I0 ω m) :
    (Measure.pi fun _ : Fin N => H) Zsimp = 0 := by
  have := hc.probH
  have h0 : H {p | p.2 ∉ Simplex d} = 0 := ae_iff.1 hc.simplex
  have : (Zsimp : Set (Fin N → ℝ × (Fin d → ℝ))) =
      ⋃ r, Function.eval r ⁻¹' {p : ℝ × (Fin d → ℝ) | p.2 ∉ Simplex d} := by
    ext z; simp [Zsimp]
  rw [this]
  exact measure_iUnion_null fun r => Measure.pi_eval_preimage_null (μ := fun _ : Fin N => H) h0

theorem Zcell_null {H : Measure (ℝ × (Fin d → ℝ))} [IsProbabilityMeasure H] (C : Fin J → Set ℝ)
    (j : Fin J) : (Measure.pi fun _ : Fin N => H) (Zcell H C j) = 0 := by
  by_cases h : H (cellSet C j) = 0
  · refine measure_mono_null (t := ⋃ r, Function.eval r ⁻¹' cellSet C j) (fun z hz => ?_)
      (measure_iUnion_null fun r => Measure.pi_eval_preimage_null (μ := fun _ : Fin N => H) h)
    obtain ⟨r, hr⟩ := Finset.card_pos.1 (count_eq C z j ▸ hz.1)
    exact mem_iUnion.2 ⟨r, mem_cellIdx.1 hr⟩
  · have : Zcell (N := N) H C j = ∅ := Set.eq_empty_iff_forall_notMem.2 fun z hz => h hz.2
    rw [this, measure_empty]

/-! ## (6) off the failure events -/

theorem unit_of_simplex {w : Fin d → ℝ} (hw : w ∈ Simplex d) (i : Fin d) : 0 ≤ w i ∧ w i ≤ 1 :=
  ⟨hw.1 i, by
    have := Finset.single_le_sum (fun k _ => hw.1 k) (Finset.mem_univ i)
    rw [hw.2] at this; exact this⟩

theorem abs_le_one_of_unit {u v : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) : |u - v| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]

theorem cellVal_unit {C : Fin J → Set ℝ} {ω : Fin d → ℝ} (hω : ω ∈ Simplex d)
    {z : Fin N → ℝ × (Fin d → ℝ)} (hz : z ∉ Zsimp) (j : Fin J) (i : Fin d) :
    0 ≤ cellVal C ω z j i ∧ cellVal C ω z j i ≤ 1 := by
  have hz' : ∀ r, 0 ≤ (z r).2 i ∧ (z r).2 i ≤ 1 := fun r =>
    unit_of_simplex (by by_contra h; exact hz ⟨r, h⟩) i
  by_cases hc : 0 < count C z j
  · rw [cellVal_pos hc]
    unfold cellMean
    have hn : (0 : ℝ) < (cellIdx C z j).card := by rw [← count_eq]; exact_mod_cast hc
    refine ⟨div_nonneg (Finset.sum_nonneg fun r _ => (hz' r).1) hn.le, (div_le_one hn).2 ?_⟩
    calc ∑ r ∈ cellIdx C z j, (z r).2 i ≤ ∑ r ∈ cellIdx C z j, (1 : ℝ) :=
          Finset.sum_le_sum fun r _ => (hz' r).2
      _ = (cellIdx C z j).card := by simp
  · rw [cellVal_zero (by omega)]; exact unit_of_simplex hω i

theorem good {H : Measure (ℝ × (Fin d → ℝ))} {ν : Measure ℝ} {I0 : ℝ} {ω : Fin d → ℝ}
    {m : Fin d → ℝ → ℝ} (hc : Contract H ν I0 ω m) {a R h L δ : ℝ} {C : Fin J → Set ℝ}
    (hP : Partition (Icc a R) C h) (hL : LipOn m (Icc a R) L) (hL0 : 0 ≤ L)
    {z : Fin N → ℝ × (Fin d → ℝ)} (h1 : z ∉ Zsimp) (h2 : ∀ j, z ∉ Zcell H C j)
    (h3 : ∀ j i, z ∉ badCell H C δ j i) (i : Fin d) {x : ℝ} (hx : x ∈ Icc a R) :
    |histFit C ω N z x i - m i x| ≤ eN C z L h δ := by
  classical
  have hω : ω ∈ Simplex d := ⟨fun k => (hc.ωpos k).le, hc.ωsum⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hP.cover.symm ▸ hx : x ∈ ⋃ j, C j)
  rw [histFit_cell hP.disj ω z hj]
  have hm := unit_of_simplex (hc.msimplex x) i
  have h01 := abs_le_one_of_unit (cellVal_unit (C := C) hω h1 j i) hm
  unfold eN
  split_ifs with hz
  · exact h01
  push Not at hz
  have hcj : 0 < count C z j := Nat.pos_of_ne_zero (hz j)
  refine le_min h01 ?_
  rw [cellVal_pos hcj]
  have hH : H (cellSet C j) ≠ 0 := fun h0 => h2 j ⟨hcj, h0⟩
  have hb := bias hc hP hL hL0 hH i hj
  have hdev : |cellMean C z j i - mbar H C j i| ≤ tN d J δ (count C z j) := by
    by_contra hlt; exact h3 j i ⟨hcj, not_le.1 hlt⟩
  have hsup : tN d J δ (count C z j) ≤
      ⨆ k, Real.sqrt (Real.log (2 * d * J / δ) / (2 * count C z k)) :=
    le_ciSup (f := fun k => Real.sqrt (Real.log (2 * d * J / δ) / (2 * count C z k)))
      (Set.finite_range _).bddAbove j
  calc |cellMean C z j i - m i x| ≤ |cellMean C z j i - mbar H C j i| + |mbar H C j i - m i x| :=
        abs_sub_le _ _ _
    _ ≤ L * h + ⨆ k, Real.sqrt (Real.log (2 * d * J / δ) / (2 * count C z k)) := by linarith

theorem coverage_holds : Standalone.D32RecoveryEstimator.coverage := by
  intro d Ω _ P H ν I0 ω m Z X a R h L δ J N C hc hS _ _ hJ _ hL0 hP hL hδ hδ1
  have := hc.probH
  have := hS.prob
  set π := Measure.pi fun _ : Fin N => H
  set Bad : Set (Fin N → ℝ × (Fin d → ℝ)) :=
    Zsimp ∪ (⋃ j, Zcell H C j) ∪ ⋃ j, ⋃ i, badCell H C δ j i
  have hsub : {ωs | ∃ i, ∃ x ∈ Icc a R, eN C (train Z N ωs) L h δ <
      |histFit C ω N (train Z N ωs) x i - m i x|} ⊆ train Z N ⁻¹' Bad := by
    intro ωs ⟨i, x, hx, hlt⟩
    by_contra hn
    simp only [Bad, mem_preimage, mem_union, mem_iUnion, not_or, not_exists] at hn
    exact absurd (good hc hP hL hL0 hn.1.1 hn.1.2 hn.2 i hx) (not_le.2 hlt)
  have hπ : π Bad ≤ ∑ j : Fin J, ∑ i : Fin d, ENNReal.ofReal (δ / (d * J)) := by
    calc π Bad ≤ π Zsimp + π (⋃ j, Zcell H C j) + π (⋃ j, ⋃ i, badCell H C δ j i) :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ 0 + 0 + ∑ j : Fin J, ∑ i : Fin d, π (badCell H C δ j i) := by
          rw [Zsimp_null hc, measure_iUnion_null fun j => Zcell_null C j]
          gcongr
          exact (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun j _ =>
            measure_iUnion_fintype_le _ _)
      _ ≤ _ := by
          rw [zero_add, zero_add]
          exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
            badCell_le hc hP.meas hJ hδ hδ1 j i
  have htot : ∑ j : Fin J, ∑ i : Fin d, ENNReal.ofReal (δ / (d * J)) ≤ ENNReal.ofReal δ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp only [CharP.cast_eq_zero, zero_mul, mul_zero]; exact hδ.le
    · have : (0 : ℝ) < d := Nat.cast_pos.2 hd
      have : (0 : ℝ) < J := Nat.cast_pos.2 hJ
      rw [show (J : ℝ) * (d * (δ / (d * J))) = δ by field_simp]
  calc P _ ≤ P (train Z N ⁻¹' Bad) := measure_mono hsub
    _ ≤ (P.map (train Z N)) Bad := Measure.le_map_apply (measurable_train hS.measZ N).aemeasurable _
    _ = π Bad := by rw [law_train hS]
    _ ≤ ENNReal.ofReal δ := hπ.trans htot

end Novel.D32RecoveryEstimator
