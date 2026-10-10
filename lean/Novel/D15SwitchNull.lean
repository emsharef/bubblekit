import Novel.D15SwitchProfileProof
import Novel.D13CEVCatalogueProof

/-!
# Claim 059: the zero-residual arrays are `μ_CEV^m`-null

A segment with zero residual has equal rates `R_j/Δ_j` on its increments. So two of its indices
`i < l` satisfy `R_i Δ_l = R_l Δ_i`. With the other coordinates fixed, this equation determines the
price `y_l` uniquely, since `R_l = log(y_l/y_{l−1})` and `R_i` does not involve `y_l`. Each section
along coordinate `l` is therefore at most one positive point, which has `μ_CEV`-measure zero. Fubini
(`measurePreserving_piFinSuccAbove`, `Measure.prod_apply_symm`) makes the set null. The arrays where
(5) is infinite lie in finitely many such sets.
-/

open MeasureTheory Set Real
open scoped ENNReal

namespace Novel.D15SwitchNull

open Standalone.CEVSupport Standalone.D13DriftNull Standalone.D15Switch

theorem muCEV_singleton {x : NNR} (hx : 0 < (x : ℝ)) : muCEV {x} = 0 := by
  rw [muCEV, Measure.add_apply, Measure.dirac_apply' _ (measurableSet_singleton x)]
  have hz : zero ∉ ({x} : Set NNR) := fun h => by
    rw [mem_singleton_iff] at h; rw [← h] at hx; exact lt_irrefl _ hx
  rw [indicator_of_notMem hz, add_zero, lebNN,
    (MeasurableEmbedding.subtype_coe (measurableSet_le measurable_const measurable_id)).comap_apply]
  simp

/-- `prev` depends only on earlier coordinates. -/
theorem prev_congr {n : ℕ} {y0 : ℝ} {y y' : Fin n → ℝ} (j : Fin n)
    (h : ∀ p : Fin n, (p : ℕ) < j → y p = y' p) : prev y0 y j = prev y0 y' j := by
  unfold prev
  by_cases hj : (j : ℕ) = 0
  · have : j.castSucc = (0 : Fin (n + 1)) := Fin.ext (by simp [hj])
    rw [this, Fin.cons_zero, Fin.cons_zero]
  · have : j.castSucc = (⟨j - 1, by omega⟩ : Fin n).succ := Fin.ext (by simp; omega)
    rw [this, Fin.cons_succ, Fin.cons_succ]
    exact h _ (by simp; omega)

/-- One pair of increments `i < l` with equal rates is a `μ_CEV`-null set of positive arrays. -/
theorem pair_null {n : ℕ} {Δ : Fin (n + 1) → ℝ} (hΔ : ∀ j, 0 < Δ j) (y0 : ℝ) {i l : Fin (n + 1)}
    (hil : (i : ℕ) < l) :
    (Measure.pi fun _ : Fin (n + 1) => muCEV)
      {v : Fin (n + 1) → NNR | (∀ j, 0 < (v j : ℝ)) ∧
        ret y0 (fun j => (v j : ℝ)) i * Δ l = ret y0 (fun j => (v j : ℝ)) l * Δ i} = 0 := by
  set S := {v : Fin (n + 1) → NNR | (∀ j, 0 < (v j : ℝ)) ∧
    ret y0 (fun j => (v j : ℝ)) i * Δ l = ret y0 (fun j => (v j : ℝ)) l * Δ i} with hSdef
  have hcoe : Measurable fun v : Fin (n + 1) → NNR => fun j => (v j : ℝ) :=
    measurable_pi_iff.2 fun j => measurable_subtype_coe.comp (measurable_pi_apply j)
  have hret : ∀ j, Measurable fun v : Fin (n + 1) → NNR => ret y0 (fun j => (v j : ℝ)) j :=
    fun j => (Novel.D13DriftNull.measurable_ret j).comp (measurable_const.prodMk hcoe)
  have hS : MeasurableSet S := by
    have : S = (⋂ j, {v : Fin (n + 1) → NNR | 0 < (v j : ℝ)}) ∩
        {v | ret y0 (fun j => (v j : ℝ)) i * Δ l = ret y0 (fun j => (v j : ℝ)) l * Δ i} := by
      ext v; simp [hSdef]
    rw [this]
    exact (MeasurableSet.iInter fun j => measurableSet_lt measurable_const
      (measurable_subtype_coe.comp (measurable_pi_apply j))).inter
      (measurableSet_eq_fun ((hret i).mul_const _) ((hret l).mul_const _))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => NNR) l
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => muCEV) l
  have h1 : (Measure.pi fun _ : Fin (n + 1) => muCEV) S =
      (muCEV.prod (Measure.pi fun _ : Fin n => muCEV)) (e.symm ⁻¹' S) := by
    rw [← hmp.measure_preimage (e.symm.measurable hS).nullMeasurableSet]
    congr 1
    ext v
    simp only [mem_preimage]
    rw [show e.symm (e v) = v from e.symm_apply_apply v]
  rw [h1, Measure.prod_apply_symm (e.symm.measurable hS)]
  have hl0 : (l : ℕ) ≠ 0 := by omega
  have h2 : ∀ w : Fin n → NNR, muCEV ((fun x => (x, w)) ⁻¹' (e.symm ⁻¹' S)) = 0 := by
    intro w
    set A := (fun x => (x, w)) ⁻¹' (e.symm ⁻¹' S)
    have hmemA : ∀ x, x ∈ A ↔ Fin.insertNth l x w ∈ S := fun x => Iff.rfl
    -- Two points of the section agree off `l`.
    have hagree : ∀ x x' : NNR, ∀ p : Fin (n + 1), p ≠ l →
        ((Fin.insertNth l x w : Fin (n + 1) → NNR) p : ℝ) =
          ((Fin.insertNth l x' w : Fin (n + 1) → NNR) p : ℝ) := fun x x' p hp => by
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hp
      simp [Fin.insertNth_apply_succAbove]
    have hsub : ∀ x ∈ A, ∀ x' ∈ A, x = x' := by
      intro x hx x' hx'
      rw [hmemA] at hx hx'
      obtain ⟨hpos, heq⟩ := hx
      obtain ⟨hpos', heq'⟩ := hx'
      set Y := fun j => ((Fin.insertNth l x w : Fin (n + 1) → NNR) j : ℝ)
      set Y' := fun j => ((Fin.insertNth l x' w : Fin (n + 1) → NNR) j : ℝ)
      have hlt : ∀ (j : Fin (n + 1)) (p : Fin (n + 1)), (p : ℕ) < j → (j : ℕ) ≤ l → p ≠ l :=
        fun j p hp hj h => by rw [h] at hp; omega
      have hreti : ret y0 Y i = ret y0 Y' i := by
        unfold ret
        rw [prev_congr i (fun p hp => hagree x x' p (hlt i p hp hil.le)),
          show Y i = Y' i from hagree x x' i (fun h => by rw [h] at hil; omega)]
      have hprev : prev y0 Y l = prev y0 Y' l := prev_congr l (fun p hp => hagree x x' p
        (fun h => by rw [h] at hp; omega))
      have hprev_pos : 0 < prev y0 Y l := by
        unfold prev
        have : l.castSucc = (⟨l - 1, by omega⟩ : Fin (n + 1)).succ := Fin.ext (by simp; omega)
        rw [this, Fin.cons_succ]
        exact hpos _
      have hYl : Y l = x := by simp [Y, Fin.insertNth_apply_same]
      have hYl' : Y' l = x' := by simp [Y', Fin.insertNth_apply_same]
      have hrl : ret y0 Y l = ret y0 Y' l := by
        have h := heq.symm.trans (hreti ▸ heq')
        exact mul_right_cancel₀ (hΔ i).ne' h
      unfold ret at hrl
      rw [hYl, hYl', ← hprev] at hrl
      have hx0 : 0 < (x : ℝ) := hYl ▸ hpos l
      have hx0' : 0 < (x' : ℝ) := hYl' ▸ hpos' l
      have := Real.log_injOn_pos (mem_Ioi.2 (div_pos hx0 hprev_pos))
        (mem_Ioi.2 (div_pos hx0' hprev_pos)) hrl
      exact Subtype.ext ((div_left_inj' hprev_pos.ne').1 this)
    by_cases hne : A.Nonempty
    · obtain ⟨x1, hx1⟩ := hne
      have hx1' := (hmemA x1).1 hx1
      have hpos : 0 < (x1 : ℝ) := by
        have := hx1'.1 l
        simpa [Fin.insertNth_apply_same] using this
      exact measure_mono_null (fun x hx => mem_singleton_iff.2 (hsub x hx x1 hx1))
        (muCEV_singleton hpos)
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]
  simp only [h2, lintegral_zero]

/-- A zero-residual segment has equal rates on any two of its increments. -/
theorem pair_of_QH {n : ℕ} {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {y0 : ℝ} {y : Fin n → ℝ}
    {H : Finset (Fin n)} (hQ : QH Δ y0 y H = 0) {i l : Fin n} (hi : i ∈ H) (hl : l ∈ H) :
    ret y0 y i * Δ l = ret y0 y l * Δ i := by
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
    div_nonneg (sq_nonneg _) (hΔ j).le).1 hQ
  have key : ∀ j ∈ H, ret y0 y j = aH Δ y0 y H * Δ j := fun j hj => by
    have h0 := hall j hj
    rw [div_eq_zero_iff, or_iff_left (hΔ j).ne', pow_eq_zero_iff two_ne_zero] at h0
    linarith
  rw [key i hi, key l hl]; ring

/-- The arrays where (5) is infinite form a `μ_CEV^m`-null set. -/
theorem Dsw_top_null {m : ℕ} {Δ : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) {K : Finset ℕ}
    (hK : ∀ c ∈ K, 2 ≤ c ∧ c + 2 ≤ m) (y0 : ℝ) :
    (Measure.pi fun _ : Fin m => muCEV) {v | Dsw Δ K y0 (fun l => (v l : ℝ)) = ⊤} = 0 := by
  classical
  rcases K.eq_empty_or_nonempty with hK0 | ⟨c0, hc0⟩
  · have : {v : Fin m → NNR | Dsw Δ K y0 (fun l => (v l : ℝ)) = ⊤} = ∅ := by
      ext v
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      unfold Dsw
      rw [hK0]
      split_ifs <;> simp
    rw [this, measure_empty]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := hK c0 hc0; omega⟩
  -- The pair sets.
  set S : ℕ → ℕ → Set (Fin (n + 1) → NNR) := fun i l => if h : i < l ∧ l < n + 1 then
    {v | (∀ j, 0 < (v j : ℝ)) ∧ ret y0 (fun j => (v j : ℝ)) ⟨i, by omega⟩ * Δ ⟨l, h.2⟩ =
      ret y0 (fun j => (v j : ℝ)) ⟨l, h.2⟩ * Δ ⟨i, by omega⟩} else ∅ with hSdef
  have hSnull : ∀ i l, (Measure.pi fun _ : Fin (n + 1) => muCEV) (S i l) = 0 := fun i l => by
    simp only [hSdef]
    split_ifs with h
    · exact pair_null hΔ y0 (i := ⟨i, by omega⟩) (l := ⟨l, h.2⟩) h.1
    · exact measure_empty
  have hsub : {v : Fin (n + 1) → NNR | Dsw Δ K y0 (fun l => (v l : ℝ)) = ⊤} ⊆
      ⋃ c ∈ (K : Set ℕ), (S 0 1 ∪ S c (c + 1)) := by
    intro v hv
    simp only [mem_ofPred_eq] at hv
    by_cases hp : PosPath y0 (fun l => (v l : ℝ))
    · have hnot : ¬ ∀ c ∈ K, 0 < QH Δ y0 (fun l => (v l : ℝ)) (segL c) ∧
          0 < QH Δ y0 (fun l => (v l : ℝ)) (segR c) := fun h =>
        (((Novel.D15Switch.finite_iff (K := K) hp).2).2 h).ne hv
      push Not at hnot
      obtain ⟨c, hc, hcQ⟩ := hnot
      have hcK := hK c hc
      simp only [mem_iUnion]
      refine ⟨c, hc, ?_⟩
      by_cases hL : 0 < QH Δ y0 (fun l => (v l : ℝ)) (segL c)
      · -- The right segment has zero residual: increments `c` and `c + 1`.
        have hQ : QH Δ y0 (fun l => (v l : ℝ)) (segR c) = 0 :=
          le_antisymm (hcQ hL) (Novel.D15Switch.QH_nonneg hΔ _)
        right
        have h : c < c + 1 ∧ c + 1 < n + 1 := ⟨by omega, by omega⟩
        simp only [hSdef, h, and_self, dite_true]
        refine ⟨hp.2, pair_of_QH hΔ hQ ?_ ?_⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp⟩
      · -- The left segment has zero residual: increments `0` and `1`.
        have hQ : QH Δ y0 (fun l => (v l : ℝ)) (segL c) = 0 :=
          le_antisymm (not_lt.1 hL) (Novel.D15Switch.QH_nonneg hΔ _)
        left
        have h : 0 < 1 ∧ 1 < n + 1 := ⟨by omega, by omega⟩
        simp only [hSdef, h, and_self, dite_true]
        refine ⟨hp.2, pair_of_QH hΔ hQ ?_ ?_⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp; omega⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp; omega⟩
    · exfalso
      unfold Dsw at hv
      simp only [hp, ↓reduceIte] at hv
      split_ifs at hv <;> simp at hv
  refine measure_mono_null hsub ((measure_biUnion_null_iff (K.countable_toSet)).2 fun c _ =>
    measure_union_null (hSnull 0 1) (hSnull c (c + 1)))

end Novel.D15SwitchNull
