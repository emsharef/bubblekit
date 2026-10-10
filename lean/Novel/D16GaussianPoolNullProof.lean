import Novel.D16GaussianPoolCostProof
import Novel.D15SwitchNull
import Novel.D16GaussianPoolScoreProof

/-!
# Claim 062: the singular arrays are null when `n ≥ m + 1`

* **One linear equation** (`lin_null`). For `a ≠ 0` and a positive endpoint, the positive arrays whose
  log returns satisfy `Σ_j a_j R_j = 0` are `μ_CEV^n`-null. With `l` the last index where `a_l ≠ 0`,
  the equation determines the price `y_l` from the earlier prices. So each section along `y_l` is at
  most one positive point (claim 059's argument).
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace Novel.D16GaussianPoolNull

open Standalone.CEVSupport Standalone.D13DriftNull Novel.D15SwitchNull

theorem lin_null {n : ℕ} {y0 : ℝ} (hy0 : 0 < y0) {a : Fin n → ℝ} (ha : a ≠ 0) :
    (Measure.pi fun _ : Fin n => muCEV)
      {v : Fin n → NNR | (∀ j, 0 < (v j : ℝ)) ∧
        ∑ j, a j * ret y0 (fun j => (v j : ℝ)) j = 0} = 0 := by
  classical
  cases n with
  | zero => exact absurd (funext fun j => j.elim0) ha
  | succ n =>
  set S := {v : Fin (n + 1) → NNR | (∀ j, 0 < (v j : ℝ)) ∧
    ∑ j, a j * ret y0 (fun j => (v j : ℝ)) j = 0} with hSdef
  have hcoe : Measurable fun v : Fin (n + 1) → NNR => fun j => (v j : ℝ) :=
    measurable_pi_iff.2 fun j => measurable_subtype_coe.comp (measurable_pi_apply j)
  have hret : ∀ j, Measurable fun v : Fin (n + 1) → NNR => ret y0 (fun j => (v j : ℝ)) j :=
    fun j => (Novel.D13DriftNull.measurable_ret j).comp (measurable_const.prodMk hcoe)
  have hS : MeasurableSet S := by
    have : S = (⋂ j, {v : Fin (n + 1) → NNR | 0 < (v j : ℝ)}) ∩
        {v | ∑ j, a j * ret y0 (fun j => (v j : ℝ)) j = 0} := by
      ext v; simp [hSdef]
    rw [this]
    exact (MeasurableSet.iInter fun j => measurableSet_lt measurable_const
      (measurable_subtype_coe.comp (measurable_pi_apply j))).inter
      (measurableSet_eq_fun (Finset.measurable_sum _ fun j _ => measurable_const.mul (hret j))
        measurable_const)
  -- The last index with a nonzero coefficient.
  have hne : (Finset.univ.filter fun j => a j ≠ 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact ha (funext fun j => by simpa using h (Finset.mem_univ j))
  set l := (Finset.univ.filter fun j => a j ≠ 0).max' hne
  have hal : a l ≠ 0 := by
    have := Finset.max'_mem _ hne; simpa using this
  have hafter : ∀ j, l < j → a j = 0 := fun j hj => by
    by_contra h
    exact absurd (Finset.le_max' _ j (by simpa using h)) (not_le.2 hj)
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
  have h2 : ∀ w : Fin n → NNR, muCEV ((fun x => (x, w)) ⁻¹' (e.symm ⁻¹' S)) = 0 := by
    intro w
    set A := (fun x => (x, w)) ⁻¹' (e.symm ⁻¹' S)
    have hmemA : ∀ x, x ∈ A ↔ Fin.insertNth l x w ∈ S := fun x => Iff.rfl
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
      -- Returns before `l` agree; returns after `l` have zero coefficient.
      have hbefore : ∀ j, j < l → ret y0 Y j = ret y0 Y' j := fun j hj => by
        unfold ret
        rw [prev_congr j (fun p hp => hagree x x' p (fun h => by
            rw [h] at hp; exact absurd hj (not_lt.2 (Fin.le_iff_val_le_val.2 hp.le)))),
          show Y j = Y' j from hagree x x' j (ne_of_lt hj)]
      have hsplit : ∀ Z : Fin (n + 1) → ℝ, ∑ j, a j * ret y0 Z j =
          ∑ j ∈ Finset.univ.filter (· < l), a j * ret y0 Z j + a l * ret y0 Z l := by
        intro Z
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < l)]
        congr 1
        rw [Finset.sum_eq_single l]
        · intro j hj hjl
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
          rw [hafter j (lt_of_le_of_ne hj (Ne.symm hjl)), zero_mul]
        · intro h; simp at h
      have hsum : ∑ j ∈ Finset.univ.filter (· < l), a j * ret y0 Y j =
          ∑ j ∈ Finset.univ.filter (· < l), a j * ret y0 Y' j :=
        Finset.sum_congr rfl fun j hj => by
          rw [hbefore j (by simpa using hj)]
      have hrl : ret y0 Y l = ret y0 Y' l := by
        have e1 := (hsplit Y).symm.trans heq
        have e2 := (hsplit Y').symm.trans heq'
        rw [hsum] at e1
        have := e1.trans e2.symm
        exact mul_left_cancel₀ hal (by linarith)
      have hprev : prev y0 Y l = prev y0 Y' l := prev_congr l (fun p hp => hagree x x' p
        (fun h => by rw [h] at hp; omega))
      have hprev_pos : 0 < prev y0 Y l := by
        unfold prev
        by_cases hl0 : (l : ℕ) = 0
        · have : l.castSucc = (0 : Fin (n + 2)) := Fin.ext (by simp [hl0])
          rw [this, Fin.cons_zero]; exact hy0
        · have : l.castSucc = (⟨l - 1, by omega⟩ : Fin (n + 1)).succ := Fin.ext (by simp; omega)
          rw [this, Fin.cons_succ]
          exact hpos _
      have hYl : Y l = x := by simp [Y, Fin.insertNth_apply_same]
      have hYl' : Y' l = x' := by simp [Y', Fin.insertNth_apply_same]
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


/-! ## One name's residual column -/

/-- The weighted centering map `R ↦ ((R_j − Δ_j â)/√Δ_j)_j`. -/
noncomputable def Mlin {n : ℕ} (Δ : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun R := fun j => (R j - Δ j * ((∑ l, Δ l)⁻¹ * ∑ l, R l)) / Real.sqrt (Δ j)
  map_add' R R' := by
    funext j; simp only [Pi.add_apply, Finset.sum_add_distrib]; ring
  map_smul' c R := by
    funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]; ring

theorem ker_Mlin {n : ℕ} {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) :
    LinearMap.ker (Mlin Δ) ≤ Submodule.span ℝ {Δ} := by
  intro R hR
  rw [LinearMap.mem_ker] at hR
  rw [Submodule.mem_span_singleton]
  refine ⟨(∑ l, Δ l)⁻¹ * ∑ l, R l, funext fun j => ?_⟩
  have h := congrFun hR j
  simp only [Mlin, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h
  rw [div_eq_zero_iff, or_iff_left (Real.sqrt_pos.2 (hΔ j)).ne'] at h
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

theorem finrank_range_Mlin {n : ℕ} {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) :
    n - 1 ≤ Module.finrank ℝ (LinearMap.range (Mlin Δ)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Mlin Δ)
  have h2 : Module.finrank ℝ (LinearMap.ker (Mlin Δ)) ≤ 1 :=
    (Submodule.finrank_mono (ker_Mlin hΔ)).trans ((finrank_span_le_card ({Δ} : Set (Fin n → ℝ))).trans
      (by simp))
  rw [Module.finrank_fin_fun] at h1
  omega

/-- A name's residual column. -/
noncomputable def colN {n : ℕ} (Δ : Fin n → ℝ) (x0 : ℝ) (w : Fin n → ℝ) : Fin n → ℝ :=
  Mlin Δ fun j => ret x0 w j

/-- A name's column falls in a subspace of dimension at most `n − 2` only on a null set. -/
theorem col_null {n : ℕ} {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {x0 : ℝ} (hx0 : 0 < x0)
    (L : Submodule ℝ (Fin n → ℝ)) (hL : Module.finrank ℝ L + 2 ≤ n) :
    (Measure.pi fun _ : Fin n => muCEV)
      {w : Fin n → NNR | (∀ j, 0 < (w j : ℝ)) ∧ colN Δ x0 (fun j => (w j : ℝ)) ∈ L} = 0 := by
  classical
  have hnot : ¬ LinearMap.range (Mlin Δ) ≤ L := fun h => by
    have := Submodule.finrank_mono h
    have := finrank_range_Mlin hΔ
    omega
  obtain ⟨y, ⟨R0, rfl⟩, hy⟩ := Set.not_subset.1 hnot
  obtain ⟨f, hf, hfL⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hy inferInstance
  have hfL' : ∀ z ∈ L, f z = 0 := fun z hz => by
    have : f z ∈ L.map f := Submodule.mem_map_of_mem hz
    rw [hfL] at this; simpa using this
  set a : Fin n → ℝ := fun j => (f ∘ₗ Mlin Δ) (Pi.single j 1)
  have hφ : ∀ R, (f ∘ₗ Mlin Δ) R = ∑ j, a j * R j := fun R => by
    rw [LinearMap.pi_apply_eq_sum_univ (f ∘ₗ Mlin Δ) R]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [smul_eq_mul, a]
    rw [mul_comm]
    congr 2
    funext i; simp [Pi.single_apply, eq_comm]
  have ha : a ≠ 0 := fun h => by
    apply hf
    have := hφ R0
    rw [h] at this
    simpa using this
  refine measure_mono_null (fun w hw => ?_) (lin_null hx0 ha)
  refine ⟨hw.1, ?_⟩
  have := hfL' _ hw.2
  rw [colN, ← LinearMap.comp_apply, hφ] at this
  exact this


/-! ## Gram determinants -/

/-- The Gram matrix of a family of vectors. -/
noncomputable def gram {k n : ℕ} (c : Fin k → Fin n → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i l => c i ⬝ᵥ c l

theorem gram_eq {k n : ℕ} (c : Fin k → Fin n → ℝ) :
    gram c = (Matrix.of fun j i => c i j : Matrix (Fin n) (Fin k) ℝ).transpose *
      (Matrix.of fun j i => c i j : Matrix (Fin n) (Fin k) ℝ) := by
  ext i l; simp [gram, Matrix.mul_apply, dotProduct]

theorem indep_iff_gram {k n : ℕ} (c : Fin k → Fin n → ℝ) :
    LinearIndependent ℝ c ↔ (gram c).det ≠ 0 := by
  let C : Matrix (Fin n) (Fin k) ℝ := Matrix.of fun j i => c i j
  have hcol : C.col = c := by funext i j; rfl
  have key : LinearIndependent ℝ C.col ↔ (C.transpose * C).det ≠ 0 := by
    rw [← Matrix.mulVec_injective_iff]
    constructor
    · intro h
      have := Matrix.PosDef.conjTranspose_mul_self C h
      exact this.det_pos.ne'
    · intro h x y hxy
      have hu : IsUnit (C.transpose * C) := (Matrix.isUnit_iff_isUnit_det _).2 h.isUnit
      have hinj := Matrix.mulVec_injective_iff_isUnit.2 hu
      apply hinj
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
  rw [gram_eq]
  exact hcol ▸ key


/-! ## Induction over names -/

theorem measurable_colN {n : ℕ} (Δ : Fin n → ℝ) (x0 : ℝ) :
    Measurable fun w : Fin n → ℝ => colN Δ x0 w := by
  have hr : Measurable fun w : Fin n → ℝ => fun j => ret x0 w j :=
    measurable_pi_iff.2 fun j => (Novel.D13DriftNull.measurable_ret j).comp
      (measurable_const.prodMk measurable_id)
  exact (Mlin Δ).continuous_of_finiteDimensional.measurable.comp hr

theorem measurable_gramDet {k n : ℕ} (Δ : Fin n → ℝ) (x : Fin k → ℝ) :
    Measurable fun v : Fin k → Fin n → NNR =>
      (gram fun i => colN Δ (x i) (fun j => (v i j : ℝ))).det := by
  have hc : ∀ i, Measurable fun v : Fin k → Fin n → NNR => colN Δ (x i) (fun j => (v i j : ℝ)) :=
    fun i => (measurable_colN Δ (x i)).comp (measurable_pi_iff.2 fun j =>
      measurable_subtype_coe.comp ((measurable_pi_apply j).comp (measurable_pi_apply i)))
  have hg : Measurable fun v : Fin k → Fin n → NNR =>
      gram fun i => colN Δ (x i) (fun j => (v i j : ℝ)) := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun l => ?_
    simp only [gram, Matrix.of_apply, dotProduct]
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp (hc i)).mul ((measurable_pi_apply j).comp (hc l))
  exact (continuous_id.matrix_det.measurable).comp hg

theorem panel_null {n : ℕ} {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) :
    ∀ (k : ℕ), k + 1 ≤ n → ∀ x : Fin k → ℝ, (∀ i, 0 < x i) →
      (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin n => muCEV)
        {v : Fin k → Fin n → NNR | (∀ i j, 0 < (v i j : ℝ)) ∧
          (gram fun i => colN Δ (x i) (fun j => (v i j : ℝ))).det = 0} = 0
  | 0, _, x, _ => by
    have : {v : Fin 0 → Fin n → NNR | (∀ i j, 0 < (v i j : ℝ)) ∧
        (gram fun i => colN Δ (x i) (fun j => (v i j : ℝ))).det = 0} = ∅ := by
      ext v; simp [Matrix.det_fin_zero]
    rw [this, measure_empty]
  | k + 1, hk, x, hx => by
    classical
    set B := {v : Fin (k + 1) → Fin n → NNR | (∀ i j, 0 < (v i j : ℝ)) ∧
      (gram fun i => colN Δ (x i) (fun j => (v i j : ℝ))).det = 0} with hBdef
    have hB : MeasurableSet B := by
      have : B = (⋂ i, ⋂ j, {v : Fin (k + 1) → Fin n → NNR | 0 < (v i j : ℝ)}) ∩
          {v | (gram fun i => colN Δ (x i) (fun j => (v i j : ℝ))).det = 0} := by
        ext v; simp [hBdef]
      rw [this]
      exact (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => measurableSet_lt
        measurable_const (measurable_subtype_coe.comp ((measurable_pi_apply j).comp
          (measurable_pi_apply i)))).inter
        (measurableSet_eq_fun (measurable_gramDet Δ x) measurable_const)
    let μn : Measure (Fin n → NNR) := Measure.pi fun _ : Fin n => muCEV
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Fin n → NNR) (Fin.last k)
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μn) (Fin.last k)
    have h1 : (Measure.pi fun _ : Fin (k + 1) => μn) B =
        (μn.prod (Measure.pi fun _ : Fin k => μn)) (e.symm ⁻¹' B) := by
      rw [← hmp.measure_preimage (e.symm.measurable hB).nullMeasurableSet]
      congr 1
      ext v
      simp only [mem_preimage]
      rw [show e.symm (e v) = v from e.symm_apply_apply v]
    show (Measure.pi fun _ : Fin (k + 1) => μn) B = 0
    rw [h1, Measure.prod_apply_symm (e.symm.measurable hB)]
    -- The induction hypothesis, for the first `k` names.
    have ih := panel_null hΔ k (by omega) (fun i => x i.castSucc) (fun i => hx _)
    have hae : ∀ᵐ r ∂(Measure.pi fun _ : Fin k => μn),
        μn ((fun w => (w, r)) ⁻¹' (e.symm ⁻¹' B)) = 0 := by
      have := measure_eq_zero_iff_ae_notMem.1 ih
      filter_upwards [this] with r hr
      have hins : ∀ w, e.symm (w, r) = (Fin.snoc r w : Fin (k + 1) → Fin n → NNR) := fun w => by
        show Fin.insertNth (Fin.last k) w r = (Fin.snoc r w : Fin (k + 1) → Fin n → NNR)
        exact Fin.insertNth_last' w r
      by_cases hpos : ∀ i j, 0 < (r i j : ℝ)
      · have hdet : (gram fun i => colN Δ (x i.castSucc) (fun j => (r i j : ℝ))).det ≠ 0 :=
          fun h => hr ⟨hpos, h⟩
        have hind := (indep_iff_gram _).2 hdet
        set L := Submodule.span ℝ (Set.range fun i => colN Δ (x i.castSucc) (fun j => (r i j : ℝ)))
        have hL : Module.finrank ℝ L + 2 ≤ n := by
          have h := finrank_range_le_card (R := ℝ)
            (fun i => colN Δ (x i.castSucc) (fun j => (r i j : ℝ)))
          rw [Fintype.card_fin] at h
          have h' : Module.finrank ℝ L ≤ k := h
          omega
        refine measure_mono_null (fun w hw => ?_) (col_null hΔ (hx (Fin.last k)) L hL)
        simp only [mem_preimage, hins, hBdef, mem_ofPred_eq] at hw
        obtain ⟨hwpos, hwdet⟩ := hw
        have hcols : (fun i => colN Δ (x i) (fun j => ((Fin.snoc r w : Fin (k + 1) → Fin n → NNR)
            i j : ℝ))) = Fin.snoc (fun i => colN Δ (x i.castSucc) (fun j => (r i j : ℝ)))
              (colN Δ (x (Fin.last k)) (fun j => (w j : ℝ))) := by
          funext i
          induction i using Fin.lastCases with
          | last => simp
          | cast i => simp
        have hnot : ¬ LinearIndependent ℝ (fun i => colN Δ (x i) (fun j =>
            ((Fin.snoc r w : Fin (k + 1) → Fin n → NNR) i j : ℝ))) :=
          fun h => ((indep_iff_gram _).1 h) hwdet
        rw [hcols, linearIndependent_finSnoc] at hnot
        push Not at hnot
        refine ⟨fun j => ?_, hnot hind⟩
        have := hwpos (Fin.last k) j
        simpa using this
      · have : (fun w => (w, r)) ⁻¹' (e.symm ⁻¹' B) = ∅ := by
          ext w
          simp only [mem_preimage, hins, hBdef, mem_ofPred_eq, mem_empty_iff_false, iff_false,
            not_and]
          intro hw
          exact absurd (fun i j => by simpa using hw i.castSucc j) hpos
        rw [this, measure_empty]
    exact lintegral_eq_zero_of_ae_eq_zero hae


/-! ## The panel -/

open Standalone.D16GaussianPool Novel.D16GaussianPoolProfile Novel.D16GaussianPoolMeas
  Novel.D16GaussianPoolScore

theorem Z_col {m n : ℕ} (Δ : Fin n → ℝ) (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ) (i : Fin m) :
    (Zres Δ (Rpool x y)).col i = colN Δ (x i) (y i) := by
  funext j
  simp only [Matrix.col, Matrix.transpose_apply, Zres, Matrix.of_apply, resid_apply, colN, Mlin,
    LinearMap.coe_mk, AddHom.coe_mk, Rpool, tauP]

theorem posDef_of_indep {m n : ℕ} {Δ : Fin n → ℝ} (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j)
    {R : Fin n → Fin m → ℝ} (h : LinearIndependent ℝ (Zres Δ R).col) : (Spool Δ R).PosDef := by
  rw [Spool_eq_Z hn hΔ]
  have hinj := Matrix.mulVec_injective_iff.2 h
  have := Matrix.PosDef.conjTranspose_mul_self (Zres Δ R) hinj
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this.smul (inv_pos.2 (by exact_mod_cast hn))

theorem nullSet_one : ∀ (m n : ℕ) (Δ : Fin n → ℝ) (x : Fin m → ℝ), 0 < m → m + 1 ≤ n →
    (∀ j, 0 < Δ j) → (∀ i, 0 < x i) →
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV)
      {v | PosRec x (fun i j => (v i j : ℝ)) ∧
        ¬ (Spool Δ (Rpool x fun i j => (v i j : ℝ))).PosDef} = 0 := by
  intro m n Δ x hm hmn hΔ hx
  have hn : 0 < n := by omega
  refine measure_mono_null (fun v hv => ?_) (panel_null hΔ m hmn x hx)
  obtain ⟨hp, hS⟩ := hv
  refine ⟨fun i j => (hp i).2 j, ?_⟩
  by_contra hdet
  apply hS
  refine posDef_of_indep hn hΔ ?_
  have : (Zres Δ (Rpool x fun i j => (v i j : ℝ))).col = fun i => colN Δ (x i) (fun j => (v i j : ℝ)) :=
    funext fun i => Z_col Δ x _ i
  rw [this]
  exact (indep_iff_gram _).2 hdet


theorem Dpool_top {m n : ℕ} {Δ : Fin n → ℝ} {x : Fin m → ℝ} {y : Fin m → Fin n → ℝ}
    (h : Dpool Δ x y = ⊤) : PosRec x y ∧ ¬ (Spool Δ (Rpool x y)).PosDef := by
  classical
  unfold Dpool at h
  split_ifs at h with h1 h2
  · exact absurd h ENNReal.ofReal_ne_top
  · exact ⟨h1, h2⟩
  · exact absurd h ENNReal.zero_ne_top

theorem nullSet_holds : nullSet := by
  refine ⟨nullSet_one, ?_⟩
  intro Ω 𝒰 _ _ P _ m n Δ U V xe ν _ hm hmn hΔ hU hV hxe hpos hmix
  classical
  have hn : 0 < n := by omega
  let μE : Measure (Fin m → Fin n → NNR) := Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV
  have hcoe : Measurable fun v : Fin m → Fin n → NNR => fun i j => (v i j : ℝ) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
      measurable_subtype_coe.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))
  let dens := fun (p : 𝒰 × ((Fin m → ℝ) × PDMat m)) (v : Fin m → Fin n → NNR) =>
    ENNReal.ofReal (gPool Δ p.2.1 p.2.2.1 (xe p.1) fun i j => (v i j : ℝ))
  have hdens : Measurable (Function.uncurry dens) :=
    ENNReal.measurable_ofReal.comp (Measurable.comp
      (g := fun q : ((Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ) × ((Fin m → ℝ) × (Fin m → Fin n → ℝ)) =>
        gPool Δ q.1.1 q.1.2 q.2.1 q.2.2)
      (f := fun p : (𝒰 × ((Fin m → ℝ) × PDMat m)) × (Fin m → Fin n → NNR) =>
        ((p.1.2.1, p.1.2.2.1), (xe p.1.1, fun i j => (p.2 i j : ℝ))))
      (measurable_gPool Δ)
      (((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        (measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))).prodMk
        ((hxe.comp (measurable_fst.comp measurable_fst)).prodMk (hcoe.comp measurable_snd))))
  let HK : Kernel (𝒰 × ((Fin m → ℝ) × PDMat m)) (Fin m → Fin n → NNR) :=
    Kernel.withDensity (Kernel.const _ μE) dens
  have hHK : ∀ p, HK p = μE.withDensity (dens p) := fun p => by
    simp only [HK]; rw [Kernel.withDensity_apply _ hdens, Kernel.const_apply]
  have hHz : ∀ u, Measurable fun θ => HK (u, θ) := fun u => HK.measurable.comp measurable_prodMk_left
  have hmix' : ∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun θ => HK (u, θ) := by
    filter_upwards [hmix] with u hu
    rw [hu]; congr 1; funext θ; rw [hHK]
  have hDm := (envelope_holds m n Δ hm hn hΔ).2
  have hSm : MeasurableSet {p : 𝒰 × (Fin m → Fin n → NNR) |
      Dpool Δ (xe p.1) (fun i j => (p.2 i j : ℝ)) = ⊤} :=
    measurableSet_eq_fun (Measurable.comp
      (g := fun q : (Fin m → ℝ) × (Fin m → Fin n → ℝ) => Dpool Δ q.1 q.2)
      (f := fun p : 𝒰 × (Fin m → Fin n → NNR) => (xe p.1, fun i j => (p.2 i j : ℝ))) hDm
      ((hxe.comp measurable_fst).prodMk (hcoe.comp measurable_snd))) measurable_const
  have hF : Measurable ({p : 𝒰 × (Fin m → Fin n → NNR) |
      Dpool Δ (xe p.1) (fun i j => (p.2 i j : ℝ)) = ⊤}.indicator
        (1 : 𝒰 × (Fin m → Fin n → NNR) → ℝ≥0∞)) := measurable_const.indicator hSm
  have hmeasω : MeasurableSet {ω | Dpool Δ (xe (U ω)) (fun i j => (V ω i j : ℝ)) = ⊤} :=
    (hU.prodMk hV) hSm
  rw [← lintegral_indicator_one hmeasω]
  refine (Eq.trans (by rfl) (Novel.D14SupportRobustness.disint (P := P) hU hV hF)).trans ?_
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [hmix', hpos] with u hu hxu
  show ∫⁻ v, (Prod.mk u ⁻¹' {p : 𝒰 × (Fin m → Fin n → NNR) |
    Dpool Δ (xe p.1) (fun i j => (p.2 i j : ℝ)) = ⊤}).indicator 1 v ∂_ = 0
  have hSu : MeasurableSet (Prod.mk u ⁻¹' {p : 𝒰 × (Fin m → Fin n → NNR) |
      Dpool Δ (xe p.1) (fun i j => (p.2 i j : ℝ)) = ⊤}) := measurable_prodMk_left hSm
  rw [lintegral_indicator_one hSu, hu, Measure.bind_apply hSu (hHz u).aemeasurable]
  refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun θ => ?_)
  show HK (u, θ) _ = 0
  rw [hHK]
  refine withDensity_absolutelyContinuous _ _ (measure_mono_null (fun v hv => Dpool_top hv)
    (nullSet_one m n Δ (xe u) hm hmn hΔ hxu))

end Novel.D16GaussianPoolNull
