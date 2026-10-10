import Standalone.D16CopulaAlgebra
import Novel.GaussianCell

/-!
# Claim 063, deterministic stage: proof

Proves `Standalone.D16CopulaAlgebra.statement` (`statement_holds`).
* **The training rule.**
  - `A_cop` is a positive-semidefinite Gram matrix: its quadratic form is
    `(1/s) Σ_j ((zt_j − zbar)·v)²`.
  - On the positive-diagonal locus, `T_cop` is the diagonal congruence `D A D` with
    `D = diag(A_ii^(−1/2))`, so it is positive semidefinite with unit diagonal.
  - Hence `vᵀ R v = (1 − γ) vᵀ T v + γ |v|² ≥ γ |v|²`. The fallback `I` satisfies the same bound since
    `γ ≤ 1`.
* **Normal scores.** `Φ` is continuous and strictly increasing with limits `0` and `1`. So
  `{x | Φ x ≤ p}` is a closed half-line whose supremum solves `Φ x = p`. Measurability follows from
  the sublevel sets `{p | Φ⁻¹ p < c}`.
* **The gain.**
  - `E_cop/E_pool = ∏_j c_R(z_j)`, and `log c_R(z) = −(1/2) log det R − (1/2) zᵀ(R⁻¹ − I)z`.
  - `zᵀBz = tr(B z zᵀ)`.
  - With `(1/n) Σ z zᵀ = R` the trace is `n tr(I − R) = 0` for unit diagonal.
-/

open Matrix Real MeasureTheory ProbabilityTheory Filter Topology

namespace Novel.D16CopulaAlgebra

open Standalone.D16CopulaAlgebra

/-! ## Quadratic forms -/

theorem quad_vecMulVec {m : ℕ} (a v : Fin m → ℝ) :
    v ⬝ᵥ (vecMulVec a a *ᵥ v) = (a ⬝ᵥ v) ^ 2 := by
  simp only [dotProduct, mulVec, vecMulVec_apply, sq, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem quad_Acop {s m : ℕ} (zt : Fin s → Fin m → ℝ) (v : Fin m → ℝ) :
    v ⬝ᵥ (Acop zt *ᵥ v) = (s : ℝ)⁻¹ * ∑ j, ((zt j - zbar zt) ⬝ᵥ v) ^ 2 := by
  unfold Acop
  rw [smul_mulVec, dotProduct_smul, sum_mulVec, dotProduct_sum, smul_eq_mul]
  simp_rw [quad_vecMulVec]

theorem quad_Acop_nonneg {s m : ℕ} (zt : Fin s → Fin m → ℝ) (v : Fin m → ℝ) :
    0 ≤ v ⬝ᵥ (Acop zt *ᵥ v) := by
  rw [quad_Acop]; positivity

theorem Acop_diag_nonneg {s m : ℕ} (zt : Fin s → Fin m → ℝ) (i : Fin m) : 0 ≤ Acop zt i i := by
  have := quad_Acop_nonneg zt (Pi.single i 1)
  simpa [mulVec, dotProduct, Pi.single_apply] using this

theorem Acop_symm {s m : ℕ} (zt : Fin s → Fin m → ℝ) (i k : Fin m) : Acop zt i k = Acop zt k i := by
  simp [Acop, Matrix.sum_apply, vecMulVec_apply, mul_comm]

/-- The quadratic form of `T_cop` is that of `A_cop` at the rescaled vector. -/
theorem quad_Tcop {s m : ℕ} (zt : Fin s → Fin m → ℝ) (h : ∀ i, Acop zt i i ≠ 0) (v : Fin m → ℝ) :
    v ⬝ᵥ (Tcop zt *ᵥ v) = (fun i => v i / Real.sqrt (Acop zt i i)) ⬝ᵥ
      (Acop zt *ᵥ fun i => v i / Real.sqrt (Acop zt i i)) := by
  have hpos : ∀ i, 0 < Acop zt i i := fun i => lt_of_le_of_ne (Acop_diag_nonneg zt i) (h i).symm
  simp only [dotProduct, mulVec, Tcop, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Real.sqrt_mul (hpos i).le]
  have hi := Real.sqrt_pos.2 (hpos i)
  have hk := Real.sqrt_pos.2 (hpos k)
  field_simp

theorem quad_Tcop_nonneg {s m : ℕ} (zt : Fin s → Fin m → ℝ) (h : ∀ i, Acop zt i i ≠ 0)
    (v : Fin m → ℝ) : 0 ≤ v ⬝ᵥ (Tcop zt *ᵥ v) := by
  rw [quad_Tcop zt h]; exact quad_Acop_nonneg _ _

theorem Tcop_diag {s m : ℕ} (zt : Fin s → Fin m → ℝ) (h : ∀ i, Acop zt i i ≠ 0) (i : Fin m) :
    Tcop zt i i = 1 := by
  have hpos : 0 < Acop zt i i := lt_of_le_of_ne (Acop_diag_nonneg zt i) (h i).symm
  simp only [Tcop, Matrix.of_apply]
  rw [Real.sqrt_mul_self hpos.le, div_self hpos.ne']

theorem Tcop_symm {s m : ℕ} (zt : Fin s → Fin m → ℝ) (i k : Fin m) : Tcop zt i k = Tcop zt k i := by
  simp only [Tcop, Matrix.of_apply]; rw [Acop_symm zt i k, mul_comm (Acop zt i i)]

/-! ## The training rule (2) -/

theorem quad_one {m : ℕ} (v : Fin m → ℝ) : v ⬝ᵥ ((1 : Matrix (Fin m) (Fin m) ℝ) *ᵥ v) = v ⬝ᵥ v := by
  rw [one_mulVec]

theorem Rcop_quad {s m : ℕ} {γ : ℝ} (hγ1 : γ ≤ 1) (zt : Fin s → Fin m → ℝ) (v : Fin m → ℝ) :
    γ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Rcop γ zt *ᵥ v) := by
  have hvv : 0 ≤ v ⬝ᵥ v := by simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  unfold Rcop
  split_ifs with h
  · rw [add_mulVec, dotProduct_add, smul_mulVec, smul_mulVec, dotProduct_smul, dotProduct_smul,
      quad_one, smul_eq_mul, smul_eq_mul]
    nlinarith [quad_Tcop_nonneg zt h v]
  · rw [quad_one]; nlinarith

theorem Rcop_herm {s m : ℕ} (γ : ℝ) (zt : Fin s → Fin m → ℝ) : (Rcop γ zt).IsHermitian := by
  unfold Rcop
  split_ifs
  · refine Matrix.IsHermitian.ext fun i k => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, star_trivial, smul_eq_mul, Matrix.one_apply]
    rw [Tcop_symm zt i k]
    by_cases hik : i = k
    · subst hik; rfl
    · simp only [hik, Ne.symm hik, ↓reduceIte]
  · exact Matrix.isHermitian_one

theorem Rcop_diag {s m : ℕ} (γ : ℝ) (zt : Fin s → Fin m → ℝ) (i : Fin m) : Rcop γ zt i i = 1 := by
  unfold Rcop
  split_ifs with h
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
      Tcop_diag zt h i]
    ring
  · exact Matrix.one_apply_eq i

theorem Rcop_posDef {s m : ℕ} {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (zt : Fin s → Fin m → ℝ) :
    (Rcop γ zt).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨Rcop_herm γ zt, fun v hv => ?_⟩
  have hvv : 0 < v ⬝ᵥ v := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    simp only [dotProduct]
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩
  have := Rcop_quad hγ1 zt v
  simp only [star_trivial]
  nlinarith

theorem continuous_Acop {s m : ℕ} (i k : Fin m) :
    Continuous fun zt : Fin s → Fin m → ℝ => Acop zt i k := by
  simp only [Acop, zbar, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, Pi.sub_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  fun_prop

theorem measurable_Rcop {s m : ℕ} (γ : ℝ) : Measurable fun zt : Fin s → Fin m → ℝ => Rcop γ zt := by
  classical
  have hset : MeasurableSet {zt : Fin s → Fin m → ℝ | ∀ i, Acop zt i i ≠ 0} := by
    have : {zt : Fin s → Fin m → ℝ | ∀ i, Acop zt i i ≠ 0} = ⋂ i, {zt | Acop zt i i ≠ 0} := by
      ext; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_eq_fun (continuous_Acop i i).measurable measurable_const).compl
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
  have e : (fun zt : Fin s → Fin m → ℝ => Rcop γ zt i k) = fun zt =>
      if ∀ i, Acop zt i i ≠ 0 then (1 - γ) * Tcop zt i k + γ * (1 : Matrix (Fin m) (Fin m) ℝ) i k
      else (1 : Matrix (Fin m) (Fin m) ℝ) i k := by
    funext zt; unfold Rcop; split_ifs <;> simp
  rw [e]
  refine Measurable.ite hset ?_ measurable_const
  refine (measurable_const.mul ?_).add measurable_const
  simp only [Tcop, Matrix.of_apply]
  exact (continuous_Acop i k).measurable.div
    (((continuous_Acop i i).measurable.mul (continuous_Acop k k).measurable).sqrt)

theorem training_holds : training := by
  refine ⟨fun s m γ zt hs hγ hγ1 => ⟨Rcop_herm γ zt, Rcop_diag γ zt, Rcop_quad hγ1 zt,
    Rcop_posDef hγ hγ1 zt, fun h1 => ?_, fun hm => ?_, fun ⟨i, hi⟩ => ?_⟩,
    fun s m γ => measurable_Rcop γ⟩
  · unfold Rcop; split_ifs <;> simp [h1]
  · subst hm
    ext i k
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero k, Rcop_diag]; rfl
  · unfold Rcop
    have : ¬ ∀ i, Acop zt i i ≠ 0 := by push Not; exact ⟨i, hi⟩
    simp only [this, ↓reduceIte]

/-! ## Normal scores -/

open Novel.GaussianCell in
theorem Phi_eq : Phi = Φ := rfl

open Novel.GaussianCell in
theorem continuous_Phi : Continuous Phi :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_Φ x).continuousAt

open Novel.GaussianCell in
theorem tendsto_Phi_atBot : Tendsto Phi atBot (𝓝 0) := by
  have h : Tendsto (fun x => 1 - Φ (-x)) atBot (𝓝 (1 - 1)) :=
    (tendsto_Φ.comp tendsto_neg_atBot_atTop).const_sub 1
  rw [sub_self] at h
  refine h.congr fun x => ?_
  simp only [Phi_eq]; rw [Φ_neg]; ring

open Novel.GaussianCell in
theorem PhiInv_spec {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : Phi (PhiInv p) = p := by
  set S := {x | Phi x ≤ p}
  obtain ⟨a, ha⟩ := ((tendsto_order.1 tendsto_Phi_atBot).2 p hp0).exists
  obtain ⟨b, hb⟩ := ((tendsto_order.1 (Phi_eq ▸ tendsto_Φ)).1 p hp1).exists
  have hne : S.Nonempty := ⟨a, ha.le⟩
  have hbdd : BddAbove S := ⟨b, fun x (hx : Phi x ≤ p) => by
    by_contra h; push Not at h
    have := Φ_lt h; rw [← Phi_eq] at this; linarith⟩
  have hcl : IsClosed S := isClosed_le continuous_Phi continuous_const
  have hmem : PhiInv p ∈ S := hcl.csSup_mem hne hbdd
  refine le_antisymm hmem ?_
  by_contra h; push Not at h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    ((continuous_Phi.tendsto (PhiInv p)).eventually (gt_mem_nhds h))
  have hy : PhiInv p + ε / 2 ∈ S := (hball (by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]; linarith)).le
  have := le_csSup hbdd hy
  change PhiInv p + ε / 2 ≤ PhiInv p at this
  linarith

open Novel.GaussianCell in
theorem PhiInv_Phi (x : ℝ) : PhiInv (Phi x) = x := by
  have : {y | Phi y ≤ Phi x} = Set.Iic x := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_Iic, Phi_eq]
    constructor
    · intro h; by_contra h'; push Not at h'; exact absurd (Φ_lt h') (not_lt.2 h)
    · intro h; rcases h.lt_or_eq with h | h
      · exact (Φ_lt h).le
      · rw [h]
  unfold PhiInv; rw [this, csSup_Iic]

open Novel.GaussianCell in
theorem strictMono_Phi : StrictMono Phi := fun _ _ h => Φ_lt h

theorem PhiInv_lt_iff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c : ℝ) : PhiInv p < c ↔ p < Phi c := by
  conv_rhs => rw [← PhiInv_spec hp0 hp1]
  exact strictMono_Phi.lt_iff_lt.symm

open Novel.GaussianCell in
theorem PhiInv_out {p : ℝ} (hp : ¬ (0 < p ∧ p < 1)) : PhiInv p = 0 := by
  unfold PhiInv
  rcases not_and_or.1 hp with h | h
  · push Not at h
    have : {x | Phi x ≤ p} = ∅ := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      rw [Phi_eq]; linarith [Φ_pos x]
    rw [this, Real.sSup_empty]
  · push Not at h
    refine Real.sSup_of_not_bddAbove fun ⟨b, hb⟩ => ?_
    have := hb (show b + 1 ∈ {x | Phi x ≤ p} by
      show Phi (b + 1) ≤ p; rw [Phi_eq]; linarith [Φ_le_one (b + 1)])
    linarith

theorem measurable_PhiInv : Measurable PhiInv := by
  refine measurable_of_Iio fun c => ?_
  have : PhiInv ⁻¹' Set.Iio c = (Set.Ioo 0 1 ∩ Set.Iio (Phi c)) ∪
      ((Set.Ioo 0 1)ᶜ ∩ {_p | 0 < c}) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_union, Set.mem_inter_iff, Set.mem_Ioo,
      Set.mem_compl_iff, Set.mem_ofPred_eq]
    by_cases hp : 0 < p ∧ p < 1
    · rw [PhiInv_lt_iff hp.1 hp.2]; tauto
    · rw [PhiInv_out hp]; tauto
  rw [this]
  exact (measurableSet_Ioo.inter measurableSet_Iio).union
    (measurableSet_Ioo.compl.inter (MeasurableSet.const _))

open Novel.GaussianCell in
theorem normalScore_holds : normalScore := by
  refine ⟨fun p h0 h1 => PhiInv_spec h0 h1, PhiInv_Phi, fun x => ⟨Φ_pos x, Φ_lt_one x⟩,
    strictMono_Phi, fun p q hp hpq hq => ?_, measurable_PhiInv⟩
  rw [PhiInv_lt_iff hp (hpq.trans hq), PhiInv_spec (hp.trans hpq) hq]
  exact hpq

/-! ## The gain (4)–(6) -/

theorem trace_vecMulVec {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) (a : Fin m → ℝ) :
    (B * vecMulVec a a).trace = a ⬝ᵥ (B *ᵥ a) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem cR_pos {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef) (z : Fin m → ℝ) :
    0 < cR R z :=
  mul_pos (Real.rpow_pos_of_pos hR.det_pos _) (Real.exp_pos _)

theorem log_cR {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef) (z : Fin m → ℝ) :
    Real.log (cR R z) = -(1 / 2) * Real.log R.det - (z ⬝ᵥ ((R⁻¹ - 1) *ᵥ z)) / 2 := by
  unfold cR
  rw [Real.log_mul (Real.rpow_pos_of_pos hR.det_pos _).ne' (Real.exp_pos _).ne',
    Real.log_rpow hR.det_pos, Real.log_exp]
  ring

theorem log_prod_cR {m n : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef)
    (z : Fin n → Fin m → ℝ) :
    Real.log (∏ j, cR R (z j)) = -((n : ℝ) / 2) * Real.log R.det -
      (1 / 2) * ((R⁻¹ - 1) * ∑ j, vecMulVec (z j) (z j)).trace := by
  rw [Real.log_prod (fun j _ => (cR_pos hR (z j)).ne'), Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [log_cR hR, trace_vecMulVec]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_div]
  ring

theorem gain_main : ∀ (m n : ℕ) (R : Matrix (Fin m) (Fin m) ℝ) (z : Fin n → Fin m → ℝ)
    (qpool D w : ℝ), R.PosDef → 0 < qpool → 0 < D → 0 < w → w < 1 →
    let C := ∏ j, cR R (z j)
    let Epool := qpool / D
    let Ecop := C * qpool / D
    let Emix := (w * qpool + (1 - w) * (C * qpool)) / D
    let G := -((n : ℝ) / 2) * Real.log R.det -
      (1 / 2) * ((R⁻¹ - 1) * ∑ j, vecMulVec (z j) (z j)).trace
    Emix = w * Epool + (1 - w) * Ecop ∧ w * Epool ≤ Emix ∧ 0 < Ecop ∧
    Real.log (Ecop / Epool) = G ∧
    Real.log (Emix / Epool) = Real.log (w + (1 - w) * Real.exp G) ∧
    Real.log w ≤ Real.log (Emix / Epool) ∧
    (R = 1 → Ecop = Epool ∧ Emix = Epool) ∧
    (0 < n → (∀ i, R i i = 1) → (n : ℝ)⁻¹ • ∑ j, vecMulVec (z j) (z j) = R →
      G = -((n : ℝ) / 2) * Real.log R.det) := by
  intro m n R z qpool D w hR hq hD hw hw1 C Epool Ecop Emix G
  have hC : 0 < C := Finset.prod_pos fun j _ => cR_pos hR (z j)
  have hG : Real.log C = G := log_prod_cR hR z
  have hratio : Ecop / Epool = C := by
    simp only [Ecop, Epool]; field_simp
  have hmix : Emix / Epool = w + (1 - w) * C := by
    simp only [Emix, Epool]; field_simp
  have hexp : Real.exp G = C := by rw [← hG, Real.exp_log hC]
  refine ⟨by simp only [Emix, Epool, Ecop]; ring, ?_, by positivity, by rw [hratio, hG],
    by rw [hmix, hexp], ?_, fun h1 => ?_, fun hn hdiag hmom => ?_⟩
  · have : 0 ≤ (1 - w) * (C * qpool) / D := by
      have : 0 < 1 - w := by linarith
      positivity
    simp only [Emix, Epool]; rw [add_div, mul_div_assoc]; linarith
  · rw [hmix]
    exact Real.log_le_log hw (by nlinarith)
  · have hC1 : C = 1 := by
      simp only [C, h1, cR, Matrix.det_one, inv_one, sub_self, zero_mulVec, dotProduct_zero,
        neg_zero, zero_div, Real.exp_zero, Real.one_rpow, mul_one, Finset.prod_const_one]
    refine ⟨by simp only [Ecop, Epool, hC1, one_mul], by simp only [Emix, Epool, hC1, one_mul]; ring_nf⟩
  · have hdet : IsUnit R.det := isUnit_iff_ne_zero.2 hR.det_pos.ne'
    have hsum : ∑ j, vecMulVec (z j) (z j) = (n : ℝ) • R := by
      rw [← hmom, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
    have htr : ((R⁻¹ - 1) * ∑ j, vecMulVec (z j) (z j)).trace = 0 := by
      rw [hsum, Matrix.mul_smul, Matrix.sub_mul, Matrix.nonsing_inv_mul R hdet, Matrix.one_mul,
        Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one]
      have : R.trace = (Fintype.card (Fin m) : ℝ) := by
        simp [Matrix.trace, hdiag]
      rw [this, sub_self, smul_zero]
    simp only [G, htr, mul_zero, sub_zero]

/-- The inverse of the two-name example. -/
theorem Rex_inv : Rex⁻¹ = !![4 / 3, -(2 / 3); -(2 / 3), 4 / 3] := by
  refine Matrix.inv_eq_left_inv ?_
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Rex, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem example_holds : Rex.PosDef ∧ (![1, 1] ⬝ᵥ ((Rex⁻¹ - 1) *ᵥ ![1, 1])) < 0 ∧
    0 < (![1, -1] ⬝ᵥ ((Rex⁻¹ - 1) *ᵥ ![1, -1])) := by
  refine ⟨Matrix.posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩, ?_, ?_⟩
  · refine Matrix.IsHermitian.ext fun i k => ?_
    fin_cases i <;> fin_cases k <;> simp [Rex]
  · have h : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h; push Not at h
      exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    simp only [star_trivial, dotProduct, mulVec, Rex, Fin.sum_univ_two]
    simp
    rcases h with h | h
    · nlinarith [mul_self_pos.2 h, sq_nonneg (x 0 + 2 * x 1), sq_nonneg (x 1)]
    · nlinarith [mul_self_pos.2 h, sq_nonneg (2 * x 0 + x 1), sq_nonneg (x 0)]
  · rw [Rex_inv]; simp [dotProduct, mulVec, Fin.sum_univ_two]; norm_num
  · rw [Rex_inv]; simp [dotProduct, mulVec, Fin.sum_univ_two]; norm_num

/-! ## The marginal CDF -/

theorem setInt_pos {f : ℝ → ℝ} (hf : Measurable f) (hpos : ∀ v, 0 < v → 0 < f v) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) : 0 < ∫⁻ v in Set.Ioc a b, ENNReal.ofReal (f v) := by
  refine (setLIntegral_pos_iff (f := fun v => ENNReal.ofReal (f v))
    (ENNReal.measurable_ofReal.comp hf)).2 ?_
  have : Function.support (fun v => ENNReal.ofReal (f v)) ∩ Set.Ioc a b = Set.Ioc a b := by
    refine Set.inter_eq_right.2 fun v hv => ?_
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hpos v (ha.trans_lt hv.1)
  rw [this, Real.volume_Ioc]
  exact ENNReal.ofReal_pos.2 (by linarith)

theorem marginal_holds : marginal := by
  intro f hf hpos hone
  have hmeas : Measurable fun v => ENNReal.ofReal (f v) := ENNReal.measurable_ofReal.comp hf
  -- `∫_(0,y] + ∫_(y,∞) = 1`.
  have hsplit : ∀ y, 0 < y → (∫⁻ v in Set.Ioc 0 y, ENNReal.ofReal (f v)) +
      ∫⁻ v in Set.Ioi y, ENNReal.ofReal (f v) = 1 := fun y hy => by
    rw [← lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi le_rfl),
      Set.Ioc_union_Ioi_eq_Ioi hy.le, hone]
  have htail : ∀ y, 0 < y → 0 < ∫⁻ v in Set.Ioi y, ENNReal.ofReal (f v) := fun y hy =>
    (setInt_pos hf hpos hy.le (lt_add_one y)).trans_le
      (lintegral_mono_set Set.Ioc_subset_Ioi_self)
  have hfin : ∀ y, 0 < y → (∫⁻ v in Set.Ioc 0 y, ENNReal.ofReal (f v)) < 1 := fun y hy => by
    have h := hsplit y hy
    have := htail y hy
    have hne : (∫⁻ v in Set.Ioi y, ENNReal.ofReal (f v)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (h ▸ le_add_self)
    calc (∫⁻ v in Set.Ioc 0 y, ENNReal.ofReal (f v))
        < (∫⁻ v in Set.Ioc 0 y, ENNReal.ofReal (f v)) + ∫⁻ v in Set.Ioi y, ENNReal.ofReal (f v) :=
          ENNReal.lt_add_right (ne_top_of_le_ne_top ENNReal.one_ne_top (h ▸ le_self_add))
            this.ne'
      _ = 1 := h
  have hbds : ∀ y, 0 < y → 0 < Fm f y ∧ Fm f y < 1 := fun y hy => by
    have hlt := hfin y hy
    refine ⟨ENNReal.toReal_pos (setInt_pos hf hpos le_rfl hy).ne' (ne_top_of_lt hlt), ?_⟩
    have := (ENNReal.toReal_lt_toReal (ne_top_of_lt hlt) ENNReal.one_ne_top).2 hlt
    simpa [Fm] using this
  have hmono : StrictMonoOn (Fm f) (Set.Ioi 0) := fun y hy y' hy' hyy' => by
    have hy : (0 : ℝ) < y := hy
    have hsum : (∫⁻ v in Set.Ioc 0 y', ENNReal.ofReal (f v)) =
        (∫⁻ v in Set.Ioc 0 y, ENNReal.ofReal (f v)) + ∫⁻ v in Set.Ioc y y', ENNReal.ofReal (f v) := by
      rw [← lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl),
        Set.Ioc_union_Ioc_eq_Ioc hy.le hyy'.le]
    have hne := ne_top_of_lt (hfin y' hy')
    have hne0 : (∫⁻ v in Set.Ioc 0 y, ENNReal.ofReal (f v)) ≠ ⊤ :=
      ne_top_of_le_ne_top hne (hsum ▸ le_self_add)
    unfold Fm
    rw [ENNReal.toReal_lt_toReal hne0 hne, hsum]
    exact ENNReal.lt_add_right hne0 (setInt_pos hf hpos hy.le hyy').ne'
  have hspec : ∀ y, 0 < y → Phi (PhiInv (Fm f y)) = Fm f y := fun y hy =>
    PhiInv_spec (hbds y hy).1 (hbds y hy).2
  refine ⟨hbds, hmono, hspec, fun y hy y' hy' hyy' => ?_, ?_⟩
  · have h := hmono hy hy' hyy'
    rw [← hspec y hy, ← hspec y' hy'] at h
    exact strictMono_Phi.lt_iff_lt.1 h
  · refine Monotone.measurable fun y y' hyy' => ENNReal.toReal_mono ?_ ?_
    · by_cases hy' : 0 < y'
      · exact ne_top_of_lt (hfin y' hy')
      · rw [Set.Ioc_eq_empty (by linarith), Measure.restrict_empty, lintegral_zero_measure]
        exact ENNReal.zero_ne_top
    · exact lintegral_mono_set (Set.Ioc_subset_Ioc_right hyy')

theorem gain_holds : gain := ⟨gain_main, example_holds⟩

theorem statement_holds : Standalone.D16CopulaAlgebra.statement :=
  ⟨training_holds, normalScore_holds, marginal_holds, gain_holds⟩

end Novel.D16CopulaAlgebra
