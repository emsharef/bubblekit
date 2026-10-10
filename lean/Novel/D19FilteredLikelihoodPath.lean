import Standalone.D19FilteredLikelihood
import Novel.D14FixedTickProof

/-!
# Claim 036: label paths in closed form

* `mlabels_eq`: the `j`-th label of the exact path from `x` is the label of `x · exp(Σ_(i ≤ j) ξ_i)`.
* `mlabels_snoc`, `mlabels_append`: the labels split at the last step, and at the training/evaluation
  boundary, with the second block started from the training endpoint.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick

/-- The partial log return up to step `j`. -/
noncomputable def psum {m : ℕ} (ξ : Fin m → ℝ) (j : Fin m) : ℝ := ∑ i, if i ≤ j then ξ i else 0

/-- The endpoint after all steps. -/
noncomputable def xEnd {m : ℕ} (x : ℝ) (ξ : Fin m → ℝ) : ℝ := x * Real.exp (∑ i, ξ i)

theorem psum_zero {m : ℕ} (ξ : Fin (m + 1) → ℝ) : psum ξ 0 = ξ 0 := by
  unfold psum
  rw [Fin.sum_univ_succ]
  simp [Fin.succ_ne_zero]

theorem psum_succ {m : ℕ} (ξ : Fin (m + 1) → ℝ) (j : Fin m) :
    psum ξ j.succ = ξ 0 + psum (Fin.tail ξ) j := by
  unfold psum
  rw [Fin.sum_univ_succ]
  simp only [Fin.zero_le, ite_true, Fin.succ_le_succ_iff, Fin.tail]

theorem mlabels_eq (δ : ℝ) : ∀ (m : ℕ) (x : ℝ) (ξ : Fin m → ℝ) (j : Fin m),
    mlabels δ m x ξ j = mlabel δ (x * Real.exp (psum ξ j))
  | 0, _, _, j => j.elim0
  | m + 1, x, ξ, j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [mlabels, psum_zero]
    · simp only [mlabels, Fin.cons_succ]
      rw [mlabels_eq δ m _ _ j, psum_succ, Real.exp_add, mul_assoc]

theorem psum_castSucc {m : ℕ} (ξ : Fin (m + 1) → ℝ) (j : Fin m) :
    psum ξ j.castSucc = psum (Fin.init ξ) j := by
  unfold psum
  rw [Fin.sum_univ_castSucc]
  have : ¬ (Fin.last m ≤ j.castSucc) := not_le.2 (Fin.castSucc_lt_last j)
  simp only [Fin.castSucc_le_castSucc_iff, this, ite_false, add_zero, Fin.init]

theorem psum_last {m : ℕ} (ξ : Fin (m + 1) → ℝ) : psum ξ (Fin.last m) = ∑ i, ξ i := by
  unfold psum; simp [Fin.le_last]

theorem sum_castSucc {m : ℕ} (ξ : Fin (m + 1) → ℝ) :
    ∑ i, ξ i = (∑ i, Fin.init ξ i) + ξ (Fin.last m) := by
  rw [Fin.sum_univ_castSucc]; rfl

/-- The labels split at the last step. -/
theorem mlabels_snoc (δ : ℝ) {m : ℕ} (x : ℝ) (ξ : Fin (m + 1) → ℝ) :
    mlabels δ (m + 1) x ξ = Fin.snoc (mlabels δ m x (Fin.init ξ))
      (mlabel δ (xEnd x (Fin.init ξ) * Real.exp (ξ (Fin.last m)))) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [Fin.snoc_last, mlabels_eq, psum_last, sum_castSucc, Real.exp_add, ← mul_assoc]; rfl
  · rw [Fin.snoc_castSucc, mlabels_eq, mlabels_eq, psum_castSucc]

theorem psum_castAdd {K n : ℕ} (ξ : Fin (K + n) → ℝ) (j : Fin K) :
    psum ξ (Fin.castAdd n j) = psum (trn ξ) j := by
  unfold psum
  rw [Fin.sum_univ_add]
  have : ∀ i : Fin n, ¬ (Fin.natAdd K i ≤ Fin.castAdd n j) := fun i => by
    rw [not_le, Fin.lt_def]; simp; omega
  simp only [this, ite_false, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Fin.castAdd n i ≤ Fin.castAdd n j ↔ i ≤ j := by
    rw [Fin.le_def, Fin.le_def, Fin.val_castAdd, Fin.val_castAdd]
  rw [if_congr this rfl rfl]; rfl

theorem psum_natAdd {K n : ℕ} (ξ : Fin (K + n) → ℝ) (j : Fin n) :
    psum ξ (Fin.natAdd K j) = (∑ i, trn ξ i) + psum (evl ξ) j := by
  unfold psum
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have : Fin.castAdd n i ≤ Fin.natAdd K j := by rw [Fin.le_def]; simp; omega
    simp [this, trn]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.natAdd_le_natAdd_iff, evl]

/-- The labels split at the training/evaluation boundary. -/
theorem mlabels_append (δ : ℝ) {K n : ℕ} (x : ℝ) (ξ : Fin (K + n) → ℝ) :
    mlabels δ (K + n) x ξ = Fin.append (mlabels δ K x (trn ξ)) (mlabels δ n (xEnd x (trn ξ)) (evl ξ)) := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.append_left, mlabels_eq, mlabels_eq, psum_castAdd]
  · rw [Fin.append_right, mlabels_eq, mlabels_eq, psum_natAdd, xEnd, Real.exp_add, mul_assoc]

theorem xEnd_append {K n : ℕ} (x : ℝ) (ξ : Fin (K + n) → ℝ) :
    xEnd x ξ = xEnd (xEnd x (trn ξ)) (evl ξ) := by
  unfold xEnd
  rw [Fin.sum_univ_add, Real.exp_add, mul_assoc]; rfl

theorem xEnd_pos {m : ℕ} {x : ℝ} (hx : 0 < x) (ξ : Fin m → ℝ) : 0 < xEnd x ξ :=
  mul_pos hx (Real.exp_pos _)

theorem measurable_xEnd (m : ℕ) : Measurable fun q : ℝ × (Fin m → ℝ) => xEnd q.1 q.2 :=
  measurable_fst.mul (Real.measurable_exp.comp (Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply i).comp measurable_snd))

end Novel.D19FilteredLikelihood
