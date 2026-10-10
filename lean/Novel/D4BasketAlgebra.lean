import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Claim 010: the deterministic algebra of parts 1–2

Finite-sum facts used by `Novel/D4BasketProof.lean`. No probability enters here.
* `ac_sum`: a finite combination of absolutely continuous functions is absolutely continuous.
* `hasDerivAt_sum`: the derivative of a finite combination.
* `hazard_mix`: the survival-adjusted hazard identity (4) and its weights summing to one.
-/

open Set

namespace Novel.D4BasketAlgebra

variable {ι : Type*}

/-- A finite combination of absolutely continuous functions is absolutely continuous. -/
theorem ac_sum (u : Finset ι) (w : ι → ℝ) (f : ι → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ i ∈ u, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun r => ∑ i ∈ u, w i * f i r) a b := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    simpa using (LipschitzOnWith.absolutelyContinuousOnInterval
      (f := fun _ : ℝ => (0 : ℝ)) (K := 0) (fun x _ y _ => by simp))
  | insert j u hj ih =>
    simp_rw [Finset.sum_insert hj]
    exact ((hf j (Finset.mem_insert_self j u)).const_mul (w j)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The derivative of a finite combination. -/
theorem hasDerivAt_sum (u : Finset ι) (w d : ι → ℝ) (f : ι → ℝ → ℝ) {r : ℝ}
    (hf : ∀ i ∈ u, HasDerivAt (f i) (d i) r) :
    HasDerivAt (fun r => ∑ i ∈ u, w i * f i r) (∑ i ∈ u, w i * d i) r :=
  HasDerivAt.fun_sum fun i hi => (hf i hi).const_mul (w i)

/-- Hazard identity (4): with `p_I = Σ wᵢ pᵢ > 0` and `pᵢ > 0`,
`−(Σ wᵢ dᵢ)/p_I = Σ (wᵢ pᵢ/p_I)(−dᵢ/pᵢ)`, and the weights `wᵢ pᵢ/p_I` sum to one. -/
theorem hazard_mix (u : Finset ι) (w p d : ι → ℝ) (hp : ∀ i ∈ u, p i ≠ 0)
    (hI : ∑ i ∈ u, w i * p i ≠ 0) :
    -(∑ i ∈ u, w i * d i) / (∑ i ∈ u, w i * p i) =
        ∑ i ∈ u, (w i * p i / ∑ j ∈ u, w j * p j) * (-d i / p i) ∧
      ∑ i ∈ u, w i * p i / (∑ j ∈ u, w j * p j) = 1 := by
  refine ⟨?_, by rw [← Finset.sum_div, div_self hI]⟩
  rw [← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := hp i hi
  field_simp

end Novel.D4BasketAlgebra
