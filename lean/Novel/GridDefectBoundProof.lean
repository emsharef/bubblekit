import Standalone.GridDefectBound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-! D9's finite-grid scalar bound applies Mathlib's telescoping-sum identity
and antitonicity of powers on [0,1]. No stochastic input is assumed here. -/
namespace Novel.GridDefectBound

theorem proof : Standalone.GridDefectBound.statement := by
  intro N π x w hp hp1 hx hw hnonneg hstep
  calc
    π ^ N * (1 - x N) =
        ∑ i ∈ Finset.range N, π ^ N * (x i - x (i + 1)) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub', hx]
    _ ≤ ∑ i ∈ Finset.range N, (w i - w (i + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hp hp1 (Nat.succ_le_of_lt hiN))
        (hnonneg i hiN)).trans (hstep i hiN)
    _ = 1 - w N := by rw [Finset.sum_range_sub', hw]

end Novel.GridDefectBound
