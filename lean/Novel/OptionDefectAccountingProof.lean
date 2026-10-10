import Standalone.OptionDefectAccounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! These are proved finite identities, not unproved pricing inputs.
Prior art: [carr2012hedging] (3.5)–(3.6), [kardaras2015strict] Example 4.8. -/
namespace Novel.OptionDefectAccounting

theorem proof : Standalone.OptionDefectAccounting.statement := by
  constructor
  · intro x K
    by_cases h : 0 ≤ x - K
    · rw [max_eq_left h, max_eq_right (show K - x ≤ 0 by linarith)]
      ring
    · rw [max_eq_right (show x - K ≤ 0 by linarith),
        max_eq_left (show 0 ≤ K - x by linarith)]
      ring
  · intro m C P K loading h
    have hc : C = m - K + P := by linarith
    rw [hc]
    ring

theorem expectation_residual (m C P K : ℝ) (h : C - P = m - K) :
    1 - K - C + P = 1 - m := by linarith

theorem restored_residual (m C P K : ℝ) (h : C - P = m - K) :
    1 - K - (C + (1 - m)) + P = 0 := by linarith

theorem quote_bounds (C P K Clo Chi Plo Phi : ℝ)
    (hCl : Clo ≤ C) (hCu : C ≤ Chi) (hPl : Plo ≤ P) (hPu : P ≤ Phi) :
    1 - K - Chi + Plo ≤ 1 - K - C + P ∧
    1 - K - C + P ≤ 1 - K - Clo + Phi := by
  constructor <;> linarith

end Novel.OptionDefectAccounting
