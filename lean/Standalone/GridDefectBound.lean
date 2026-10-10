import Mathlib.Basic.Real.Basic

/-! Finite mean-loss bound for D9. This is only scalar algebra after the
conditional-expectation step; it does not assert stochastic hypotheses. -/
namespace Standalone.GridDefectBound

def statement : Prop :=
  ∀ (N : ℕ) (π : ℝ) (x w : ℕ → ℝ),
    0 ≤ π → π ≤ 1 → x 0 = 1 → w 0 = 1 →
    (∀ i < N, 0 ≤ x i - x (i + 1)) →
    (∀ i < N, π ^ (i + 1) * (x i - x (i + 1)) ≤ w i - w (i + 1)) →
    π ^ N * (1 - x N) ≤ 1 - w N

end Standalone.GridDefectBound
