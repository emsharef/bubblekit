import Mathlib.Basic.Real.Basic

/-! Finite daily-return accounting credited to [avellaneda2009path], (1)–(2).
These are algebraic identities, not stochastic or empirical hypotheses.
No strict-local-martingale conclusion is part of this statement. -/
namespace Standalone.DiscreteReturnAccounting

def statement : Prop :=
  ∀ (π x r f borrow Δ : ℝ),
    (1 - π) * (1 + r * Δ) + π * (1 + x) - f * Δ + π * borrow * Δ - 1 =
      π * x - ((π - 1) * r + f - π * borrow) * Δ

end Standalone.DiscreteReturnAccounting
