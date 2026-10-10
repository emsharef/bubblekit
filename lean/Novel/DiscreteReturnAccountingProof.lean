import Standalone.DiscreteReturnAccounting
import Mathlib.Tactic.Ring

/-! The project proves the finite algebra from [avellaneda2009path], (1)–(2),
instead of assuming a closed algebraic proposition in an Upstream structure. -/
namespace Novel.DiscreteReturnAccounting

theorem proof : Standalone.DiscreteReturnAccounting.statement := by
  intro π x r f borrow Δ
  ring

-- The mean-gap identity is algebra once integrability and the mean are supplied.
theorem mean_gap (π m c e : ℝ) :
    1 - ((1 - π) + π * m - c + e) = π * (1 - m) + c - e := by
  ring

end Novel.DiscreteReturnAccounting
