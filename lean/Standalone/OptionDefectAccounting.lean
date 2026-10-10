import Mathlib.Basic.Real.Basic

/-! Finite call-put algebra, with pricing-operator motivation from
[carr2012hedging] Corollary 3.8 and [kardaras2015strict] Example 4.8.
The loading is a declared scalar parameter; no market pricing convention,
expectation identity, stochastic model or test calibration is assumed here. -/
namespace Standalone.OptionDefectAccounting

def statement : Prop :=
  (∀ x K : ℝ, max (x - K) 0 - max (K - x) 0 = x - K) ∧
  (∀ m C P K loading : ℝ, C - P = m - K →
    1 - K - (C + loading * (1 - m)) + P = (1 - loading) * (1 - m))

end Standalone.OptionDefectAccounting
