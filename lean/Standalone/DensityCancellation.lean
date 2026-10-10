import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Density cancellation on the visited range (deterministic part of claim 008)

Statement only; the proof is `Novel/DensityCancellationProof.lean`. This is the deterministic step
of claim 008, with no stochastic input.

Fix one path. A time path `s` on `(0, t]` occupies levels with the time weight `k`, and that
occupation has the density `Λ` in the level. Assume:
* the occupation formula holds for **every** Borel weight `f ≥ 0`, selected after the path is fixed;
* `k = σ(s)²` where `s > 0`, and `k = 0` where `s = 0`;
* up to a Lebesgue-null set of positive levels, the covered set `{Λ > 0}` is the open interval
  `(m, M)`.

Then for every Borel `B ⊆ (0, ∞)`,
`∫₀ᵗ 1_B(s_u) h(u) du = ∫_{B ∩ (m, M)} x/σ(x)² dx`. The reciprocal weight is `h(u) = s_u / Λ(s_u)`
where `s_u > 0` and `Λ(s_u) > 0`, and `0` otherwise. Integrals are extended nonnegative.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Standalone.DensityCancellation

/-- The reciprocal-local-time weight, with the zero convention. -/
noncomputable def weight (s Λ : ℝ → ℝ) (u : ℝ) : ℝ :=
  if 0 < s u ∧ 0 < Λ (s u) then s u / Λ (s u) else 0

/-- The deterministic density cancellation. -/
def statement : Prop :=
  ∀ (t m M : ℝ) (s k Λ σ : ℝ → ℝ), Measurable s → Measurable Λ → Measurable σ →
    (∀ x, 0 < x → σ x ≠ 0) → (∀ u, 0 ≤ s u) → (∀ x, 0 ≤ Λ x) →
    (∀ u, k u = if 0 < s u then σ (s u) ^ 2 else 0) →
    (∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ u in Ioc 0 t, f (s u) * ENNReal.ofReal (k u) = ∫⁻ x, f x * ENNReal.ofReal (Λ x)) →
    (∀ᵐ x, 0 < x → (x ∈ Ioo m M ↔ 0 < Λ x)) →
    ∀ B : Set ℝ, MeasurableSet B → B ⊆ Ioi 0 →
      ∫⁻ u in Ioc 0 t, B.indicator 1 (s u) * ENNReal.ofReal (weight s Λ u) =
        ∫⁻ x in B ∩ Ioo m M, ENNReal.ofReal (x / σ x ^ 2)

end Standalone.DensityCancellation
