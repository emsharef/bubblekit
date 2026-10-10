import Upstream.BoundedStopping

/-!
# AX-06  Nonnegative local martingales are supermartingales

Ledger entry AX-06 (`ledger/AXIOMS.md`). Sources: [hulley2019weak], Section 2, paragraph after the
proof of Lemma 2.1, printed p. 3; [mijatovic2010martingale], Discussion after (9), printed p. 5.

## Field

`supermartingale`: on a filtered probability space with a right-continuous filtration, a
nonnegative local martingale `S` is a supermartingale (Mathlib's `Supermartingale`: integrable,
adapted, `E[S_t | 𝓕_u] ≤ S_u` a.s. for `u ≤ t`). The premises are the D8 restriction in the ledger
(`ContLocMart` of `Upstream/BoundedStopping.lean`): adapted, continuous paths, deterministic start
`s₀ > 0`. These premises make the field weaker than the source's càdlàg statement, never stronger.

Deterministic consequences, proved here: expectations are nonincreasing in time (`integral_mono_time`)
and bounded by `s₀` (`integral_le_start`).

## Instance: DEGENERATE (genuine, not vacuous)

`NonnegativeSupermartingale.degenerateInstance` is on the one-point base. There every local martingale
is constant in time (`Stopping.unit_localMartingale_const`), hence a martingale and a supermartingale,
with equality in every inequality. The premises are satisfiable there (`Stopping.constant_model`).
This is a genuine model of the field, and degenerate: it is no evidence for any non-constant process.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace Upstream

open Diffusion Stopping

/-- AX-06 on the base `(Ω, Q, 𝓕)`. -/
structure NonnegativeSupermartingale {Ω : Type*} {mΩ : MeasurableSpace Ω} (Q : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) : Prop where
  /-- A nonnegative local martingale is a supermartingale. -/
  supermartingale : ∀ (S : ℝ≥0 → Ω → ℝ) (s₀ : ℝ), ContLocMart Q 𝓕 S s₀ →
    (∀ t ω, 0 ≤ S t ω) → Supermartingale S 𝓕 Q

namespace NonnegativeSupermartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- Expectations are nonincreasing in time. -/
theorem integral_mono_time [IsFiniteMeasure Q] {S : ℝ≥0 → Ω → ℝ} (h : Supermartingale S 𝓕 Q)
    {u t : ℝ≥0} (hut : u ≤ t) : ∫ ω, S t ω ∂Q ≤ ∫ ω, S u ω ∂Q := by
  have := h.setIntegral_le hut MeasurableSet.univ
  simpa using this

/-- `E[S_t] ≤ s₀`. -/
theorem integral_le_start [IsProbabilityMeasure Q] {S : ℝ≥0 → Ω → ℝ} {s₀ : ℝ}
    (h : Supermartingale S 𝓕 Q) (hstart : ∀ ω, S 0 ω = s₀) (t : ℝ≥0) :
    ∫ ω, S t ω ∂Q ≤ s₀ := by
  have := integral_mono_time h (bot_le : (0 : ℝ≥0) ≤ t)
  simpa [hstart] using this

end NonnegativeSupermartingale

/-- **Degenerate** instance on the one-point base. Genuine, not vacuous. -/
theorem NonnegativeSupermartingale.degenerateInstance :
    NonnegativeSupermartingale (Measure.dirac ()) unitFiltration where
  supermartingale S _ hS _ := by
    have hconst : S = fun _ _ => S 0 () := by
      ext t ω; cases ω; exact unit_localMartingale_const hS.localMart t
    rw [hconst]
    exact (martingale_const _ _ _).supermartingale

end Upstream
