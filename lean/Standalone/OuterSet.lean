import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Basic.Real.Basic

/-!
# Claim 014, deterministic part: exact elimination of the outer constraints (4)

Statement only; the proof is `Novel/OuterSetProof.lean`. Source claim:
`claims/014-d9-cross-pi-test.md`, part 1. No probability enters.

For a nonempty finite index type `ι`, coefficients `aⱼ > 0` and arbitrary reals `Lⱼ, Uⱼ` (possibly
inconsistent), `Bout a L U` is the set of `δ ∈ [0,1]` for which there are reals `zⱼ` with
`Lⱼ ≤ zⱼ ≤ Uⱼ`, `0 ≤ zⱼ ≤ 1`, `aⱼδ ≤ zⱼ` and `zⱼ = 0 ⇔ δ = 0` (4). Put `bⱼ = min(1, Uⱼ)` (`bnd`) and
`upper a U = min(1, minⱼ bⱼ/aⱼ)`.

**Statement.**
* Zero part: `0 ∈ Bout` iff `Lⱼ ≤ 0 ≤ Uⱼ` for every `j`. Equivalently, zero is excluded iff some
  `Lⱼ > 0` or some `Uⱼ < 0`.
* Positive part: empty if some `j` has `bⱼ ≤ 0` or `Lⱼ > bⱼ`; otherwise exactly
  `(0, upper a U]` (5), with the closed upper and open lower endpoint.
* Exact prices `L = U = d`:
  - a value outside `[0,1]`, or a mixture of zero and positive values, gives `∅`;
  - all zero gives `{0}`;
  - all in `(0,1]` gives `(0, upper a d]`, with a positive upper endpoint. The set excludes zero but
    has infimum zero: it contains values below every `ε > 0`.
-/

open Set

namespace Standalone.OuterSet

variable {ι : Type} [Fintype ι]

/-- The outer set `B_out(L,U)`, (4). -/
def Bout (a L U : ι → ℝ) : Set ℝ :=
  {δ | 0 ≤ δ ∧ δ ≤ 1 ∧ ∃ z : ι → ℝ, ∀ j, L j ≤ z j ∧ z j ≤ U j ∧ 0 ≤ z j ∧ z j ≤ 1 ∧
    a j * δ ≤ z j ∧ (z j = 0 ↔ δ = 0)}

/-- `bⱼ = min(1, Uⱼ)`. -/
noncomputable def bnd (U : ι → ℝ) (j : ι) : ℝ := min 1 (U j)

/-- `min(1, minⱼ bⱼ/aⱼ)`. -/
noncomputable def upper [Nonempty ι] (a U : ι → ℝ) : ℝ :=
  min 1 (Finset.univ.inf' Finset.univ_nonempty fun j => bnd U j / a j)

/-- Claim 014, the elimination of (4). -/
def statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (a L U : ι → ℝ), (∀ j, 0 < a j) →
    ((0 : ℝ) ∈ Bout a L U ↔ ∀ j, L j ≤ 0 ∧ 0 ≤ U j) ∧
    ((0 : ℝ) ∉ Bout a L U ↔ ∃ j, 0 < L j ∨ U j < 0) ∧
    ((∃ j, bnd U j ≤ 0 ∨ bnd U j < L j) → Bout a L U ∩ Ioi 0 = ∅) ∧
    ((∀ j, 0 < bnd U j ∧ L j ≤ bnd U j) → Bout a L U ∩ Ioi 0 = Ioc 0 (upper a U)) ∧
    ∀ d : ι → ℝ,
      ((∃ j, d j < 0 ∨ 1 < d j) → Bout a d d = ∅) ∧
      ((∃ i j, d i = 0 ∧ 0 < d j) → Bout a d d = ∅) ∧
      ((∀ j, d j = 0) → Bout a d d = {0}) ∧
      ((∀ j, 0 < d j ∧ d j ≤ 1) → Bout a d d = Ioc 0 (upper a d) ∧ 0 < upper a d ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ ∈ Bout a d d, δ < ε)

end Standalone.OuterSet
