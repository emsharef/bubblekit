import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Basic.Real.Basic

/-!
# Claim 018, deterministic part: exact elimination of the leveraged outer constraints (3)

Statement only; the proof is `Novel/OuterSetLevProof.lean`. Source claim:
`claims/018-d9-positive-liquidation.md`, part 2. No probability enters.

For a nonempty finite index type, coefficients `Mⱼ > 1`, floors `0 ≤ Aⱼ < 1` and arbitrary reals
`Lⱼ, Uⱼ`, `Blev M A L U` is the set of `δ ∈ [0,1]` admitting reals `zⱼ` with `Lⱼ ≤ zⱼ ≤ Uⱼ`,
`0 ≤ zⱼ ≤ 1 − Aⱼ` and `zⱼ ≤ Mⱼδ` (3). Put `ℓⱼ = max(0, Lⱼ)`, `uⱼ = min(Uⱼ, 1 − Aⱼ)` and
`lower M L = maxⱼ ℓⱼ/Mⱼ`.

**Statement.**
* If some `ℓⱼ > uⱼ`, `Blev` is empty. Otherwise it is the closed interval `[lower M L, 1]` (4),
  with `lower M L ∈ [0, 1]`.
* `0 ∈ Blev` iff `Lⱼ ≤ 0 ≤ Uⱼ` for every `j`. Equivalently, zero is excluded iff some `Lⱼ > 0` or some
  `Uⱼ < 0`.
* Exact prices `L = U = d` with `0 ≤ dⱼ ≤ 1 − Aⱼ` give `[maxⱼ dⱼ/Mⱼ, 1]`. All-zero defects give
  `[0, 1]`: they impose no restriction.
-/

open Set

namespace Standalone.OuterSetLev

variable {ι : Type}

/-- The outer set `B_lev(L,U)`, (3). -/
def Blev (M A L U : ι → ℝ) : Set ℝ :=
  {δ | 0 ≤ δ ∧ δ ≤ 1 ∧ ∃ z : ι → ℝ, ∀ j, L j ≤ z j ∧ z j ≤ U j ∧ 0 ≤ z j ∧ z j ≤ 1 - A j ∧
    z j ≤ M j * δ}

/-- `ℓⱼ = max(0, Lⱼ)`. -/
noncomputable def lo (L : ι → ℝ) (j : ι) : ℝ := max 0 (L j)

/-- `uⱼ = min(Uⱼ, 1 − Aⱼ)`. -/
noncomputable def up (A U : ι → ℝ) (j : ι) : ℝ := min (U j) (1 - A j)

/-- `maxⱼ ℓⱼ/Mⱼ`. -/
noncomputable def lower [Fintype ι] [Nonempty ι] (M L : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j => lo L j / M j

/-- Claim 018, the elimination of (3). -/
def statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (M A L U : ι → ℝ), (∀ j, 1 < M j) →
    (∀ j, 0 ≤ A j ∧ A j < 1) →
    ((∃ j, up A U j < lo L j) → Blev M A L U = ∅) ∧
    ((∀ j, lo L j ≤ up A U j) → Blev M A L U = Icc (lower M L) 1 ∧
      0 ≤ lower M L ∧ lower M L ≤ 1) ∧
    ((0 : ℝ) ∈ Blev M A L U ↔ ∀ j, L j ≤ 0 ∧ 0 ≤ U j) ∧
    ((0 : ℝ) ∉ Blev M A L U ↔ ∃ j, 0 < L j ∨ U j < 0) ∧
    ∀ d : ι → ℝ, (∀ j, 0 ≤ d j ∧ d j ≤ 1 - A j) →
      Blev M A d d = Icc (Finset.univ.sup' Finset.univ_nonempty fun j => d j / M j) 1 ∧
      ((∀ j, d j = 0) → Blev M A d d = Icc 0 1)

end Standalone.OuterSetLev
