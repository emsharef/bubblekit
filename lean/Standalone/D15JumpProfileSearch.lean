import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Claim 061 (D15), deterministic stage: the search rectangle (5) and box enclosures (6)

Statement only; the proof is `Novel/D15JumpProfileSearchProof.lean`. Source claim:
`claims/061-d15-shared-jump-profile.md`, parts 2 and 3. Part 1 (coverage, `V_J ≤ U_J`, scores)
and the price bound (7)–(8) build on claim 060's definitions and are a later stage.

**Structure.** `statement := search ∧ enclosure`.
* `search`: part 2. For a finite cap the profile `F_J` of (1) has an attained maximum over
  `a ∈ ℝ, s ≥ σ_min`, at a point of the rectangle `[a₋, a₊] × [σ_min, s₊]` of (4)–(5).
  - `L > 0` and `σ_min ≤ s₀ ≤ s₊`; the start `(a₀, s₀)` lies in the rectangle.
  - The ceiling `F_J(a, s) ≤ C_d s^(−n)` holds.
* `enclosure`: part 3.
  - (6) bounds `F_J` on its box. It is monotone under shrinking the box, and equals `F_J` on a
    degenerate box.
  - A finite cover of the rectangle gives `sup F_J ≤ B_P`, and refinement does not raise `B_P`.
  - **Convergence.** For every `ε > 0` there is a mesh `η > 0` such that any boxes inside the
    rectangle with sides `≤ η`, each with an evaluated point, have `B_P ≤ max_i F_J(p_i) + ε`. With
    `L_P ≤ max F_J ≤ B_P`, the gap is at most `ε`.

**Encodings** (return coordinates; `n` evaluation increments with durations `d_j > 0` and log
returns `r_j`; finite cap `Λ ≥ 0` and floor `σ_min > 0`).
* `qJ Λ d_j = exp(−Λ d_j)`, `Cd d = ∏ (2π d_j)^(−1/2)`. `brk Λ d_j x s = 1 − q_j + q_j
  exp(−x²/(2 s² d_j))` is (1)'s bracket at residual `x`, and `FJ` is `F_J(a, s)` of (1).
* `aLo`, `aHi`, `a0`, `Qres`, `s0`, `L0` and `sP` are (4): `a₋ = min r_j/d_j`, `a₊ = max r_j/d_j`,
  `a₀`, `Q`, `s₀`, `L` and `s₊ = (C_d/L)^(1/n)`.
* A box is `(l_a, u_a, l_s, u_s)`, the set `[l_a, u_a] × [l_s, u_s]`. `edst` is
  `e_j(B) = dist(r_j, [l_a d_j, u_a d_j])`, and `WJ` is (6).
-/

open Set Real

namespace Standalone.D15JumpProfileSearch

variable {n : ℕ}

/-- `q_j = exp(−Λ d_j)`. -/
noncomputable def qJ (Λ dj : ℝ) : ℝ := Real.exp (-(Λ * dj))

/-- `C_d = ∏_j (2π d_j)^(−1/2)`. -/
noncomputable def Cd (d : Fin n → ℝ) : ℝ := ∏ j, (Real.sqrt (2 * π * d j))⁻¹

/-- (1)'s bracket `p_j + q_j exp(−x²/(2 s² d_j))` at residual `x`. -/
noncomputable def brk (Λ dj x s : ℝ) : ℝ :=
  1 - qJ Λ dj + qJ Λ dj * Real.exp (-x ^ 2 / (2 * s ^ 2 * dj))

/-- (1): the shared-parameter profile `F_J(a, s)`. -/
noncomputable def FJ (Λ : ℝ) (d r : Fin n → ℝ) (a s : ℝ) : ℝ :=
  Cd d * (s ^ n)⁻¹ * ∏ j, brk Λ (d j) (r j - a * d j) s

/-- (4): `a₋ = min_j r_j/d_j`. -/
noncomputable def aLo (d r : Fin n → ℝ) : ℝ := ⨅ j, r j / d j

/-- (4): `a₊ = max_j r_j/d_j`. -/
noncomputable def aHi (d r : Fin n → ℝ) : ℝ := ⨆ j, r j / d j

/-- (4): `a₀ = Σ r_j / Σ d_j`. -/
noncomputable def a0 (d r : Fin n → ℝ) : ℝ := (∑ j, r j) / ∑ j, d j

/-- (4): `Q = Σ (r_j − a₀ d_j)²/d_j`. -/
noncomputable def Qres (d r : Fin n → ℝ) : ℝ := ∑ j, (r j - a0 d r * d j) ^ 2 / d j

/-- (4): `s₀ = max(σ_min, √(Q/n))`. -/
noncomputable def s0 (σmin : ℝ) (d r : Fin n → ℝ) : ℝ := max σmin (Real.sqrt (Qres d r / n))

/-- (4): `L = F_J(a₀, s₀)`. -/
noncomputable def L0 (Λ σmin : ℝ) (d r : Fin n → ℝ) : ℝ := FJ Λ d r (a0 d r) (s0 σmin d r)

/-- (4): `s₊ = (C_d/L)^(1/n)`. -/
noncomputable def sP (Λ σmin : ℝ) (d r : Fin n → ℝ) : ℝ :=
  (Cd d / L0 Λ σmin d r) ^ ((n : ℝ)⁻¹)

/-- The search rectangle of (5). -/
def rect (Λ σmin : ℝ) (d r : Fin n → ℝ) : Set (ℝ × ℝ) :=
  Icc (aLo d r) (aHi d r) ×ˢ Icc σmin (sP Λ σmin d r)

/-- The box `[l_a, u_a] × [l_s, u_s]` of `B = (l_a, u_a, l_s, u_s)`. -/
def box (B : ℝ × ℝ × ℝ × ℝ) : Set (ℝ × ℝ) := Icc B.1 B.2.1 ×ˢ Icc B.2.2.1 B.2.2.2

/-- `e_j(B) = dist(r_j, [l_a d_j, u_a d_j])`. -/
noncomputable def edst (dj rj la ua : ℝ) : ℝ := max 0 (max (la * dj - rj) (rj - ua * dj))

/-- (6): the box bound `W_J(B)`. -/
noncomputable def WJ (Λ : ℝ) (d r : Fin n → ℝ) (B : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  Cd d * (B.2.2.1 ^ n)⁻¹ * ∏ j, brk Λ (d j) (edst (d j) (r j) B.1 B.2.1) B.2.2.2

/-- `B'` lies inside `B`, in endpoint form, with a nonempty scale side. -/
def Inside (B' B : ℝ × ℝ × ℝ × ℝ) : Prop :=
  B.1 ≤ B'.1 ∧ B'.2.1 ≤ B.2.1 ∧ B.2.2.1 ≤ B'.2.2.1 ∧ B'.2.2.1 ≤ B'.2.2.2 ∧ B'.2.2.2 ≤ B.2.2.2

/-- Part 2: the compact search rectangle (5). -/
def search : Prop :=
  ∀ (n : ℕ) (d r : Fin n → ℝ) (Λ σmin : ℝ), 0 < n → (∀ j, 0 < d j) → 0 ≤ Λ → 0 < σmin →
    0 < L0 Λ σmin d r ∧ σmin ≤ s0 σmin d r ∧ s0 σmin d r ≤ sP Λ σmin d r ∧
    aLo d r ≤ aHi d r ∧ (a0 d r, s0 σmin d r) ∈ rect Λ σmin d r ∧
    (∀ a s, 0 < s → 0 < FJ Λ d r a s ∧ FJ Λ d r a s ≤ Cd d * (s ^ n)⁻¹) ∧
    ∃ p ∈ rect Λ σmin d r, ∀ a s, σmin ≤ s → FJ Λ d r a s ≤ FJ Λ d r p.1 p.2

/-- Part 3: the box enclosures (6) and their convergence. -/
def enclosure : Prop :=
  ∀ (n : ℕ) (d r : Fin n → ℝ) (Λ σmin : ℝ), 0 < n → (∀ j, 0 < d j) → 0 ≤ Λ → 0 < σmin →
    -- (6) bounds `F_J` on its box.
    (∀ B a s, 0 < B.2.2.1 → (a, s) ∈ box B → FJ Λ d r a s ≤ WJ Λ d r B) ∧
    -- Shrinking a box does not raise (6).
    (∀ B B', 0 < B.2.2.1 → Inside B' B → WJ Λ d r B' ≤ WJ Λ d r B) ∧
    -- On a degenerate box, (6) is `F_J`.
    (∀ a s, 0 < s → WJ Λ d r (a, a, s, s) = FJ Λ d r a s) ∧
    -- A finite cover of the rectangle bounds the supremum: `sup F_J ≤ B_P`.
    (∀ {ι : Type} (I : Finset ι) (hI : I.Nonempty) (bx : ι → ℝ × ℝ × ℝ × ℝ),
      (∀ i ∈ I, 0 < (bx i).2.2.1) → rect Λ σmin d r ⊆ ⋃ i ∈ I, box (bx i) →
      ∀ a s, σmin ≤ s → FJ Λ d r a s ≤ I.sup' hI fun i => WJ Λ d r (bx i)) ∧
    -- Refinement does not raise `B_P`.
    (∀ {ι κ : Type} (I : Finset ι) (hI : I.Nonempty) (bx : ι → ℝ × ℝ × ℝ × ℝ)
      (K : Finset κ) (hK : K.Nonempty) (bx' : κ → ℝ × ℝ × ℝ × ℝ),
      (∀ i ∈ I, 0 < (bx i).2.2.1) → (∀ k ∈ K, ∃ i ∈ I, Inside (bx' k) (bx i)) →
      (K.sup' hK fun k => WJ Λ d r (bx' k)) ≤ I.sup' hI fun i => WJ Λ d r (bx i)) ∧
    -- Convergence: fine boxes inside the rectangle, each with an evaluated point, close the gap.
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ {ι : Type} (I : Finset ι) (hI : I.Nonempty) (bx : ι → ℝ × ℝ × ℝ × ℝ) (pt : ι → ℝ × ℝ),
        (∀ i ∈ I, box (bx i) ⊆ rect Λ σmin d r) →
        (∀ i ∈ I, (bx i).2.1 - (bx i).1 ≤ η ∧ (bx i).2.2.2 - (bx i).2.2.1 ≤ η) →
        (∀ i ∈ I, pt i ∈ box (bx i)) →
        (I.sup' hI fun i => WJ Λ d r (bx i)) ≤ (I.sup' hI fun i => FJ Λ d r (pt i).1 (pt i).2) + ε

/-- Claim 061, deterministic stage. -/
def statement : Prop := search ∧ enclosure

end Standalone.D15JumpProfileSearch
