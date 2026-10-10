import Standalone.D14RoundedStart
import Standalone.D14Cell

/-!
# Claim 030 (D14): monotone subdivision of the Gaussian rounded-cell likelihood envelope

Statement only; the proof is `Novel/D14CellSubdivisionProof.lean`. Source claim:
`claims/030-d14-cell-subdivision.md`.

**Structure.** `statement := interval ∧ bounds ∧ level0 ∧ monotone ∧ validity ∧ panel`.
* `interval`: (1) = (2). For a Gaussian step with mean `μ` and standard deviation `s > 0`, the
  probability of landing in `[L, R)` from an exact start in `[l, r)` has least upper bound `Wf`,
  the clipped-midpoint formula. It lies in `(0, 1]`. Source and target widths may differ.
* `bounds`: every `U` in (3) lies in `(0, 1]` and bounds the probability of the remaining observed
  label path from every exact log state in its subcell.
* `level0`: level zero is claim 029's product envelope `Standalone.D14Cell.Bcell`.
* `monotone`: (6).
* `validity`: parts 1 and 3. Under claim 028's observation contract, (5) holds at every level, for
  every label array, at almost every training record. Then the score with any measurable level
  `L(u, v)`, which may depend on the evaluation labels, has conditional and unconditional null
  moments `≤ 1`, size `≤ α`, and lower scores keep the moment.
* `panel`: claim 026's union bound and e-BH under AX-53, with lower scores and zero masks.

**Inputs.** FDR is conditional on AX-53 (claim 053's `AX53`). Everything else is proved: the
interval maximum, the backward induction over subcells, and claim 028's latent-endpoint mixture.
AX-58's domination is the finite sum `Σ_v (q/D) P(v | u) ≤ Σ_v q = 1`.

**Encodings.**
* Log coordinates. Cell `z` is `[h(z − 1/2), h(z + 1/2))`, claim 024's label cell of
  `exp`-coordinates. At level `ℓ` it splits into `2^ℓ` equal half-open subcells `sub h ℓ z a`,
  `a < 2^ℓ`, in increasing order; `lo h ℓ z a` is the left end of subcell `a`.
* A path is the last training label `z` and evaluation labels `v : Fin n → ℤ`, with step durations
  `Δ : Fin n → ℝ`. Step `j` has mean `(b − κ²/2)Δ_j` and standard deviation `κ √Δ_j`.
* `Ub h b κ ℓ n Δ z v a` is `U^ℓ_{θ,0,a}` of (3) for `θ = (b, κ)`. The bounds `U^ℓ_{θ,j,a}` for
  `j > 0` are `Ub` of the suffix, so (3)'s backward recursion is recursion on the suffix. At level
  `0` the parent term is `1`, which leaves `min(1, T)`.
* `Bθ` and `Dl` are (4)'s `B^ref` and `D^ref`. Claim 029's envelope is its own `Standalone.D14Cell.Bcell`.
* The actual law is claim 028's contract. `U` is the rounded training record in any measurable
  space, with measurable last label `z U`. `X > 0` is the latent exact endpoint with
  `Q_h(X) = rep h (z U)` almost surely. `R` is the vector of future log returns, whose conditional
  law given `(U, X)` is `lawR Δ b κ` almost surely, and `V = labF h X R` are the evaluation labels.
  The conditional law of `X` given `U` is otherwise arbitrary.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Standalone.D14CellSubdivision

open Standalone.RoundedCells Standalone.D14Misspecification Standalone.D14RoundedStart

/-- Clipping `x` to `[lo, hi]`. -/
def clip (lo hi x : ℝ) : ℝ := max lo (min hi x)

/-- (2): the largest probability of `[L, R)` from a start in `[l, r)`. -/
noncomputable def Wf (l r L R μ s : ℝ) : ℝ :=
  Φ ((R - clip (l + μ) (r + μ) ((L + R) / 2)) / s) -
    Φ ((L - clip (l + μ) (r + μ) ((L + R) / 2)) / s)

/-- The left end of subcell `a` of cell `z` at level `ℓ`, in log coordinates. -/
noncomputable def lo (h : ℝ) (ℓ : ℕ) (z : ℤ) (a : ℕ) : ℝ := h * (z - 1 / 2) + a * h / 2 ^ ℓ

/-- Subcell `a` of cell `z` at level `ℓ`. -/
def sub (h : ℝ) (ℓ : ℕ) (z : ℤ) (a : ℕ) : Set ℝ := Ico (lo h ℓ z a) (lo h ℓ z (a + 1))

/-- (1)–(2) for one step of duration `Δj` under `θ = (b, κ)`: source subcell `(z, a)`, target
subcell `(z', d)`. -/
noncomputable def Wst (h b κ Δj : ℝ) (ℓ : ℕ) (z : ℤ) (a : ℕ) (z' : ℤ) (d : ℕ) : ℝ :=
  Wf (lo h ℓ z a) (lo h ℓ z (a + 1)) (lo h ℓ z' d) (lo h ℓ z' (d + 1)) ((b - κ ^ 2 / 2) * Δj)
    (κ * Real.sqrt Δj)

/-- (3): the remaining-path bound `U^ℓ_{θ,0,a}` of the path `(z, v)`. -/
noncomputable def Ub (h b κ : ℝ) : (ℓ n : ℕ) → (Fin n → ℝ) → ℤ → (Fin n → ℤ) → ℕ → ℝ
  | _, 0, _, _, _, _ => 1
  | 0, n + 1, Δ, z, v, a =>
      min 1 (∑ d ∈ Finset.range (2 ^ 0), Wst h b κ (Δ 0) 0 z a (v 0) d *
        Ub h b κ 0 n (Fin.tail Δ) (v 0) (Fin.tail v) d)
  | ℓ + 1, n + 1, Δ, z, v, a =>
      min (min 1 (∑ d ∈ Finset.range (2 ^ (ℓ + 1)), Wst h b κ (Δ 0) (ℓ + 1) z a (v 0) d *
        Ub h b κ (ℓ + 1) n (Fin.tail Δ) (v 0) (Fin.tail v) d))
        (Ub h b κ ℓ (n + 1) Δ z v (a / 2))
termination_by ℓ n => (n, ℓ)

/-- (4): `B^ref,ℓ_θ`. -/
noncomputable def Bθ (h b κ : ℝ) (ℓ n : ℕ) (Δ : Fin n → ℝ) (z : ℤ) (v : Fin n → ℤ) : ℝ :=
  (Finset.range (2 ^ ℓ)).sup' ⟨0, Finset.mem_range.2 (pow_pos two_pos ℓ)⟩ (Ub h b κ ℓ n Δ z v)

/-- (4): `D^ref,ℓ`, over a catalogue `Γ` of pairs `(b, κ)`. -/
noncomputable def Dl (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty) (h : ℝ) (ℓ n : ℕ) (Δ : Fin n → ℝ)
    (z : ℤ) (v : Fin n → ℤ) : ℝ :=
  Γ.sup' hΓ fun θ => Bθ h θ.1 θ.2 ℓ n Δ z v

/-- (1) = (2): the Gaussian interval maximum. -/
def interval : Prop :=
  ∀ l r L R μ s : ℝ, l < r → L < R → 0 < s →
    0 < Wf l r L R μ s ∧ Wf l r L R μ s ≤ 1 ∧
    IsLUB ((fun x => (gaussianReal μ (s ^ 2).toNNReal).real {t | x + t ∈ Ico L R}) '' Ico l r)
      (Wf l r L R μ s)

/-- Part 1's subcell assertion: every `U` is in `(0, 1]` and bounds the remaining-path probability
from every exact log state of its subcell. -/
def bounds : Prop :=
  ∀ (h b κ : ℝ) (n : ℕ) (Δ : Fin n → ℝ) (ℓ : ℕ) (z : ℤ) (v : Fin n → ℤ) (a : ℕ),
    0 < h → 0 < κ → (∀ j, 0 < Δ j) → a < 2 ^ ℓ →
    0 < Ub h b κ ℓ n Δ z v a ∧ Ub h b κ ℓ n Δ z v a ≤ 1 ∧
    ∀ y ∈ sub h ℓ z a, (gres h Δ b κ (Real.exp y)).real {v} ≤ Ub h b κ ℓ n Δ z v a

/-- Part 2: level zero is claim 029's product envelope `Standalone.D14Cell.Bcell`. -/
def level0 : Prop :=
  ∀ (h b κ : ℝ) (n : ℕ) (Δ : Fin n → ℝ) (z : ℤ) (v : Fin n → ℤ),
    0 < h → 0 < κ → (∀ j, 0 < Δ j) →
    Bθ h b κ 0 n Δ z v =
      Standalone.D14Cell.Bcell h (Standalone.D14Cell.muθ Δ (b, κ)) (Standalone.D14Cell.sθ Δ (b, κ)) z v

/-- Part 2, (6). -/
def monotone : Prop :=
  (∀ (h b κ : ℝ) (n : ℕ) (Δ : Fin n → ℝ) (ℓ : ℕ) (z : ℤ) (v : Fin n → ℤ),
    Bθ h b κ (ℓ + 1) n Δ z v ≤ Bθ h b κ ℓ n Δ z v) ∧
  (∀ (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty) (h : ℝ) (n : ℕ) (Δ : Fin n → ℝ) (ℓ : ℕ) (z : ℤ)
    (v : Fin n → ℤ), Dl Γ hΓ h (ℓ + 1) n Δ z v ≤ Dl Γ hΓ h ℓ n Δ z v) ∧
  ∀ (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty) (h : ℝ) (n : ℕ) (Δ : Fin n → ℝ) (ℓ : ℕ) (z : ℤ)
    (v : Fin n → ℤ) (q : ℝ), 0 < h → (∀ j, 0 < Δ j) → (∀ θ ∈ Γ, 0 < θ.2) → 0 ≤ q →
    q / Dl Γ hΓ h ℓ n Δ z v ≤ q / Dl Γ hΓ h (ℓ + 1) n Δ z v

/-- Parts 1 and 3 for one name: (5) at every level, and validity at any measurable level choice. -/
def validity : Prop :=
  ∀ {Ω 𝒰 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Δ : Fin n → ℝ) (h b κ : ℝ) (U : Ω → 𝒰) (X : Ω → ℝ) (R : Ω → Fin n → ℝ)
    (z : 𝒰 → ℤ) (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty) (q : 𝒰 → (Fin n → ℤ) → ℝ)
    (Lv : 𝒰 → (Fin n → ℤ) → ℕ),
    (∀ j, 0 < Δ j) → 0 < h → (b, κ) ∈ Γ → (∀ θ ∈ Γ, 0 < θ.2) →
    Measurable U → Measurable X → Measurable R → Measurable z →
    (∀ v, Measurable fun u => q u v) → (∀ u v, 0 ≤ q u v) → (∀ u, HasSum (q u) 1) →
    (∀ v, Measurable fun u => Lv u v) →
    (∀ᵐ ω ∂P, 0 < X ω ∧ Qh h (X ω) = rep h (z (U ω))) →
    (∀ᵐ w ∂(P.map fun ω => (U ω, X ω)), condDistrib R (fun ω => (U ω, X ω)) P w = lawR Δ b κ) →
    let V := fun ω => labF h (X ω) (R ω)
    let E := fun u v => q u v / Dl Γ hΓ h (Lv u v) n Δ (z u) v
    -- (5), at every level and label array.
    (∀ᵐ u ∂(P.map U), ∀ (v : Fin n → ℤ) (ℓ : ℕ),
      (condDistrib V U P u).real {v} ≤ Bθ h b κ ℓ n Δ (z u) v ∧
      Bθ h b κ ℓ n Δ (z u) v ≤ Dl Γ hΓ h ℓ n Δ (z u) v) ∧
    -- The denominator is positive and finite; the score is measurable and nonnegative.
    (∀ (ℓ : ℕ) (z0 : ℤ) (v : Fin n → ℤ), 0 < Dl Γ hΓ h ℓ n Δ z0 v ∧ Dl Γ hΓ h ℓ n Δ z0 v ≤ 1) ∧
    Measurable (Function.uncurry E) ∧ (∀ u v, 0 ≤ E u v) ∧
    -- Null moments, conditional and unconditional.
    (∀ᵐ u ∂(P.map U), ∫⁻ v, ENNReal.ofReal (E u v) ∂(condDistrib V U P u) ≤ 1) ∧
    ∫⁻ ω, ENNReal.ofReal (E (U ω) (V ω)) ∂P ≤ 1 ∧
    -- Size at `1/α`, conditional and unconditional.
    (∀ α : ℝ, 0 < α → ∀ᵐ u ∂(P.map U),
      condDistrib V U P u {v | 1 / α < E u v} ≤ ENNReal.ofReal α) ∧
    (∀ α : ℝ, 0 < α → P.real {ω | 1 / α < E (U ω) (V ω)} ≤ α) ∧
    -- Lower implemented scores.
    ∀ F : Ω → ℝ, Measurable F → (∀ ω, 0 ≤ F ω ∧ F ω ≤ E (U ω) (V ω)) →
      ∫⁻ ω, ENNReal.ofReal (F ω) ∂P ≤ 1

/-- Claim 030. -/
def statement : Prop :=
  interval ∧ bounds ∧ level0 ∧ monotone ∧ validity ∧ Standalone.D14JumpRobustness.panel

end Standalone.D14CellSubdivision
