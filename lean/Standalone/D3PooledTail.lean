import Standalone.D3PowerTail

/-!
# Claim 015 (D3): shared power tails, sharp ratio intersection and occupation-based pooling

Statement only; the proof is `Novel/D3PooledTailProof.lean`. Source claim:
`claims/015-d3-pooled-tail.md`.

**Inputs.** The coefficient-level parts (exact observations, rectangles, the limitation of the
intersection rule) are deterministic and unconditional. The coverage parts are finite probability
statements with simultaneous coverage **supplied** as a premise. The occupation part is conditional,
for each name, on claim 013 part 3's premises, i.e. on **claim 012's conclusion** on both blocks
and **AX-51's** event convergence (claim 013's `TightOn` and `P(D_i^n Δ D_i) → 0`), all under one
joint law with no independence. The binary label's strict/true reading is conditional on AX-03 and is
commentary.

**Encodings.** The panel is a nonempty finite type `ι`, with onsets `R i > 0` and a common `r > 1`.
* `Shared R σ`: every `σ i` is in claim 013's `C_pow(R i)`, and one common `p` has
  `σ i x = κ_i x^p` for `x ≥ R i` with separate `κ_i > 0`. `SharedP R σ p` names that `p`.
* `B1 (R i) r (σ i)`, `B2 (R i) r (σ i)` and `θ (R i) (σ i)` are claim 013's.
* Rectangles: `ell i = L₂ᵢ/U₁ᵢ`, `u i = U₂ᵢ/L₁ᵢ`, `ellStar = max_i ell i`, `uStar = min_i u i`
  (`Finset.sup'`/`inf'` over the nonempty panel).
* `qSet`, `pSet`, `labelSet`: the sharp sets of the common ratio, exponent and label over shared
  coefficients whose `2m` integrals lie in the rectangles.
* `rejects`: the rule `ℓ_* ≤ u_* < 1`. Random rectangles are measurable functions of `ω`, with a
  positive lower first band (the claim's positive rectangles; only `L₁ > 0` is used).
* Occupation pooling: name `i` has claim 013's estimators `Bh1 i`, `Bh2 i`, block events `D1 i`,
  `D2 i`, sample and population occupation events `Ds i n`, `D i`, and a common `h`. `Φₙ = 1` is
  the union of the names' `reject` events; `D_union^n`, `D_union` are the unions.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D3PooledTail

open Standalone.D8TailCompletions (θ)
open Standalone.D3PowerTail

variable {ι : Type*}

/-- One common exponent `p`, separate scales. -/
def SharedP (R : ι → ℝ) (σ : ι → ℝ → ℝ) (p : ℝ) : Prop :=
  (∀ i, CPow (R i) (σ i)) ∧ ∀ i, ∃ κ : ℝ, 0 < κ ∧ ∀ x, R i ≤ x → σ i x = κ * x ^ p

/-- The shared-power class. -/
def Shared (R : ι → ℝ) (σ : ι → ℝ → ℝ) : Prop := ∃ p, SharedP R σ p

/-- The rectangle observation: all `2m` integrals lie in their intervals. -/
def InRect (R : ι → ℝ) (r : ℝ) (L1 U1 L2 U2 : ι → ℝ) (σ : ι → ℝ → ℝ) : Prop :=
  ∀ i, B1 (R i) r (σ i) ∈ Icc (L1 i) (U1 i) ∧ B2 (R i) r (σ i) ∈ Icc (L2 i) (U2 i)

/-- `ℓᵢ = L₂ᵢ/U₁ᵢ`. -/
noncomputable def ell (U1 L2 : ι → ℝ) (i : ι) : ℝ := L2 i / U1 i

/-- `uᵢ = U₂ᵢ/L₁ᵢ`. -/
noncomputable def u (L1 U2 : ι → ℝ) (i : ι) : ℝ := U2 i / L1 i

/-- `ℓ_* = max_i ℓᵢ`. -/
noncomputable def ellStar [Fintype ι] [Nonempty ι] (U1 L2 : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (ell U1 L2)

/-- `u_* = min_i uᵢ`. -/
noncomputable def uStar [Fintype ι] [Nonempty ι] (L1 U2 : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (u L1 U2)

/-- The sharp set of the common ratio. -/
def qSet (R : ι → ℝ) (r : ℝ) (L1 U1 L2 U2 : ι → ℝ) : Set ℝ :=
  {q | ∃ σ, Shared R σ ∧ InRect R r L1 U1 L2 U2 σ ∧ ∀ i, B2 (R i) r (σ i) / B1 (R i) r (σ i) = q}

/-- The sharp set of the common exponent. -/
def pSet (R : ι → ℝ) (r : ℝ) (L1 U1 L2 U2 : ι → ℝ) : Set ℝ :=
  {p | ∃ σ, SharedP R σ p ∧ InRect R r L1 U1 L2 U2 σ}

/-- The sharp set of the common label. -/
def labelSet (R : ι → ℝ) (r : ℝ) (L1 U1 L2 U2 : ι → ℝ) : Set ℕ :=
  {n | ∃ σ, Shared R σ ∧ InRect R r L1 U1 L2 U2 σ ∧ ∀ i, θ (R i) (σ i) = n}

/-- The rule `ℓ_* ≤ u_* < 1`. -/
def rejects [Fintype ι] [Nonempty ι] (L1 U1 L2 U2 : ι → ℝ) : Prop :=
  ellStar U1 L2 ≤ uStar L1 U2 ∧ uStar L1 U2 < 1

/-- Claim 015. -/
def statement : Prop :=
  -- The common ratio and the common label.
  (∀ {ι : Type*} (R : ι → ℝ) (r : ℝ) (σ : ι → ℝ → ℝ) (p : ℝ), (∀ i, 0 < R i) → 1 < r →
    SharedP R σ p → ∀ i, B2 (R i) r (σ i) / B1 (R i) r (σ i) = r ^ (2 - 2 * p) ∧
      θ (R i) (σ i) = if r ^ (2 - 2 * p) < 1 then 1 else 0) ∧
  -- Exact observations: positive first blocks fit every exponent; label set `{0, 1}`.
  (∀ {ι : Type*} [Nonempty ι] (R : ι → ℝ) (r : ℝ) (b1 : ι → ℝ), (∀ i, 0 < R i) → 1 < r →
    (∀ i, 0 < b1 i) →
    (∀ p : ℝ, ∃ σ, SharedP R σ p ∧ ∀ i, B1 (R i) r (σ i) = b1 i) ∧
    {n | ∃ σ, Shared R σ ∧ (∀ i, B1 (R i) r (σ i) = b1 i) ∧ ∀ i, θ (R i) (σ i) = n} = {0, 1}) ∧
  -- Exact observations: any common positive ratio is attained with any positive first blocks.
  (∀ {ι : Type*} (R : ι → ℝ) (r q : ℝ) (b1 : ι → ℝ), (∀ i, 0 < R i) → 1 < r → 0 < q →
    (∀ i, 0 < b1 i) → ∃ σ, Shared R σ ∧
      ∀ i, B1 (R i) r (σ i) = b1 i ∧ B2 (R i) r (σ i) = q * b1 i) ∧
  -- Rectangles: sharp sets, and the limitation of the intersection rule.
  (∀ {ι : Type*} [Fintype ι] [Nonempty ι] (R : ι → ℝ) (r : ℝ) (L1 U1 L2 U2 : ι → ℝ),
    (∀ i, 0 < R i) → 1 < r → (∀ i, 0 < L1 i) → (∀ i, L1 i ≤ U1 i) → (∀ i, 0 < L2 i) →
    (∀ i, L2 i ≤ U2 i) →
    qSet R r L1 U1 L2 U2 = ⋂ i, Icc (ell U1 L2 i) (u L1 U2 i) ∧
    qSet R r L1 U1 L2 U2 = Icc (ellStar U1 L2) (uStar L1 U2) ∧
    (ellStar U1 L2 ≤ uStar L1 U2 →
      pSet R r L1 U1 L2 U2 = Icc (1 - Real.log (uStar L1 U2) / (2 * Real.log r))
        (1 - Real.log (ellStar U1 L2) / (2 * Real.log r)) ∧
      (0 ∈ labelSet R r L1 U1 L2 U2 ↔ 1 ≤ uStar L1 U2) ∧
      (1 ∈ labelSet R r L1 U1 L2 U2 ↔ ellStar U1 L2 < 1) ∧
      (uStar L1 U2 < 1 ↔ ∃ i, u L1 U2 i < 1)) ∧
    (uStar L1 U2 < ellStar U1 L2 → labelSet R r L1 U1 L2 U2 = ∅) ∧
    ∀ i, (u L1 U2 i < 1 ↔ U2 i < L1 i)) ∧
  -- Conditional coverage: supplied simultaneous coverage bounds the size of the rule.
  (∀ {ι : Type*} [Fintype ι] [Nonempty ι] (R : ι → ℝ) (r : ℝ) (σ : ι → ℝ → ℝ),
    (∀ i, 0 < R i) → 1 < r → Shared R σ → (∀ i, θ (R i) (σ i) = 0) →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (L1 U1 L2 U2 : ι → Ω → ℝ) (α : ℝ), (∀ i, Measurable (L1 i)) → (∀ i, Measurable (U1 i)) →
      (∀ i, Measurable (L2 i)) → (∀ i, Measurable (U2 i)) → (∀ i ω, 0 < L1 i ω) →
      1 - α ≤ P.real {ω | InRect R r (fun i => L1 i ω) (fun i => U1 i ω) (fun i => L2 i ω)
        (fun i => U2 i ω) σ} →
      P.real {ω | rejects (fun i => L1 i ω) (fun i => U1 i ω) (fun i => L2 i ω)
        (fun i => U2 i ω)} ≤ α) ∧
  -- Bonferroni: per-name joint coverage failures summing to `α` give simultaneous coverage.
  (∀ {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (C : ι → Set Ω) (a : ι → ℝ) (α : ℝ), (∀ i, MeasurableSet (C i)) →
    (∀ i, P.real (C i)ᶜ ≤ a i) → ∑ i, a i ≤ α → 1 - α ≤ P.real (⋂ i, C i)) ∧
  -- The two-name example: marginal joint coverage `1 − α` each, pooled rejection probability `2α`.
  (∀ (R : Fin 2 → ℝ) (r α : ℝ), (∀ i, 0 < R i) → 1 < r → 0 < α → α ≤ 1 / 2 →
    ∃ σ : Fin 2 → ℝ → ℝ, Shared R σ ∧ (∀ i, θ (R i) (σ i) = 0) ∧
      (∀ i, B1 (R i) r (σ i) = 1 ∧ B2 (R i) r (σ i) = 1) ∧
      ∃ (P : Measure (Fin 3)) (_ : IsProbabilityMeasure P) (L1 U1 L2 U2 : Fin 2 → Fin 3 → ℝ),
        (∀ i, P.real {ω | B1 (R i) r (σ i) ∈ Icc (L1 i ω) (U1 i ω) ∧
          B2 (R i) r (σ i) ∈ Icc (L2 i ω) (U2 i ω)} = 1 - α) ∧
        P.real {ω | rejects (fun i => L1 i ω) (fun i => U1 i ω) (fun i => L2 i ω)
          (fun i => U2 i ω)} = 2 * α) ∧
  -- Occupation pooling, conditional on claim 013 part 3's premises for every name.
  (∀ {ι : Type*} [Fintype ι] (R : ι → ℝ) (r : ℝ) (σ : ι → ℝ → ℝ), (∀ i, 0 < R i) → 1 < r →
    Shared R σ →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Bh1 Bh2 : ι → ℕ → Ω → ℝ) (D1 D2 Ds : ι → ℕ → Set Ω) (D : ι → Set Ω) (h : ℕ → ℝ),
      (∀ i n, Measurable (Bh1 i n)) → (∀ i n, Measurable (Bh2 i n)) →
      (∀ i n, MeasurableSet (Ds i n)) → (∀ i, MeasurableSet (D i)) →
      (∀ i n, Ds i n ⊆ D1 i n) → (∀ i n, Ds i n ⊆ D2 i n) →
      (∀ i, TightOn P (Bh1 i) (B1 (R i) r (σ i)) (D1 i)) →
      (∀ i, TightOn P (Bh2 i) (B2 (R i) r (σ i)) (D2 i)) →
      (∀ i, Tendsto (fun n => P (symmDiff (Ds i n) (D i))) atTop (𝓝 0)) →
      Tendsto h atTop (𝓝 0) → Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * h n) atTop atTop →
      ((∀ i, θ (R i) (σ i) = 0) →
        Tendsto (fun n => P.real (⋃ i, reject (Bh1 i) (Bh2 i) h (Ds i) n)) atTop (𝓝 0)) ∧
      ((∀ i, θ (R i) (σ i) = 1) →
        Tendsto (fun n => P.real (⋃ i, reject (Bh1 i) (Bh2 i) h (Ds i) n)) atTop
          (𝓝 (P.real (⋃ i, D i))) ∧
        (0 < P.real (⋃ i, D i) →
          Tendsto (fun n => P.real (⋃ i, reject (Bh1 i) (Bh2 i) h (Ds i) n) /
            P.real (⋃ i, Ds i n)) atTop (𝓝 1)) ∧
        ∀ i, P.real (D i) ≤ P.real (⋃ i, D i)))

end Standalone.D3PooledTail
