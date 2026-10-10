import Standalone.PriceChain
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF

/-!
# Claim 024, deterministic part: rounding cells, the counterexample's constants, cell likelihoods

Statement only; the proof is `Novel/RoundedCellsProof.lean`. Source claim:
`claims/024-d14-rounded-observations.md`, parts 1 and 4, part 2's constants, and part 3's
cell-probability facts. No stochastic process enters. The probabilistic statement is
`Standalone.D14RoundedObservations`.

**Rounding.** For `h > 0` the label of `x` is `⌊log x / h + 1/2⌋`, `Q_h(x) = exp(h · label)`, and the
cell (1) of label `z` is `[exp(h(z − 1/2)), exp(h(z + 1/2)))`. For `x > 0` the label is `z` exactly
when `x` lies in that cell. For `x ≤ 0`, `Q_h` uses Lean's `log`; part 1 holds for every law,
including positive ones. "Atomless" is Mathlib's `NullSingletonClass`.

**TV.** As in claim 023, TV is `sup_A |H(A) − G(A)|` over measurable `A`, without the factor two.
TV = 1 is stated as `|H(A) − G(A)| ≤ 1` for every `A`, together with some measurable `A` having
`H(A) = 1` and `G(A) = 0`.

**Cell likelihoods.** For a density `d` on `(0, ∞)^{k+1+m}` relative to `posVol`, `lawD d` is the
law. `massU` is the training-cell mass `a(u)` and `massUV` the joint-cell mass `b(u, v)`, both in
`[0, ∞]`, and `gh = b/a` is (6).

**Statement.**
* **Part 1.**
  - Any law rounded by `Q_h` has TV one from any atomless law on `ℝ`.
  - Coordinatewise rounding of any law on `ℝⁿ`, `n ≥ 1`, has TV one from any law absolutely
    continuous with respect to Lebesgue measure.
* **Part 2's constants.**
  - `f₂(κ; 1, 1, 1)/f₁(1; 1, 1, 1) = R_h(κ)`, which is (3).
  - The `f₁` mass of the cell `0` is `p_h = Φ(1/2 + h/2) − Φ(1/2 − h/2) > 0`, which is (4), with
    `Φ` the standard normal distribution function.
  - `R_h(1/100) > 20` and `p_{1/2} > 1/20`.
  - `p_h R_h(κ) → ∞` as `κ ↓ 0`.
* **Part 3's cell facts.** For a positive, measurable, normalized density, `0 < g^h(v|u) ≤ 1`, and
  `g^h(·|u)` sums to one over `v ∈ ℤ^m` for every `u`.
* **Part 4.**
  - (7): with one training and one evaluation price, the joint and training cell masses are the
    displayed iterated integrals of a two-step chain with a measurable kernel, nonnegative at
    positive prices. The
    training mass uses the second kernel's normalization.
  - For GBM with `κ = 1`, grid `0, 1, 2`, start `1` and training label `0`, some evaluation label
    has `g^h(v|0)` different from the cell probability started at the rounded state
    `exp(h · 0) = 1`. This holds at every `h > 0`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Standalone.RoundedCells

open Standalone.PriceChain

/-- The cell label `⌊log x / h + 1/2⌋`. -/
noncomputable def lab (h x : ℝ) : ℤ := ⌊Real.log x / h + 1 / 2⌋

/-- The rounding operator `Q_h(x) = exp(h ⌊log x / h + 1/2⌋)`. -/
noncomputable def Qh (h x : ℝ) : ℝ := Real.exp (h * lab h x)

/-- The cell (1) with label `z`. -/
def cell (h : ℝ) (z : ℤ) : Set ℝ := Ico (Real.exp (h * (z - 1 / 2))) (Real.exp (h * (z + 1 / 2)))

/-- Rounding every coordinate. -/
noncomputable def QhV {n : ℕ} (h : ℝ) (x : Fin n → ℝ) : Fin n → ℝ := fun j => Qh h (x j)

/-- The law with density `d` relative to `posVol^n`. -/
noncomputable def lawD {n : ℕ} (d : (Fin n → PosReal) → ℝ) : Measure (Fin n → PosReal) :=
  (Measure.pi fun _ : Fin n => posVol).withDensity fun y => ENNReal.ofReal (d y)

/-- The training-cell mass `a(u)`. -/
noncomputable def massU {k m : ℕ} (h : ℝ) (d : (Fin (k + 1 + m) → PosReal) → ℝ)
    (u : Fin (k + 1) → ℤ) : ℝ≥0∞ :=
  lawD d {y | ∀ j, lab h (y (Fin.castAdd m j)) = u j}

/-- The joint-cell mass `b(u, v)`. -/
noncomputable def massUV {k m : ℕ} (h : ℝ) (d : (Fin (k + 1 + m) → PosReal) → ℝ)
    (u : Fin (k + 1) → ℤ) (v : Fin m → ℤ) : ℝ≥0∞ :=
  lawD d {y | (∀ j, lab h (y (Fin.castAdd m j)) = u j) ∧
    ∀ l, lab h (y (Fin.natAdd (k + 1) l)) = v l}

/-- (6): `g^h(v | u) = b(u, v)/a(u)`. -/
noncomputable def gh {k m : ℕ} (h : ℝ) (d : (Fin (k + 1 + m) → PosReal) → ℝ)
    (u : Fin (k + 1) → ℤ) (v : Fin m → ℤ) : ℝ :=
  (massUV h d u v / massU h d u).toReal

/-- (3). -/
noncomputable def Rh (κ : ℝ) : ℝ := Real.exp (1 / 8) * (1 - Real.exp (-2 / κ ^ 2)) / κ

/-- The standard normal distribution function. -/
noncomputable def Φ : ℝ → ℝ := cdf (gaussianReal 0 1)

/-- (4). -/
noncomputable def ph (h : ℝ) : ℝ := Φ (1 / 2 + h / 2) - Φ (1 / 2 - h / 2)

/-- The deterministic part of claim 024. -/
def statement : Prop :=
  -- Rounding cells.
  (∀ h x : ℝ, 0 < h → 0 < x → ∀ z : ℤ, (lab h x = z ↔ x ∈ cell h z)) ∧
  -- Part 1: TV one from an atomless reference, and from an absolutely continuous one on `ℝⁿ`.
  (∀ (h : ℝ) (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G] [NullSingletonClass G],
    0 < h →
    (∀ A, MeasurableSet A → |(H.map (Qh h)).real A - G.real A| ≤ 1) ∧
    ∃ A, MeasurableSet A ∧ H.map (Qh h) A = 1 ∧ G A = 0) ∧
  (∀ (h : ℝ) (n : ℕ) (H G : Measure (Fin n → ℝ)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G], 0 < h → 0 < n → G ≪ volume →
    (∀ A, MeasurableSet A → |(H.map (QhV h)).real A - G.real A| ≤ 1) ∧
    ∃ A, MeasurableSet A ∧ H.map (QhV h) A = 1 ∧ G A = 0) ∧
  -- Part 2's constants.
  (∀ κ : ℝ, 0 < κ → f2 κ 1 1 1 / f1 1 1 1 1 = Rh κ) ∧
  (∀ h : ℝ, 0 < h →
    ENNReal.ofReal (ph h) = ∫⁻ y in {y : PosReal | lab h y = 0}, ENNReal.ofReal (f1 1 1 1 y)
      ∂posVol ∧ 0 < ph h) ∧
  20 < Rh (1 / 100) ∧ 1 / 20 < ph (1 / 2) ∧
  (∀ h : ℝ, 0 < h → Tendsto (fun κ => ph h * Rh κ) (𝓝[>] 0) atTop) ∧
  -- Part 3's cell facts.
  (∀ (h : ℝ) (k m : ℕ) (d : (Fin (k + 1 + m) → PosReal) → ℝ), 0 < h → Measurable d →
    (∀ y, 0 < d y) → ∫⁻ y, ENNReal.ofReal (d y) ∂(Measure.pi fun _ => posVol) = 1 →
    ∀ u, (∀ v, 0 < gh h d u v ∧ gh h d u v ≤ 1) ∧ HasSum (fun v => gh h d u v) 1) ∧
  -- Part 4: (7), and the GBM disagreement with substitution of the rounded state.
  (∀ (h : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (Δ : Fin 2 → ℝ) (s : ℝ) (u v : Fin 1 → ℤ),
    (∀ Δ', Measurable (Function.uncurry (f Δ'))) → (∀ Δ' x y, 0 < y → 0 ≤ f Δ' x y) →
    (∀ x : ℝ, 0 < x → ∫⁻ y, ENNReal.ofReal (f (Δ 1) x y) ∂posVol = 1) →
    massUV (k := 0) h (chain f Δ s) u v =
      ∫⁻ x in {x : PosReal | lab h x = u 0}, ENNReal.ofReal (f (Δ 0) s x) *
        ∫⁻ y in {y : PosReal | lab h y = v 0}, ENNReal.ofReal (f (Δ 1) x y) ∂posVol ∂posVol ∧
    massU (m := 1) h (chain f Δ s) u =
      ∫⁻ x in {x : PosReal | lab h x = u 0}, ENNReal.ofReal (f (Δ 0) s x) ∂posVol) ∧
  (∀ h : ℝ, 0 < h → ∃ v : Fin 1 → ℤ,
    gh (k := 0) h (chain (f1 1) (fun _ => 1) 1) (fun _ => 0) v ≠
      (∫⁻ y in {y : PosReal | lab h y = v 0},
        ENNReal.ofReal (f1 1 1 (Real.exp (h * ((0 : ℤ) : ℝ))) y) ∂posVol).toReal)

end Standalone.RoundedCells
