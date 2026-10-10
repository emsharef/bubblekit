import Standalone.D12CatalogueFDR
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Function.Floor

/-!
# Claim 029 (D14): a computable Gaussian cell envelope for rounded-price likelihoods

Statement only; the proof is `Novel/D14CellProof.lean`. Source claim:
`claims/029-d14-gaussian-cell-envelope.md`.

**Inputs.**
* The validity of part 1 is AX-58's pointwise step with counting measure: `D ≥ P(v | u)` at every
  label vector, so `Σ_v (q/D) P(v | u) ≤ Σ_v q = 1`. It is proved directly here.
* The FDR conjunct is conditional on AX-53 (claim 053's `AX53`).
* The Gaussian cell probabilities use Mathlib's normal CDF (`cdf (gaussianReal 0 1)`), with the
  derivative by the fundamental theorem of calculus.

**Encodings** (log-price coordinates, tick `h > 0`, steps `Δ_j > 0`, `n` evaluation steps).
* `label h x = ⌊x/h + 1/2⌋`, so `x` lies in the cell `I_z = [h(z−1/2), h(z+1/2))` exactly when its
  label is `z`.
* `labelsW h x₀ ξ` is the evaluation label vector of the walk `x₀ + ξ₁ + ⋯ + ξ_j`.
* `walkLaw h μ s x₀` is its law, with independent increments `ξ_j ~ Normal(μ_j, s_j²)`. Here
  `μ_j = (b − κ²/2)Δ_j` and `s_j = κ√Δ_j` for a Gaussian null `θ = (b, κ)`.
* `Kcell` is (1), `Bcell` is the path envelope in (2), and `Dcell = max_{θ ∈ Γ} Bcell`.
* The rounded training block `U` lives in `Fin (k+1) → ℤ` and ends at label `z₀ = U_last`.
* **The contract** (claim 028's, in log coordinates).
  - `X` is the latent exact log endpoint, with `X ∈ I_{z₀}` almost surely; its conditional law given
    `U` is otherwise arbitrary.
  - `R` is the vector of future log increments. Its conditional law given `(U, X)` is, almost surely,
    the product of the `Normal(μ_j, s_j²)` laws of `θ`.
  - The evaluation labels are `V = labelsW h X R`.
* The numerator is any normalized forecast `q(u, ·)` on label vectors. The score is
  `E = ofReal q / D` in `[0, ∞]`; it is finite since `D > 0`.

Part 2 (an operation count for the exact formula) is commentary and is not formalized.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Standalone.D14Cell

/-- The standard normal CDF. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The rounding label of a log price. -/
noncomputable def label (h x : ℝ) : ℤ := ⌊x / h + 1 / 2⌋

/-- The labels of the walk `x₀ + ξ₁ + ⋯ + ξ_j`. -/
noncomputable def labelsW (h : ℝ) : (n : ℕ) → ℝ → (Fin n → ℝ) → (Fin n → ℤ)
  | 0, _, _ => Fin.elim0
  | n + 1, x₀, ξ => Fin.cons (label h (x₀ + ξ 0)) (labelsW h n (x₀ + ξ 0) (Fin.tail ξ))

/-- The law of the evaluation labels from the exact log start `x₀`. -/
noncomputable def walkLaw (h : ℝ) {n : ℕ} (μ s : Fin n → ℝ) (x₀ : ℝ) : Measure (Fin n → ℤ) :=
  (Measure.pi fun j => gaussianReal (μ j) (s j ^ 2).toNNReal).map (labelsW h n x₀)

/-- (1): the largest probability of cell `z` over exact starts in cell `zp`. -/
noncomputable def Kcell (h μ s : ℝ) (zp z : ℤ) : ℝ :=
  let m := min (h * (zp + 1 / 2) + μ) (max (h * (zp - 1 / 2) + μ) (h * z))
  Phi ((h * (z + 1 / 2) - m) / s) - Phi ((h * (z - 1 / 2) - m) / s)

/-- The path envelope `B` of (2). -/
noncomputable def Bcell (h : ℝ) {n : ℕ} (μ s : Fin n → ℝ) (z₀ : ℤ) (v : Fin n → ℤ) : ℝ :=
  ∏ j, Kcell h (μ j) (s j) ((Fin.cons z₀ v : Fin (n + 1) → ℤ) j.castSucc) (v j)

/-- The step means and scales of a Gaussian null `θ = (b, κ)`. -/
noncomputable def muθ {n : ℕ} (Δ : Fin n → ℝ) (θ : ℝ × ℝ) : Fin n → ℝ :=
  fun j => (θ.1 - θ.2 ^ 2 / 2) * Δ j
noncomputable def sθ {n : ℕ} (Δ : Fin n → ℝ) (θ : ℝ × ℝ) : Fin n → ℝ :=
  fun j => θ.2 * Real.sqrt (Δ j)

/-- The denominator `D = max_{θ ∈ Γ} B_θ`. -/
noncomputable def Dcell (h : ℝ) {n : ℕ} (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (z₀ : ℤ)
    (v : Fin n → ℤ) : ℝ≥0∞ :=
  ⨆ θ ∈ Γ, ENNReal.ofReal (Bcell h (muθ Δ θ) (sθ Δ θ) z₀ v)

/-- The cell `I_z`. -/
def cell (h : ℝ) (z : ℤ) : Set ℝ := Ico (h * (z - 1 / 2)) (h * (z + 1 / 2))

open Classical in
/-- Claim 029, part 1. -/
def part1 : Prop :=
  -- (1) bounds the one-step cell probability from every start in the previous cell, and is the
  -- least such bound.
  (∀ (h μ s : ℝ) (zp z : ℤ), 0 < h → 0 < s →
    (∀ x ∈ cell h zp, gaussianReal (x + μ) (s ^ 2).toNNReal (cell h z) ≤
      ENNReal.ofReal (Kcell h μ s zp z)) ∧
    (∀ y < Kcell h μ s zp z, ∃ x ∈ cell h zp,
      ENNReal.ofReal y < gaussianReal (x + μ) (s ^ 2).toNNReal (cell h z)) ∧
    0 < Kcell h μ s zp z ∧ Kcell h μ s zp z < 1) ∧
  -- (3) along a path: the label law from any start in `I_{z₀}` is at most the envelope.
  (∀ (h : ℝ) (n : ℕ) (μ s : Fin n → ℝ) (x₀ : ℝ) (z₀ : ℤ) (v : Fin n → ℤ), 0 < h →
    (∀ j, 0 < s j) → x₀ ∈ cell h z₀ → walkLaw h μ s x₀ {v} ≤ ENNReal.ofReal (Bcell h μ s z₀ v)) ∧
  -- Validity under the latent-endpoint contract.
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (k n : ℕ)
    (h : ℝ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (U : Ω → Fin (k + 1) → ℤ) (X : Ω → ℝ)
    (R : Ω → Fin n → ℝ) (q : (Fin (k + 1) → ℤ) → (Fin n → ℤ) → ℝ) (θ : ℝ × ℝ),
    0 < h → (∀ j, 0 < Δ j) → (∀ θ' ∈ Γ, 0 < θ'.2) → θ ∈ Γ →
    Measurable U → Measurable X → Measurable R →
    (∀ u v, 0 ≤ q u v) → (∀ u, ∑' v, ENNReal.ofReal (q u v) = 1) →
    -- The latent exact log endpoint lies in the last training cell.
    (∀ᵐ ω ∂P, X ω ∈ cell h (U ω (Fin.last k))) →
    -- Given the training record and the exact endpoint, the future log increments are
    -- independent Gaussians under `θ`.
    (∀ᵐ w ∂(P.map fun ω => (U ω, X ω)), condDistrib R (fun ω => (U ω, X ω)) P w =
      Measure.pi fun j => gaussianReal (muθ Δ θ j) (sθ Δ θ j ^ 2).toNNReal) →
    let V := fun ω => labelsW h n (X ω) (R ω)
    let D := fun u v => Dcell h Δ Γ (u (Fin.last k)) v
    let E := fun u v => ENNReal.ofReal (q u v) / D u v
    (∀ u v, 0 < D u v ∧ D u v < ⊤) ∧ (∀ u v, E u v < ⊤) ∧
    (∀ᵐ u ∂(P.map U), ∀ v, condDistrib V U P u {v} ≤
      ENNReal.ofReal (Bcell h (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v) ∧
      ENNReal.ofReal (Bcell h (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v) ≤ D u v) ∧
    (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
    ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
    ∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
  -- The panel: union bound; e-BH under AX-53, with or without a mask.
  (∀ {ι Ω : Type} [Fintype ι] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Rj : ι → Set Ω) (b : ι → ℝ) (N₀ : Finset ι), (∀ i ∈ N₀, P.real (Rj i) ≤ b i) →
    P.real (⋃ i ∈ N₀, Rj i) ≤ min 1 (∑ i ∈ N₀, b i)) ∧
  (Standalone.D12CatalogueFDR.AX53 → ∀ {ι : Type} [Fintype ι] [Nonempty ι] {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Er : ι → Ω → ℝ) (N₀ : Finset ι)
    (q : ℝ), 0 < q → q < 1 → (∀ i, Measurable (Er i)) → (∀ i ω, 0 ≤ Er i ω) →
    (∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (Er i ω) ∂P ≤ 1) →
    ∫ ω, Standalone.D12CatalogueFDR.fdp q (fun i => Er i ω) N₀ ∂P ≤ q * N₀.card / Fintype.card ι ∧
    ∀ S : Ω → Finset ι, (∀ i, MeasurableSet {ω | i ∈ S ω}) →
      ∫ ω, Standalone.D12CatalogueFDR.fdp q (fun i => if i ∈ S ω then Er i ω else 0) N₀ ∂P ≤
        q * N₀.card / Fintype.card ι)

/-- Claim 029, part 3: zero log drift, equal steps. -/
def part3 : Prop :=
  ∀ (h s : ℝ), 0 < h → 0 < s →
    -- (4): every row of the one-step envelope has total mass `S_cell = 2Φ(h/(2s)) > 1`.
    (∀ zp : ℤ, HasSum (fun z : ℤ => Kcell h 0 s zp z) (2 * Phi (h / (2 * s)))) ∧
    1 < 2 * Phi (h / (2 * s)) ∧
    -- Over `n` future labels the path envelope has mass `S_cell^n`; the normalized sequential
    -- forecast with transitions `K/S_cell` sums to one and has the constant score `S_cell^(−n)`.
    (∀ (n : ℕ) (z₀ : ℤ),
      HasSum (fun v : Fin n → ℤ => Bcell h (fun _ => 0) (fun _ => s) z₀ v)
        ((2 * Phi (h / (2 * s))) ^ n) ∧
      HasSum (fun v : Fin n → ℤ => ∏ j, Kcell h 0 s ((Fin.cons z₀ v : Fin (n + 1) → ℤ) j.castSucc)
        (v j) / (2 * Phi (h / (2 * s)))) 1 ∧
      ∀ v : Fin n → ℤ, (∏ j, Kcell h 0 s ((Fin.cons z₀ v : Fin (n + 1) → ℤ) j.castSucc)
        (v j) / (2 * Phi (h / (2 * s)))) / Bcell h (fun _ => 0) (fun _ => s) z₀ v =
        ((2 * Phi (h / (2 * s))) ^ n)⁻¹) ∧
    -- Normalizing the envelope is invalid: one step from the representative `0` of label `0`,
    -- the forecast concentrated on label `0`, and the denominator `B/S_cell` give null mean
    -- `S_cell > 1`.
    (walkLaw h (fun _ : Fin 1 => (0 : ℝ)) (fun _ => s) 0 {fun _ => 0} =
        ENNReal.ofReal (Kcell h 0 s 0 0) ∧
      ENNReal.ofReal (2 * Phi (h / (2 * s)) / Kcell h 0 s 0 0) *
        walkLaw h (fun _ : Fin 1 => (0 : ℝ)) (fun _ => s) 0 {fun _ => 0} =
        ENNReal.ofReal (2 * Phi (h / (2 * s))))

/-- Claim 029. -/
def statement : Prop := part1 ∧ part3

end Standalone.D14Cell
