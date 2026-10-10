import Standalone.D14Cell

/-!
# Claim 031 (D14): Gaussian cell envelopes for fixed monetary ticks, including zero quotes

Statement only; the proof is `Novel/D14FixedTickProof.lean`. Source claim:
`claims/031-d14-fixed-tick-cells.md`.

**Structure.** `statement := part1 ∧ part2 ∧ part3`.

**Inputs.**
* The validity of parts 1 and 2 is AX-58's pointwise step with counting measure: the denominator
  dominates the actual label mass, so `Σ_v (q/D) P(v | u) ≤ Σ_v q = 1`. It is proved directly.
* The FDR conjunct is conditional on AX-53 (claim 053's `AX53`).
* Normal probabilities use Mathlib's normal CDF, as in claim 029 (`Standalone.D14Cell.Phi`).

**Encodings** (prices, not log prices; tick `δ > 0`).
* `mlabel δ x = ⌊x/δ + 1/2⌋₊` is the label of a nonnegative exact price, so `Q_δ(x) = δ · mlabel δ x`.
* `mcell δ z = [mlo, mhi)` is `C_z^δ`: `mlo δ z = max 0 (δ(z − 1/2))` is `0` for `z = 0` and
  `δ(z − 1/2)` otherwise, and `mhi δ z = δ(z + 1/2)`.
* One step from the exact price `x ≥ 0` is `x · exp ξ` with `ξ ~ Normal(μ, s²)`. `stepP μ s x T` is the
  probability that it lies in `T`. From `x = 0` the step stays at `0`: the trapped state.
* `Wm a b c d μ s` is (2) for the source `[a, b)` and target `[c, d)`.
* `mlabels δ x ξ` are the labels of the exact path `x · exp(ξ₁ + ⋯ + ξ_j)`, which is identically
  zero from `x = 0`. `walkM δ μ s x` is their law under independent `ξ_j ~ Normal(μ_j, s_j²)`, with
  `μ_j = (b − κ²/2)Δ_j` and `s_j = κ√Δ_j` (claim 029's `muθ`, `sθ`).
* `Bm` is part 1's direct envelope `B^δ`.
* **Level `ℓ`.** Cell `z` splits into `2^ℓ` equal price-width half-open subcells `sub δ ℓ z a`,
  `a < 2^ℓ`, in increasing order. Subcell `0` of `C_0^δ` contains the exact state `0`.
  - `Wsub` is (2) between subcells.
  - `Ub δ ℓ n μ s z v a` is claim 030's backward recursion (3) for the path `(z, v)` from subcell
    `a`: `min(1, T)` at level `0`, and `min(1, T, U^(ℓ−1)_(⌊a/2⌋))` above.
  - `Bl` is the maximum over the initial subcells, and `Dm` the maximum over the catalogue.
* **The contract.**
  - `U` is the rounded training record, ending at label `z₀ = U_last`.
  - `X ≥ 0` is the exact endpoint, with `X ∈ C_(z₀)^δ` almost surely; its conditional law given `U`
    is otherwise arbitrary.
  - `R` is the vector of future log returns. Given `(U, X)` with `X > 0`, its conditional law is
    almost surely the product of the `Normal(μ_j, s_j²)` laws. Nothing is assumed about `R` when
    `X = 0`, since the path `X · exp(⋯)` is then zero.
  - The evaluation labels are `V = mlabels δ X R`.

Part 2's operation count `O(n K² |Γ|)` is commentary and is not formalized.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Standalone.D14FixedTick

open Standalone.D14Cell

/-- The monetary label of a nonnegative exact price. -/
noncomputable def mlabel (δ x : ℝ) : ℕ := ⌊x / δ + 1 / 2⌋₊

/-- The left end of `C_z^δ`. -/
noncomputable def mlo (δ : ℝ) (z : ℕ) : ℝ := max 0 (δ * (z - 1 / 2))

/-- The right end of `C_z^δ`. -/
noncomputable def mhi (δ : ℝ) (z : ℕ) : ℝ := δ * (z + 1 / 2)

/-- The monetary cell `C_z^δ` of (1). -/
def mcell (δ : ℝ) (z : ℕ) : Set ℝ := Ico (mlo δ z) (mhi δ z)

/-- The probability that one Gaussian step from the exact price `x` lands in `T`. -/
noncomputable def stepP (μ s x : ℝ) (T : Set ℝ) : ℝ≥0∞ :=
  gaussianReal μ (s ^ 2).toNNReal {ξ | x * Real.exp ξ ∈ T}

/-- (2): the largest probability of `[c, d)` from an exact price in `[a, b)`. -/
noncomputable def Wm (a b c d μ s : ℝ) : ℝ :=
  if c = 0 then (if a = 0 then 1 else Phi ((Real.log d - Real.log a - μ) / s))
  else
    let m := if a = 0 then min (Real.log b + μ) ((Real.log c + Real.log d) / 2)
      else min (Real.log b + μ) (max (Real.log a + μ) ((Real.log c + Real.log d) / 2))
    Phi ((Real.log d - m) / s) - Phi ((Real.log c - m) / s)

/-- The labels of the exact path `x · exp(ξ₁ + ⋯ + ξ_j)`. -/
noncomputable def mlabels (δ : ℝ) : (n : ℕ) → ℝ → (Fin n → ℝ) → (Fin n → ℕ)
  | 0, _, _ => Fin.elim0
  | n + 1, x, ξ => Fin.cons (mlabel δ (x * Real.exp (ξ 0)))
      (mlabels δ n (x * Real.exp (ξ 0)) (Fin.tail ξ))

/-- The law of the evaluation labels from the exact price `x`. -/
noncomputable def walkM (δ : ℝ) {n : ℕ} (μ s : Fin n → ℝ) (x : ℝ) : Measure (Fin n → ℕ) :=
  (Measure.pi fun j => gaussianReal (μ j) (s j ^ 2).toNNReal).map (mlabels δ n x)

/-- Part 1's direct envelope `B^δ`. -/
noncomputable def Bm (δ : ℝ) {n : ℕ} (μ s : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ) : ℝ :=
  ∏ j, let zp := (Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc
    Wm (mlo δ zp) (mhi δ zp) (mlo δ (v j)) (mhi δ (v j)) (μ j) (s j)

/-- The left end of subcell `a` of `C_z^δ` at level `ℓ`. -/
noncomputable def slo (δ : ℝ) (ℓ z a : ℕ) : ℝ := mlo δ z + a * (mhi δ z - mlo δ z) / 2 ^ ℓ

/-- Subcell `a` of `C_z^δ` at level `ℓ`. -/
def sub (δ : ℝ) (ℓ z a : ℕ) : Set ℝ := Ico (slo δ ℓ z a) (slo δ ℓ z (a + 1))

/-- (2) between subcells. -/
noncomputable def Wsub (δ μ s : ℝ) (ℓ z a z' d : ℕ) : ℝ :=
  Wm (slo δ ℓ z a) (slo δ ℓ z (a + 1)) (slo δ ℓ z' d) (slo δ ℓ z' (d + 1)) μ s

/-- Claim 030's backward recursion (3) on monetary subcells: the remaining-path bound for the path
`(z, v)` from subcell `a`. -/
noncomputable def Ub (δ : ℝ) : (ℓ n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → ℕ → (Fin n → ℕ) → ℕ → ℝ
  | _, 0, _, _, _, _, _ => 1
  | 0, n + 1, μ, s, z, v, a =>
      min 1 (∑ d ∈ Finset.range (2 ^ 0), Wsub δ (μ 0) (s 0) 0 z a (v 0) d *
        Ub δ 0 n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d)
  | ℓ + 1, n + 1, μ, s, z, v, a =>
      min (min 1 (∑ d ∈ Finset.range (2 ^ (ℓ + 1)), Wsub δ (μ 0) (s 0) (ℓ + 1) z a (v 0) d *
        Ub δ (ℓ + 1) n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d))
        (Ub δ ℓ (n + 1) μ s z v (a / 2))
termination_by ℓ n => (n, ℓ)

/-- `B^(δ,ℓ)`: the maximal initial-subcell bound. -/
noncomputable def Bl (δ : ℝ) (ℓ : ℕ) {n : ℕ} (μ s : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ) : ℝ :=
  (Finset.range (2 ^ ℓ)).sup' ⟨0, Finset.mem_range.2 (pow_pos two_pos ℓ)⟩
    (Ub δ ℓ n μ s z₀ v)

/-- `D^(δ,ℓ)`: the catalogue maximum of (4). -/
noncomputable def Dm (δ : ℝ) (ℓ : ℕ) {n : ℕ} (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (z₀ : ℕ)
    (v : Fin n → ℕ) : ℝ≥0∞ :=
  ⨆ θ ∈ Γ, ENNReal.ofReal (Bl δ ℓ (muθ Δ θ) (sθ Δ θ) z₀ v)

/-- The forecast prototype's representative of label `z`: `δ/4` for `z = 0`, `δ z` otherwise. -/
noncomputable def mrep (δ : ℝ) (z : ℕ) : ℝ := if z = 0 then δ / 4 else δ * z

/-- The forecast prototype's one-step cell probability. -/
noncomputable def fstep (δ μ s : ℝ) (zp z : ℕ) : ℝ := (stepP μ s (mrep δ zp) (mcell δ z)).toReal

/-- Claim 031, part 1. -/
def part1 : Prop :=
  -- (2) is the supremum of the one-step target probability over exact sources in `[a, b)`, and
  -- lies in `(0, 1]`.
  (∀ (a b c d μ s : ℝ), 0 ≤ a → a < b → 0 ≤ c → c < d → 0 < s →
    (∀ x ∈ Ico a b, stepP μ s x (Ico c d) ≤ ENNReal.ofReal (Wm a b c d μ s)) ∧
    (∀ y < Wm a b c d μ s, ∃ x ∈ Ico a b, ENNReal.ofReal y < stepP μ s x (Ico c d)) ∧
    0 < Wm a b c d μ s ∧ Wm a b c d μ s ≤ 1) ∧
  -- The trapped state gives zero to every positive target and one to every zero-cell target.
  (∀ (c d μ s : ℝ), (0 < c → stepP μ s 0 (Ico c d) = 0) ∧ (0 < d → stepP μ s 0 (Ico 0 d) = 1)) ∧
  -- The direct envelope dominates the label law from every exact start in `C_(z₀)^δ`.
  (∀ (δ : ℝ) (n : ℕ) (μ s : Fin n → ℝ) (x₀ : ℝ) (z₀ : ℕ) (v : Fin n → ℕ), 0 < δ →
    (∀ j, 0 < s j) → x₀ ∈ mcell δ z₀ → walkM δ μ s x₀ {v} ≤ ENNReal.ofReal (Bm δ μ s z₀ v))

open Classical in
/-- Claim 031, part 2. -/
def part2 : Prop :=
  -- Every `U` lies in `(0, 1]` and bounds the remaining-path probability from its subcell.
  (∀ (δ : ℝ) (ℓ n : ℕ) (μ s : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (a : ℕ), 0 < δ →
    (∀ j, 0 < s j) → a < 2 ^ ℓ →
    0 < Ub δ ℓ n μ s z v a ∧ Ub δ ℓ n μ s z v a ≤ 1 ∧
    ∀ x ∈ sub δ ℓ z a, walkM δ μ s x {v} ≤ ENNReal.ofReal (Ub δ ℓ n μ s z v a)) ∧
  -- (3)'s ordering: `0 < B^(δ,ℓ+1) ≤ B^(δ,ℓ) ≤ B^δ ≤ 1`.
  (∀ (δ : ℝ) (ℓ n : ℕ) (μ s : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ), 0 < δ → (∀ j, 0 < s j) →
    0 < Bl δ (ℓ + 1) μ s z₀ v ∧ Bl δ (ℓ + 1) μ s z₀ v ≤ Bl δ ℓ μ s z₀ v ∧
    Bl δ ℓ μ s z₀ v ≤ Bm δ μ s z₀ v ∧ Bm δ μ s z₀ v ≤ 1) ∧
  -- Validity at every level, with any data-selected level `L(u, v)`.
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (k n : ℕ)
    (δ : ℝ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (U : Ω → Fin (k + 1) → ℕ) (X : Ω → ℝ)
    (R : Ω → Fin n → ℝ) (q : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ)
    (Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ) (θ : ℝ × ℝ),
    0 < δ → (∀ j, 0 < Δ j) → (∀ θ' ∈ Γ, 0 < θ'.2) → θ ∈ Γ →
    Measurable U → Measurable X → Measurable R →
    (∀ u v, 0 ≤ q u v) → (∀ u, ∑' v, ENNReal.ofReal (q u v) = 1) →
    -- The exact endpoint lies in the last training cell.
    (∀ᵐ ω ∂P, X ω ∈ mcell δ (U ω (Fin.last k))) →
    -- From a positive endpoint, the future log returns are independent Gaussians under `θ`.
    (∀ᵐ w ∂(P.map fun ω => (U ω, X ω)), 0 < w.2 →
      condDistrib R (fun ω => (U ω, X ω)) P w =
        Measure.pi fun j => gaussianReal (muθ Δ θ j) (sθ Δ θ j ^ 2).toNNReal) →
    let V := fun ω => mlabels δ n (X ω) (R ω)
    let E := fun u v => ENNReal.ofReal (q u v) / Dm δ (Lv u v) Δ Γ (u (Fin.last k)) v
    (∀ (ℓ : ℕ) (u : Fin (k + 1) → ℕ) (v : Fin n → ℕ),
      0 < Dm δ ℓ Δ Γ (u (Fin.last k)) v ∧ Dm δ ℓ Δ Γ (u (Fin.last k)) v ≤ 1) ∧
    (∀ u v, E u v < ⊤) ∧
    (∀ᵐ u ∂(P.map U), ∀ v ℓ, condDistrib V U P u {v} ≤
      ENNReal.ofReal (Bl δ ℓ (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v) ∧
      ENNReal.ofReal (Bl δ ℓ (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v) ≤
        Dm δ ℓ Δ Γ (u (Fin.last k)) v) ∧
    (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
    ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
    (∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
    -- Lower implemented scores keep the moment.
    ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1) ∧
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
        q * N₀.card / Fintype.card ι) ∧
  -- The forecast prototype: each row is a probability on the labels, and the product over an
  -- evaluation path is a normalized forecast with positive masses.
  (∀ (δ : ℝ) (n : ℕ) (μ s : Fin n → ℝ) (z₀ : ℕ), 0 < δ → (∀ j, 0 < s j) →
    (∀ j zp, HasSum (fun z => fstep δ (μ j) (s j) zp z) 1) ∧
    HasSum (fun v : Fin n → ℕ => ∏ j, fstep δ (μ j) (s j)
      ((Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc) (v j)) 1 ∧
    ∀ v : Fin n → ℕ, 0 < ∏ j, fstep δ (μ j) (s j) ((Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc)
      (v j))

/-- Claim 031, part 3. -/
def part3 : Prop :=
  -- (5): the log width of a positive cell, and its ratio to `δ/y` tends to one as `δ/y → 0`.
  (∀ (δ : ℝ) (z : ℕ), 0 < δ → 1 ≤ z →
    Real.log (mhi δ z) - Real.log (mlo δ z) = Real.log ((δ * z + δ / 2) / (δ * z - δ / 2))) ∧
  Tendsto (fun t : ℝ => Real.log ((1 + t / 2) / (1 - t / 2)) / t) (𝓝[>] 0) (𝓝 1) ∧
  -- The zero-quote cell has no finite log width.
  (∀ (δ M : ℝ), 0 < δ → ∃ x ∈ mcell δ 0, 0 < x ∧ M < Real.log (mhi δ 0) - Real.log x) ∧
  -- (6): re-emergence from the positive state `δ/4`, but not from the trapped state.
  (∀ (δ μ s : ℝ), 0 < δ → 0 < s →
    stepP μ s (δ / 4) {x | 1 ≤ mlabel δ x} = ENNReal.ofReal (1 - Phi ((Real.log 2 - μ) / s)) ∧
    0 < 1 - Phi ((Real.log 2 - μ) / s) ∧ stepP μ s 0 {x | 1 ≤ mlabel δ x} = 0) ∧
  -- On the all-zero path from a zero quote, the envelope is one at every level.
  (∀ (δ : ℝ) (ℓ n : ℕ) (μ s : Fin n → ℝ), 0 < δ → (∀ j, 0 < s j) →
    Bm δ μ s 0 (fun _ => 0) = 1 ∧ Bl δ ℓ μ s 0 (fun _ => 0) = 1 ∧
    walkM δ μ s 0 {fun _ => 0} = 1)

/-- Claim 031. -/
def statement : Prop := part1 ∧ part2 ∧ part3

end Standalone.D14FixedTick
