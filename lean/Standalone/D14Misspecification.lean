import Standalone.D12CatalogueFDR
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Claim 023 (D14): conditional-law robustness of catalogue scores

Statement only; the proof is `Novel/D14MisspecificationProof.lean`. Source claim:
`claims/023-d14-conditional-misspecification.md`.

**Scope.** All four parts. Part 3's decimal evaluations (0.08319, 0.13319, 0.08034, 0.35594,
0.999987) are numerical illustrations and are not formalized; the formulas they evaluate are.

**Inputs.** The FDR bound (4) is conditional on AX-53 (claim 053's restated `AX53`). Everything
else here is proved: disintegration of the actual joint law, the split-density cancellation under
the reference (as in `Novel.SplitLikelihood.ax52_holds`), Markov, the eventwise TV comparison,
layer-cake integration and finite algebra.

**Encodings.** One name has claim 051's catalogue model (`CatalogueModel`: measurable blocks,
s-finite `μ`, positive normalized densities `g`, a training-only selector `sel` with measurable
fibres), exponents `p` and the score `E = Eval …`.
* The actual law `P` need **not** be in the catalogue. Its conditional evaluation law given the
  training block is `H u = condDistrib V U P u`.
* A null reference is `ref : 𝒰 → Θ`, with measurable fibres and `p (ref u) ≤ 1`. Its conditional law
  is `G u = μ.withDensity (g (ref u) u ·)`.
* (1) is `TVEnv`: for `P∘U⁻¹`-almost every `u` and every measurable `A`, `|H u A − G u A| ≤ ε u`.
  This is TV without the factor two. The envelope `ε` is measurable with values in `[0, 1]`.
* `Erob = min(E, c)/(1 + c ε(U))` is (3).
* Part 3 works on evaluation log returns `R ∈ ℝ^n`. `lawR Δ b σ` is (6): independent
  `Normal((b − σ²/2)Δ_j, σ²Δ_j)` coordinates. The reference with volatility `κ` and zero drift is
  `lawR Δ 0 κ`. `densR` is the product density, `AG` is (7) and `εG = √(1 − AG²)`.
  The passage to prices is any measurable map `T` (for the lower bound, a measurable embedding,
  such as the log-return bijection at a fixed last training price). The link to (1) takes the actual
  conditional law and the catalogue reference to be pushforwards of these two laws at each training
  value.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Standalone.D14Misspecification

open Standalone.D3PowerTail Standalone.D3CatalogueCalibration Standalone.D12CatalogueFDR

/-- (1): the actual conditional evaluation law is within `ε u` in TV of the null reference. -/
def TVEnv {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒱] [Nonempty 𝒱] (P : Measure Ω) [IsFiniteMeasure P] (U : Ω → 𝒰)
    (V : Ω → 𝒱) (μ : Measure 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ) (ref : 𝒰 → Θ) (ε : 𝒰 → ℝ) : Prop :=
  ∀ᵐ u ∂(P.map U), ∀ A : Set 𝒱, MeasurableSet A →
    |(condDistrib V U P u).real A -
      (μ.withDensity fun v => ENNReal.ofReal (g (ref u) u v)).real A| ≤ ε u

/-- A null reference with a valid envelope. -/
structure NullRef {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒱] [Nonempty 𝒱] (P : Measure Ω) [IsFiniteMeasure P] (U : Ω → 𝒰)
    (V : Ω → 𝒱) (μ : Measure 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ) (p : Θ → ℝ) (ref : 𝒰 → Θ) (ε : 𝒰 → ℝ) :
    Prop where
  measRef : ∀ θ, MeasurableSet (ref ⁻¹' {θ})
  null : ∀ u, p (ref u) ≤ 1
  measε : Measurable ε
  ε_nonneg : ∀ u, 0 ≤ ε u
  ε_le_one : ∀ u, ε u ≤ 1
  env : TVEnv P U V μ g ref ε

/-- (3): the clipped, deflated score. -/
noncomputable def Erob {Ω 𝒰 𝒱 Θ : Type} (U : Ω → 𝒰) (V : Ω → 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ)
    (sel : 𝒰 → Θ) (p : Θ → ℝ) (ε : 𝒰 → ℝ) (c : ℝ) (ω : Ω) : ℝ :=
  min (Eval U V g sel p ω) c / (1 + c * ε (U ω))

/-- (6): independent Normal log returns with drift `b`, volatility `σ` and increments `Δ`. -/
noncomputable def lawR {n : ℕ} (Δ : Fin n → ℝ) (b σ : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi fun j => gaussianReal ((b - σ ^ 2 / 2) * Δ j) (σ ^ 2 * Δ j).toNNReal

/-- The product density of `lawR`. -/
noncomputable def densR {n : ℕ} (Δ : Fin n → ℝ) (b σ : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ j, gaussianPDFReal ((b - σ ^ 2 / 2) * Δ j) (σ ^ 2 * Δ j).toNNReal (x j)

/-- (7): the Gaussian affinity, with `n` increments of total length `τ`. -/
noncomputable def AG (n : ℕ) (τ b σ κ : ℝ) : ℝ :=
  (2 * σ * κ / (σ ^ 2 + κ ^ 2)) ^ ((n : ℝ) / 2) *
    Real.exp (-(b + (κ ^ 2 - σ ^ 2) / 2) ^ 2 * τ / (4 * (σ ^ 2 + κ ^ 2)))

/-- (8): the envelope. -/
noncomputable def εG (n : ℕ) (τ b σ κ : ℝ) : ℝ := Real.sqrt (1 - AG n τ b σ κ ^ 2)

/-- Claim 023, part 3: the Gaussian budget. -/
def part3 : Prop :=
  -- (7) and (8) for one design.
  (∀ (n : ℕ) (Δ : Fin n → ℝ) (b σ κ : ℝ), (∀ j, 0 < Δ j) → 0 < σ → 0 < κ →
    lawR Δ b σ = volume.withDensity (fun x => ENNReal.ofReal (densR Δ b σ x)) ∧
    ∫ x, Real.sqrt (densR Δ b σ x * densR Δ 0 κ x) = AG n (∑ j, Δ j) b σ κ ∧
    0 ≤ AG n (∑ j, Δ j) b σ κ ∧ AG n (∑ j, Δ j) b σ κ ≤ 1 ∧
    (∀ S, MeasurableSet S →
      |(lawR Δ b σ).real S - (lawR Δ 0 κ).real S| ≤ εG n (∑ j, Δ j) b σ κ) ∧
    (∃ S, MeasurableSet S ∧
      1 - AG n (∑ j, Δ j) b σ κ ≤ (lawR Δ b σ).real S - (lawR Δ 0 κ).real S) ∧
    -- Transfer to prices.
    (∀ {𝒳 : Type} [MeasurableSpace 𝒳] (T : (Fin n → ℝ) → 𝒳), Measurable T →
      ∀ A, MeasurableSet A →
        |((lawR Δ b σ).map T).real A - ((lawR Δ 0 κ).map T).real A| ≤ εG n (∑ j, Δ j) b σ κ) ∧
    (∀ {𝒳 : Type} [MeasurableSpace 𝒳] (T : (Fin n → ℝ) → 𝒳), MeasurableEmbedding T →
      ∃ A, MeasurableSet A ∧
        1 - AG n (∑ j, Δ j) b σ κ ≤ ((lawR Δ b σ).map T).real A - ((lawR Δ 0 κ).map T).real A)) ∧
  -- `εG` is an admissible envelope for (1) at every training value.
  (∀ {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒱] [Nonempty 𝒱] (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → 𝒰)
    (V : Ω → 𝒱) (μ : Measure 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ) (ref : 𝒰 → Θ) (n : ℕ) (Δ : Fin n → ℝ)
    (b σ κ : ℝ) (T : 𝒰 → (Fin n → ℝ) → 𝒱), (∀ j, 0 < Δ j) → 0 < σ → 0 < κ →
    (∀ u, Measurable (T u)) →
    (∀ᵐ u ∂(P.map U), condDistrib V U P u = (lawR Δ b σ).map (T u) ∧
      μ.withDensity (fun v => ENNReal.ofReal (g (ref u) u v)) = (lawR Δ 0 κ).map (T u)) →
    TVEnv P U V μ g ref fun _ => εG n (∑ j, Δ j) b σ κ) ∧
  -- The smallest bound over a finite volatility grid is attained by a grid member.
  (∀ (n : ℕ) (Δ : Fin n → ℝ) (b σ : ℝ) (K : Finset ℝ), (∀ j, 0 < Δ j) → 0 < σ → K.Nonempty →
    (∀ κ ∈ K, 0 < κ) → ∃ κ₀ ∈ K, (∀ κ ∈ K, εG n (∑ j, Δ j) b σ κ₀ ≤ εG n (∑ j, Δ j) b σ κ) ∧
      ∀ S, MeasurableSet S →
        |(lawR Δ b σ).real S - (lawR Δ 0 κ₀).real S| ≤ εG n (∑ j, Δ j) b σ κ₀) ∧
  -- Matching volatility: the drift-only envelope, independent of `n`.
  (∀ (n : ℕ) (τ b κ : ℝ), 0 < κ → 0 ≤ τ →
    εG n τ b κ κ = Real.sqrt (1 - Real.exp (-(b ^ 2 * τ / (4 * κ ^ 2)))) ∧
    εG n τ b κ κ ≤ |b| * Real.sqrt τ / (2 * κ)) ∧
  -- Off-grid volatility: at fixed `τ`, `AG → 0`, and the TV distance to every member of a finite
  -- grid omitting `σ` tends to one, uniformly over designs.
  (∀ (τ b σ κ : ℝ), 0 < σ → 0 < κ → σ ≠ κ →
    Tendsto (fun n : ℕ => AG n τ b σ κ) atTop (𝓝 0)) ∧
  (∀ (τ b σ : ℝ) (K : Finset ℝ), 0 < σ → (∀ κ ∈ K, 0 < κ) → σ ∉ K → ∀ δ > 0,
    ∀ᶠ n : ℕ in atTop, ∀ κ ∈ K, ∀ Δ : Fin n → ℝ, (∀ j, 0 < Δ j) → ∑ j, Δ j = τ →
      ∃ S, MeasurableSet S ∧ 1 - δ ≤ (lawR Δ b σ).real S - (lawR Δ 0 κ).real S)

open Classical in
/-- Claim 023. -/
def statement : Prop :=
  -- Part 1: error inflation (2) for one name, any contained rejection event, and the adjusted
  -- threshold.
  (∀ {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒱] [Nonempty 𝒱] [Fintype Θ] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → 𝒰) (V : Ω → 𝒱) (μ : Measure 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ) (sel : 𝒰 → Θ) (p : Θ → ℝ)
    (ref : 𝒰 → Θ) (ε : 𝒰 → ℝ) (α : ℝ),
    CatalogueModel U V μ g sel → NullRef P U V μ g p ref ε → 0 < α → α < 1 →
    P.real {ω | 1 / α < Eval U V g sel p ω} ≤ min 1 (α + ∫ ω, ε (U ω) ∂P) ∧
    (∀ R : Set Ω, R ⊆ {ω | 1 / α < Eval U V g sel p ω} →
      P.real R ≤ min 1 (α + ∫ ω, ε (U ω) ∂P)) ∧
    (∀ e : ℝ, (∀ u, ε u ≤ e) → e < α →
      P.real {ω | 1 / (α - e) < Eval U V g sel p ω} ≤ α)) ∧
  -- Part 1: claim 051's block-band rule rejects only where `E > 1/α`, whatever the truth, so (2)
  -- bounds it too.
  (∀ {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒱] [Nonempty 𝒱] [Fintype Θ] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → 𝒰) (V : Ω → 𝒱) (μ : Measure 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ) (sel : 𝒰 → Θ) (p : Θ → ℝ)
    (ref : 𝒰 → Θ) (ε : 𝒰 → ℝ) (α R r : ℝ) (σ : Θ → ℝ → ℝ),
    CatalogueModel U V μ g sel → NullRef P U V μ g p ref ε → 0 < α → α < 1 → 0 < R → 1 < r →
    (∀ ϑ, ∃ κ : ℝ, 0 < κ ∧ ∀ x, R ≤ x → σ ϑ x = κ * x ^ p ϑ) →
    (∀ ω, Hi (Cset U V g sel α ω) (fun ϑ => B2 R r (σ ϑ)) <
        Lo (Cset U V g sel α ω) (fun ϑ => B1 R r (σ ϑ)) → 1 / α < Eval U V g sel p ω) ∧
    P.real {ω | Hi (Cset U V g sel α ω) (fun ϑ => B2 R r (σ ϑ)) <
        Lo (Cset U V g sel α ω) (fun ϑ => B1 R r (σ ϑ))} ≤ min 1 (α + ∫ ω, ε (U ω) ∂P)) ∧
  -- Part 1: the panel union bound, with no independence.
  (∀ {ι Ω : Type} [Fintype ι] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Rj : ι → Set Ω) (b : ι → ℝ) (N₀ : Finset ι), (∀ i ∈ N₀, P.real (Rj i) ≤ b i) →
    P.real (⋃ i ∈ N₀, Rj i) ≤ min 1 (∑ i ∈ N₀, b i)) ∧
  -- Part 2: the clipped score has a valid null moment; the cap condition (5).
  (∀ {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒱] [Nonempty 𝒱] [Fintype Θ] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → 𝒰) (V : Ω → 𝒱) (μ : Measure 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ) (sel : 𝒰 → Θ) (p : Θ → ℝ)
    (ref : 𝒰 → Θ) (ε : 𝒰 → ℝ) (c : ℝ),
    CatalogueModel U V μ g sel → NullRef P U V μ g p ref ε → 0 < c →
    Measurable (Erob U V g sel p ε c) ∧ (∀ ω, 0 ≤ Erob U V g sel p ε c ω) ∧
    (∀ ω, Erob U V g sel p ε c ω ≤ Eval U V g sel p ω) ∧
    ∫⁻ ω, ENNReal.ofReal (Erob U V g sel p ε c ω) ∂P ≤ 1 ∧
    ∀ α : ℝ, 0 < α → ∀ ω, 1 / α < Erob U V g sel p ε c ω →
      ε (U ω) < α ∧ 1 / (α - ε (U ω)) < c) ∧
  -- Part 2: (4), the base e-BH rule on clipped scores, conditional on AX-53.
  (AX53 → ∀ {ι : Type} [Fintype ι] [Nonempty ι] {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Er : ι → Ω → ℝ) (N₀ : Finset ι) (q : ℝ),
    0 < q → q < 1 → (∀ i, Measurable (Er i)) → (∀ i ω, 0 ≤ Er i ω) →
    (∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (Er i ω) ∂P ≤ 1) →
    ∫ ω, fdp q (fun i => Er i ω) N₀ ∂P ≤ q * N₀.card / Fintype.card ι ∧
    -- claim 053's zero-masking with the original `m`.
    ∀ S : Ω → Finset ι, (∀ i, MeasurableSet {ω | i ∈ S ω}) →
      ∫ ω, fdp q (fun i => if i ∈ S ω then Er i ω else 0) N₀ ∂P ≤ q * N₀.card / Fintype.card ι) ∧
  -- Part 4: the two-point raw-moment obstruction (9) and its unboundedness.
  (∀ p e : ℝ, 0 < p → 0 < e → p + e < 1 →
    (1 - p - e) * ((1 / 2) / (1 - p)) + (p + e) * ((1 / 2) / p) =
      1 + e * (1 / (2 * p) - 1 / (2 * (1 - p)))) ∧
  (∀ e : ℝ, 0 < e → e < 1 →
    Tendsto (fun p : ℝ => 1 + e * (1 / (2 * p) - 1 / (2 * (1 - p)))) (𝓝[>] 0) atTop) ∧
  -- Part 4: a small budget need not preserve exact size.
  (∀ α e : ℝ, 0 < α → α < 1 → 0 < e → e < min α (1 - α) →
    let p := α - e / 2
    0 < p ∧ p < 1 ∧ 1 / α < (1 - e / (4 * α)) / p ∧ (e / (4 * α)) / (1 - p) < 1 / α ∧
      α < p + e ∧ p + e = α + e / 2) ∧
  -- Part 4: (10), eventwise TV transfer.
  (∀ {Ω : Type} [MeasurableSpace Ω] (P Pref : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Pref] (η : ℝ) (R : Set Ω), MeasurableSet R →
    |P.real R - Pref.real R| ≤ η →
    max 0 (Pref.real R - η) ≤ P.real R ∧ P.real R ≤ min 1 (Pref.real R + η)) ∧
  -- Part 3.
  part3

end Standalone.D14Misspecification
