import Standalone.D14Misspecification
import Standalone.D13DriftRect

/-!
# Claim 027 (D14): conditional Gaussian volatility-path budgets for enlarged-null scores

Statement only; the proof is `Novel/D14VolPathsProof.lean`. Source claim:
`claims/027-d14-conditional-volatility-paths.md`.

**Structure.** `statement := component ∧ averaging ∧ cev`.
* `component`: part 1's budget for one latent component and part 3's uniform envelope.
* `averaging`: part 2 for an abstract latent mixture.
  - **Setup.** A score with reference moment `≤ 1` at every `(u, z)`. Component laws within `ε(u, z)`
    of their references, eventwise. The actual conditional law of `V` given `U` is the `ν(u, ·)`
    mixture (1) of the components.
  - **Conclusions.**
    - The conditional and unconditional size (5) with `ε̄(u) = ∫ ε(u, z) ν(u, dz)` (4).
    - The shifted threshold.
    - The capped score (6), with any measurable budget `≥ ε̄` in `[0, 1]`.
    - The raw moment when every component budget is zero.
    - The panel results: the union bound, and e-BH under AX-53 with or without a mask.
* `cev`: part 2 for claim 055's score `E^drift` and claim 057's score `E^(B,C)`.
  - **Components and references.** Each component's price law is (2) on evaluation prices: `gV`,
    claim 055's (1) with increment-varying drift and scale, against `μ_CEV^m`. Its parameters
    `b(u, z)`, `σ(u, z) > 0` are measurable functions of training and latent value. The reference
    is claim 055's Gaussian null density with measurable `b_ref(u, z)`, `κ(u, z) > 0`, which lie in
    the rectangle for claim 057.
  - **Budget.** `ε(u, z)` is the component budget (3) at a positive endpoint and `0` at a zero
    endpoint, and `ε̄` is (4).
  - **Conclusion.** If the actual conditional law is the `ν(u, ·)` mixture (1) of the component laws,
    (5), the shifted threshold, (6) and the zero-budget raw moment hold for the chosen score.

**Inputs.** FDR is conditional on AX-53. AX-55 and AX-56 supply claim 054's kernels on a base
carrying a Brownian motion. AX-58 is proved from Mathlib. The Gaussian affinity and the log-normal
substitution are proved.

**Encodings.** One component has evaluation log returns on `ℝ^n` with steps `Δ_j > 0`.
* `lawV Δ b σ` is (2): independent `Normal((b_j − σ_j²/2)Δ_j, σ_j²Δ_j)` coordinates, with drifts
  `b_j` and scales `σ_j > 0` that may vary with the increment.
* The reference with drift `b_ref` and scale `κ > 0`, constant across increments, is claim 023's
  `lawR Δ b_ref κ`.
* `Acomp` is the affinity (3). `εcomp = √(1 − A²)` is the component budget.
* The passage to prices is any measurable map, such as the log-return bijection at a fixed positive
  last training price.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Standalone.D14VolPaths

open Standalone.D14Misspecification

variable {n : ℕ}

/-- (2): independent Normal log returns with increment-varying drift `b` and scale `σ`. -/
noncomputable def lawV (Δ b σ : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi fun j => gaussianReal ((b j - σ j ^ 2 / 2) * Δ j) (σ j ^ 2 * Δ j).toNNReal

/-- (3): the affinity against the constant reference `(b_ref, κ)`. -/
noncomputable def Acomp (Δ b σ : Fin n → ℝ) (bref κ : ℝ) : ℝ :=
  (∏ j, Real.sqrt (2 * σ j * κ / (σ j ^ 2 + κ ^ 2))) *
    Real.exp (-∑ j, Δ j * (b j - bref + (κ ^ 2 - σ j ^ 2) / 2) ^ 2 / (4 * (σ j ^ 2 + κ ^ 2)))

/-- The component budget `ε = √(1 − A²)`. -/
noncomputable def εcomp (Δ b σ : Fin n → ℝ) (bref κ : ℝ) : ℝ :=
  Real.sqrt (1 - Acomp Δ b σ bref κ ^ 2)

/-- Claim 027, part 1 (one component) and part 3. -/
def component : Prop :=
  -- Part 1: the component budget bounds TV, also after any measurable map to prices.
  (∀ (n : ℕ) (Δ b σ : Fin n → ℝ) (bref κ : ℝ), (∀ j, 0 < Δ j) → (∀ j, 0 < σ j) → 0 < κ →
    0 ≤ Acomp Δ b σ bref κ ∧ Acomp Δ b σ bref κ ≤ 1 ∧
    0 ≤ εcomp Δ b σ bref κ ∧ εcomp Δ b σ bref κ ≤ 1 ∧
    (∀ S, MeasurableSet S → |(lawV Δ b σ).real S - (lawR Δ bref κ).real S| ≤ εcomp Δ b σ bref κ) ∧
    ∀ {𝒳 : Type} [MeasurableSpace 𝒳] (T : (Fin n → ℝ) → 𝒳), Measurable T →
      ∀ A, MeasurableSet A →
        |((lawV Δ b σ).map T).real A - ((lawR Δ bref κ).map T).real A| ≤ εcomp Δ b σ bref κ) ∧
  -- Part 1: the budget is a measurable function of the parameters.
  (∀ (n : ℕ) (Δ : Fin n → ℝ),
    Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ => εcomp Δ p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  -- Part 2's constant case: a component equal to its admitted reference has zero budget.
  (∀ (n : ℕ) (Δ : Fin n → ℝ) (bref κ : ℝ), 0 < κ →
    Acomp Δ (fun _ => bref) (fun _ => κ) bref κ = 1 ∧
    εcomp Δ (fun _ => bref) (fun _ => κ) bref κ = 0) ∧
  -- Part 3: the uniform variability envelope (7).
  (∀ (n : ℕ) (Δ b σ : Fin n → ℝ) (bref κ smin smax hvol Bphys : ℝ), (∀ j, 0 < Δ j) →
    0 < smin → (∀ j, σ j ∈ Icc smin smax) → κ ∈ Icc smin smax →
    (∀ j, |Real.log (σ j / κ)| ≤ hvol) → (∀ j, |b j - bref| ≤ Bphys) →
    εcomp Δ b σ bref κ ≤ Real.sqrt (1 - Real.exp (-(n * Real.log (Real.cosh hvol) +
      (∑ j, Δ j) * (Bphys / (2 * smin) + smax * Real.sinh hvol / 2) ^ 2))))


open Standalone.D12CatalogueFDR in
open Classical in
/-- Claim 027, part 2, for an abstract latent mixture. -/
def averaging : Prop :=
  (∀ {Ω 𝒰 𝒱 𝒵 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [MeasurableSpace 𝒵] [StandardBorelSpace 𝒱] [Nonempty 𝒱] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → 𝒰) (V : Ω → 𝒱) (ν : ProbabilityTheory.Kernel 𝒰 𝒵) [ProbabilityTheory.IsMarkovKernel ν]
    (H G : ProbabilityTheory.Kernel (𝒰 × 𝒵) 𝒱) [ProbabilityTheory.IsMarkovKernel H]
    [ProbabilityTheory.IsMarkovKernel G] (E : 𝒰 → 𝒱 → ℝ) (ε : 𝒰 × 𝒵 → ℝ),
    Measurable U → Measurable V → Measurable (Function.uncurry E) → (∀ u v, 0 ≤ E u v) →
    Measurable ε → (∀ p, 0 ≤ ε p ∧ ε p ≤ 1) →
    -- The reference moment at every training value and component.
    (∀ u z, ∫⁻ v, ENNReal.ofReal (E u v) ∂(G (u, z)) ≤ 1) →
    -- The eventwise component budget.
    (∀ u z A, MeasurableSet A → |(H (u, z)).real A - (G (u, z)).real A| ≤ ε (u, z)) →
    -- (1): the actual conditional law is the latent mixture.
    (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z => H (u, z)) →
    let εbar := fun u => ∫ z, ε (u, z) ∂(ν u)
    -- (5), conditional and unconditional.
    (∀ α : ℝ, 0 < α → ∀ᵐ u ∂(P.map U),
      condDistrib V U P u {v | 1 / α < E u v} ≤ ENNReal.ofReal (α + εbar u)) ∧
    (∀ α : ℝ, 0 < α →
      P.real {ω | 1 / α < E (U ω) (V ω)} ≤ min 1 (α + ∫ ω, εbar (U ω) ∂P)) ∧
    -- The shifted threshold.
    (∀ α e : ℝ, 0 ≤ e → (∀ u, εbar u ≤ e) → e < α →
      P.real {ω | 1 / (α - e) < E (U ω) (V ω)} ≤ α) ∧
    -- (6), with any measurable budget at least `ε̄`, conditional and unconditional.
    (∀ (c : ℝ) (eb : 𝒰 → ℝ), 0 < c → Measurable eb → (∀ u, εbar u ≤ eb u) →
      (∀ᵐ u ∂(P.map U), ∫⁻ v, ENNReal.ofReal (min (E u v) c / (1 + c * eb u))
        ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, ENNReal.ofReal (min (E (U ω) (V ω)) c / (1 + c * eb (U ω))) ∂P ≤ 1) ∧
    -- Zero component budgets: the raw score keeps its moment.
    ((∀ p, ε p = 0) →
      (∀ᵐ u ∂(P.map U), ∫⁻ v, ENNReal.ofReal (E u v) ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, ENNReal.ofReal (E (U ω) (V ω)) ∂P ≤ 1)) ∧
  -- The panel: union bound; e-BH on all `m` scores, with or without a mask, under AX-53.
  (∀ {ι Ω : Type} [Fintype ι] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Rj : ι → Set Ω) (b : ι → ℝ) (N₀ : Finset ι), (∀ i ∈ N₀, P.real (Rj i) ≤ b i) →
    P.real (⋃ i ∈ N₀, Rj i) ≤ min 1 (∑ i ∈ N₀, b i)) ∧
  (AX53 → ∀ {ι : Type} [Fintype ι] [Nonempty ι] {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Er : ι → Ω → ℝ) (N₀ : Finset ι) (q : ℝ),
    0 < q → q < 1 → (∀ i, Measurable (Er i)) → (∀ i ω, 0 ≤ Er i ω) →
    (∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (Er i ω) ∂P ≤ 1) →
    ∫ ω, fdp q (fun i => Er i ω) N₀ ∂P ≤ q * N₀.card / Fintype.card ι ∧
    ∀ S : Ω → Finset ι, (∀ i, MeasurableSet {ω | i ∈ S ω}) →
      ∫ ω, fdp q (fun i => if i ∈ S ω then Er i ω else 0) N₀ ∂P ≤ q * N₀.card / Fintype.card ι) ∧
  (∀ {ι : Type} [Fintype ι] (q : ℝ) (x : ι → ℝ), 0 < q → q < 1 → ∀ i ∈ rej q x, 1 < x i)


open Standalone.D13DriftNull in
/-- (2) on prices: claim 055's (1) with increment-varying drift `b` and scale `σ`, with the trapped
extension. -/
noncomputable def gV (Δ b σ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  open Classical in
  if PosPath y0 y then
    ∏ j, Real.exp (-(ret y0 y j - (b j - σ j ^ 2 / 2) * Δ j) ^ 2 / (2 * σ j ^ 2 * Δ j)) /
      (y j * Real.sqrt (2 * π * σ j ^ 2 * Δ j))
  else if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated
  Standalone.D13DriftNull Standalone.D13DriftRect in
/-- Claim 027, part 2, for claims 055 and 057's scores. -/
def cev : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ) {𝒵 : Type} [MeasurableSpace 𝒵]
    (ν : ProbabilityTheory.Kernel (Fin (k + 1) → NNR) 𝒵) [ProbabilityTheory.IsMarkovKernel ν]
    (b σ : (Fin (k + 1) → NNR) × 𝒵 → Fin m → ℝ) (br κr : (Fin (k + 1) → NNR) × 𝒵 → ℝ)
    (blo bhi slo shi : ℝ),
    Measurable b → Measurable σ → Measurable br → Measurable κr → (∀ p j, 0 < σ p j) →
    (∀ p, 0 < κr p) →
    let g := gC t pw κ
    let sel := selC hN.size t s pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    -- The chosen score: claim 055's, or claim 057's on the declared rectangle.
    let E055 := fun u v => (Edrift (g (sel u) u v) (Dmax Δe pw g u v)).toReal
    let E057 := fun u v => (Edrift (g (sel u) u v)
      (max (Gnull pw g u v) (DGRN Δe blo bhi slo shi u v))).toReal
    -- The component price laws (2) and their budgets (3).
    let H := fun (u : Fin (k + 1) → NNR) (z : 𝒵) => (Measure.pi fun _ : Fin m => muCEV).withDensity
      fun v => ENNReal.ofReal (gV Δe (b (u, z)) (σ (u, z)) (u (Fin.last k) : ℝ) fun l => (v l : ℝ))
    let ε := fun p : (Fin (k + 1) → NNR) × 𝒵 =>
      if 0 < (p.1 (Fin.last k) : ℝ) then εcomp Δe (b p) (σ p) (br p) (κr p) else 0
    let εbar := fun u => ∫ z, ε (u, z) ∂(ν u)
    (∀ u, 0 ≤ εbar u ∧ εbar u ≤ 1) ∧ Measurable εbar ∧
    ∀ (E : (Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ),
      -- Claim 055's score, or claim 057's with references in the rectangle.
      (E = E055 ∨ (E = E057 ∧ blo ≤ bhi ∧ 0 < slo ∧ slo ≤ shi ∧
        ∀ p, br p ∈ Icc blo bhi ∧ κr p ∈ Icc slo shi)) →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      -- (1): the actual conditional law is the latent mixture of the component laws.
      (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z => H u z) →
      (∀ α : ℝ, 0 < α → ∀ᵐ u ∂(P.map U),
        condDistrib V U P u {v | 1 / α < E u v} ≤ ENNReal.ofReal (α + εbar u)) ∧
      (∀ α : ℝ, 0 < α →
        P.real {ω | 1 / α < E (U ω) (V ω)} ≤ min 1 (α + ∫ ω, εbar (U ω) ∂P)) ∧
      (∀ α e : ℝ, 0 ≤ e → (∀ u, εbar u ≤ e) → e < α →
        P.real {ω | 1 / (α - e) < E (U ω) (V ω)} ≤ α) ∧
      (∀ (c : ℝ) (eb : (Fin (k + 1) → NNR) → ℝ), 0 < c → Measurable eb → (∀ u, εbar u ≤ eb u) →
        (∀ᵐ u ∂(P.map U), ∫⁻ v, ENNReal.ofReal (min (E u v) c / (1 + c * eb u))
          ∂(condDistrib V U P u) ≤ 1) ∧
        ∫⁻ ω, ENNReal.ofReal (min (E (U ω) (V ω)) c / (1 + c * eb (U ω))) ∂P ≤ 1) ∧
      ((∀ p, ε p = 0) →
        (∀ᵐ u ∂(P.map U), ∫⁻ v, ENNReal.ofReal (E u v) ∂(condDistrib V U P u) ≤ 1) ∧
        ∫⁻ ω, ENNReal.ofReal (E (U ω) (V ω)) ∂P ≤ 1)

/-- Claim 027. -/
def statement : Prop := component ∧ averaging ∧ cev

end Standalone.D14VolPaths
