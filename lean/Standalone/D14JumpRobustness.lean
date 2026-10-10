import Standalone.D13DriftNull

/-!
# Claim 026 (D14): conditional jump-contamination budgets for the Gaussian-enlarged score

Statement only; the proof is `Novel/D14JumpRobustnessProof.lean`. Source claim:
`claims/026-d14-jump-robustness.md`.

**Structure.** `statement := reference ∧ oneName ∧ cap ∧ panel ∧ jumpLaw ∧ dependent`.
* `reference`: claim 055's score `E^drift` and its Gaussian conditional law `G(u)`, (1) of
  claim 055 from the last training price, on claim 054's design. The conclusions:
  - the score is measurable and finite;
  - every `G(u)` is a probability;
  - `∫ E^drift(u, ·) dG(u) ≤ 1` at **every** training value `u`, including impossible ones.
* `oneName`: parts 1–2 for any measurable score `E` with a reference `G(u)` satisfying that
  pointwise moment. The actual conditional law `condDistrib V U P u` must satisfy the mixture
  contract (1), `H(u) = (1 − p)G(u) + pJ` with a probability `J` and `0 ≤ p ≤ ρ(u)`, for
  `P∘U⁻¹`-almost every `u` (the actual training law). The conclusions:
  - TV `≤ p`;
  - the conditional and unconditional size bounds (2);
  - the adjusted threshold `(1 − e)/(α − e)`;
  - the clipped score (3), `Ejump`, with conditional and unconditional moments at most one; the
    moment bound also holds for any measurable value between `0` and `Ejump`.
* `cap`: the necessary condition (4) for a strict rejection, and its weak form for a base e-BH
  selection at the rank threshold `q k*/m`.
* `panel`: the union bound over actual nulls, capped at one. Conditional on AX-53 (claim 053's
  `AX53`), the FDR bound holds for any measurable nonnegative scores that are at most `Ejump` at
  the actual nulls. This covers zero masks and certified lower values.
* `jumpLaw`: part 3 at a positive training endpoint `x₀`.
  - `Z` has independent `Normal((b − κ²/2)Δⱼ, κ²Δⱼ)` coordinates, and `L` is independent of `Z` with
    any law `νL`.
  - The prices `x₀ exp(Σ_{i≤j}(Zᵢ + Lᵢ))` satisfy (1) with `p = νL(L ≠ 0)`, and the reference is
    claim 055's Gaussian law.
  - Also: the Bernoulli instance with every `0 < p < 1`, and the survival budget.
* `dependent`: if `L` may depend on `Z` (any joint law with the Gaussian `Z` marginal),
  TV `≤ P(L ≠ 0)`. Under a TV contract, claim 023's consequences hold: raw size
  `≤ min(1, α + Eρ)`, and the null moment of `min(E, c)/(1 + cρ)`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Standalone.D14JumpRobustness

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.D13DriftNull
  Standalone.SplitLikelihoodDominated Standalone.D3CatalogueCalibration Standalone.D12CatalogueFDR

/-- (3): `min(E, c)/(1 + (c − 1)ρ)`. -/
noncomputable def Ejump (c ρ : ℝ) (e : ℝ≥0∞) : ℝ :=
  (min e (ENNReal.ofReal c)).toReal / (1 + (c - 1) * ρ)

/-- Claim 023's clipped score `min(E, c)/(1 + cρ)`. -/
noncomputable def Edep (c ρ : ℝ) (e : ℝ≥0∞) : ℝ :=
  (min e (ENNReal.ofReal c)).toReal / (1 + c * ρ)

/-- The mixture contract (1) at one training value. -/
def Mix {𝒱 : Type} [MeasurableSpace 𝒱] (H G : Measure 𝒱) (ρ : ℝ) : Prop :=
  ∃ (p : ℝ) (J : Measure 𝒱), IsProbabilityMeasure J ∧ 0 ≤ p ∧ p ≤ ρ ∧
    H = ENNReal.ofReal (1 - p) • G + ENNReal.ofReal p • J

/-- The price vector `x₀ exp(Σ_{i ≤ j} yᵢ)` in `[0, ∞)`. -/
noncomputable def priceMap {m : ℕ} (x0 : ℝ) (y : Fin m → ℝ) : Fin m → NNR :=
  fun j => toNNR (x0 * Real.exp (∑ i ∈ Finset.Iic j, y i))

/-- The Gaussian log-return law. -/
noncomputable def lawZ {m : ℕ} (Δ : Fin m → ℝ) (b κ : ℝ) : Measure (Fin m → ℝ) :=
  Measure.pi fun j => gaussianReal ((b - κ ^ 2 / 2) * Δ j) (κ ^ 2 * Δ j).toNNReal

/-- Claim 055's Gaussian conditional price law (1) from `x₀`. -/
noncomputable def Gref {m : ℕ} (Δ : Fin m → ℝ) (b κ x0 : ℝ) : Measure (Fin m → NNR) :=
  (Measure.pi fun _ : Fin m => muCEV).withDensity fun v =>
    ENNReal.ofReal (gG Δ b κ x0 fun l => (v l : ℝ))

/-- Claim 055's score and Gaussian reference meet the pointwise reference moment. -/
def reference : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ) (b κg : ℝ), 0 < κg →
    let g := gC t pw κ
    let sel := selC hN.size t s pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    let E := fun u v => Edrift (g (sel u) u v) (Dmax Δe pw g u v)
    let G := fun u : Fin (k + 1) → NNR => Gref Δe b κg (u (Fin.last k) : ℝ)
    Measurable (Function.uncurry E) ∧ (∀ u v, E u v < ⊤) ∧ (∀ u, IsProbabilityMeasure (G u)) ∧
      ∀ u, ∫⁻ v, E u v ∂(G u) ≤ 1

/-- Parts 1–2 for one name. -/
def oneName : Prop :=
  ∀ {Ω 𝒰 𝒱 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒱] [Nonempty 𝒱] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → 𝒰) (V : Ω → 𝒱) (E : 𝒰 → 𝒱 → ℝ≥0∞) (G : 𝒰 → Measure 𝒱) (ρ : 𝒰 → ℝ),
    Measurable U → Measurable V → Measurable (Function.uncurry E) → Measurable ρ →
    (∀ u, 0 ≤ ρ u ∧ ρ u ≤ 1) → (∀ u, IsProbabilityMeasure (G u)) →
    (∀ u, ∫⁻ v, E u v ∂(G u) ≤ 1) →
    (∀ᵐ u ∂(P.map U), Mix (condDistrib V U P u) (G u) (ρ u)) →
    -- TV at most the mixing probability.
    (∀ᵐ u ∂(P.map U), ∀ (p : ℝ) (J : Measure 𝒱), IsProbabilityMeasure J → 0 ≤ p → p ≤ 1 →
      condDistrib V U P u = ENNReal.ofReal (1 - p) • G u + ENNReal.ofReal p • J →
      ∀ A, MeasurableSet A → |(condDistrib V U P u).real A - (G u).real A| ≤ p) ∧
    -- (2), conditional and unconditional.
    (∀ α : ℝ, 0 < α → α < 1 →
      (∀ᵐ u ∂(P.map U), condDistrib V U P u {v | ENNReal.ofReal (1 / α) < E u v} ≤
        ENNReal.ofReal (α + (1 - α) * ρ u)) ∧
      P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤
        ENNReal.ofReal (α + (1 - α) * ∫ ω, ρ (U ω) ∂P)) ∧
    -- The adjusted threshold.
    (∀ α e : ℝ, 0 ≤ e → e < α → α < 1 → (∀ᵐ u ∂(P.map U), ρ u ≤ e) →
      P {ω | ENNReal.ofReal ((1 - e) / (α - e)) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
    -- (3): the clipped score.
    ∀ c : ℝ, 1 ≤ c →
      Measurable (fun x : 𝒰 × 𝒱 => Ejump c (ρ x.1) (E x.1 x.2)) ∧
      (∀ u v, 0 ≤ Ejump c (ρ u) (E u v) ∧ Ejump c (ρ u) (E u v) ≤ c) ∧
      (∀ᵐ u ∂(P.map U), ∫⁻ v, ENNReal.ofReal (Ejump c (ρ u) (E u v)) ∂(condDistrib V U P u) ≤ 1) ∧
      ∀ F : Ω → ℝ, Measurable F → (∀ ω, 0 ≤ F ω ∧ F ω ≤ Ejump c (ρ (U ω)) (E (U ω) (V ω))) →
        ∫⁻ ω, ENNReal.ofReal (F ω) ∂P ≤ 1

/-- (4) and its e-BH form. -/
def cap : Prop :=
  (∀ c ρ α : ℝ, ∀ e : ℝ≥0∞, 1 ≤ c → 0 ≤ ρ → ρ ≤ 1 → 0 < α → α < 1 →
    (1 / α < Ejump c ρ e → ρ < α ∧ (1 - ρ) / (α - ρ) < c) ∧
    (1 / α ≤ Ejump c ρ e → ρ < α ∧ (1 - ρ) / (α - ρ) ≤ c)) ∧
  ∀ {ι : Type} [Fintype ι] (q : ℝ) (c ρ : ι → ℝ) (e : ι → ℝ≥0∞), 0 < q → q < 1 →
    (∀ i, 1 ≤ c i ∧ 0 ≤ ρ i ∧ ρ i ≤ 1) →
    ∀ i ∈ rej q (fun j => Ejump (c j) (ρ j) (e j)),
      let a := q * kstar q (fun j => Ejump (c j) (ρ j) (e j)) / Fintype.card ι
      ρ i < a ∧ (1 - ρ i) / (a - ρ i) ≤ c i

open Classical in
/-- The panel: the union bound, and e-BH conditional on AX-53. -/
def panel : Prop :=
  (∀ {ι Ω : Type} [Fintype ι] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Rj : ι → Set Ω) (bd : ι → ℝ) (N₀ : Finset ι), (∀ i ∈ N₀, P.real (Rj i) ≤ bd i) →
    P.real (⋃ i ∈ N₀, Rj i) ≤ min 1 (∑ i ∈ N₀, bd i)) ∧
  (AX53 → ∀ {ι : Type} [Fintype ι] [Nonempty ι] {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Er Ej : ι → Ω → ℝ) (N₀ : Finset ι) (q : ℝ),
    0 < q → q < 1 → (∀ i, Measurable (Er i)) → (∀ i ω, 0 ≤ Er i ω) →
    (∀ i ∈ N₀, ∀ ω, Er i ω ≤ Ej i ω) → (∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (Ej i ω) ∂P ≤ 1) →
    ∫ ω, fdp q (fun i => Er i ω) N₀ ∂P ≤ q * N₀.card / Fintype.card ι ∧
    ∀ S : Ω → Finset ι, (∀ i, MeasurableSet {ω | i ∈ S ω}) →
      (∀ ω, rej q (fun i => if i ∈ S ω then Er i ω else 0) ⊆ S ω) ∧
      ∫ ω, fdp q (fun i => if i ∈ S ω then Er i ω else 0) N₀ ∂P ≤ q * N₀.card / Fintype.card ι)

/-- Part 3: the independent finite-grid jump law supplies (1). -/
def jumpLaw : Prop :=
  ∀ (m : ℕ) (Δ : Fin m → ℝ) (b κ x0 : ℝ), (∀ j, 0 < Δ j) → 0 < κ → 0 < x0 →
    -- No jump: claim 055's Gaussian law.
    (lawZ Δ b κ).map (priceMap x0) = Gref Δ b κ x0 ∧
    -- Independent jumps: (1) with `p = νL(L ≠ 0)`.
    (∀ νL : Measure (Fin m → ℝ), IsProbabilityMeasure νL →
      let p := (νL {l | l ≠ 0}).toReal
      ∃ J : Measure (Fin m → NNR), IsProbabilityMeasure J ∧
        ((lawZ Δ b κ).prod νL).map (fun x => priceMap x0 (x.1 + x.2)) =
          ENNReal.ofReal (1 - p) • Gref Δ b κ x0 + ENNReal.ofReal p • J) ∧
    -- The Bernoulli instance realizes every `0 < p < 1`.
    (∀ (p : ℝ) (w : Fin m → ℝ), 0 < p → p < 1 → w ≠ 0 →
      let νL := ENNReal.ofReal (1 - p) • Measure.dirac (0 : Fin m → ℝ) + ENNReal.ofReal p • Measure.dirac w
      IsProbabilityMeasure νL ∧ (νL {l | l ≠ 0}).toReal = p) ∧
    -- A supplied no-jump survival probability bounds the budget.
    ∀ (νL : Measure (Fin m → ℝ)) (lam τ : ℝ), IsProbabilityMeasure νL → 0 ≤ lam → 0 ≤ τ →
      ENNReal.ofReal (Real.exp (-(lam * τ))) ≤ νL {0} →
      (νL {l | l ≠ 0}).toReal ≤ 1 - Real.exp (-(lam * τ))

/-- The dependent-jump correction. -/
def dependent : Prop :=
  -- The coupling bound.
  (∀ (m : ℕ) (Δ : Fin m → ℝ) (b κ x0 : ℝ), (∀ j, 0 < Δ j) → 0 < κ → 0 < x0 →
    ∀ ν : Measure ((Fin m → ℝ) × (Fin m → ℝ)), IsProbabilityMeasure ν →
      ν.map Prod.fst = lawZ Δ b κ →
      ∀ A, MeasurableSet A → |(ν.map fun x => priceMap x0 (x.1 + x.2)).real A -
        (Gref Δ b κ x0).real A| ≤ (ν {x | x.2 ≠ 0}).toReal) ∧
  -- Claim 023's consequences under a TV contract.
  ∀ {Ω 𝒰 𝒱 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒱] [Nonempty 𝒱] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → 𝒰) (V : Ω → 𝒱) (E : 𝒰 → 𝒱 → ℝ≥0∞) (G : 𝒰 → Measure 𝒱) (ρ : 𝒰 → ℝ),
    Measurable U → Measurable V → Measurable (Function.uncurry E) → Measurable ρ →
    (∀ u, 0 ≤ ρ u ∧ ρ u ≤ 1) → (∀ u, IsProbabilityMeasure (G u)) →
    (∀ u, ∫⁻ v, E u v ∂(G u) ≤ 1) →
    (∀ᵐ u ∂(P.map U), ∀ A, MeasurableSet A →
      |(condDistrib V U P u).real A - (G u).real A| ≤ ρ u) →
    (∀ α : ℝ, 0 < α → α < 1 →
      P.real {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ min 1 (α + ∫ ω, ρ (U ω) ∂P)) ∧
    ∀ c : ℝ, 0 < c → ∫⁻ ω, ENNReal.ofReal (Edep c (ρ (U ω)) (E (U ω) (V ω))) ∂P ≤ 1

/-- Claim 026. -/
def statement : Prop := reference ∧ oneName ∧ cap ∧ panel ∧ jumpLaw ∧ dependent

end Standalone.D14JumpRobustness
