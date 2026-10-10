import Standalone.D17ClockDrift

/-!
# Claim 067 (D20): cross-sectional clock confidence and safe per-name scores

Statement only; the proof is `Novel/D20ClockConfidenceProof.lean`. Source claim:
`claims/067-d20-cross-sectional-clock-confidence.md`.

**Structure.** `statement := sets ∧ scores ∧ model ∧ panel`.
* `sets`: (1)'s clock set, deterministically. It contains `Δ` and lies in `𝒱`, it can only grow
  when `δ` decreases, and proportional clocks have identical reference profiles.
* `scores`: (2), parts 1–3, for one tested name on claim 033's design (claim 054's name, retained
  CEV nulls and `Edrift` convention) with `r ≥ 1` reference names.
  - Measurability and finiteness, the comparisons (5), the safe ceiling and its necessary
    condition for strict rejection, the `n = 1` boundary, and the boundary cases of claim 054's
    CEV-candidate forecast.
  - Under the actual null contract: (3), the covered raw moment, (4) conditionally on `A` and
    unconditionally, the raw-score threshold, and lower scores.
* `model`: the proof's nonzero model, so the contract is not vacuous: positive Gaussian prices on
  the calendar clock with any finite drifts and positive scales satisfy it.
* `panel`: claim 026's union bound and e-BH with masks at the original `m` under AX-53, applied
  to the safe scores.

**Inputs.** As in claim 033: AX-55 and AX-56 supply claim 054's kernels on a base carrying a
Brownian motion, AX-58 is applied through its pointwise step (proved), and AX-53 is used only
for FDR.

**Encodings** (claim 033's, on `m` evaluation prices after the training record, calendar steps
`Δ`, here `Δe`).
* The pre-evaluation information is `A = (U, ξ)`: the tested name's training record `U` (claim
  054's) and the rest `ξ ∈ 𝒳` (reference training records and endpoints, any other training
  data). The reference evaluation panel is `W ∈ (Fin r → Fin m → NNR)`, with positive starting
  prices `sref(A)`.
* `Dref Δ v s W` is `∏_a D_v(W_a)`, claim 033's profile `Dv` from each reference's start.
  `RefPos s W` says the reference inputs are positive finite arrays. `Tref` is `q^ref/D^ref` with
  `q/∞ = 0`. `Csel δ Δ 𝒱 s q W` is (1): `{Δ} ∪ {v ∈ 𝒱 : T_v ≤ 1/δ}` on positive reference inputs,
  `𝒱` otherwise.
* `q^ref` is any measurable nonnegative function of `(A, W)` with mass at most one over positive
  arrays (on which `μ_CEV` is Lebesgue measure). The tested forecast `q(A, W, ·)` is any measurable
  nonnegative forecast of mass one, positive only where `G₀ > 0`.
* `D^sel = Dclock Δ C pw g` (claim 033's `max(G₀, D_G, max_(v ∈ C) D_v)`, where `D_G = D_Δ` and
  `Δ ∈ C`). `E^sel` uses claim 054's `Edrift` convention: zero if `q = 0` or `D = ∞`, `q/D`
  otherwise (and `D > 0` wherever `q > 0`). `Esafe δ c E = min(E, c)/(1 + (c − 1)δ)`.
* **The contract.** The latent component `Z` is a retained CEV null, or a clock `v ∈ 𝒱` with
  tested `(b, w)` and reference `(b_a, w_a)`.
  - Given `((A, Z), W)` the tested suffix has the component's density: the retained null's, or
    claim 033's `g_(v,b,w)`. So on a Gaussian component it is independent of `W` given `(A, Z)`.
  - Given `(A, Z)` on a Gaussian component, the reference suffixes are mutually independent with
    claim 033's densities `g_(v,b_a,w_a)` from their starts: their joint law has the product
    density `∏_a g_(v,b_a,w_a)(W_a)` against `μ_CEV^(r n)`.
  - The joint law of `Z` given `A` is arbitrary.

The operation counts in part 3 are commentary, not formalized.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace Standalone.D20ClockConfidence

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.D13DriftNull
  Standalone.D17ClockDrift Standalone.SplitLikelihoodDominated Standalone.D15JumpEnvelope

variable {r m : ℕ}

/-- `D_(i,v)^ref = ∏_a D_(a,v)(W_a)`: claim 033's profile of each reference from its start. -/
noncomputable def Dref (Δ v : Fin m → ℝ) (s : Fin r → ℝ) (W : Fin r → Fin m → NNR) : ℝ≥0∞ :=
  ∏ a, Dv Δ v (s a) fun l => (W a l : ℝ)

/-- Positive finite reference inputs. -/
def RefPos (s : Fin r → ℝ) (W : Fin r → Fin m → NNR) : Prop :=
  ∀ a, PosPath (s a) fun l => (W a l : ℝ)

/-- `T_(i,v)^ref = q^ref/D^ref`, with `q/∞ = 0`. -/
noncomputable def Tref (Δ v : Fin m → ℝ) (s : Fin r → ℝ) (qr : ℝ) (W : Fin r → Fin m → NNR) :
    ℝ≥0∞ :=
  ENNReal.ofReal qr / Dref Δ v s W

/-- (1): the clock set, with the calendar clock always retained. -/
noncomputable def Csel (δ : ℝ) (Δ : Fin m → ℝ) (𝒱 : Finset (Fin m → ℝ)) (s : Fin r → ℝ) (qr : ℝ)
    (W : Fin r → Fin m → NNR) : Finset (Fin m → ℝ) :=
  open Classical in
  if RefPos s W then insert Δ (𝒱.filter fun v => Tref Δ v s qr W ≤ ENNReal.ofReal (1 / δ))
  else 𝒱

/-- (2): the safe score `min(E, c)/(1 + (c − 1)δ)`. -/
noncomputable def Esafe (δ c : ℝ) (E : ℝ≥0∞) : ℝ≥0∞ :=
  min E (ENNReal.ofReal c) / ENNReal.ofReal (1 + (c - 1) * δ)

/-- The latent components: a retained CEV null, or a clock with tested and reference Gaussian
parameters. -/
abbrev Comp {c : ℕ} (pw : Fin c → ℝ) (𝒱 : Finset (Fin m → ℝ)) (r : ℕ) : Type :=
  {ϑ : Fin c // pw ϑ ≤ 1} ⊕ (Clock 𝒱 × GPar × (Fin r → GPar))

/-- Part 1's set facts. -/
def sets : Prop :=
  ∀ (r m : ℕ) (δ : ℝ) (Δ : Fin m → ℝ) (𝒱 : Finset (Fin m → ℝ)) (s : Fin r → ℝ) (qr : ℝ)
    (W : Fin r → Fin m → NNR), Δ ∈ 𝒱 →
    -- The set always contains `Δ`, lies in `𝒱` and is never empty.
    (Δ ∈ Csel δ Δ 𝒱 s qr W ∧ Csel δ Δ 𝒱 s qr W ⊆ 𝒱) ∧
    -- Decreasing `δ` can only grow it.
    (∀ δ', 0 < δ → δ ≤ δ' → Csel δ' Δ 𝒱 s qr W ⊆ Csel δ Δ 𝒱 s qr W) ∧
    -- Proportional clocks have identical reference profiles and statistics.
    (0 < m → (∀ j, 0 < Δ j) → ∀ v : Fin m → ℝ, (∀ j, 0 < v j) → ∀ c : ℝ, 0 < c →
      Dref Δ (c • v) s W = Dref Δ v s W ∧ Tref Δ (c • v) s qr W = Tref Δ v s qr W)

open Classical in
/-- Parts 1–3 for one tested name on claim 033's design. -/
def scores : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ) (𝒱 : Finset (Fin m → ℝ)) (r : ℕ) (δ cap : ℝ)
    {𝒳 : Type} [MeasurableSpace 𝒳]
    (sref : (Fin (k + 1) → NNR) × 𝒳 → Fin r → ℝ)
    (qref : (Fin (k + 1) → NNR) × 𝒳 → (Fin r → Fin m → NNR) → ℝ)
    (q : (Fin (k + 1) → NNR) × 𝒳 → (Fin r → Fin m → NNR) → (Fin m → NNR) → ℝ),
    let g := gC t pw κ
    let sel := selC hN.size t s pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    let μm : Measure (Fin m → NNR) := Measure.pi fun _ : Fin m => muCEV
    let μr : Measure (Fin r → Fin m → NNR) := Measure.pi fun _ : Fin r => μm
    (∀ v ∈ 𝒱, ∀ j, 0 < v j) → Δe ∈ 𝒱 → 0 < r → 0 < δ → δ < 1 → 1 ≤ cap →
    Measurable sref → (∀ x a, 0 < sref x a) →
    Measurable (Function.uncurry qref) → (∀ x w, 0 ≤ qref x w) →
    (∀ x, ∫⁻ w in {w | RefPos (sref x) w}, ENNReal.ofReal (qref x w) ∂μr ≤ 1) →
    Measurable (fun p : ((Fin (k + 1) → NNR) × 𝒳) × ((Fin r → Fin m → NNR) × (Fin m → NNR)) =>
      q p.1 p.2.1 p.2.2) →
    (∀ x w y, 0 ≤ q x w y) → (∀ x w, ∫⁻ y, ENNReal.ofReal (q x w y) ∂μm = 1) →
    (∀ x w y, 0 < q x w y → 0 < ⨆ ϑ ∈ {ϑ | pw ϑ ≤ 1}, ENNReal.ofReal (g ϑ x.1 y)) →
    let C := fun x w => Csel δ Δe 𝒱 (sref x) (qref x w) w
    let Esel := fun x w y => Edrift (q x w y) (Dclock Δe (C x w) pw g x.1 y)
    let Eall := fun x w y => Edrift (q x w y) (Dclock Δe 𝒱 pw g x.1 y)
    let ES := fun x w y => Esafe δ cap (Esel x w y)
    -- Measurable and finite scores.
    Measurable (fun p : ((Fin (k + 1) → NNR) × 𝒳) × ((Fin r → Fin m → NNR) × (Fin m → NNR)) =>
      Esel p.1 p.2.1 p.2.2) ∧
    Measurable (fun p : ((Fin (k + 1) → NNR) × 𝒳) × ((Fin r → Fin m → NNR) × (Fin m → NNR)) =>
      ES p.1 p.2.1 p.2.2) ∧
    (∀ x w y, Esel x w y < ⊤) ∧
    -- (5) and the ceiling.
    (∀ x w y, Eall x w y ≤ Esel x w y ∧ Esafe δ cap (Eall x w y) ≤ ES x w y ∧
      ES x w y ≤ ENNReal.ofReal (cap / (1 + (cap - 1) * δ))) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∀ x w y, ENNReal.ofReal (1 / α) < ES x w y →
      δ < α ∧ (1 - δ) / (α - δ) < cap) ∧
    -- `n = 1`: no clock is excluded, and positive tested paths score zero.
    (m = 1 → ∀ x w, (RefPos (sref x) w → C x w = 𝒱) ∧
      ∀ y, PosPath (x.1 (Fin.last k) : ℝ) (fun l => (y l : ℝ)) → Esel x w y = 0) ∧
    -- Claim 054's CEV-candidate forecast: zero endpoints and first absorption keep raw scores
    -- `≤ 1`, so the safe score is `≤ 1`.
    (∀ x w y, (((x.1 (Fin.last k) : ℝ) = 0 ∧ ∀ l, (y l : ℝ) = 0) ∨
        (0 < (x.1 (Fin.last k) : ℝ) ∧ ∃ l, (y l : ℝ) = 0)) →
      Edrift (g (sel x.1) x.1 y) (Dclock Δe (C x w) pw g x.1 y) ≤ 1 ∧
      Esafe δ cap (Edrift (g (sel x.1) x.1 y) (Dclock Δe (C x w) pw g x.1 y)) ≤ 1) ∧
    -- The actual null contract.
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U : Ω → Fin (k + 1) → NNR) (ξ : Ω → 𝒳) (Z : Ω → Comp pw 𝒱 r)
      (W : Ω → Fin r → Fin m → NNR) (V : Ω → Fin m → NNR),
      Measurable U → Measurable ξ → Measurable Z → Measurable W → Measurable V →
      let A := fun ω => (U ω, ξ ω)
      let X3 := fun ω => (A ω, Z ω)
      let X4 := fun ω => (X3 ω, W ω)
      -- The tested suffix given `((A, Z), W)`.
      (∀ᵐ x ∂(P.map X4), condDistrib V X4 P x = μm.withDensity fun y => ENNReal.ofReal
        (Sum.elim (fun ϑ : {ϑ : Fin c // pw ϑ ≤ 1} => g ϑ.1 x.1.1.1 y)
          (fun p : Clock 𝒱 × GPar × (Fin r → GPar) =>
            gVN Δe p.1.1 p.2.1.1.1 p.2.1.1.2 x.1.1.1 y) x.1.2)) →
      -- The references given `(A, Z)` on a Gaussian component.
      (∀ᵐ x ∂(P.map X3), ∀ p : Clock 𝒱 × GPar × (Fin r → GPar), x.2 = Sum.inr p →
        condDistrib W X3 P x = μr.withDensity fun w => ∏ a, ENNReal.ofReal
          (gV Δe p.1.1 (p.2.2 a).1.1 (p.2.2 a).1.2 (sref x.1 a) fun l => (w a l : ℝ))) →
      -- (3): the true clock is excluded with probability at most `δ`.
      (∀ᵐ x ∂(P.map X3), ∀ p : Clock 𝒱 × GPar × (Fin r → GPar), x.2 = Sum.inr p →
        condDistrib W X3 P x {w | p.1.1 ∉ C x.1 w} ≤ ENNReal.ofReal δ) ∧
      -- The raw target moment given `((A, Z), W)` when the Gaussian clock is retained.
      (∀ᵐ x ∂(P.map X4), (∀ p : Clock 𝒱 × GPar × (Fin r → GPar), x.1.2 = Sum.inr p →
          p.1.1 ∈ C x.1.1 x.2) →
        ∫⁻ y, Esel x.1.1 x.2 y ∂(condDistrib V X4 P x) ≤ 1) ∧
      -- (4), conditionally on `A` and unconditionally.
      (∀ᵐ a ∂(P.map A), ∫⁻ p, ES a p.1 p.2 ∂(condDistrib (fun ω => (W ω, V ω)) A P a) ≤ 1) ∧
      ∫⁻ ω, ES (A ω) (W ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 → ∀ᵐ a ∂(P.map A),
        condDistrib (fun ω => (W ω, V ω)) A P a {p | ENNReal.ofReal (1 / α) < Esel a p.1 p.2} ≤
          ENNReal.ofReal (α + (1 - α) * δ)) ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < Esel (A ω) (W ω) (V ω)} ≤
          ENNReal.ofReal (α + (1 - α) * δ)) ∧
      -- The raw-score threshold `(1 − δ)/(α − δ)` when `δ < α`.
      (∀ α : ℝ, δ < α → α < 1 →
        P {ω | ENNReal.ofReal ((1 - δ) / (α - δ)) < Esel (A ω) (W ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      -- Lower implemented scores, including zero masks, keep the moment.
      ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ ES (A ω) (W ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1

/-- The proof's nonzero model: on the calendar clock, with any finite drifts and positive scales,
positive Gaussian reference and tested prices satisfy the contract, from a fixed training record
with a positive endpoint and positive reference starts. -/
def model : Prop :=
  ∀ (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (_ : NameC s R t pw κ) (𝒱 : Finset (Fin m → ℝ)) (r : ℕ) {𝒳 : Type} [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] (sref : (Fin (k + 1) → NNR) × 𝒳 → Fin r → ℝ)
    (u₀ : Fin (k + 1) → NNR) (ξ₀ : 𝒳) (p : Clock 𝒱 × GPar × (Fin r → GPar)),
    let g := gC t pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    let μm : Measure (Fin m → NNR) := Measure.pi fun _ : Fin m => muCEV
    let μr : Measure (Fin r → Fin m → NNR) := Measure.pi fun _ : Fin r => μm
    p.1.1 = Δe → (∀ a, 0 < sref (u₀, ξ₀) a) → 0 < (u₀ (Fin.last k) : ℝ) →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (U : Ω → Fin (k + 1) → NNR) (ξ : Ω → 𝒳) (Z : Ω → Comp pw 𝒱 r)
      (W : Ω → Fin r → Fin m → NNR) (V : Ω → Fin m → NNR),
      Measurable U ∧ Measurable ξ ∧ Measurable Z ∧ Measurable W ∧ Measurable V ∧
      (∀ ω, U ω = u₀ ∧ ξ ω = ξ₀ ∧ Z ω = Sum.inr p) ∧
      (∀ᵐ ω ∂P, (∀ l, 0 < (V ω l : ℝ)) ∧ RefPos (sref (u₀, ξ₀)) (W ω)) ∧
      let A := fun ω => (U ω, ξ ω)
      let X3 := fun ω => (A ω, Z ω)
      let X4 := fun ω => (X3 ω, W ω)
      (∀ᵐ x ∂(P.map X4), condDistrib V X4 P x = μm.withDensity fun y => ENNReal.ofReal
        (Sum.elim (fun ϑ : {ϑ : Fin c // pw ϑ ≤ 1} => g ϑ.1 x.1.1.1 y)
          (fun p : Clock 𝒱 × GPar × (Fin r → GPar) =>
            gVN Δe p.1.1 p.2.1.1.1 p.2.1.1.2 x.1.1.1 y) x.1.2)) ∧
      (∀ᵐ x ∂(P.map X3), ∀ p : Clock 𝒱 × GPar × (Fin r → GPar), x.2 = Sum.inr p →
        condDistrib W X3 P x = μr.withDensity fun w => ∏ a, ENNReal.ofReal
          (gV Δe p.1.1 (p.2.2 a).1.1 (p.2.2 a).1.2 (sref x.1 a) fun l => (w a l : ℝ)))

/-- Claim 067. -/
def statement : Prop := sets ∧ scores ∧ model ∧ Standalone.D15JumpEnvelope.panel

end Standalone.D20ClockConfidence
