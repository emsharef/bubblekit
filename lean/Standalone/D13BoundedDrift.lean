import Standalone.D13DriftRect

/-!
# Claim 056 (D13): exact likelihood profiling under a declared physical-drift interval

Statement only; the proof is `Novel/D13BoundedDriftProof.lean`. Source claim:
`claims/056-d13-bounded-drift.md`.

**Structure.** `statement := profile ∧ score`.
* `profile` is part 1: the supremum of claim 055's Gaussian price density (1) over `b ∈ B` and
  all `κ > 0`, on every input array, as a closed form `DGBc`.
* `score` is parts 2 and 3 on claim 054's design for the score (1), plus the panel results.

**Inputs.** AX-58 is proved from Mathlib. AX-53 enters as claim 053's `AX53` (FDR only). AX-55 and
AX-56 supply claim 054's kernels, on a base carrying a Brownian motion, as in claims 055 and 057.

**Encodings** (on top of claims 055 and 057: `ret`, `PosPath`, `gG`, `aG`, `QG`, `ellG`, `AGb`,
`vEdge`, and claim 057's `DGB`, the supremum over `b ∈ B`, `κ > 0`).
* `Exc` is the exceptional case `Q_G = 0` and `a_G ∈ B`.
* `IntB` is the feasibility of the interior candidate (4): `Q_G > 0` and `a_G + Q_G/(2n) ∈ B`.
* `candB` is the largest of `ellG` at the endpoint candidates `(c, w_c)`, (3), and at (4) when
  feasible. An infeasible interior candidate is replaced by the first endpoint, which changes no
  maximum.
* `DGBc` is `∞` on `Exc` and `exp(candB)` otherwise, on positive paths. On the other strata it
  takes claim 055's zero and trapped values.

**Part 4** (pricing labels) is a supplied premise linking the physical and pricing laws. It is
commentary here; the labels themselves are claims 054/055's.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal

namespace Standalone.D13BoundedDrift

open Standalone.D13DriftNull Standalone.D13DriftRect

variable {n : ℕ}

/-- The exceptional case: zero residual with `a_G ∈ B`. -/
def Exc (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (blo bhi : ℝ) : Prop :=
  QG Δ y0 y = 0 ∧ aG Δ y0 y ∈ Icc blo bhi

/-- The interior candidate (4) is feasible. -/
def IntB (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (blo bhi : ℝ) : Prop :=
  0 < QG Δ y0 y ∧ aG Δ y0 y + QG Δ y0 y / (2 * n) ∈ Icc blo bhi

/-- (5): the largest log density at the candidates. -/
noncomputable def candB (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (blo bhi : ℝ) : ℝ :=
  open Classical in
  let e1 := ellG Δ y0 y blo (vEdge Δ y0 y blo)
  let e2 := ellG Δ y0 y bhi (vEdge Δ y0 y bhi)
  let e5 := if IntB Δ y0 y blo bhi then
    ellG Δ y0 y (aG Δ y0 y + QG Δ y0 y / (2 * n)) (QG Δ y0 y / n) else e1
  max (max e1 e2) e5

/-- The closed form of `D_{G,B}` on every input array. -/
noncomputable def DGBc (Δ : Fin n → ℝ) (blo bhi y0 : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  open Classical in
  if PosPath y0 y then
    (if Exc Δ y0 y blo bhi then ⊤ else ENNReal.ofReal (Real.exp (candB Δ y0 y blo bhi)))
  else if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0

/-- Claim 056, part 1. -/
def profile : Prop :=
  ∀ (n : ℕ) (Δ : Fin n → ℝ) (blo bhi : ℝ), 0 < n → (∀ j, 0 < Δ j) → blo ≤ bhi →
    -- The supremum over the drift interval and all positive scales is the closed form.
    (∀ y0 y, (⨆ b ∈ Icc blo bhi, ⨆ κ ∈ Ioi (0 : ℝ), ENNReal.ofReal (gG Δ b κ y0 y)) =
      DGBc Δ blo bhi y0 y) ∧
    -- (2): on positive paths the log density is `ℓ_G(b, κ²)`.
    (∀ y0 y, PosPath y0 y → ∀ b κ, 0 < κ → gG Δ b κ y0 y = Real.exp (ellG Δ y0 y b (κ ^ 2))) ∧
    -- (3): outside the exceptional case the endpoint variances are positive.
    (∀ y0 y, PosPath y0 y → ¬ Exc Δ y0 y blo bhi →
      0 < vEdge Δ y0 y blo ∧ 0 < vEdge Δ y0 y bhi) ∧
    -- One increment: the supremum is infinite exactly when `a_G ∈ B`.
    (n = 1 → ∀ y0 y, PosPath y0 y → (DGBc Δ blo bhi y0 y = ⊤ ↔ aG Δ y0 y ∈ Icc blo bhi)) ∧
    -- `D_{G,B}` is measurable, from its closed form.
    Measurable fun x : ℝ × (Fin n → ℝ) => DGBc Δ blo bhi x.1 x.2

/-! ## The score on claim 054's design -/

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated
  Standalone.D3CatalogueCalibration Standalone.D12CatalogueFDR

open Classical in
/-- Claim 056, parts 2–3 on claim 054's design, and the panel results. -/
def score : Prop :=
  (∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ) (blo bhi : ℝ), blo ≤ bhi →
    let g := gC t pw κ
    let sel := selC hN.size t s pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    let G0 := Gnull pw g
    let D := fun u v => max (G0 u v) (DGB Δe blo bhi u v)
    let E := fun u v => Edrift (g (sel u) u v) (D u v)
    -- (1): the denominator is part 1's closed form; the score is finite and measurable.
    (∀ u v, DGB Δe blo bhi u v = DGBc Δe blo bhi (u (Fin.last k) : ℝ) fun l => (v l : ℝ)) ∧
    (∀ u v, E u v = if g (sel u) u v = 0 ∨ D u v = ⊤ then 0 else
      ENNReal.ofReal (g (sel u) u v) / D u v) ∧
    (∀ u v, 0 < g (sel u) u v → 0 < D u v) ∧
    (∀ u v, E u v < ⊤) ∧ Measurable (Function.uncurry E) ∧
    -- Part 2: under any null conditional law, catalogue or Gaussian with `b ∈ B`, `κ > 0`.
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      ((∃ ϑ, pw ϑ ≤ 1 ∧ IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (g ϑ)) ∨
        ∃ b ∈ Icc blo bhi, ∃ κg : ℝ, 0 < κg ∧
          IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (gGN Δe b κg)) →
      (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a) ∧
    -- Part 3: the ordering (7), `E^drift ≤ E^B ≤ E`.
    (∀ u v, Edrift (g (sel u) u v) (Dmax Δe pw g u v) ≤ E u v ∧
      E u v ≤ Ecomp pw (fun ϑ => g ϑ u v) (sel u)) ∧
    -- Part 3: `B ⊆ B'` gives `E^{B'} ≤ E^B`.
    (∀ blo' bhi' : ℝ, blo' ≤ blo → bhi ≤ bhi' → ∀ u v,
      Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe blo' bhi' u v)) ≤ E u v) ∧
    -- Part 3: intervals increasing to `ℝ` give scores decreasing to `E^drift`.
    (∀ bl bh : ℕ → ℝ, Antitone bl → Monotone bh → (∀ i, bl i ≤ bh i) →
      Tendsto bl atTop atBot → Tendsto bh atTop atTop → ∀ u v,
      Antitone (fun i => Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe (bl i) (bh i) u v))) ∧
      Tendsto (fun i => Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe (bl i) (bh i) u v)))
        atTop (𝓝 (Edrift (g (sel u) u v) (Dmax Δe pw g u v)))) ∧
    -- Part 3: absorbed arrays.
    (∀ u v, (u (Fin.last k) : ℝ) = 0 → (∀ l, (v l : ℝ) = 0) → E u v = 1) ∧
    (∀ u v, 0 < (u (Fin.last k) : ℝ) → (∃ l, (v l : ℝ) = 0) →
      E u v = Ecomp pw (fun ϑ => g ϑ u v) (sel u) ∧ E u v ≤ 1)) ∧
  -- Part 2 on the panel: the union bound, e-BH under AX-53 with or without a mask, and e-BH never
  -- selects a score at most one.
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

/-- Claim 056. -/
def statement : Prop := profile ∧ score

end Standalone.D13BoundedDrift
