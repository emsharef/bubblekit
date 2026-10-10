import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Standalone.SplitLikelihoodDominated
import Standalone.D13CEVCatalogue

/-!
# Claim 055 (D13): a continuous Gaussian physical null for the absorbed CEV score

Statement only; the proof is `Novel/D13DriftNullProof.lean`. Source claim:
`claims/055-d13-drift-null.md`.

**Structure.** `statement := profile ∧ drift`.
* `profile` is the Gaussian conditional family (1) and the exact profile of part 1:
  - the continuum supremum `D_G` over all `b ∈ ℝ`, `κ > 0`;
  - its closed form (3) and maximizer when `Q_G > 0`;
  - the value `∞` without a maximizer when `Q_G = 0`;
  - the zero and trapped boundary values;
  - the measurability of `D_G` from its closed form.
* `drift` adds claim 054's design: the normalization of (1) against `μ_CEV^m`, the score (2), and
  parts 1, 2 and 4 for one name, plus the panel results of parts 2 and 3.

**Inputs.**
* AX-58 is proved from Mathlib (`Novel.SplitLikelihoodDominated.ax58_holds`) and applied.
* AX-53 is claim 053's `AX53` (FDR only).
* AX-55 and AX-56 (claims 052 and 054's restatements, on a base carrying a Brownian motion) supply
  claim 054's kernel normalization and positivity, as in claim 054.
* The Gaussian family's normalization is proved here, by the substitution `y = x e^r` and Mathlib's
  Gaussian integral.

**Encodings for `drift`.**
* Arrays are nonnegative: `u : Fin (k+1) → [0,∞)` (training) and `v : Fin m → [0,∞)` (evaluation).
* `gGN Δ b κ u v` is (1) from the last training price. `Dmax` is `D = max(G₀, D_G)`, with
  `G₀ = sup` over catalogue nulls of `g_ϑ`.
* The score is AX-58's `Edrift(Ĝ, D)`: `0` if `Ĝ = 0` or `D = ∞`, otherwise `Ĝ/D` (with `D > 0`
  whenever `Ĝ > 0`, so it is finite).
* The actual conditional law in part 2 is, for a fixed name, one catalogue-null density or one
  Gaussian density (1); the training law and `P` are otherwise arbitrary.

**Encodings.** One name's evaluation block has `n ≥ 1` prices `y : Fin n → ℝ` after the last
training price `y0`, on positive steps `Δ`. The previous price of `y j` is `Fin.cons y0 y` at
`j.castSucc`, and `R_j = log(y_j / y_{j−1})`.
* `gG Δ b κ y0 y` is (1) on positive paths (`0 < y0` and every `y_j > 0`). Elsewhere it is the
  trapped extension: `1` if `y0 = 0` and the suffix is all zero, and `0` otherwise.
* `τ = Σ Δ_j`, `aG = Σ R_j / τ` and `QG = Σ (R_j − aG Δ_j)²/Δ_j`.
* `logDG` is the right side of (3).
* `DG` is the closed form: `exp(logDG)` if `QG > 0` and `∞` if `QG = 0` on positive paths, and the
  boundary values elsewhere.

The supremum is the actual `[0, ∞]`-valued supremum `⨆ b, ⨆ κ > 0` of `ofReal (gG …)`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace Standalone.D13DriftNull

variable {n : ℕ}

/-- The previous price of `y j`. -/
def prev (y0 : ℝ) (y : Fin n → ℝ) (j : Fin n) : ℝ := (Fin.cons y0 y : Fin (n + 1) → ℝ) j.castSucc

/-- Log returns. -/
noncomputable def ret (y0 : ℝ) (y : Fin n → ℝ) (j : Fin n) : ℝ := Real.log (y j / prev y0 y j)

/-- Positive paths from a positive endpoint. -/
def PosPath (y0 : ℝ) (y : Fin n → ℝ) : Prop := 0 < y0 ∧ ∀ j, 0 < y j

/-- (1), with the trapped extension. -/
noncomputable def gG (Δ : Fin n → ℝ) (b κ y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  open Classical in
  if PosPath y0 y then
    ∏ j, Real.exp (-(ret y0 y j - (b - κ ^ 2 / 2) * Δ j) ^ 2 / (2 * κ ^ 2 * Δ j)) /
      (y j * Real.sqrt (2 * π * κ ^ 2 * Δ j))
  else if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0

/-- `a_G = Σ R_j / τ_e`. -/
noncomputable def aG (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  (∑ j, ret y0 y j) / ∑ j, Δ j

/-- `Q_G = Σ (R_j − a_G Δ_j)²/Δ_j`. -/
noncomputable def QG (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ j, (ret y0 y j - aG Δ y0 y * Δ j) ^ 2 / Δ j

/-- The right side of (3). -/
noncomputable def logDG (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  -((n : ℝ) / 2) * (Real.log (2 * π * QG Δ y0 y / n) + 1) - (1 / 2) * ∑ j, Real.log (Δ j) -
    ∑ j, Real.log (y j)

/-- The closed form of `D_G`. -/
noncomputable def DG (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  open Classical in
  if PosPath y0 y then
    (if 0 < QG Δ y0 y then ENNReal.ofReal (Real.exp (logDG Δ y0 y)) else ⊤)
  else if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0

/-- Claim 055, part 1: the Gaussian profile. -/
def profile : Prop :=
  ∀ (n : ℕ) (Δ : Fin n → ℝ), 0 < n → (∀ j, 0 < Δ j) →
    -- (1) is nonnegative and, for fixed `(b, κ)`, measurable in the price array.
    (∀ b κ y0 y, 0 ≤ gG Δ b κ y0 y) ∧
    (∀ b κ, Measurable fun x : ℝ × (Fin n → ℝ) => gG Δ b κ x.1 x.2) ∧
    -- The continuum supremum is the closed form, on every input array.
    (∀ y0 y, (⨆ (b : ℝ) (κ : ℝ) (_ : 0 < κ), ENNReal.ofReal (gG Δ b κ y0 y)) = DG Δ y0 y) ∧
    -- `Q_G > 0`: the supremum (3) is attained at `κ² = w_G = Q_G/n`, `b = a_G + w_G/2`.
    (∀ y0 y, PosPath y0 y → 0 < QG Δ y0 y →
      gG Δ (aG Δ y0 y + QG Δ y0 y / n / 2) (Real.sqrt (QG Δ y0 y / n)) y0 y =
        Real.exp (logDG Δ y0 y)) ∧
    -- `Q_G = 0`: `D_G = ∞`, and no `κ > 0` attains it.
    (∀ y0 y, PosPath y0 y → QG Δ y0 y = 0 →
      DG Δ y0 y = ⊤ ∧ ∀ b κ, 0 < κ → ENNReal.ofReal (gG Δ b κ y0 y) < DG Δ y0 y) ∧
    (∀ y0 y, 0 ≤ QG Δ y0 y) ∧
    -- One evaluation increment: a positive path always has zero residual.
    (n = 1 → ∀ y0 y, PosPath y0 y → QG Δ y0 y = 0) ∧
    -- `D_G` is measurable, from its closed form.
    Measurable fun x : ℝ × (Fin n → ℝ) => DG Δ x.1 x.2


/-! ## The score on claim 054's design -/

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated
  Standalone.D3CatalogueCalibration Standalone.D12CatalogueFDR

/-- (1) on nonnegative arrays, from the last training price. -/
noncomputable def gGN {k m : ℕ} (Δ : Fin m → ℝ) (b κ : ℝ) (u : Fin (k + 1) → NNR)
    (v : Fin m → NNR) : ℝ :=
  gG Δ b κ (u (Fin.last k) : ℝ) fun l => (v l : ℝ)

/-- `D = max(G₀, D_G)`, with `G₀` the largest catalogue-null density. -/
noncomputable def Dmax {k m c : ℕ} (Δ : Fin m → ℝ) (pw : Fin c → ℝ)
    (g : Fin c → (Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ) (u : Fin (k + 1) → NNR)
    (v : Fin m → NNR) : ℝ≥0∞ :=
  max (⨆ ϑ ∈ {ϑ | pw ϑ ≤ 1}, ENNReal.ofReal (g ϑ u v)) (DG Δ (u (Fin.last k) : ℝ) fun l => (v l : ℝ))

open Classical in
/-- Claim 055 on claim 054's design: (1)'s normalization, the score (2), parts 1, 2 and 4 for one
name, and the panel results. -/
def drift : Prop :=
  (∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ),
    let g := gC t pw κ
    let sel := selC hN.size t s pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    let E := fun u v => Edrift (g (sel u) u v) (Dmax Δe pw g u v)
    -- (1) is normalized against `μ_CEV^m` at every training value.
    (∀ (b κg : ℝ) (u : Fin (k + 1) → NNR), 0 < κg →
      ∫⁻ v, ENNReal.ofReal (gGN Δe b κg u v) ∂(Measure.pi fun _ : Fin m => muCEV) = 1) ∧
    -- Part 1: `D` dominates every null density; the score is measurable and finite.
    (∀ u v ϑ, pw ϑ ≤ 1 → ENNReal.ofReal (g ϑ u v) ≤ Dmax Δe pw g u v) ∧
    (∀ (b κg : ℝ) u v, 0 < κg → ENNReal.ofReal (gGN Δe b κg u v) ≤ Dmax Δe pw g u v) ∧
    Measurable (fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => Dmax Δe pw g p.1 p.2) ∧
    Measurable (Function.uncurry E) ∧ (∀ u v, E u v < ⊤) ∧
    (∀ u v, 0 < g (sel u) u v → 0 < Dmax Δe pw g u v) ∧
    -- Part 2: under any null conditional law, catalogue or Gaussian.
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      ((∃ ϑ, pw ϑ ≤ 1 ∧ IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (g ϑ)) ∨
        ∃ b κg : ℝ, 0 < κg ∧
          IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (gGN Δe b κg)) →
      (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a) ∧
    -- Part 4: domination by the old score, absorption, zero residual, one increment.
    (∀ u v, E u v ≤ Ecomp pw (fun ϑ => g ϑ u v) (sel u)) ∧
    (∀ u v, (u (Fin.last k) : ℝ) = 0 → (∀ l, (v l : ℝ) = 0) → E u v = 1) ∧
    (∀ u v, 0 < (u (Fin.last k) : ℝ) → (∃ l, (v l : ℝ) = 0) →
      E u v = Ecomp pw (fun ϑ => g ϑ u v) (sel u) ∧ E u v ≤ 1) ∧
    (∀ u v, PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) →
      QG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) = 0 → E u v = 0) ∧
    (m = 1 → ∀ u v, E u v ≤ 1)) ∧
  -- Parts 2 and 3 on the panel: the union bound, and e-BH on all `m` scores (with or without a
  -- measurable zero mask, original `m`), conditional on AX-53; e-BH never selects a score `≤ 1`.
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

/-- Claim 055. -/
def statement : Prop := profile ∧ drift

end Standalone.D13DriftNull
