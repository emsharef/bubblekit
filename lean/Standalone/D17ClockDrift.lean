import Standalone.D13DriftNull
import Standalone.D15JumpEnvelope

/-!
# Claim 033 (D17): a declared variance-clock profile with calendar-time drift

Statement only; the proof is `Novel/D17ClockDriftProof.lean`. Source claim:
`claims/033-d17-calendar-drift-clock.md`.

**Structure.** `statement := profile ∧ scale ∧ score ∧ panel`.
* `profile`: part 1 for one clock vector `v`.
  - (1) is nonnegative and measurable.
  - On positive paths: `A_v > 0`, `Q_v ≥ 0`, `H_v ≥ 0`, and the identity (6).
  - The continuum supremum over `b ∈ ℝ, w > 0` equals the closed form `D_v` on every array.
  - When `Q_v > 0`, (3) attains (4) uniquely. When `Q_v = 0`, `D_v = ∞` and no parameter attains it.
  - `Q_v = 0` exactly when all `R_j/Δ_j` coincide, independently of `v`. For `n = 1` every positive
    path is singular. For `n ≥ 2` the singular positive arrays are `μ_CEV^n`-null at every positive
    endpoint, hence of probability zero under every component (1).
  - `D_v` is measurable.
* `scale`: part 3.
  - `g_(cv, b, w/c) = g_(v, b, w)`, so `D_(cv) = D_v`, with `w*` scaled by `1/c` and `b*` unchanged.
  - At `v = Δ`, (1) is claim 055's family (with `κ = √w`), and `D_Δ = D_G`.
* `score`: part 2 on claim 054's design, under claim 055's inputs, for a finite clock catalogue
  `𝒱 ∋ Δ` of positive vectors.
  - `D^clock = max(G₀, D_G, max_(v ∈ 𝒱) D_v)` dominates every retained CEV null and every
    clock-Gaussian law; `D_G = D_Δ` is already in the clock maximum.
  - The score (5) is measurable and finite.
  - Under the actual conditional mixture premise, the conditional and unconditional moments are
    `≤ 1` and the size is `≤ α`, with the reciprocal-p bound.
  - `E^clock ≤ E^drift` (claim 055's score), and adding clocks lowers the score.
  - The absorbed, zero-endpoint and single-increment cases are claim 055's.
  - A singular positive path gives score `0`.
  - A catalogue of multiples of `Δ` gives exactly claim 055's score.
* `panel`: claim 026's union bound and e-BH with masks at the original `m` under AX-53, and e-BH
  never selects a score `≤ 1`.

**Inputs.** As in claim 055. AX-55 and AX-56 supply claim 054's kernels on a base carrying a
Brownian motion, AX-58 is proved and applied, and AX-53 is used only for FDR. The clock family (1)
enters only through the mixture premise, which supplies the actual law; its normalization is not
used, as in claim 060.

**Encodings** (claim 055's, on `n` evaluation prices `y` after `y0`, calendar steps `Δ_j > 0`).
* `gV Δ v b w y0 y` is (1): `Normal(bΔ_j − w v_j/2, w v_j)` log returns, with the price Jacobian
  and the trapped extension.
* `Av`, …, `Hv` are (2), `wstar` and `bstar` are (3), `logDv` is (4), and `Dv` is the closed
  form: `exp(logDv)` if `Q_v > 0` and `∞` if `Q_v = 0` on positive paths, with the boundary values
  elsewhere.
* **The mixture premise.** The latent space is the disjoint union of the retained catalogue nulls
  and of `𝒱 × {(b, w) : w > 0}`. The actual conditional law is, `P∘U⁻¹`-a.e., the `ν(u, ·)` mixture
  of the component laws, for a Markov kernel `ν`. This covers the claim's finite convex mixtures
  with measurable weights and components.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace Standalone.D17ClockDrift

open Standalone.D13DriftNull

variable {n : ℕ}

/-- (1): the clock-Gaussian price density, with the trapped extension. -/
noncomputable def gV (Δ v : Fin n → ℝ) (b w y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  open Classical in
  if PosPath y0 y then
    ∏ j, Real.exp (-(ret y0 y j - b * Δ j + w * v j / 2) ^ 2 / (2 * w * v j)) /
      (y j * Real.sqrt (2 * π * w * v j))
  else if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0

/-- (2): `A_v = Σ Δ_j²/v_j`. -/
noncomputable def Av (Δ v : Fin n → ℝ) : ℝ := ∑ j, Δ j ^ 2 / v j

/-- (2): `B_v = Σ Δ_j R_j/v_j`. -/
noncomputable def Bv (Δ v : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ j, Δ j * ret y0 y j / v j

/-- (2): `C_v = Σ R_j²/v_j`. -/
noncomputable def Cv (v : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ := ∑ j, ret y0 y j ^ 2 / v j

/-- (2): `Q_v = C_v − B_v²/A_v`. -/
noncomputable def Qv (Δ v : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  Cv v y0 y - Bv Δ v y0 y ^ 2 / Av Δ v

/-- (2): `K_v = S − B_v T/A_v`. -/
noncomputable def Kv (Δ v : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ j, ret y0 y j - Bv Δ v y0 y * (∑ j, Δ j) / Av Δ v

/-- (2): `H_v = V_v − T²/A_v`. -/
noncomputable def Hv (Δ v : Fin n → ℝ) : ℝ := ∑ j, v j - (∑ j, Δ j) ^ 2 / Av Δ v

/-- (3): `w_v* = 2Q_v/(n + √(n² + H_v Q_v))`. -/
noncomputable def wstar (Δ v : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  2 * Qv Δ v y0 y / (n + Real.sqrt ((n : ℝ) ^ 2 + Hv Δ v * Qv Δ v y0 y))

/-- (3): `b_v* = (B_v + w_v* T/2)/A_v`. -/
noncomputable def bstar (Δ v : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  (Bv Δ v y0 y + wstar Δ v y0 y * (∑ j, Δ j) / 2) / Av Δ v

/-- The right side of (4). -/
noncomputable def logDv (Δ v : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log (2 * π * wstar Δ v y0 y) - (1 / 2) * ∑ j, Real.log (v j) -
    ∑ j, Real.log (y j) - Qv Δ v y0 y / (2 * wstar Δ v y0 y) - Kv Δ v y0 y / 2 -
    wstar Δ v y0 y * Hv Δ v / 8

/-- `D_v`: the closed form of the supremum, with the boundary values. -/
noncomputable def Dv (Δ v : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  open Classical in
  if PosPath y0 y then
    (if 0 < Qv Δ v y0 y then ENNReal.ofReal (Real.exp (logDv Δ v y0 y)) else ⊤)
  else if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0

/-- Part 1 for one clock vector. -/
def profile : Prop :=
  ∀ (n : ℕ) (Δ v : Fin n → ℝ), 0 < n → (∀ j, 0 < Δ j) → (∀ j, 0 < v j) →
    (∀ b w y0 y, 0 ≤ gV Δ v b w y0 y) ∧
    (∀ b w, Measurable fun x : ℝ × (Fin n → ℝ) => gV Δ v b w x.1 x.2) ∧
    -- (2)'s signs and the identity (6).
    0 < Av Δ v ∧ 0 ≤ Hv Δ v ∧ (∀ y0 y, 0 ≤ Qv Δ v y0 y) ∧
    (∀ y0 y b w, ∑ j, (ret y0 y j - b * Δ j + w * v j / 2) ^ 2 / v j =
      Av Δ v * (b - (Bv Δ v y0 y + w * (∑ j, Δ j) / 2) / Av Δ v) ^ 2 + Qv Δ v y0 y +
        w * Kv Δ v y0 y + w ^ 2 * Hv Δ v / 4) ∧
    -- The supremum is the closed form, on every array.
    (∀ y0 y, (⨆ (b : ℝ) (w : ℝ) (_ : 0 < w), ENNReal.ofReal (gV Δ v b w y0 y)) = Dv Δ v y0 y) ∧
    -- `Q_v > 0`: (3) attains (4), uniquely.
    (∀ y0 y, PosPath y0 y → 0 < Qv Δ v y0 y →
      0 < wstar Δ v y0 y ∧
      gV Δ v (bstar Δ v y0 y) (wstar Δ v y0 y) y0 y = Real.exp (logDv Δ v y0 y) ∧
      ∀ b w, 0 < w → (b, w) ≠ (bstar Δ v y0 y, wstar Δ v y0 y) →
        gV Δ v b w y0 y < Real.exp (logDv Δ v y0 y)) ∧
    -- `Q_v = 0`: `D_v = ∞`, unattained.
    (∀ y0 y, PosPath y0 y → Qv Δ v y0 y = 0 →
      Dv Δ v y0 y = ⊤ ∧ ∀ b w, 0 < w → ENNReal.ofReal (gV Δ v b w y0 y) < Dv Δ v y0 y) ∧
    -- The singular set is `R ∝ Δ`, independently of `v`.
    (∀ y0 y, PosPath y0 y →
      (Qv Δ v y0 y = 0 ↔ ∀ j j', ret y0 y j / Δ j = ret y0 y j' / Δ j')) ∧
    (n = 1 → ∀ y0 y, PosPath y0 y → Qv Δ v y0 y = 0) ∧
    (2 ≤ n → ∀ y0 : ℝ, 0 < y0 →
      (Measure.pi fun _ : Fin n => Standalone.CEVSupport.muCEV)
        {y | PosPath y0 (fun j => (y j : ℝ)) ∧ Qv Δ v y0 (fun j => (y j : ℝ)) = 0} = 0) ∧
    Measurable fun x : ℝ × (Fin n → ℝ) => Dv Δ v x.1 x.2

/-- Part 3: clock scaling, and the reduction to claim 055. -/
def scale : Prop :=
  ∀ (n : ℕ) (Δ v : Fin n → ℝ), 0 < n → (∀ j, 0 < Δ j) → (∀ j, 0 < v j) →
    (∀ (c : ℝ), 0 < c →
      (∀ b w y0 y, 0 < w → gV Δ (c • v) b (w / c) y0 y = gV Δ v b w y0 y) ∧
      (∀ y0 y, Dv Δ (c • v) y0 y = Dv Δ v y0 y) ∧
      (∀ y0 y, wstar Δ (c • v) y0 y = wstar Δ v y0 y / c ∧
        bstar Δ (c • v) y0 y = bstar Δ v y0 y)) ∧
    (∀ b w y0 y, 0 < w → gV Δ Δ b w y0 y = gG Δ b (Real.sqrt w) y0 y) ∧
    (∀ y0 y, Dv Δ Δ y0 y = DG Δ y0 y)

/-! ## The score on claim 054's design -/

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated
  Standalone.D3CatalogueCalibration Standalone.D13DriftRect

/-- (1) on nonnegative arrays, from the last training price. -/
noncomputable def gVN {k m : ℕ} (Δ v : Fin m → ℝ) (b w : ℝ) (u : Fin (k + 1) → NNR)
    (y : Fin m → NNR) : ℝ :=
  gV Δ v b w (u (Fin.last k) : ℝ) fun l => (y l : ℝ)

/-- (5)'s denominator `D^clock = max(G₀, D_G, max_(v ∈ 𝒱) D_v)`. -/
noncomputable def Dclock {k m c : ℕ} (Δ : Fin m → ℝ) (𝒱 : Finset (Fin m → ℝ)) (pw : Fin c → ℝ)
    (g : Fin c → (Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ) (u : Fin (k + 1) → NNR)
    (y : Fin m → NNR) : ℝ≥0∞ :=
  max (Standalone.D13DriftNull.Dmax Δ pw g u y)
    (𝒱.sup fun v => Dv Δ v (u (Fin.last k) : ℝ) fun l => (y l : ℝ))

/-- A clock of the catalogue. -/
def Clock {m : ℕ} (𝒱 : Finset (Fin m → ℝ)) : Type := {v : Fin m → ℝ // v ∈ 𝒱}

instance {m : ℕ} (𝒱 : Finset (Fin m → ℝ)) : MeasurableSpace (Clock 𝒱) :=
  Subtype.instMeasurableSpace

open Standalone.D15JumpEnvelope in
/-- Part 2 on claim 054's design, for one name. -/
def score : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ) (𝒱 : Finset (Fin m → ℝ)),
    let g := gC t pw κ
    let sel := selC hN.size t s pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    (∀ v ∈ 𝒱, ∀ j, 0 < v j) → Δe ∈ 𝒱 →
    let μm : Measure (Fin m → NNR) := Measure.pi fun _ : Fin m => muCEV
    let D := Dclock Δe 𝒱 pw g
    let E := fun u y => Edrift (g (sel u) u y) (D u y)
    let ED := fun u y => Edrift (g (sel u) u y) (Standalone.D13DriftNull.Dmax Δe pw g u y)
    -- Domination of every retained null and every clock-Gaussian law.
    (∀ u y ϑ, pw ϑ ≤ 1 → ENNReal.ofReal (g ϑ u y) ≤ D u y) ∧
    (∀ v ∈ 𝒱, ∀ (b w : ℝ) u y, 0 < w → ENNReal.ofReal (gVN Δe v b w u y) ≤ D u y) ∧
    -- The score is measurable and finite.
    Measurable (Function.uncurry E) ∧ (∀ u y, E u y < ⊤) ∧
    -- Validity under the actual conditional mixture premise.
    (∀ (ν : ProbabilityTheory.Kernel (Fin (k + 1) → NNR)
        ({ϑ : Fin c // pw ϑ ≤ 1} ⊕ (Clock 𝒱 × GPar))) [ProbabilityTheory.IsMarkovKernel ν]
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z =>
        μm.withDensity fun y => ENNReal.ofReal
          (Sum.elim (fun ϑ => g ϑ.1 u y) (fun p : Clock 𝒱 × GPar => gVN Δe p.1.1 p.2.1.1 p.2.1.2 u y)
            z)) →
      (∀ᵐ u ∂(P.map U), ∫⁻ y, E u y ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a) ∧
    -- Orderings: below claim 055's score, and adding clocks lowers the score.
    (∀ u y, E u y ≤ ED u y) ∧
    (∀ 𝒱' : Finset (Fin m → ℝ), 𝒱 ⊆ 𝒱' →
      ∀ u y, Edrift (g (sel u) u y) (Dclock Δe 𝒱' pw g u y) ≤ E u y) ∧
    -- The boundary cases.
    (∀ u y, (u (Fin.last k) : ℝ) = 0 → (∀ l, (y l : ℝ) = 0) → E u y = 1) ∧
    (∀ u y, 0 < (u (Fin.last k) : ℝ) → (∃ l, (y l : ℝ) = 0) →
      E u y = Ecomp pw (fun ϑ => g ϑ u y) (sel u) ∧ E u y ≤ 1) ∧
    (∀ u y, PosPath (u (Fin.last k) : ℝ) (fun l => (y l : ℝ)) →
      QG Δe (u (Fin.last k) : ℝ) (fun l => (y l : ℝ)) = 0 → E u y = 0) ∧
    (m = 1 → ∀ u y, E u y ≤ 1) ∧
    -- Clocks proportional to `Δ` give exactly claim 055's score.
    ((∀ v ∈ 𝒱, ∃ c : ℝ, 0 < c ∧ v = c • Δe) → ∀ u y, E u y = ED u y)

/-- Claim 033. -/
def statement : Prop := profile ∧ scale ∧ score ∧ Standalone.D15JumpEnvelope.panel

end Standalone.D17ClockDrift
