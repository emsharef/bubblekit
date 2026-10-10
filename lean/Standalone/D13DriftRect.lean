import Standalone.D13DriftNull

/-!
# Claim 057 (D13): exact Gaussian null profiling over declared drift and scale intervals

Statement only; the proof is `Novel/D13DriftRectProof.lean`. Source claim:
`claims/057-d13-drift-scale-rectangle.md`.

**Structure.** `statement := profile ∧ score`.
* `profile` is part 1's exact finite profile: the maximum of claim 055's Gaussian price density (1)
  over the declared rectangle `b ∈ [b_lo, b_hi]`, `κ ∈ [s_lo, s_hi]` (`0 < s_lo`), on every
  nonnegative input array.
* `score` covers, on claim 054's design:
  - the score (2) and its finiteness, measurability and positivity;
  - part 2's moments and tests;
  - part 3's ordering (7), rectangle nesting and the limit to claim 056's score;
  - absorption, together with the panel results.

**Inputs.** AX-58 (proved from Mathlib) and AX-53 (FDR) as in claim 055. AX-55 and AX-56 supply
claim 054's kernels, on a base carrying a Brownian motion.

**Claim 056's score** `E^B` enters (7) only through its definition. Its denominator is the
supremum `DGB` of (1) over `b ∈ B`, `κ > 0`, maxed with the catalogue-null maximum, and the score
is AX-58's `Edrift`. Claim 056's closed form for that supremum is not used.

**Encodings** (on top of `Standalone.D13DriftNull`: `ret`, `PosPath`, `gG`, `aG`, `QG`).
* `ellG Δ y0 y b w` is the positive-path log density at drift `b` and variance `w = κ²`, including
  the Jacobian `∏ 1/y_j`. It is claim 056's `ℓ_G(b, w)`.
* `AGb b = Q_G + τ_e (b − a_G)²` is claim 056's `A_G(b)`.
* `vEdge c = 2 A_G(c)/(n + √(n² + τ_e A_G(c)))` is (3).
* `clip l h x = min h (max l x)`.
* `candMax` is the largest of `ellG` at the at most five candidates:
  - the two drift edges (3), at `b = b_lo` and `b = b_hi`;
  - the two variance edges (4), at `w = w_lo` and `w = w_hi`;
  - the interior pair (5), when feasible.

  An infeasible interior pair is replaced by the first drift-edge candidate, which changes no
  maximum.
* `DGR` is `exp(candMax)` on positive paths. On the other strata it takes claim 055's zero and
  trapped values.

**Statement.**
* The continuum supremum `⨆_{b ∈ B, κ ∈ C} g^G_{b,κ}` equals `DGR` on every nonnegative input array.
* Every candidate lies in the rectangle.
* `DGR` is finite, positive on positive paths, and measurable.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal

namespace Standalone.D13DriftRect

open Standalone.D13DriftNull

variable {n : ℕ}

/-- `clip_[l,h](x) = min(h, max(l, x))`. -/
noncomputable def clip (l h x : ℝ) : ℝ := min h (max l x)

/-- The positive-path log density at drift `b` and variance `w`, with the price Jacobian. -/
noncomputable def ellG (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (b w : ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log (2 * π * w) -
    ((1 / 2) * ∑ j, Real.log (Δ j) + ∑ j, Real.log (y j)) -
    (∑ j, (ret y0 y j - (b - w / 2) * Δ j) ^ 2 / Δ j) / (2 * w)

/-- `A_G(b) = Q_G + τ_e (b − a_G)²`. -/
noncomputable def AGb (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (b : ℝ) : ℝ :=
  QG Δ y0 y + (∑ j, Δ j) * (b - aG Δ y0 y) ^ 2

/-- (3): the unconstrained variance maximizer on the drift edge `b = c`. -/
noncomputable def vEdge (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (c : ℝ) : ℝ :=
  2 * AGb Δ y0 y c / (n + Real.sqrt ((n : ℝ) ^ 2 + (∑ j, Δ j) * AGb Δ y0 y c))

/-- The interior candidate (5) is feasible. -/
def IntFeas (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (blo bhi slo shi : ℝ) : Prop :=
  aG Δ y0 y + QG Δ y0 y / (2 * n) ∈ Icc blo bhi ∧ QG Δ y0 y / n ∈ Icc (slo ^ 2) (shi ^ 2)

/-- The largest log density at the candidates (3), (4) and (5). -/
noncomputable def candMax (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (blo bhi slo shi : ℝ) : ℝ :=
  open Classical in
  let e1 := ellG Δ y0 y blo (clip (slo ^ 2) (shi ^ 2) (vEdge Δ y0 y blo))
  let e2 := ellG Δ y0 y bhi (clip (slo ^ 2) (shi ^ 2) (vEdge Δ y0 y bhi))
  let e3 := ellG Δ y0 y (clip blo bhi (aG Δ y0 y + slo ^ 2 / 2)) (slo ^ 2)
  let e4 := ellG Δ y0 y (clip blo bhi (aG Δ y0 y + shi ^ 2 / 2)) (shi ^ 2)
  let e5 := if IntFeas Δ y0 y blo bhi slo shi then
    ellG Δ y0 y (aG Δ y0 y + QG Δ y0 y / (2 * n)) (QG Δ y0 y / n) else e1
  max (max (max e1 e2) (max e3 e4)) e5

/-- The closed form of `D_{G,B,C}` on every nonnegative input array. -/
noncomputable def DGR (Δ : Fin n → ℝ) (blo bhi slo shi y0 : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  open Classical in
  if PosPath y0 y then ENNReal.ofReal (Real.exp (candMax Δ y0 y blo bhi slo shi))
  else if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0

/-- Claim 057, part 1: the exact finite profile on the declared rectangle. -/
def profile : Prop :=
  ∀ (n : ℕ) (Δ : Fin n → ℝ) (blo bhi slo shi : ℝ), 0 < n → (∀ j, 0 < Δ j) → blo ≤ bhi →
    0 < slo → slo ≤ shi →
    -- The continuum supremum over the rectangle is the closed form, on every input array.
    (∀ y0 y, (⨆ b ∈ Icc blo bhi, ⨆ κ ∈ Icc slo shi, ENNReal.ofReal (gG Δ b κ y0 y)) =
      DGR Δ blo bhi slo shi y0 y) ∧
    -- On positive paths, every candidate lies in the rectangle, and each is the log density there.
    (∀ y0 y, PosPath y0 y →
      clip (slo ^ 2) (shi ^ 2) (vEdge Δ y0 y blo) ∈ Icc (slo ^ 2) (shi ^ 2) ∧
      clip (slo ^ 2) (shi ^ 2) (vEdge Δ y0 y bhi) ∈ Icc (slo ^ 2) (shi ^ 2) ∧
      clip blo bhi (aG Δ y0 y + slo ^ 2 / 2) ∈ Icc blo bhi ∧
      clip blo bhi (aG Δ y0 y + shi ^ 2 / 2) ∈ Icc blo bhi ∧
      ∀ b κ, 0 < κ → gG Δ b κ y0 y = Real.exp (ellG Δ y0 y b (κ ^ 2))) ∧
    -- The supremum is finite, positive on positive paths, and measurable.
    (∀ y0 y, DGR Δ blo bhi slo shi y0 y < ⊤) ∧
    (∀ y0 y, PosPath y0 y → 0 < DGR Δ blo bhi slo shi y0 y) ∧
    Measurable fun x : ℝ × (Fin n → ℝ) => DGR Δ blo bhi slo shi x.1 x.2


/-! ## The score on claim 054's design -/

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated
  Standalone.D3CatalogueCalibration Standalone.D12CatalogueFDR

/-- Claim 056's Gaussian denominator: the supremum of (1) over `b ∈ B`, `κ > 0`. -/
noncomputable def DGB {k m : ℕ} (Δ : Fin m → ℝ) (blo bhi : ℝ) (u : Fin (k + 1) → NNR)
    (v : Fin m → NNR) : ℝ≥0∞ :=
  ⨆ b ∈ Icc blo bhi, ⨆ κ ∈ Ioi (0 : ℝ), ENNReal.ofReal (gGN Δ b κ u v)

/-- The largest catalogue-null density `G₀`. -/
noncomputable def Gnull {k m c : ℕ} (pw : Fin c → ℝ)
    (g : Fin c → (Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ) (u : Fin (k + 1) → NNR)
    (v : Fin m → NNR) : ℝ≥0∞ :=
  ⨆ ϑ ∈ {ϑ | pw ϑ ≤ 1}, ENNReal.ofReal (g ϑ u v)

/-- `D_{G,B,C}` on nonnegative arrays, from the last training price. -/
noncomputable def DGRN {k m : ℕ} (Δ : Fin m → ℝ) (blo bhi slo shi : ℝ) (u : Fin (k + 1) → NNR)
    (v : Fin m → NNR) : ℝ≥0∞ :=
  DGR Δ blo bhi slo shi (u (Fin.last k) : ℝ) fun l => (v l : ℝ)

open Classical in
/-- Claim 057 on claim 054's design: the score (2), parts 1–4 and the panel results. -/
def score : Prop :=
  (∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ) (blo bhi slo shi : ℝ), blo ≤ bhi → 0 < slo → slo ≤ shi →
    let g := gC t pw κ
    let sel := selC hN.size t s pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    let G0 := Gnull pw g
    let E := fun u v => Edrift (g (sel u) u v) (max (G0 u v) (DGRN Δe blo bhi slo shi u v))
    -- Part 1: (2) is finite, measurable, and zero exactly when `Ĝ = 0`.
    (∀ u v, max (G0 u v) (DGRN Δe blo bhi slo shi u v) < ⊤) ∧
    (∀ u v, E u v = if g (sel u) u v = 0 then 0 else
      ENNReal.ofReal (g (sel u) u v) / max (G0 u v) (DGRN Δe blo bhi slo shi u v)) ∧
    (∀ u v, E u v < ⊤) ∧ Measurable (Function.uncurry E) ∧
    (∀ u v, 0 < g (sel u) u v → 0 < E u v) ∧
    -- Part 2: under any null conditional law, catalogue or Gaussian in the rectangle.
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      ((∃ ϑ, pw ϑ ≤ 1 ∧ IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (g ϑ)) ∨
        ∃ b ∈ Icc blo bhi, ∃ κg ∈ Icc slo shi,
          IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (gGN Δe b κg)) →
      (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a) ∧
    -- Part 3: the ordering (7), `E^drift ≤ E^B ≤ E^{B,C} ≤ E`.
    (∀ u v, Edrift (g (sel u) u v) (Dmax Δe pw g u v) ≤
        Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe blo bhi u v)) ∧
      Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe blo bhi u v)) ≤ E u v ∧
      E u v ≤ Ecomp pw (fun ϑ => g ϑ u v) (sel u)) ∧
    -- Part 3: enlarging the rectangle decreases the score.
    (∀ blo' bhi' slo' shi' : ℝ, blo' ≤ blo → bhi ≤ bhi' → 0 < slo' → slo' ≤ slo → shi ≤ shi' →
      ∀ u v, Edrift (g (sel u) u v) (max (G0 u v) (DGRN Δe blo' bhi' slo' shi' u v)) ≤ E u v) ∧
    -- Part 3: scale intervals increasing to `(0, ∞)` decrease the score to claim 056's.
    (∀ sl sh : ℕ → ℝ, Antitone sl → Monotone sh → (∀ i, 0 < sl i) → (∀ i, sl i ≤ sh i) →
      Tendsto sl atTop (𝓝 0) → Tendsto sh atTop atTop → ∀ u v,
      Antitone (fun i => Edrift (g (sel u) u v) (max (G0 u v) (DGRN Δe blo bhi (sl i) (sh i) u v))) ∧
      Tendsto (fun i => Edrift (g (sel u) u v) (max (G0 u v) (DGRN Δe blo bhi (sl i) (sh i) u v)))
        atTop (𝓝 (Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe blo bhi u v))))) ∧
    -- Part 3: absorbed arrays.
    (∀ u v, (u (Fin.last k) : ℝ) = 0 → (∀ l, (v l : ℝ) = 0) → E u v = 1) ∧
    (∀ u v, 0 < (u (Fin.last k) : ℝ) → (∃ l, (v l : ℝ) = 0) →
      E u v = Ecomp pw (fun ϑ => g ϑ u v) (sel u) ∧ E u v ≤ 1)) ∧
  -- Parts 2 and 3 on the panel: the union bound, e-BH under AX-53 with or without a mask, and
  -- e-BH never selects a score at most one.
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

/-- Claim 057. -/
def statement : Prop := profile ∧ score

end Standalone.D13DriftRect
