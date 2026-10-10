import Standalone.D14VolPaths

/-!
# Claim 059 (D15): a calibrated Gaussian single-switch null with minimum segment length

Statement only; the proof is `Novel/D15SwitchProof.lean`. Source claim:
`claims/059-d15-single-switch.md`.

**Structure.** `statement := profile ∧ score ∧ nullSet`.
* `profile`: part 1's exact profile (5) with its finiteness, measurability and exceptional arrays.
* `score`: the score (3) on claim 054's design, part 2's inference under the mixture premise (2)
  (including `P(D_sw = ∞) = 0`), part 3's ordering (7), absorption, and the panel results.
* `nullSet`: part 1's exceptional arrays, where (5) is infinite, form a `μ_CEV^m`-null set.

**Inputs.**
* AX-58 is proved from Mathlib and enters through its pointwise step.
* AX-53 is used for FDR only.
* AX-55 and AX-56 supply claim 054's kernels, on a base carrying a Brownian motion.
* The Gaussian profile, the switch normalization and the mixture integration are proved.

**Mixture premise.** The latent space is the disjoint union of the catalogue nulls and
`K × ℝ × (0,∞) × ℝ × (0,∞)`, the latter encoded as a subtype of `ℕ × ℝ⁴`. The component law of a
latent value is its density times `μ_CEV^m`. The premise is that the actual conditional law equals
the `ν(u, ·)` mixture, for `P∘U⁻¹`-a.e. `u`.

**Encodings** (on `n` evaluation prices `y` after the last training price `y0`, with steps `Δ_j > 0`;
indices are `0, …, n−1`).
* A cut `c` splits the increments into `H_L = {j < c}` and `H_R = {j ≥ c}` (the claim's
  `{1, …, c}` and `{c+1, …, n_e}`).
* `gSw Δ c b_L κ_L b_R κ_R` is (1): claim 027's increment-varying price density `gV`, with
  `(b_L, κ_L)` on `H_L` and `(b_R, κ_R)` on `H_R`, the price Jacobian, and the zero/trapped
  extension.
* For a set `H` of increments: `n_H`, `τ_H`, `a_H`, `Q_H` as in part 1. `DGH H` is the segment
  maximum (4) when `Q_H > 0`, and `∞` when `Q_H = 0`.
* `Dsw Δ K y0 y` is (5): on positive paths, the largest `DGH(H_L) · DGH(H_R)` over the declared
  cuts `K`; elsewhere, claim 055's zero/trapped values.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Standalone.D15Switch

open Standalone.D13DriftNull Standalone.D14VolPaths

variable {n : ℕ}

/-- The piecewise-constant parameter: `pL` before the cut, `pR` from it. -/
def swp (c : ℕ) (pL pR : ℝ) : Fin n → ℝ := fun j => if (j : ℕ) < c then pL else pR

/-- (1): the single-switch price density. -/
noncomputable def gSw (Δ : Fin n → ℝ) (c : ℕ) (bL κL bR κR y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  gV Δ (swp c bL bR) (swp c κL κR) y0 y

/-- The left and right segments of a cut. -/
def segL (c : ℕ) : Finset (Fin n) := Finset.univ.filter fun j => (j : ℕ) < c
def segR (c : ℕ) : Finset (Fin n) := Finset.univ.filter fun j => c ≤ (j : ℕ)

/-- `τ_H`. -/
def tauH (Δ : Fin n → ℝ) (H : Finset (Fin n)) : ℝ := ∑ j ∈ H, Δ j

/-- `a_H = Σ_H R_j / τ_H`. -/
noncomputable def aH (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (H : Finset (Fin n)) : ℝ :=
  (∑ j ∈ H, ret y0 y j) / tauH Δ H

/-- `Q_H = Σ_H (R_j − a_H Δ_j)²/Δ_j`. -/
noncomputable def QH (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (H : Finset (Fin n)) : ℝ :=
  ∑ j ∈ H, (ret y0 y j - aH Δ y0 y H * Δ j) ^ 2 / Δ j

/-- The right side of (4). -/
noncomputable def logDGH (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (H : Finset (Fin n)) : ℝ :=
  -((H.card : ℝ) / 2) * (Real.log (2 * π * QH Δ y0 y H / H.card) + 1) -
    (1 / 2) * ∑ j ∈ H, Real.log (Δ j) - ∑ j ∈ H, Real.log (y j)

/-- The segment maximum (4), `∞` at zero residual. -/
noncomputable def DGH (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (H : Finset (Fin n)) : ℝ≥0∞ :=
  open Classical in
  if 0 < QH Δ y0 y H then ENNReal.ofReal (Real.exp (logDGH Δ y0 y H)) else ⊤

/-- (5), with the zero/trapped values off positive paths. -/
noncomputable def Dsw (Δ : Fin n → ℝ) (K : Finset ℕ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  open Classical in
  if PosPath y0 y then K.sup fun c => DGH Δ y0 y (segL c) * DGH Δ y0 y (segR c)
  else if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0

/-- Claim 059, part 1. -/
def profile : Prop :=
  ∀ (n : ℕ) (Δ : Fin n → ℝ), (∀ j, 0 < Δ j) →
    -- At one cut with nonempty segments: the supremum over both segments' parameters is the
    -- product of the segment maxima.
    (∀ (c : ℕ) y0 y, PosPath y0 y → 1 ≤ c → c < n →
      (⨆ (bL : ℝ) (κL : ℝ) (_ : 0 < κL) (bR : ℝ) (κR : ℝ) (_ : 0 < κR),
        ENNReal.ofReal (gSw Δ c bL κL bR κR y0 y)) =
        DGH Δ y0 y (segL c) * DGH Δ y0 y (segR c)) ∧
    -- (5) is the supremum over the declared cuts and all parameters, on every input array.
    (∀ (K : Finset ℕ) y0 y, K.Nonempty → (∀ c ∈ K, 1 ≤ c ∧ c < n) →
      (⨆ c ∈ K, ⨆ (bL : ℝ) (κL : ℝ) (_ : 0 < κL) (bR : ℝ) (κR : ℝ) (_ : 0 < κR),
        ENNReal.ofReal (gSw Δ c bL κL bR κR y0 y)) = Dsw Δ K y0 y) ∧
    -- Both segment factors are positive on positive paths; the maximum is finite exactly when
    -- every allowed segment has positive residual.
    (∀ (K : Finset ℕ) y0 y, PosPath y0 y → (∀ c ∈ K, 1 ≤ c ∧ c < n) →
      (∀ c ∈ K, 0 < DGH Δ y0 y (segL c) ∧ 0 < DGH Δ y0 y (segR c)) ∧
      (Dsw Δ K y0 y < ⊤ ↔ ∀ c ∈ K, 0 < QH Δ y0 y (segL c) ∧ 0 < QH Δ y0 y (segR c))) ∧
    -- Measurability.
    (∀ K : Finset ℕ, Measurable fun x : ℝ × (Fin n → ℝ) => Dsw Δ K x.1 x.2) ∧
    -- A one-increment segment has zero residual, so a cut at `1` or `n − 1` makes (5) infinite.
    (∀ (K : Finset ℕ) y0 y, PosPath y0 y → (∀ c ∈ K, 1 ≤ c ∧ c < n) →
      (1 ∈ K ∨ n - 1 ∈ K) → Dsw Δ K y0 y = ⊤) ∧
    -- The nonzero example: returns `R_j = (j+1)Δ_j` give positive residual on every segment of at
    -- least two increments.
    (∀ y0 y, PosPath y0 y → (∀ j, ret y0 y j = ((j : ℕ) + 1) * Δ j) →
      ∀ H : Finset (Fin n), 2 ≤ H.card → 0 < QH Δ y0 y H)


open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated
  Standalone.D3CatalogueCalibration Standalone.D13DriftRect

/-- The switch parameters `(c, b_L, κ_L, b_R, κ_R)` with `c ∈ K` and positive scales. -/
def SwPar (K : Finset ℕ) : Type :=
  {θ : ℕ × ℝ × ℝ × ℝ × ℝ // θ.1 ∈ K ∧ 0 < θ.2.2.1 ∧ 0 < θ.2.2.2.2}

instance (K : Finset ℕ) : MeasurableSpace (SwPar K) := Subtype.instMeasurableSpace

open Classical in
/-- Claim 059 on claim 054's design: the score (3), parts 2 and 3, and the panel results. -/
def score : Prop :=
  (∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ) (K : Finset ℕ), K.Nonempty → (∀ c' ∈ K, 2 ≤ c' ∧ c' + 2 ≤ m) →
    let g := gC t pw κ
    let sel := selC hN.size t s pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    let gSwN := fun (c' : ℕ) (bL κL bR κR : ℝ) (u : Fin (k + 1) → NNR) (v : Fin m → NNR) =>
      gSw Δe c' bL κL bR κR (u (Fin.last k) : ℝ) fun l => (v l : ℝ)
    let DswN := fun (K' : Finset ℕ) (u : Fin (k + 1) → NNR) (v : Fin m → NNR) =>
      Dsw Δe K' (u (Fin.last k) : ℝ) fun l => (v l : ℝ)
    let EK := fun (K' : Finset ℕ) u v => Edrift (g (sel u) u v) (max (Gnull pw g u v) (DswN K' u v))
    let E := EK K
    -- The switch laws are normalized against `μ_CEV^m` at every training value.
    (∀ (c' : ℕ) (bL κL bR κR : ℝ) (u : Fin (k + 1) → NNR), 0 < κL → 0 < κR →
      ∫⁻ v, ENNReal.ofReal (gSwN c' bL κL bR κR u v) ∂(Measure.pi fun _ : Fin m => muCEV) = 1) ∧
    -- Part 1: the score is measurable and finite on every array.
    Measurable (Function.uncurry E) ∧ (∀ u v, E u v < ⊤) ∧
    -- Part 2, under the mixture premise (2).
    (∀ (ν : ProbabilityTheory.Kernel (Fin (k + 1) → NNR) ({ϑ : Fin c // pw ϑ ≤ 1} ⊕ SwPar K))
      [ProbabilityTheory.IsMarkovKernel ν] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR),
      Measurable U → Measurable V →
      (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z =>
        (Measure.pi fun _ : Fin m => muCEV).withDensity fun v => ENNReal.ofReal
          (Sum.elim (fun ϑ => g ϑ.1 u v)
            (fun θ : SwPar K => gSwN θ.1.1 θ.1.2.1 θ.1.2.2.1 θ.1.2.2.2.1 θ.1.2.2.2.2 u v) z)) →
      -- Part 1: (5) is finite almost surely under every law (2).
      P {ω | DswN K (U ω) (V ω) = ⊤} = 0 ∧
      (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a) ∧
    -- Part 3: the ordering (7), and fewer allowed cuts give a larger score.
    (∀ u v, E u v ≤ Edrift (g (sel u) u v) (Dmax Δe pw g u v) ∧
      Edrift (g (sel u) u v) (Dmax Δe pw g u v) ≤ Ecomp pw (fun ϑ => g ϑ u v) (sel u)) ∧
    (∀ K' : Finset ℕ, K ⊆ K' → (∀ c' ∈ K', 2 ≤ c' ∧ c' + 2 ≤ m) → ∀ u v, EK K' u v ≤ E u v) ∧
    -- Part 3: the nonzero example (every allowed segment has positive residual and `Ĝ > 0`).
    (∀ u v, PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) →
      (∀ c' ∈ K, 0 < QH Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) (segL c') ∧
        0 < QH Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) (segR c')) →
      0 < g (sel u) u v → 0 < E u v) ∧
    -- Part 3: absorbed arrays.
    (∀ u v, (u (Fin.last k) : ℝ) = 0 → (∀ l, (v l : ℝ) = 0) → E u v = 1) ∧
    (∀ u v, 0 < (u (Fin.last k) : ℝ) → (∃ l, (v l : ℝ) = 0) →
      E u v = Ecomp pw (fun ϑ => g ϑ u v) (sel u) ∧ E u v ≤ 1)) ∧
  -- The panel: union bound; e-BH under AX-53 with or without a mask; e-BH never selects `≤ 1`.
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
  (∀ {ι : Type} [Fintype ι] (q : ℝ) (x : ι → ℝ), 0 < q → q < 1 →
    ∀ i ∈ Standalone.D12CatalogueFDR.rej q x, 1 < x i)

/-- Claim 059, part 1: the arrays where (5) is infinite are `μ_CEV^m`-null. -/
def nullSet : Prop :=
  ∀ (m : ℕ) (Δ : Fin m → ℝ), (∀ j, 0 < Δ j) → ∀ (K : Finset ℕ), (∀ c ∈ K, 2 ≤ c ∧ c + 2 ≤ m) →
    ∀ y0 : ℝ, (Measure.pi fun _ : Fin m => muCEV) {v | Dsw Δ K y0 (fun l => (v l : ℝ)) = ⊤} = 0

/-- Claim 059. -/
def statement : Prop := profile ∧ score ∧ nullSet

end Standalone.D15Switch
