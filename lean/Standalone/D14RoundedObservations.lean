import Standalone.RoundedCells
import Standalone.D3PriceCatalogue
import Standalone.D12CatalogueFDR

/-!
# Claim 024 (D14): rounded-price likelihood failure and the matched observation-law correction

Statement only; the proof is `Novel/D14RoundedObservationsProof.lean`. Source claim:
`claims/024-d14-rounded-observations.md`.
* Part 1, part 2's constants, part 3's cell facts and part 4 are deterministic, in
  `Standalone.RoundedCells`.
* This file holds part 2's probabilities and the stochastic content of part 3.

**Inputs.** AX-55 and AX-54 are claim 052's restatements (`AX55`, `AX54`), and AX-53 is claim 053's
(`AX53`). AX-52's moment form is proved (claim 051's `core_holds`).

**Part 2.** The true price is `S_t = exp(W_t − t/2)` with `W` an `(𝓕, P)`-Brownian motion: AX-55
with start 1 and volatility 1, `P = Q`. Write `X = S_1` and `Y = Q_h(X)`.
* The exact-data null score `f₂(κ; 1, 1, X)/f₁(1; 1, 1, X)` has mean one.
* The plug-in score `E^plug = f₂(κ; 1, 1, Y)/f₁(1; 1, 1, Y)` equals `R_h(κ)` on `{Y = 1}`, which has
  probability `p_h`.
* Hence `E[E^plug] ≥ p_h R_h(κ)` (as a `[0, ∞]` integral), and `E[E^plug] → ∞` as `κ ↓ 0`.
* At `h = 1/2` and `κ = 1/100`, `P(E^plug > 20) ≥ p_h`.
* The matched terminal score, the ratio of the alternative and null cell probabilities of `X`'s
  label, has mean one. On `{Y = 1}` it is at most `1/p_h`, which is below 20 at `h = 1/2`.

**Part 3.** Claim 052's model: per-name filtrations, `P = Q`, catalogues of powers in `{1, 2}`, and
prices measurable at fixed times (a disclosed premise). Every observed price is rounded by
`Q_h`, keeping the known start.
* `U i`, `V i` are the integer training and evaluation labels.
* The reference measure is counting measure on `ℤ^m`.
* `g` is (6), built from the full joint chain density of each candidate (`dens`).
* The selector is **any** function of the training labels. Every such function is measurable.

The conclusions are:
* the true candidate's cell masses are the actual label probabilities;
* `0 < g ≤ 1`, and `g(·|u)` sums to one;
* claim 051's premises (`CatalogueModel`, `IsCondDensity`) and its conclusions;
* claim 053's e-BH bounds, base and masked, conditional on AX-53.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D14RoundedObservations

open Standalone.PriceChain Standalone.RoundedCells Standalone.D3PriceCatalogue
  Standalone.D3CatalogueCalibration Standalone.D3PowerTail Standalone.D3VisitedRange
  Standalone.D12CatalogueFDR

variable {Ω : Type}

/-- The rounded training labels. -/
noncomputable def Uh {k m : ℕ} (h : ℝ) (S : ℝ≥0 → Ω → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0)
    (ω : Ω) : Fin (k + 1) → ℤ :=
  fun j => lab h (Ublock S t ω j)

/-- The rounded evaluation labels. -/
noncomputable def Vh {k m : ℕ} (h : ℝ) (S : ℝ≥0 → Ω → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0)
    (ω : Ω) : Fin m → ℤ :=
  fun l => lab h (Vblock S t ω l)

/-- A candidate's full joint price density on the grid (claim 052's chain from `s`). -/
noncomputable def dens {k m c : ℕ} (t : Fin (k + 1 + m + 1) → ℝ≥0) (s : ℝ) (pw : Fin c → ℕ)
    (κ : Fin c → ℝ) (ϑ : Fin c) : (Fin (k + 1 + m) → PosReal) → ℝ :=
  chain (ker (pw ϑ) (κ ϑ)) (incr t) s

/-- (6) for a candidate. -/
noncomputable def gcell {k m c : ℕ} (h : ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0) (s : ℝ)
    (pw : Fin c → ℕ) (κ : Fin c → ℝ) (ϑ : Fin c) (u : Fin (k + 1) → ℤ) (v : Fin m → ℤ) : ℝ :=
  gh h (dens t s pw κ ϑ) u v

/-- A terminal cell probability of the density `f` on `(0, ∞)`. -/
noncomputable def cellMass (f : ℝ → ℝ) (h : ℝ) (z : ℤ) : ℝ :=
  (∫⁻ y in {y : PosReal | lab h y = z}, ENNReal.ofReal (f y) ∂posVol).toReal

open Classical in
/-- Claim 024's probabilistic content. -/
def statement : Prop :=
  -- Part 2: the terminal counterexample and its matched score.
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (W S : ℝ≥0 → Ω → ℝ)
    (Solves : ℝ → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop) (h : ℝ),
    AX55 P 𝓕 W → AX54 P 𝓕 W Solves → IsFBrownian 𝓕 W P →
    (∀ t' ω, S t' ω = Real.exp (W t' ω - t' / 2)) → 0 < h →
    let X := S 1
    let Eplug := fun (κa : ℝ) ω => f2 κa 1 1 (Qh h (X ω)) / f1 1 1 1 (Qh h (X ω))
    let Mcell := fun (κa : ℝ) ω =>
      cellMass (f2 κa 1 1) h (lab h (X ω)) / cellMass (f1 1 1 1) h (lab h (X ω))
    P {ω | Qh h (X ω) = 1} = ENNReal.ofReal (ph h) ∧
    (∀ κa : ℝ, 0 < κa →
      ∫⁻ ω, ENNReal.ofReal (f2 κa 1 1 (X ω) / f1 1 1 1 (X ω)) ∂P = 1 ∧
      (∀ ω, Qh h (X ω) = 1 → Eplug κa ω = Rh κa) ∧
      ENNReal.ofReal (ph h * Rh κa) ≤ ∫⁻ ω, ENNReal.ofReal (Eplug κa ω) ∂P ∧
      ∫⁻ ω, ENNReal.ofReal (Mcell κa ω) ∂P = 1 ∧
      (∀ ω, Qh h (X ω) = 1 → Mcell κa ω ≤ 1 / ph h)) ∧
    Tendsto (fun κa => ∫⁻ ω, ENNReal.ofReal (Eplug κa ω) ∂P) (𝓝[>] 0) (𝓝 ⊤) ∧
    (h = 1 / 2 → ENNReal.ofReal (ph h) ≤ P {ω | 20 < Eplug (1 / 100) ω} ∧
      ∀ κa : ℝ, 0 < κa → ∀ ω, Qh h (X ω) = 1 → Mcell κa ω < 20)) ∧
  -- Part 3: the matched correction on claim 052's model.
  (∀ {ι : Type} [Fintype ι] [Nonempty ι] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : ι → Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W S : ι → ℝ≥0 → Ω → ℝ) (ζ : ι → Ω → WithTop ℝ≥0)
    (Solves : ι → ℝ → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop)
    (h : ℝ) (s R : ι → ℝ) (r : ℝ) (k m c : ι → ℕ) (t : ∀ i, Fin (k i + 1 + m i + 1) → ℝ≥0)
    (pw : ∀ i, Fin (c i) → ℕ) (κ : ∀ i, Fin (c i) → ℝ) (θs : ∀ i, Fin (c i))
    (sel : ∀ i, (Fin (k i + 1) → ℤ) → Fin (c i)) (α : ι → ℝ) (αt : ℝ),
    0 < h → (∀ i, Name (s i) (R i) (t i) (pw i) (κ i)) → 1 < r →
    (∀ i, AX55 P (𝓕 i) (W i)) → (∀ i, AX54 P (𝓕 i) (W i) (Solves i)) →
    (∀ i, IsFBrownian (𝓕 i) (W i) P) → (∀ i t', Measurable (S i t')) →
    -- `P = Q`: each observed price follows its true candidate's pricing law.
    (∀ i, pw i (θs i) = 1 →
      ∀ t' ω, S i t' ω = s i * Real.exp (κ i (θs i) * W i t' ω - κ i (θs i) ^ 2 * t' / 2)) →
    (∀ i, pw i (θs i) = 2 → Solves i (κ i (θs i)) (s i) (S i) (ζ i)) →
    (∀ i, 0 < α i ∧ α i < 1) → ∑ i, α i ≤ αt →
    let U := fun i => Uh h (S i) (t i)
    let V := fun i => Vh h (S i) (t i)
    let μ := fun i => (Measure.count : Measure (Fin (m i) → ℤ))
    let g := fun i => gcell h (t i) (s i) (pw i) (κ i)
    let σ := fun i (ϑ : Fin (c i)) => sigmaCat (pw i ϑ) (κ i ϑ)
    let p := fun i (ϑ : Fin (c i)) => (pw i ϑ : ℝ)
    -- (6) and claim 051's premises for the rounded observations.
    ((∀ i u v, P {ω | U i ω = u ∧ V i ω = v} =
          massUV h (dens (t i) (s i) (pw i) (κ i) (θs i)) u v ∧
        P {ω | U i ω = u} = massU h (dens (t i) (s i) (pw i) (κ i) (θs i)) u) ∧
      (∀ i ϑ u v, 0 < g i ϑ u v ∧ g i ϑ u v ≤ 1) ∧ (∀ i ϑ u, HasSum (fun v => g i ϑ u v) 1) ∧
      ∀ i, CatalogueModel (U i) (V i) (μ i) (g i) (sel i) ∧
        IsCondDensity P (U i) (V i) (μ i) (g i (θs i))) ∧
    -- Claim 051's conclusions.
    (let C := fun i ω => Cset (U i) (V i) (g i) (sel i) (α i) ω
     let b1 := fun i ϑ => B1 (R i) r (σ i ϑ)
     let b2 := fun i ϑ => B2 (R i) r (σ i ϑ)
     ((∀ i ω, (C i ω).Nonempty ∧ 0 < Lo (C i ω) (b1 i) ∧ Lo (C i ω) (b1 i) ≤ Hi (C i ω) (b1 i) ∧
        0 < Lo (C i ω) (b2 i) ∧ Lo (C i ω) (b2 i) ≤ Hi (C i ω) (b2 i)) ∧
      1 - αt ≤ P.real {ω | ∀ i, b1 i (θs i) ∈ Icc (Lo (C i ω) (b1 i)) (Hi (C i ω) (b1 i)) ∧
        b2 i (θs i) ∈ Icc (Lo (C i ω) (b2 i)) (Hi (C i ω) (b2 i))} ∧
      ∀ i, p i (θs i) ≤ 1 →
        P.real {ω | Hi (C i ω) (b2 i) < Lo (C i ω) (b1 i)} ≤ α i) ∧
     (∀ q : ℝ, (∀ i, p i (θs i) = q) →
      P.real {ω | ¬ ∃ q' : ℝ, ∀ i, q' ∈ p i '' C i ω} ≤ αt) ∧
     (∀ i,
      let E := Eval (U i) (V i) (g i) (sel i) (p i)
      (∀ ω, 0 < E ω) ∧ Measurable E ∧
      (p i (θs i) ≤ 1 → ∫⁻ ω, ENNReal.ofReal (E ω) ∂P ≤ 1 ∧
        ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P.real {ω | min 1 (1 / E ω) ≤ a} ≤ a) ∧
      (∀ ω, (C i ω ∩ {ϑ | p i ϑ ≤ 1} = ∅ ↔ 1 / α i < E ω) ∧
        (1 / α i < E ω ↔ min 1 (1 / E ω) < α i)) ∧
      ∀ ω, Hi (C i ω) (b2 i) < Lo (C i ω) (b1 i) → C i ω ∩ {ϑ | p i ϑ ≤ 1} = ∅)) ∧
    -- Claim 053's e-BH conclusions, conditional on AX-53.
    (AX53 → ∀ q : ℝ, 0 < q → q < 1 →
      let E : ι → Ω → ℝ := fun i => Eval (U i) (V i) (g i) (sel i) (p i)
      let N₀ : Finset ι := Finset.univ.filter fun i => p i (θs i) ≤ 1
      ∫ ω, fdp q (fun i => E i ω) N₀ ∂P ≤ q * N₀.card / Fintype.card ι ∧
      ∀ Scr : Ω → Finset ι, (∀ i, MeasurableSet {ω | i ∈ Scr ω}) →
        let E' : ι → Ω → ℝ := fun i ω => if i ∈ Scr ω then E i ω else 0
        (∀ ω, rej q (fun i => E' i ω) ⊆ Scr ω) ∧
        ∫ ω, fdp q (fun i => E' i ω) N₀ ∂P ≤ q * N₀.card / Fintype.card ι))

end Standalone.D14RoundedObservations
