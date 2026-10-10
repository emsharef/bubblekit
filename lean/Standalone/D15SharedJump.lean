import Standalone.D15JumpEnvelope
import Standalone.D15JumpProfileSearch

/-!
# Claim 061 (D15): a shared-parameter jump envelope with convergent two-dimensional enclosures

Statement only; the proof is `Novel/D15SharedJumpProof.lean`. Source claim:
`claims/061-d15-shared-jump-profile.md`.

**Structure.** `statement := envelope ∧ score ∧ Standalone.D15JumpProfileSearch.statement`.
* `envelope`: the price-space envelopes.
  - Part 1's (2): `g_J ≤ V_J ≤ U_J` for every `θ ∈ Θ_J`. `V_J` is finite and measurable, and takes the
    zero/trapped values off the positive stratum.
  - For a finite cap, `V_J` is `J_y` times the profile maximum attained in the rectangle (5); at
    cap `∞` it is `M_J`.
  - Part 1's orderings: `V_J` rises with the cap and as the floor falls, and is at most `D_G` at cap
    `0`.
  - Part 3's (7): for every measurable rule producing a finite cover of the rectangle,
    `V_J ≤ V_J^P ≤ U_J`; `V_J^P` is finite and measurable. Refining the cover lowers `V_J^P`.
* `score`: the scores on claim 054's design, under claim 060's inputs.
  - `E^prof`, with denominator `max(G₀, D_G, V_J)`, has all of claim 060's part-1 and part-2
    conclusions (`Valid`).
  - (3): `E^J ≤ E^prof ≤ E^drift ≤ E`, the cap and floor monotonicity, and `E^prof = E^drift` at
    cap `0`, `E^prof = E^J` at cap `∞`. Also the nonzero example and claim 055's score off the
    positive stratum.
  - For every measurable cover rule, `E^P` (denominator `max(G₀, D_G, V_J^P)`) is `Valid`, and (8)
    `E^J ≤ E^P ≤ E^prof` holds. Refinement raises `E^P`.
* `Standalone.D15JumpProfileSearch.statement`: parts 2 and 3 in return coordinates. These are the
  search rectangle (5), the box bounds (6), their refinement and their convergence.

**Inputs.** As in claim 060: AX-55 and AX-56 supply claim 054's kernels, AX-58 is proved, AX-53 is
used only for FDR (claim 060's panel), and AX-59 is not needed.

**Encodings** (claim 060's, on `n` evaluation prices `y` after `y0`).
* `Jy y = ∏ 1/y_j`. The returns are claim 055's `ret y0 y`, with durations `Δ`.
* `VJ σmin Λ` is (1)'s `V_J`:
  - on positive paths, `M_J` at `Λ = ∞`;
  - otherwise `⨆_{a ∈ ℝ, s ≥ σmin} J_y F_J(a, s)`, with `F_J` the profile `FJ (Λ.toReal)` of
    `Standalone.D15JumpProfileSearch`;
  - off the positive stratum, claim 055's zero/trapped values.
* **A cover rule** is `(Nb, bx)`: on data `x = (y0, y)` it uses the boxes `bx x i` for `i ≤ Nb x`.
  - `CoverRule` asks that `Nb` and every `bx · i` be measurable.
  - On positive paths with a finite cap, it asks that the boxes have positive lower scale and cover
    the rectangle (5).
  - The rule may depend on the evaluation data, as the claim allows for an enclosure of the
    unchanged null envelope.
* `BP` is `B_P = max_i W_J(bx i)` and `VP` is (7)'s `min(U_J, J_y B_P)`. At `Λ = ∞`, `VP = U_J = M_J`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Standalone.D15SharedJump

open Standalone.D13DriftNull Standalone.D15JumpEnvelope Standalone.D15JumpProfileSearch
  Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated
  Standalone.D3CatalogueCalibration

variable {n : ℕ}

/-- The price Jacobian `J_y = ∏_j 1/y_j`. -/
noncomputable def Jy (y : Fin n → ℝ) : ℝ := ∏ j, (y j)⁻¹

/-- (1): the shared-parameter envelope `V_J`, with the zero/trapped values off the positive stratum. -/
noncomputable def VJ (σmin : ℝ) (Λ : ℝ≥0∞) (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  open Classical in
  if PosPath y0 y then
    (if Λ = ⊤ then ENNReal.ofReal (MJ σmin Δ y)
      else ⨆ a : ℝ, ⨆ s : ℝ, ⨆ (_ : σmin ≤ s),
        ENNReal.ofReal (Jy y * FJ Λ.toReal Δ (ret y0 y) a s))
  else if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0

/-- `B_P`: the largest box bound (6) of the cover produced by the rule `(Nb, bx)`. -/
noncomputable def BP (Λ : ℝ≥0∞) (Δ : Fin n → ℝ) (Nb : ℝ × (Fin n → ℝ) → ℕ)
    (bx : ℝ × (Fin n → ℝ) → ℕ → ℝ × ℝ × ℝ × ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ⨆ i : ℕ, ⨆ (_ : i ≤ Nb (y0, y)), ENNReal.ofReal (WJ Λ.toReal Δ (ret y0 y) (bx (y0, y) i))

/-- (7): the price bound `V_J^P = min(U_J, J_y B_P)`, with the direct zero/trapped values. -/
noncomputable def VP (σmin : ℝ) (Λ : ℝ≥0∞) (Δ : Fin n → ℝ) (Nb : ℝ × (Fin n → ℝ) → ℕ)
    (bx : ℝ × (Fin n → ℝ) → ℕ → ℝ × ℝ × ℝ × ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  open Classical in
  if PosPath y0 y then
    (if Λ = ⊤ then UJ σmin Λ Δ y0 y
      else min (UJ σmin Λ Δ y0 y) (ENNReal.ofReal (Jy y) * BP Λ Δ Nb bx y0 y))
  else if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0

/-- A measurable rule producing, on positive paths with a finite cap, a finite cover of the search
rectangle (5) by boxes with positive lower scale. -/
def CoverRule (σmin : ℝ) (Λ : ℝ≥0∞) (Δ : Fin n → ℝ) (Nb : ℝ × (Fin n → ℝ) → ℕ)
    (bx : ℝ × (Fin n → ℝ) → ℕ → ℝ × ℝ × ℝ × ℝ) : Prop :=
  Measurable Nb ∧ (∀ i, Measurable fun x => bx x i) ∧
  ∀ y0 y, PosPath y0 y → Λ ≠ ⊤ →
    (∀ i ≤ Nb (y0, y), 0 < (bx (y0, y) i).2.2.1) ∧
    rect Λ.toReal σmin Δ (ret y0 y) ⊆ ⋃ i ∈ Finset.range (Nb (y0, y) + 1), box (bx (y0, y) i)

/-- The rule `(Nb', bx')` refines `(Nb, bx)`: every new box lies inside an old one. -/
def Refines (Nb' : ℝ × (Fin n → ℝ) → ℕ) (bx' : ℝ × (Fin n → ℝ) → ℕ → ℝ × ℝ × ℝ × ℝ)
    (Nb : ℝ × (Fin n → ℝ) → ℕ) (bx : ℝ × (Fin n → ℝ) → ℕ → ℝ × ℝ × ℝ × ℝ) : Prop :=
  ∀ x, ∀ k ≤ Nb' x, ∃ i ≤ Nb x, Inside (bx' x k) (bx x i)

/-- Parts 1 and 3 for the envelopes. -/
def envelope : Prop :=
  ∀ (n : ℕ) (Δ : Fin n → ℝ) (σmin : ℝ) (Λ : ℝ≥0∞), 0 < n → (∀ j, 0 < Δ j) → 0 < σmin →
    -- (2): every jump law in `Θ_J` is below `V_J`, which is below `U_J`.
    (∀ θ, ThetaJ σmin Λ θ → ∀ y0 y, ENNReal.ofReal (gJ Δ θ y0 y) ≤ VJ σmin Λ Δ y0 y) ∧
    (∀ y0 y, VJ σmin Λ Δ y0 y ≤ UJ σmin Λ Δ y0 y) ∧
    -- `V_J` is finite and measurable, with `D_G`'s values off the positive stratum.
    (∀ y0 y, VJ σmin Λ Δ y0 y < ⊤) ∧
    Measurable (fun x : ℝ × (Fin n → ℝ) => VJ σmin Λ Δ x.1 x.2) ∧
    (∀ y0 y, ¬ PosPath y0 y → VJ σmin Λ Δ y0 y = DG Δ y0 y) ∧
    -- (5) in price coordinates: a finite cap's supremum is attained in the rectangle.
    (Λ ≠ ⊤ → ∀ y0 y, PosPath y0 y → ∃ p ∈ rect Λ.toReal σmin Δ (ret y0 y),
      VJ σmin Λ Δ y0 y = ENNReal.ofReal (Jy y * FJ Λ.toReal Δ (ret y0 y) p.1 p.2)) ∧
    (Λ = ⊤ → ∀ y0 y, PosPath y0 y → VJ σmin Λ Δ y0 y = ENNReal.ofReal (MJ σmin Δ y)) ∧
    -- Raising the cap or lowering the floor raises `V_J`; at cap zero `V_J ≤ D_G`.
    (∀ Λ' : ℝ≥0∞, Λ ≤ Λ' → ∀ y0 y, VJ σmin Λ Δ y0 y ≤ VJ σmin Λ' Δ y0 y) ∧
    (∀ σ' : ℝ, 0 < σ' → σ' ≤ σmin → ∀ y0 y, VJ σmin Λ Δ y0 y ≤ VJ σ' Λ Δ y0 y) ∧
    (Λ = 0 → ∀ y0 y, VJ σmin Λ Δ y0 y ≤ DG Δ y0 y) ∧
    -- (7): every measurable cover rule gives a finite measurable bound between `V_J` and `U_J`.
    (∀ Nb bx, CoverRule σmin Λ Δ Nb bx →
      (∀ y0 y, VJ σmin Λ Δ y0 y ≤ VP σmin Λ Δ Nb bx y0 y ∧
        VP σmin Λ Δ Nb bx y0 y ≤ UJ σmin Λ Δ y0 y) ∧
      (∀ y0 y, VP σmin Λ Δ Nb bx y0 y < ⊤) ∧
      Measurable (fun x : ℝ × (Fin n → ℝ) => VP σmin Λ Δ Nb bx x.1 x.2) ∧
      (∀ y0 y, ¬ PosPath y0 y → VP σmin Λ Δ Nb bx y0 y = DG Δ y0 y)) ∧
    -- Refining a cover does not raise `V_J^P`.
    (∀ Nb bx Nb' bx', CoverRule σmin Λ Δ Nb bx → Refines Nb' bx' Nb bx →
      ∀ y0 y, VP σmin Λ Δ Nb' bx' y0 y ≤ VP σmin Λ Δ Nb bx y0 y)

/-- Claim 060's part-1 and part-2 conclusions for the score with denominator `D`. -/
def Valid {k m c : ℕ} (Δe : Fin m → ℝ) (pw : Fin c → ℝ)
    (g : Fin c → (Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ) (sel : (Fin (k + 1) → NNR) → Fin c)
    (σmin : ℝ) (Λ : ℝ≥0∞) (D : (Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ≥0∞) : Prop :=
  let μm : Measure (Fin m → NNR) := Measure.pi fun _ : Fin m => muCEV
  let gJN := fun (θ : ℝ × ℝ × ℝ × ℝ × ℝ) (u : Fin (k + 1) → NNR) (v : Fin m → NNR) =>
    gJ Δe θ (u (Fin.last k) : ℝ) fun l => (v l : ℝ)
  let E := fun u v => Edrift (g (sel u) u v) (D u v)
  (∀ θ, ThetaJ σmin Λ θ → ∀ u v, ENNReal.ofReal (gJN θ u v) ≤ D u v) ∧
  Measurable (Function.uncurry E) ∧ (∀ u v, E u v < ⊤) ∧
  (∀ u v, D u v = ⊤ → DG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) = ⊤) ∧
  (∀ u, μm {v | D u v = ⊤} = 0) ∧
  ∀ (ν : ProbabilityTheory.Kernel (Fin (k + 1) → NNR)
      ({ϑ : Fin c // pw ϑ ≤ 1} ⊕ (GPar ⊕ JPar σmin Λ))) [ProbabilityTheory.IsMarkovKernel ν]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
    (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z =>
      μm.withDensity fun v => ENNReal.ofReal
        (Sum.elim (fun ϑ => g ϑ.1 u v)
          (Sum.elim (fun p : GPar => gGN Δe p.1.1 p.1.2 u v)
            (fun θ : JPar σmin Λ => gJN θ.1 u v)) z)) →
    P {ω | D (U ω) (V ω) = ⊤} = 0 ∧
    (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
    ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
    ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a

/-- The scores of parts 1 and 3 on claim 054's design. -/
def score : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ) (σmin : ℝ) (Λ : ℝ≥0∞), 2 ≤ m → 0 < σmin →
    let g := gC t pw κ
    let sel := selC hN.size t s pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    let y0 := fun u : Fin (k + 1) → NNR => (u (Fin.last k) : ℝ)
    let yv := fun v : Fin m → NNR => fun l => (v l : ℝ)
    let ED := fun u v => Edrift (g (sel u) u v) (Dmax Δe pw g u v)
    let EJ := fun u v => Edrift (g (sel u) u v) (max (Dmax Δe pw g u v) (UJ σmin Λ Δe (y0 u) (yv v)))
    let DP := fun (σ' : ℝ) (Λ' : ℝ≥0∞) u v => max (Dmax Δe pw g u v) (VJ σ' Λ' Δe (y0 u) (yv v))
    let EP := fun σ' Λ' u v => Edrift (g (sel u) u v) (DP σ' Λ' u v)
    let E := EP σmin Λ
    -- Part 1: `E^prof` has all of claim 060's conclusions.
    Valid Δe pw g sel σmin Λ (DP σmin Λ) ∧
    -- (3), with the ordering against claim 054's score `E`.
    (∀ u v, EJ u v ≤ E u v ∧ E u v ≤ ED u v ∧ ED u v ≤ Ecomp pw (fun ϑ => g ϑ u v) (sel u)) ∧
    -- Raising the cap, or lowering the floor, weakly lowers the score.
    (∀ Λ' : ℝ≥0∞, Λ ≤ Λ' → ∀ u v, EP σmin Λ' u v ≤ E u v) ∧
    (∀ σ' : ℝ, 0 < σ' → σ' ≤ σmin → ∀ u v, EP σ' Λ u v ≤ E u v) ∧
    -- Cap zero is claim 055's score; cap infinity is claim 060's.
    (Λ = 0 → ∀ u v, E u v = ED u v) ∧ (Λ = ⊤ → ∀ u v, E u v = EJ u v) ∧
    -- The nonzero example, and claim 055's score off the positive stratum.
    (∀ u v, PosPath (y0 u) (yv v) → 0 < QG Δe (y0 u) (yv v) → 0 < g (sel u) u v → 0 < E u v) ∧
    (∀ u v, ¬ PosPath (y0 u) (yv v) → E u v = ED u v) ∧
    -- Part 3: every measurable cover rule gives a valid score with (8).
    (∀ Nb bx, CoverRule σmin Λ Δe Nb bx →
      let EB := fun u v => Edrift (g (sel u) u v)
        (max (Dmax Δe pw g u v) (VP σmin Λ Δe Nb bx (y0 u) (yv v)))
      Valid Δe pw g sel σmin Λ (fun u v =>
        max (Dmax Δe pw g u v) (VP σmin Λ Δe Nb bx (y0 u) (yv v))) ∧
      ∀ u v, EJ u v ≤ EB u v ∧ EB u v ≤ E u v) ∧
    -- Refinement raises the analytic score.
    (∀ Nb bx Nb' bx', CoverRule σmin Λ Δe Nb bx → Refines Nb' bx' Nb bx → ∀ u v,
      Edrift (g (sel u) u v) (max (Dmax Δe pw g u v) (VP σmin Λ Δe Nb bx (y0 u) (yv v))) ≤
        Edrift (g (sel u) u v) (max (Dmax Δe pw g u v) (VP σmin Λ Δe Nb' bx' (y0 u) (yv v))))

/-- Claim 061. -/
def statement : Prop := envelope ∧ score ∧ Standalone.D15JumpProfileSearch.statement

end Standalone.D15SharedJump
