import Standalone.D3CatalogueCalibration
import Standalone.PriceChain
import Standalone.D3VisitedRange

/-!
# Claim 052 (D3): a price-law instance of finite-catalogue calibration

Statement only; the proof is `Novel/D3PriceCatalogueProof.lean`. Source claim:
`claims/052-d3-price-catalogue.md`. The deterministic kernel and chain facts are the separate
statement `Standalone.PriceChain`, and claim 051's `core` is applied.

**Inputs.** AX-55 and AX-54 are restated on each name's base as `AX55` and `AX54`. AX-54 is stated
over a solution relation variable `Solves κ x S ζ` for `dS = κS² dW` on `(0, ∞)`. The proof derives
both from `Upstream.PriceKernels`. Their grid fields are the finite-grid iterates of the cited
Markov kernels:
* `GridLaw`: the full-grid density;
* `SplitLaw`: the conditional density of the evaluation block given the training block, started at
  the last training price.

The statement supplies these through the restated inputs. It does not derive them from a one-step
Markov field, as the formalization notes require us to say.

**Model** (`Name`). For each name in a finite panel:
* start `s > 0`; grid `0 = t₀ < … ` with `k+1 ≥ 1` training and `m ≥ 1` evaluation prices;
* an ordered catalogue `Fin c`, `c ≥ 1`, of pairs `(pwⱼ, κⱼ)` with `pwⱼ ∈ {1, 2}`, `κⱼ > 0` and at
  least one `pw = 1`; and `R > 0`.
* **`P = Q`**: the observed price is, under `P`, the pricing law of the true pair `θs` driven by an
  `(𝓕ᵢ, P)`-Brownian `Wᵢ`. That is the explicit exponential for `pw = 1`, and a `Solves` solution
  for `pw = 2`. **Each name has its own filtration `𝓕ᵢ`**, and its martingale null is stated in `𝓕ᵢ`.
  Names may depend on each other arbitrarily, including lead–lag dependence that no common
  filtration would allow, and conditioning uses only a name's own prices. The observed prices are measurable at each fixed time, a disclosed premise: AX-54's
  solution relation does not supply it.

**Objects.**
* `ker pw κ` is `f1 κ` or `f2 κ`.
* `gcat`, (2): the evaluation chain started at the last training price.
* `Ltrain`: the training chain from `s`.
* `selector`: the first maximizer of `Ltrain` in the fixed order.
* `sigmaCat`: the coefficient `κ x^pw` on all of `(0, ∞)`, with exponent `pw`.

**Statement.**
* **Part 1.** Claim 051's premises hold for these price laws:
  - `CatalogueModel` and `IsCondDensity` at the true pair;
  - `CPow` for every candidate, with the blocks (3);
  - the martingale null: `pw = 1` is a martingale, and `pw = 2` is not a martingale on any `[0, T]`.
* **Part 2.** Claim 051's conclusions (`core`), instantiated.
* **Part 3.** On each fixed grid, any two candidate grid laws are mutually absolutely continuous, and
  the actual grid law is the true candidate's. So an event of probability one at an alternative
  has probability one at every null candidate.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Standalone.D3PriceCatalogue

open Standalone.PriceChain Standalone.D3CatalogueCalibration Standalone.D3PowerTail Standalone.D1TwoEndpoint
  Standalone.D3VisitedRange

/-! ## Grid vocabulary (shared with `Upstream.PriceKernels`) -/

/-- `x` if positive, else `1`. -/
noncomputable def toPos (x : ℝ) : PosReal := if h : 0 < x then ⟨x, h⟩ else ⟨1, one_pos⟩

/-- Grid increments. -/
def incr {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (j : Fin n) : ℝ := (t j.succ : ℝ) - t j.castSucc

variable {Ω : Type} {mΩ : MeasurableSpace Ω}

/-- The grid prices. -/
noncomputable def obs {n : ℕ} (S : ℝ≥0 → Ω → ℝ) (t : Fin (n + 1) → ℝ≥0) (ω : Ω) :
    Fin n → PosReal := fun j => toPos (S (t j.succ) ω)

/-- The training block. -/
noncomputable def Ublock {k m : ℕ} (S : ℝ≥0 → Ω → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0) (ω : Ω) :
    Fin (k + 1) → PosReal := fun j => obs S t ω (Fin.castAdd m j)

/-- The evaluation block. -/
noncomputable def Vblock {k m : ℕ} (S : ℝ≥0 → Ω → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0) (ω : Ω) :
    Fin m → PosReal := fun l => obs S t ω (Fin.natAdd (k + 1) l)

/-- The full-grid law has the chain density from `x`. -/
def GridLaw {n : ℕ} (P : Measure Ω) (S : ℝ≥0 → Ω → ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (t : Fin (n + 1) → ℝ≥0) (x : ℝ) : Prop :=
  P.map (obs S t) =
    (Measure.pi fun _ : Fin n => posVol).withDensity fun y => ENNReal.ofReal (chain f (incr t) x y)

/-- The evaluation block given the training block has the chain density from the last training
price. -/
def SplitLaw {k m : ℕ} (P : Measure Ω) [IsFiniteMeasure P] (S : ℝ≥0 → Ω → ℝ)
    (f : ℝ → ℝ → ℝ → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0) : Prop :=
  ∀ᵐ u ∂(P.map (Ublock S t)), condDistrib (Vblock S t) (Ublock S t) P u =
    (Measure.pi fun _ : Fin m => posVol).withDensity fun v =>
      ENNReal.ofReal (chain f (fun l => incr t (Fin.natAdd (k + 1) l)) (u (Fin.last k) : ℝ) v)

/-- AX-55 restated on a base with driver `W`. -/
def AX55 (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) :
    Prop :=
  IsFBrownian 𝓕 W P →
    (∀ (S : ℝ≥0 → Ω → ℝ) (κ x : ℝ), 0 < κ → 0 < x →
      (∀ t ω, S t ω = x * Real.exp (κ * W t ω - κ ^ 2 * t / 2)) →
      Martingale S 𝓕 P ∧
      (∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), t 0 = 0 → StrictMono t → GridLaw P S (f1 κ) t x) ∧
      ∀ (k m : ℕ) (t : Fin (k + 1 + m + 1) → ℝ≥0), t 0 = 0 → StrictMono t →
        SplitLaw P S (f1 κ) t) ∧
    ∀ κ Δ x : ℝ, 0 < κ → 0 < Δ → 0 < x → ∫⁻ y, ENNReal.ofReal (f1 κ Δ x y) ∂posVol = 1

/-- AX-54 restated on a base with driver `W`, over the solution relation `Solves κ x S ζ` of
`dS = κS² dW` on `(0, ∞)` from `x`. Its one-step normalization of `f₂` is not restated: it is a
deterministic identity, proved as `Novel.D30SmallScale.kernelNorm2_holds`. -/
def AX54 (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (Solves : ℝ → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop) : Prop :=
  IsFBrownian 𝓕 W P →
    (∀ (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (κ x : ℝ), 0 < κ → 0 < x → Solves κ x S ζ →
      (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t, 0 < S t ω) ∧ IsLocalMartingale S 𝓕 P ∧
      (∀ T : ℝ≥0, 0 < T → ¬ Martingale (fun t => S (min t T)) 𝓕 P) ∧
      (∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), t 0 = 0 → StrictMono t → GridLaw P S (f2 κ) t x) ∧
      ∀ (k m : ℕ) (t : Fin (k + 1 + m + 1) → ℝ≥0), t 0 = 0 → StrictMono t →
        SplitLaw P S (f2 κ) t)

/-! ## The catalogue -/

/-- The kernel of a candidate. -/
noncomputable def ker (pw : ℕ) (κ : ℝ) : ℝ → ℝ → ℝ → ℝ := if pw = 1 then f1 κ else f2 κ

/-- (2): the evaluation chain from the last training price. -/
noncomputable def gcat {k m c : ℕ} (t : Fin (k + 1 + m + 1) → ℝ≥0) (pw : Fin c → ℕ) (κ : Fin c → ℝ)
    (ϑ : Fin c) (u : Fin (k + 1) → PosReal) (v : Fin m → PosReal) : ℝ :=
  chain (ker (pw ϑ) (κ ϑ)) (fun l => incr t (Fin.natAdd (k + 1) l)) (u (Fin.last k) : ℝ) v

/-- The training likelihood from `s`. -/
noncomputable def Ltrain {k m c : ℕ} (t : Fin (k + 1 + m + 1) → ℝ≥0) (s : ℝ) (pw : Fin c → ℕ)
    (κ : Fin c → ℝ) (ϑ : Fin c) (u : Fin (k + 1) → PosReal) : ℝ :=
  chain (ker (pw ϑ) (κ ϑ)) (fun j => incr t (Fin.castAdd m j)) s u

/-- The first maximizer of the training likelihood in the fixed catalogue order. -/
noncomputable def selector {k m c : ℕ} (hc : 0 < c) (t : Fin (k + 1 + m + 1) → ℝ≥0) (s : ℝ)
    (pw : Fin c → ℕ) (κ : Fin c → ℝ) (u : Fin (k + 1) → PosReal) : Fin c :=
  open Classical in
  if h : (Finset.univ.filter fun j => ∀ h, Ltrain t s pw κ h u ≤ Ltrain t s pw κ j u).Nonempty
  then (Finset.univ.filter fun j => ∀ h, Ltrain t s pw κ h u ≤ Ltrain t s pw κ j u).min' h
  else ⟨0, hc⟩

/-- The candidate coefficient `κ x^pw` on `(0, ∞)`. -/
noncomputable def sigmaCat (pw : ℕ) (κ : ℝ) (x : ℝ) : ℝ := κ * x ^ (pw : ℝ)

/-- One name's declared design. -/
structure Name (s R : ℝ) {k m c : ℕ} (t : Fin (k + 1 + m + 1) → ℝ≥0) (pw : Fin c → ℕ)
    (κ : Fin c → ℝ) : Prop where
  start : 0 < s
  onset : 0 < R
  grid0 : t 0 = 0
  gridMono : StrictMono t
  evals : 1 ≤ m
  size : 0 < c
  powers : ∀ j, pw j = 1 ∨ pw j = 2
  scales : ∀ j, 0 < κ j
  hasNull : ∃ j, pw j = 1

/-- Claim 052. -/
def statement : Prop :=
  ∀ {ι : Type} [Fintype ι] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : ι → Filtration ℝ≥0 ‹MeasurableSpace Ω›) (W S : ι → ℝ≥0 → Ω → ℝ) (ζ : ι → Ω → WithTop ℝ≥0)
    (Solves : ι → ℝ → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop)
    (s R : ι → ℝ) (r : ℝ) (k m c : ι → ℕ) (t : ∀ i, Fin (k i + 1 + m i + 1) → ℝ≥0)
    (pw : ∀ i, Fin (c i) → ℕ) (κ : ∀ i, Fin (c i) → ℝ) (θs : ∀ i, Fin (c i)) (α : ι → ℝ) (αt : ℝ)
    (hc : ∀ i, 0 < c i),
    (∀ i, Name (s i) (R i) (t i) (pw i) (κ i)) → 1 < r →
    (∀ i, AX55 P (𝓕 i) (W i)) → (∀ i, AX54 P (𝓕 i) (W i) (Solves i)) →
    (∀ i, IsFBrownian (𝓕 i) (W i) P) →
    (∀ i t', Measurable (S i t')) →
    -- `P = Q`: each observed price follows its true candidate's pricing law.
    (∀ i, pw i (θs i) = 1 →
      ∀ t' ω, S i t' ω = s i * Real.exp (κ i (θs i) * W i t' ω - κ i (θs i) ^ 2 * t' / 2)) →
    (∀ i, pw i (θs i) = 2 → Solves i (κ i (θs i)) (s i) (S i) (ζ i)) →
    (∀ i, 0 < α i ∧ α i < 1) → ∑ i, α i ≤ αt →
    let U := fun i => Ublock (S i) (t i)
    let V := fun i => Vblock (S i) (t i)
    let μ := fun i => Measure.pi fun _ : Fin (m i) => posVol
    let g := fun i => gcat (t i) (pw i) (κ i)
    let sel := fun i => selector (hc i) (t i) (s i) (pw i) (κ i)
    let σ := fun i (ϑ : Fin (c i)) => sigmaCat (pw i ϑ) (κ i ϑ)
    let p := fun i (ϑ : Fin (c i)) => (pw i ϑ : ℝ)
    -- Part 1: claim 051's premises, for these price laws.
    ((∀ i, CatalogueModel (U i) (V i) (μ i) (g i) (sel i) ∧
        IsCondDensity P (U i) (V i) (μ i) (g i (θs i)) ∧
        ∀ ϑ, CPow (R i) (σ i ϑ) ∧ (∃ κ' : ℝ, 0 < κ' ∧ ∀ x, R i ≤ x → σ i ϑ x = κ' * x ^ p i ϑ)) ∧
      (∀ i ϑ, pw i ϑ = 1 → B1 (R i) r (σ i ϑ) = Real.log r / κ i ϑ ^ 2 ∧
        B2 (R i) r (σ i ϑ) = Real.log r / κ i ϑ ^ 2) ∧
      (∀ i ϑ, pw i ϑ = 2 →
        B1 (R i) r (σ i ϑ) = (1 - r ^ (-2 : ℤ)) / (2 * κ i ϑ ^ 2 * R i ^ 2) ∧
        B2 (R i) r (σ i ϑ) = r ^ (-2 : ℤ) * B1 (R i) r (σ i ϑ)) ∧
      (∀ i, pw i (θs i) = 1 → Martingale (S i) (𝓕 i) P) ∧
      (∀ i, pw i (θs i) = 2 → ∀ T : ℝ≥0, 0 < T →
        ¬ Martingale (fun t' => S i (min t' T)) (𝓕 i) P)) ∧
    -- Part 2: claim 051's conclusions.
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
     (∀ i, (∃ ϑ, p i ϑ ≤ 1) →
      let E := Eval (U i) (V i) (g i) (sel i) (p i)
      (∀ ω, 0 < E ω) ∧ Measurable E ∧
      (p i (θs i) ≤ 1 → ∫⁻ ω, ENNReal.ofReal (E ω) ∂P ≤ 1 ∧
        ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P.real {ω | min 1 (1 / E ω) ≤ a} ≤ a) ∧
      (∀ ω, (C i ω ∩ {ϑ | p i ϑ ≤ 1} = ∅ ↔ 1 / α i < E ω) ∧
        (1 / α i < E ω ↔ min 1 (1 / E ω) < α i)) ∧
      ∀ ω, Hi (C i ω) (b2 i) < Lo (C i ω) (b1 i) → C i ω ∩ {ϑ | p i ϑ ≤ 1} = ∅)) ∧
    -- Part 3: fixed-grid equivalence.
    (∀ i (ϑ ϑ' : Fin (c i)),
      (Measure.pi fun _ : Fin (k i + 1 + m i) => posVol).withDensity
          (fun y => ENNReal.ofReal (chain (ker (pw i ϑ) (κ i ϑ)) (incr (t i)) (s i) y)) ≪
        (Measure.pi fun _ : Fin (k i + 1 + m i) => posVol).withDensity
          (fun y => ENNReal.ofReal (chain (ker (pw i ϑ') (κ i ϑ')) (incr (t i)) (s i) y))) ∧
    (∀ i, GridLaw P (S i) (ker (pw i (θs i)) (κ i (θs i))) (t i) (s i))

end Standalone.D3PriceCatalogue
