import Standalone.CEVSupport
import Standalone.D3PriceCatalogue
import Standalone.D12CatalogueFDR

/-!
# Claim 054 (D13): calibrated CEV catalogue inference with absorption retained

Statement only; the proof is `Novel/D13CEVCatalogueProof.lean`. Source claim:
`claims/054-d13-cev-catalogue.md`. The finite-array facts are the separate deterministic statement
`Standalone.CEVSupport`.

**Inputs.**
* AX-55 is claim 052's restatement (`D3PriceCatalogue.AX55`) and AX-56 is restated here (`AX56`),
  over a solution relation for `dS = κS^p dW` absorbed at zero. The proof derives both from their
  Upstream structures. Their grid conditional laws are supplied as fields: the finite-grid iterates
  of the cited Markov kernels. The p = 1 law, given on `(0, ∞)`, is transferred to `[0, ∞)` by the
  proof.
* AX-57 is `SplitLikelihoodSupport.AX57`, proved from Mathlib.
* AX-53 is claim 053's restatement (`D12CatalogueFDR.AX53`).
* AX-03 is restated for the coefficients `κx^p` over the same solution relation (`AX03`). A finite
  `I∞` gives a strict local martingale on every `[0, T]`, and an infinite one gives a martingale.
  The proof derives it from `Upstream.DriftlessIntegralCriterion`.

**Model** (`NameC`). For each name:
* a start `s > 0` and a grid with `k+1 ≥ 1` training and `m ≥ 1` evaluation prices;
* an ordered catalogue `Fin c` of pairs `(p, κ)` with `p > 0` and `κ > 0`, and a nonempty null
  `{p ≤ 1}`; and `R > 0`.

**`P = Q` per name.** The observed price is the true pair's pricing law under `P`, driven by an
`(𝓕ᵢ, P)`-Brownian motion with a per-name filtration:
* the explicit exponential for `p = 1`;
* an absorbed `Solves` solution otherwise.

Dependence across names is arbitrary. Prices are measurable at fixed times (a disclosed premise).

**Objects.** Every object is defined on all nonnegative arrays.
* Prices are observed in `[0, ∞)` (`toNNR`).
* `gC` is the evaluation chain of the claim's kernel `Kc`, started at the last training price.
* `selC` is the first maximizer of the training chain from `s`.
* `T₊ = R₊(Ĝ, gϑ)`, the confidence set `Cset = {ϑ : T₊ ≤ 1/α}`, and `Eval054 = min_{null} T₊`.
* The p-value is `zval = 1` if `E = 0`, else `min(1, 1/E)`.
* The blocks are `blk1` and `r^{2−2p} blk1`, with bands `Lo`/`Hi` over `Cset`.

**Statement.** Parts 1–4 of the claim, as listed in the conclusion.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Standalone.D13CEVCatalogue

open Standalone.CEVSupport Standalone.SplitLikelihoodSupport Standalone.D3CatalogueCalibration
  Standalone.D3PowerTail Standalone.D3VisitedRange Standalone.D1TwoEndpoint
  Standalone.D12CatalogueFDR

variable {Ω : Type} {mΩ : MeasurableSpace Ω}

/-- Grid increments. -/
def incr {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (j : Fin n) : ℝ := (t j.succ : ℝ) - t j.castSucc

/-- The grid prices in `[0, ∞)`. -/
noncomputable def obsN {n : ℕ} (S : ℝ≥0 → Ω → ℝ) (t : Fin (n + 1) → ℝ≥0) (ω : Ω) :
    Fin n → NNR := fun j => toNNR (S (t j.succ) ω)

/-- The training block. -/
noncomputable def UblockN {k m : ℕ} (S : ℝ≥0 → Ω → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0) (ω : Ω) :
    Fin (k + 1) → NNR := fun j => obsN S t ω (Fin.castAdd m j)

/-- The evaluation block. -/
noncomputable def VblockN {k m : ℕ} (S : ℝ≥0 → Ω → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0) (ω : Ω) :
    Fin m → NNR := fun l => obsN S t ω (Fin.natAdd (k + 1) l)

/-- The full-grid law relative to `muCEV^n`. -/
def GridLawN {n : ℕ} (P : Measure Ω) (S : ℝ≥0 → Ω → ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (t : Fin (n + 1) → ℝ≥0) (x : ℝ) : Prop :=
  P.map (obsN S t) = (Measure.pi fun _ : Fin n => muCEV).withDensity fun y =>
    ENNReal.ofReal (chainN f (incr t) x y)

/-- The conditional law of evaluation given training relative to `muCEV^m`. -/
def SplitLawN {k m : ℕ} (P : Measure Ω) [IsFiniteMeasure P] (S : ℝ≥0 → Ω → ℝ)
    (f : ℝ → ℝ → ℝ → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0) : Prop :=
  ∀ᵐ u ∂(P.map (UblockN S t)), condDistrib (VblockN S t) (UblockN S t) P u =
    (Measure.pi fun _ : Fin m => muCEV).withDensity fun v =>
      ENNReal.ofReal (chainN f (fun l => incr t (Fin.natAdd (k + 1) l)) (u (Fin.last k) : ℝ) v)

/-- AX-56 restated on a base with driver `W`, over `Solves p κ x S ζ` for `dS = κS^p dW` absorbed
at zero. -/
def AX56 (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (Solves : ℝ → ℝ → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop) : Prop :=
  IsFBrownian 𝓕 W P →
    (∀ (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (p κ x : ℝ), 0 < p → p ≠ 1 → 0 < κ → 0 < x →
      Solves p κ x S ζ →
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ S t ω) ∧
      (∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), t 0 = 0 → StrictMono t → GridLawN P S (K p κ) t x) ∧
      ∀ (k m : ℕ) (t : Fin (k + 1 + m + 1) → ℝ≥0), t 0 = 0 → StrictMono t →
        SplitLawN P S (K p κ) t) ∧
    ∀ p κ Δ : ℝ, 0 < p → p ≠ 1 → 0 < κ → 0 < Δ →
      (∀ x y, 0 < x → 0 < y → 0 < fcev p κ Δ x y) ∧
      (p < 1 → ∀ x, 0 < x → 0 < acev p κ Δ x ∧ acev p κ Δ x < 1) ∧
      ∀ x, 0 < x → (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (fcev p κ Δ x y)) +
        ENNReal.ofReal (acev p κ Δ x) = 1

/-- AX-03 (Corollary 4.3 and the Remark after it) restated on a base with driver `W`, for the
coefficients `κx^p` over the solution relation `Solves`. -/
def AX03 (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (Solves : ℝ → ℝ → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop) : Prop :=
  IsFBrownian 𝓕 W P →
    ∀ (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (p κ x : ℝ), 0 < p → 0 < κ → 0 < x →
      Solves p κ x S ζ →
      (IInftyFinite (fun y => κ * y ^ p) → ∀ T : ℝ≥0, 0 < T → IsStrictLocalMartingaleOn T S 𝓕 P) ∧
      (¬ IInftyFinite (fun y => κ * y ^ p) → Martingale S 𝓕 P)

/-! ## The catalogue -/

/-- The evaluation chain from the last training price. -/
noncomputable def gC {k m c : ℕ} (t : Fin (k + 1 + m + 1) → ℝ≥0) (pw κ : Fin c → ℝ) (ϑ : Fin c)
    (u : Fin (k + 1) → NNR) (v : Fin m → NNR) : ℝ :=
  chainN (Kc (pw ϑ) (κ ϑ)) (fun l => incr t (Fin.natAdd (k + 1) l)) (u (Fin.last k) : ℝ) v

/-- The training chain from `s`. -/
noncomputable def LtrainC {k m c : ℕ} (t : Fin (k + 1 + m + 1) → ℝ≥0) (s : ℝ) (pw κ : Fin c → ℝ)
    (ϑ : Fin c) (u : Fin (k + 1) → NNR) : ℝ :=
  chainN (Kc (pw ϑ) (κ ϑ)) (fun j => incr t (Fin.castAdd m j)) s u

/-- The first maximizer of the training chain in the fixed order (ties, including all-zero
likelihoods, broken by the order). -/
noncomputable def selC {k m c : ℕ} (hc : 0 < c) (t : Fin (k + 1 + m + 1) → ℝ≥0) (s : ℝ)
    (pw κ : Fin c → ℝ) (u : Fin (k + 1) → NNR) : Fin c :=
  open Classical in
  if h : (Finset.univ.filter fun j => ∀ h, LtrainC t s pw κ h u ≤ LtrainC t s pw κ j u).Nonempty
  then (Finset.univ.filter fun j => ∀ h, LtrainC t s pw κ h u ≤ LtrainC t s pw κ j u).min' h
  else ⟨0, hc⟩

/-- One name's declared design. -/
structure NameC (s R : ℝ) {k m c : ℕ} (t : Fin (k + 1 + m + 1) → ℝ≥0) (pw κ : Fin c → ℝ) :
    Prop where
  start : 0 < s
  onset : 0 < R
  grid0 : t 0 = 0
  gridMono : StrictMono t
  evals : 1 ≤ m
  size : 0 < c
  powers : ∀ j, 0 < pw j
  scales : ∀ j, 0 < κ j
  hasNull : ∃ j, pw j ≤ 1

/-- The p-value `z = 1` if `E = 0`, else `min(1, 1/E)`. -/
noncomputable def zval (E : ℝ≥0∞) : ℝ := if E = 0 then 1 else min 1 (1 / E.toReal)

open Classical in
/-- Claim 054. -/
def statement : Prop :=
  AX57 → AX53 →
  ∀ {ι : Type} [Fintype ι] [Nonempty ι] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : ι → Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W S : ι → ℝ≥0 → Ω → ℝ) (ζ : ι → Ω → WithTop ℝ≥0)
    (Solves : ι → ℝ → ℝ → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop)
    (s R : ι → ℝ) (r : ℝ) (k m c : ι → ℕ) (t : ∀ i, Fin (k i + 1 + m i + 1) → ℝ≥0)
    (pw κ : ∀ i, Fin (c i) → ℝ) (θs : ∀ i, Fin (c i)) (α : ι → ℝ) (αt : ℝ) (hc : ∀ i, 0 < c i),
    (∀ i, NameC (s i) (R i) (t i) (pw i) (κ i)) → 1 < r →
    (∀ i, Standalone.D3PriceCatalogue.AX55 P (𝓕 i) (W i)) → (∀ i, AX56 P (𝓕 i) (W i) (Solves i)) →
    (∀ i, IsFBrownian (𝓕 i) (W i) P) → (∀ i t', Measurable (S i t')) →
    -- `P = Q`: each observed price follows its true candidate's pricing law.
    (∀ i, pw i (θs i) = 1 →
      ∀ t' ω, S i t' ω = s i * Real.exp (κ i (θs i) * W i t' ω - κ i (θs i) ^ 2 * t' / 2)) →
    (∀ i, pw i (θs i) ≠ 1 → Solves i (pw i (θs i)) (κ i (θs i)) (s i) (S i) (ζ i)) →
    (∀ i, AX03 P (𝓕 i) (W i) (Solves i)) →
    (∀ i, 0 < α i ∧ α i < 1) → ∑ i, α i ≤ αt →
    let U := fun i => UblockN (S i) (t i)
    let V := fun i => VblockN (S i) (t i)
    let g := fun i => gC (t i) (pw i) (κ i)
    let sel := fun i => selC (hc i) (t i) (s i) (pw i) (κ i)
    let T := fun i ϑ ω => TplusE (U i) (V i) (g i) (sel i) ϑ ω
    let C := fun i ω => {ϑ | T i ϑ ω ≤ ENNReal.ofReal (1 / α i)}
    let E := fun i ω => Ecomp (pw i) (fun ϑ => g i ϑ (U i ω) (V i ω)) (sel i (U i ω))
    let null := fun i => {ϑ : Fin (c i) | pw i ϑ ≤ 1}
    let b1 := fun i (ϑ : Fin (c i)) => blk1 (R i) r (pw i ϑ) (κ i ϑ)
    let b2 := fun i (ϑ : Fin (c i)) => r ^ (2 - 2 * pw i ϑ) * b1 i ϑ
    let N₀ := Finset.univ.filter fun i => pw i (θs i) ≤ 1
    -- Part 1: coverage and finite evidence.
    ((∀ i ω, (C i ω).Nonempty) ∧ (∀ i ϑ, MeasurableSet {ω | ϑ ∈ C i ω}) ∧
      (∀ i, P {ω | θs i ∉ C i ω} ≤ ENNReal.ofReal (α i)) ∧
      P {ω | ∃ i, θs i ∉ C i ω} ≤ ENNReal.ofReal αt ∧
      (∀ i ω, E i ω < ⊤ ∧ (g i (sel i (U i ω)) (U i ω) (V i ω) = 0 → E i ω = 0) ∧
        (0 < g i (sel i (U i ω)) (U i ω) (V i ω) → ∃ G₀ : ℝ, 0 < G₀ ∧
          (∀ ϑ ∈ null i, g i ϑ (U i ω) (V i ω) ≤ G₀) ∧
          (∃ ϑ ∈ null i, g i ϑ (U i ω) (V i ω) = G₀) ∧
          E i ω = ENNReal.ofReal (g i (sel i (U i ω)) (U i ω) (V i ω) / G₀))) ∧
      (∀ i, pw i (θs i) ≤ 1 → ∫⁻ ω, E i ω ∂P ≤ 1 ∧
        ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E i ω) ≤ a} ≤ ENNReal.ofReal a) ∧
      ∀ i ω, (C i ω ∩ null i = ∅ ↔ ENNReal.ofReal (1 / α i) < E i ω) ∧
        (ENNReal.ofReal (1 / α i) < E i ω ↔ zval (E i ω) < α i)) ∧
    -- Part 2: bands and compatibility.
    ((∀ i ω, 0 < Lo (C i ω) (b1 i) ∧ Lo (C i ω) (b1 i) ≤ Hi (C i ω) (b1 i) ∧
        0 < Lo (C i ω) (b2 i) ∧ Lo (C i ω) (b2 i) ≤ Hi (C i ω) (b2 i)) ∧
      (∀ i ϑ, B1 (R i) r (fun x => κ i ϑ * x ^ pw i ϑ) = b1 i ϑ ∧
        B2 (R i) r (fun x => κ i ϑ * x ^ pw i ϑ) = b2 i ϑ) ∧
      1 - αt ≤ P.real {ω | ∀ i, b1 i (θs i) ∈ Icc (Lo (C i ω) (b1 i)) (Hi (C i ω) (b1 i)) ∧
        b2 i (θs i) ∈ Icc (Lo (C i ω) (b2 i)) (Hi (C i ω) (b2 i))} ∧
      (∀ i, pw i (θs i) ≤ 1 → P.real {ω | Hi (C i ω) (b2 i) < Lo (C i ω) (b1 i)} ≤ α i) ∧
      (∀ i ω, Hi (C i ω) (b2 i) < Lo (C i ω) (b1 i) → C i ω ∩ null i = ∅) ∧
      ∀ q : ℝ, (∀ i, pw i (θs i) = q) →
        P.real {ω | ¬ ∃ q' : ℝ, ∀ i, q' ∈ pw i '' C i ω} ≤ αt) ∧
    -- Part 3: discovery lists and labels.
    ((∀ q : ℝ, 0 < q → q < 1 →
        ∫ ω, fdp q (fun i => (E i ω).toReal) N₀ ∂P ≤ q * N₀.card / Fintype.card ι) ∧
      (∀ (q : ℝ) (Scr : Ω → Finset ι), 0 < q → q < 1 → (∀ i, MeasurableSet {ω | i ∈ Scr ω}) →
        (∀ ω, rej q (fun i => if i ∈ Scr ω then (E i ω).toReal else 0) ⊆ Scr ω) ∧
        ∫ ω, fdp q (fun i => if i ∈ Scr ω then (E i ω).toReal else 0) N₀ ∂P ≤
          q * N₀.card / Fintype.card ι) ∧
      ∀ i (T' : ℝ≥0), 0 < T' → (pw i (θs i) ≤ 1 → MartingaleOn T' (S i) (𝓕 i) P) ∧
        (1 < pw i (θs i) → IsStrictLocalMartingaleOn T' (S i) (𝓕 i) P)) ∧
    -- Part 4: absorbed samples.
    (∀ i ω, ((U i ω (Fin.last _) : ℝ) = 0 → (∀ l, (V i ω l : ℝ) = 0) →
        E i ω = 1 ∧ C i ω = Set.univ) ∧
      (0 < (U i ω (Fin.last _) : ℝ) → (∃ l, (V i ω l : ℝ) = 0) → E i ω ≤ 1) ∧
      (E i ω ≤ 1 → ¬ ENNReal.ofReal (1 / α i) < E i ω ∧
        ¬ Hi (C i ω) (b2 i) < Lo (C i ω) (b1 i) ∧
        ∀ (q : ℝ) (Scr : Ω → Finset ι), 0 < q → q < 1 →
          i ∉ rej q (fun j => (E j ω).toReal) ∧
          i ∉ rej q (fun j => if j ∈ Scr ω then (E j ω).toReal else 0)))

end Standalone.D13CEVCatalogue
