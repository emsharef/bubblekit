import Standalone.D17ClockDrift
import Standalone.D14FixedTick
import Standalone.D16GaussianPool
import Standalone.D17ClockCells

/-!
# Claim 035 (D17): training-selected CEV clock forecasts for exact and rounded prices

Statement only; the proof is `Novel/D17ClockForecastProof.lean`. Source claim:
`claims/035-d17-clock-aware-cev-forecast.md`.

**Structure.** `statement := exact ∧ labels ∧ cells ∧ evalMax ∧ panel`.
* `exact`: parts 1 and 3 on claim 033's design, under claim 033's inputs and null contract.
  - The forecast (1) and the training-only blend (2) are measurable, nonnegative and of mass one
    at every training record. The scores use claim 033's unchanged denominator `D^clock`.
  - Both scores are measurable and finite, with the conditional and unconditional moments, size and
    the reciprocal-p bound under claim 033's mixture premise.
  - Part 3: (5) and its floor, the log protection `≥ log λ`, and the exact boundary cases.
* `labels`: part 2's forecast on rounded labels.
  - The row masses (3) are positive, at most one and sum to one.
  - The label forecast (4) and any training-only blend with a normalized baseline are positive,
    normalized forecasts on all future label vectors.
* `cells`: part 2's scores and part 3 on claim 034's design, with its denominator
  `D_clock^(h,ℓ)` unchanged.
  - The pure CEV label forecast and its training-only blend with any normalized baseline satisfy
    all of claim 034's conclusions under its null contract and compact Gaussian null only. These
    are the domination, finiteness, the moments, strict size and lower scores, at finite
    evaluation-selected levels.
  - (5), its floor and the log protection on labels. On an all-zero suffix from a zero quote, the
    denominator is one and both scores are at most one.
* `panel`: claim 026's union bound and base e-BH under AX-53, at the original `m`.
* `evalMax`: the proof's example. Maximizing over normalized forecasts after seeing the outcome
  gives a score that is not an e-value: 21 point-mass forecasts on 21 equally likely outcomes give
  score 21 everywhere.

**Inputs.** AX-56's kernel facts (claim 054's `Kc`, through AX-55 and AX-56 on a base carrying a
Brownian motion), AX-58 (proved), and AX-53 for FDR only.

**Encodings.**
* A forecast catalogue `Ξ = Fin r`, ordered by index: powers `pf`, scales `κf`, training clock
  increments `vT` and evaluation clock increments `vE`.
* `Lex … a u` is (1)'s training likelihood: claim 054's chain from the known start `s`.
  `selEx` is its first maximizer (`firstMax`), and `qEx` is (1).
* `Pcell δ p κ v z z'` is (3): the `Kc` mass of cell `C_(z')` from the representative `r_δ(z)`
  (claim 031's `mrep`). `selCell` is the first maximizer of the training label likelihood, and
  `qCell` is (4).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Standalone.D17ClockForecast

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.D13DriftNull
  Standalone.SplitLikelihoodDominated Standalone.D17ClockDrift Standalone.D15JumpEnvelope
  Standalone.D16GaussianPool

/-- (1)'s training likelihood of forecast `a`, from the known start `s`. -/
noncomputable def Lex {k r : ℕ} (pf κf : Fin r → ℝ) (vT : Fin r → Fin (k + 1) → ℝ) (s : ℝ)
    (a : Fin r) (u : Fin (k + 1) → NNR) : ℝ :=
  chainN (Kc (pf a) (κf a)) (vT a) s u

/-- (1)'s training-selected forecast: the first likelihood maximizer. -/
noncomputable def selEx {k r : ℕ} [NeZero r] (pf κf : Fin r → ℝ) (vT : Fin r → Fin (k + 1) → ℝ)
    (s : ℝ) (u : Fin (k + 1) → NNR) : Fin r :=
  firstMax fun a => Lex pf κf vT s a u

/-- (1): the selected CEV clock forecast of the evaluation block. -/
noncomputable def qEx {k m r : ℕ} [NeZero r] (pf κf : Fin r → ℝ) (vT : Fin r → Fin (k + 1) → ℝ)
    (vE : Fin r → Fin m → ℝ) (s : ℝ) (u : Fin (k + 1) → NNR) (y : Fin m → NNR) : ℝ :=
  chainN (Kc (pf (selEx pf κf vT s u)) (κf (selEx pf κf vT s u))) (vE (selEx pf κf vT s u))
    (u (Fin.last k) : ℝ) y

/-- (3): the `Kc` mass of cell `C_(z')` from the representative of `z`. -/
noncomputable def Pcell (δ p κ v : ℝ) (z z' : ℕ) : ℝ :=
  (∫⁻ y in {y : NNR | (y : ℝ) ∈ Standalone.D14FixedTick.mcell δ z'},
    ENNReal.ofReal (Kc p κ v (Standalone.D14FixedTick.mrep δ z) y) ∂muCEV).toReal

/-- A product of label transitions along a path started at `z₀`. -/
noncomputable def chainCell {n : ℕ} (δ p κ : ℝ) (v : Fin n → ℝ) (z₀ : ℕ) (w : Fin n → ℕ) : ℝ :=
  ∏ j, Pcell δ p κ (v j) ((Fin.cons z₀ w : Fin (n + 1) → ℕ) j.castSucc) (w j)

/-- The training-selected label forecast: first maximizer of the training label likelihood. -/
noncomputable def selCell {k r : ℕ} [NeZero r] (δ : ℝ) (pf κf : Fin r → ℝ)
    (vT : Fin r → Fin k → ℝ) (u : Fin (k + 1) → ℕ) : Fin r :=
  firstMax fun a => chainCell δ (pf a) (κf a) (vT a) (u 0) (Fin.tail u)

/-- (4): the selected label forecast of the evaluation labels. -/
noncomputable def qCell {k n r : ℕ} [NeZero r] (δ : ℝ) (pf κf : Fin r → ℝ)
    (vT : Fin r → Fin k → ℝ) (vE : Fin r → Fin n → ℝ) (u : Fin (k + 1) → ℕ) (w : Fin n → ℕ) : ℝ :=
  chainCell δ (pf (selCell δ pf κf vT u)) (κf (selCell δ pf κf vT u)) (vE (selCell δ pf κf vT u))
    (u (Fin.last k)) w

open Classical in
/-- Parts 1 and 3 on claim 033's design. -/
def exact : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ) (𝒱 : Finset (Fin m → ℝ)) (r : ℕ) [NeZero r] (pf κf : Fin r → ℝ)
    (vT : Fin r → Fin (k + 1) → ℝ) (vE : Fin r → Fin m → ℝ)
    (lam : (Fin (k + 1) → NNR) → ℝ),
    let g := gC t pw κ
    let sel := selC hN.size t s pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    (∀ v ∈ 𝒱, ∀ j, 0 < v j) → Δe ∈ 𝒱 →
    (∀ a, 1 < pf a) → (∀ a, 0 < κf a) → (∀ a j, 0 < vT a j) → (∀ a j, 0 < vE a j) →
    Measurable lam → (∀ u, 0 < lam u ∧ lam u < 1) →
    let μm : Measure (Fin m → NNR) := Measure.pi fun _ : Fin m => muCEV
    let D := Dclock Δe 𝒱 pw g
    let qB := fun u y => g (sel u) u y
    let qC := qEx pf κf vT vE s
    let qM := fun u y => lam u * qB u y + (1 - lam u) * qC u y
    let EB := fun u y => Edrift (qB u y) (D u y)
    let EC := fun u y => Edrift (qC u y) (D u y)
    let EM := fun u y => Edrift (qM u y) (D u y)
    -- (1) and (2) are measurable normalized forecasts.
    (∀ q ∈ ({qC, qM} : Set ((Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ)),
      Measurable (Function.uncurry q) ∧ (∀ u y, 0 ≤ q u y) ∧
      ∀ u, ∫⁻ y, ENNReal.ofReal (q u y) ∂μm = 1) ∧
    -- Both scores are measurable, finite and valid under claim 033's null.
    (∀ E ∈ ({EC, EM} : Set ((Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ≥0∞)),
      Measurable (Function.uncurry E) ∧ (∀ u y, E u y < ⊤) ∧
      ∀ (ν : ProbabilityTheory.Kernel (Fin (k + 1) → NNR)
          ({ϑ : Fin c // pw ϑ ≤ 1} ⊕ (Clock 𝒱 × GPar))) [ProbabilityTheory.IsMarkovKernel ν]
        {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
        (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z =>
          μm.withDensity fun y => ENNReal.ofReal
            (Sum.elim (fun ϑ => g ϑ.1 u y)
              (fun p : Clock 𝒱 × GPar => gVN Δe p.1.1 p.2.1.1 p.2.1.2 u y) z)) →
        (∀ᵐ u ∂(P.map U), ∫⁻ y, E u y ∂(condDistrib V U P u) ≤ 1) ∧
        ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
        (∀ α : ℝ, 0 < α → α < 1 →
          P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
        ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a) ∧
    -- (5) and its floor, on every array; the log protection.
    (∀ u y, EM u y = ENNReal.ofReal (lam u) * EB u y + ENNReal.ofReal (1 - lam u) * EC u y ∧
      ENNReal.ofReal (lam u) * EB u y ≤ EM u y) ∧
    (∀ u y, 0 < EB u y →
      Real.log (lam u) ≤ Real.log ((EM u y).toReal / (EB u y).toReal)) ∧
    -- The exact boundary cases.
    (∀ u y, (u (Fin.last k) : ℝ) = 0 → (∀ l, (y l : ℝ) = 0) → EC u y = 1 ∧ EM u y = 1) ∧
    (∀ u y, 0 < (u (Fin.last k) : ℝ) → (∃ l, (y l : ℝ) = 0) →
      EC u y = 0 ∧ EM u y = ENNReal.ofReal (lam u) * EB u y ∧ EM u y ≤ 1) ∧
    (m = 1 → ∀ u y, EC u y ≤ 1 ∧ EM u y ≤ 1)

/-- Part 2's label forecast. -/
def labels : Prop :=
  -- (3): positive row masses, at most one, summing to one.
  (∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
    (∀ (δ p κ v : ℝ) (z : ℕ), 0 < δ → 1 < p → 0 < κ → 0 < v →
      (∀ z', 0 < Pcell δ p κ v z z' ∧ Pcell δ p κ v z z' ≤ 1) ∧
      HasSum (fun z' => Pcell δ p κ v z z') 1) ∧
    -- (4) is a positive normalized forecast on all evaluation label vectors, as is any
    -- training-only blend with a normalized baseline.
    ∀ (k n r : ℕ) [NeZero r] (δ : ℝ) (pf κf : Fin r → ℝ) (vT : Fin r → Fin k → ℝ)
      (vE : Fin r → Fin n → ℝ), 0 < δ → (∀ a, 1 < pf a) → (∀ a, 0 < κf a) →
      (∀ a j, 0 < vE a j) →
      ∀ u : Fin (k + 1) → ℕ,
        (∀ w, 0 < qCell δ pf κf vT vE u w) ∧ HasSum (qCell δ pf κf vT vE u) 1 ∧
        ∀ (lam : ℝ) (qb : (Fin n → ℕ) → ℝ), 0 < lam → lam < 1 → (∀ w, 0 ≤ qb w) →
          HasSum qb 1 → HasSum (fun w => lam * qb w + (1 - lam) * qCell δ pf κf vT vE u w) 1)

/-- Part 2's scores and part 3 on claim 034's design. -/
def cells : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (k n r : ℕ) [NeZero r] (δ : ℝ) (pf κf : Fin r → ℝ) (vT : Fin r → Fin k → ℝ)
    (vE : Fin r → Fin n → ℝ) (qb : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ)
    (lam : (Fin (k + 1) → ℕ) → ℝ) (Δ : Fin n → ℝ) (𝒱 : Finset (Fin n → ℝ))
    (ℬ : Standalone.D17ClockCells.Box),
    0 < δ → (∀ a, 1 < pf a) → (∀ a, 0 < κf a) → (∀ a j, 0 < vE a j) →
    (∀ u w, 0 ≤ qb u w) → (∀ u, ∑' w, ENNReal.ofReal (qb u w) = 1) →
    (∀ u, 0 < lam u ∧ lam u < 1) →
    (∀ j, 0 < Δ j) → 𝒱.Nonempty → (∀ vc ∈ 𝒱, ∀ j, 0 < vc j) → ℬ.Valid →
    let qC := qCell δ pf κf vT vE
    let qM := fun u w => lam u * qb u w + (1 - lam u) * qC u w
    let D := fun h ℓ (u : Fin (k + 1) → ℕ) w =>
      Standalone.D17ClockCells.Dclock δ ℬ h ℓ Δ 𝒱 (u (Fin.last k)) w
    -- Both scores satisfy claim 034's conclusions under its null contract.
    (∀ q ∈ ({qC, qM} : Set ((Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ)),
      (∀ u w, 0 ≤ q u w) ∧ (∀ u, ∑' w, ENNReal.ofReal (q u w) = 1) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (U : Ω → Fin (k + 1) → ℕ) (X₀ : Ω → ℝ) (Vc : Ω → Fin n → ℝ) (Bp : Ω → ℝ × ℝ)
        (R : Ω → Fin n → ℝ) (Hv Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ),
        Measurable U → Measurable X₀ → Measurable Vc → Measurable Bp → Measurable R →
        (∀ᵐ ω ∂P, X₀ ω ∈ Standalone.D14FixedTick.mcell δ (U ω (Fin.last k)) ∧ Vc ω ∈ 𝒱 ∧
          ℬ.Mem (Bp ω)) →
        (∀ᵐ w ∂(P.map fun ω => (U ω, X₀ ω, Vc ω, Bp ω)), 0 < w.2.1 →
          condDistrib R (fun ω => (U ω, X₀ ω, Vc ω, Bp ω)) P w =
            Measure.pi fun j => gaussianReal (w.2.2.2.1 * Δ j - w.2.2.2.2 * w.2.2.1 j / 2)
              (w.2.2.2.2 * w.2.2.1 j).toNNReal) →
        let Z := fun ω => Standalone.D14FixedTick.mlabels δ n (X₀ ω) (R ω)
        let E := fun u w => ENNReal.ofReal (q u w) / D (Hv u w) (Lv u w) u w
        (∀ h ℓ u w, 0 < D h ℓ u w ∧ D h ℓ u w ≤ 1) ∧ (∀ u w, E u w < ⊤) ∧
        (∀ᵐ u ∂(P.map U), ∀ w h ℓ, condDistrib Z U P u {w} ≤ D h ℓ u w) ∧
        (∀ᵐ u ∂(P.map U), ∫⁻ w, E u w ∂(condDistrib Z U P u) ≤ 1) ∧
        ∫⁻ ω, E (U ω) (Z ω) ∂P ≤ 1 ∧
        (∀ α : ℝ, 0 < α → α < 1 →
          P {ω | ENNReal.ofReal (1 / α) < E (U ω) (Z ω)} ≤ ENNReal.ofReal α) ∧
        ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (Z ω)) → ∫⁻ ω, F ω ∂P ≤ 1) ∧
    -- (5), its floor and the log protection, at every pair of levels.
    (∀ h ℓ u w,
      let EB := ENNReal.ofReal (qb u w) / D h ℓ u w
      let EC := ENNReal.ofReal (qC u w) / D h ℓ u w
      let EM := ENNReal.ofReal (qM u w) / D h ℓ u w
      EM = ENNReal.ofReal (lam u) * EB + ENNReal.ofReal (1 - lam u) * EC ∧
      ENNReal.ofReal (lam u) * EB ≤ EM ∧
      (0 < EB → Real.log (lam u) ≤ Real.log (EM.toReal / EB.toReal))) ∧
    -- An all-zero suffix from a zero quote: the denominator is one and both scores are at most one.
    ∀ h ℓ (u : Fin (k + 1) → ℕ), u (Fin.last k) = 0 →
      D h ℓ u (fun _ => 0) = 1 ∧ ENNReal.ofReal (qC u fun _ => 0) / D h ℓ u (fun _ => 0) ≤ 1 ∧
        ENNReal.ofReal (qM u fun _ => 0) / D h ℓ u (fun _ => 0) ≤ 1

/-- The proof's example: maximizing after seeing the outcome breaks the e-value property. On 21
equally likely outcomes, the pointwise maximum of the 21 point-mass forecasts is 21 everywhere,
while the uniform fixed mixture of them is 1 everywhere. -/
def evalMax : Prop :=
  let q : Fin 21 → Fin 21 → ℝ := fun i o => if o = i then 1 else 0
  let null : Fin 21 → ℝ := fun _ => 1 / 21
  (∀ i, ∑ o, q i o = 1) ∧ (∑ o, null o = 1) ∧
  (∀ o, (Finset.univ.sup' Finset.univ_nonempty fun i => q i o) / null o = 21) ∧
  (∀ o, (∑ i, q i o / 21) / null o = 1)

/-- Claim 035. -/
def statement : Prop :=
  exact ∧ labels ∧ cells ∧ evalMax ∧ Standalone.D14JumpRobustness.panel

end Standalone.D17ClockForecast
