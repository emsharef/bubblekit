import Standalone.D15Switch
import Standalone.D14JumpRobustness

/-!
# Claim 060 (D15): a calibrated Poisson-jump envelope with a declared diffusion-scale floor

Statement only; the proof is `Novel/D15JumpEnvelopeProof.lean`. Source claim:
`claims/060-d15-jump-envelope.md`.

**Structure.** `statement := envelope ∧ truncation ∧ score ∧ panel`.
* `envelope`: part 1's domination `g_J ≤ U_J` for every `θ ∈ Θ_J`, finiteness, positivity and
  measurability of (4), and part 3's orderings of (4) in the cap and the floor, at cap `0` and `∞`,
  and off the positive stratum. Also the nonzero example's positive residual.
* `truncation`: part 4's bound (7) for one increment.
* `score`: the score (5) on claim 054's design.
  - Part 1: domination of every jump density by the denominator; measurability and finiteness of
    the score. An infinite denominator forces `D_G = ∞`, and those arrays are `μ_CEV^m`-null.
  - Part 2: inference under the mixture premise (3).
  - Part 3: the ordering against claim 055's score, monotonicity in the cap and the floor, the cap
    `0` and cap `∞` forms, positivity on the nonzero example, and agreement with claim 055's score
    off the positive stratum (absorbed arrays).
* `panel`: claim 026's union bound and e-BH under AX-53 (lower scores and masks at the original
  `m`), and claim 055's fact that e-BH never selects a score `≤ 1`.

**Inputs.**
* AX-58 is proved from Mathlib and enters through its pointwise step.
* AX-53 is used for FDR only.
* AX-55 and AX-56 supply claim 054's kernels on a base carrying a Brownian motion, as in claims
  055 and 059.
* **AX-59 is not used by any proof here.** The jump law (2) enters only through the mixture premise
  (3), which supplies the actual conditional law. The proofs never use its normalization or its
  link to a jump process, so no AX-59 hypothesis structure is needed.

**Encodings** (on `n` evaluation prices `y` after the last training price `y0`, steps `Δ_j > 0`).
* `θ = (a_J, σ_J, λ_J, μ_J, η_J) ∈ ℝ⁵`. `ThetaJ σmin Λ θ` is (1): `σ_J ≥ σmin`, `0 ≤ λ_J`,
  `λ_J ≤ Λ` (as `ofReal λ_J ≤ Λ` with `Λ ∈ [0, ∞]`), and `η_J > 0`. `a_J` and `μ_J` are free.
* `wP t k = e^{−t} t^k / k!`, the Poisson weight. Lean's `0^0 = 1` gives `w_0(0) = 1`.
* `hJ` is (2): the real series `Σ_k w_k(λ_J Δ) φ(r; a_J Δ + k μ_J, σ_J² Δ + k η_J²)`, with `φ` Mathlib's
  `gaussianPDFReal`. `hJK K` is its truncation at `k ≤ K`.
* `gJ` is the price density: on positive paths `∏_j hJ(R_j; Δ_j)/y_j`. Off them it is claim 055's
  extension: `1` on the trapped all-zero suffix from `0`, and `0` otherwise.
* `MJ`, `ρJ` and `UJ` are (4). `ρJ ⊤ = 1`. Off the positive stratum `UJ` is `1` on the trapped
  suffix and `0` otherwise, with no price reciprocal evaluated.
* The denominator of (5) is `max(Dmax, U_J)`, where claim 055's `Dmax` is `max(G₀, D_G)`. The score is
  AX-58's `Edrift`: `0` if `Ĝ = 0` or the denominator is `∞`, and `Ĝ/D` otherwise.
* **The mixture premise (3).** The latent space is the disjoint union of the catalogue nulls, the
  constant Gaussian parameters `ℝ × (0, ∞)`, and `Θ_J`, the last two as subtypes. The component law
  of a latent value is its density times `μ_CEV^m`. The premise is that the actual conditional law
  is the `ν(u, ·)` mixture, for `P∘U⁻¹`-a.e. `u`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Standalone.D15JumpEnvelope

open Standalone.D13DriftNull

variable {n : ℕ}

/-- The Poisson weight `w_k(t) = e^{−t} t^k / k!`. -/
noncomputable def wP (t : ℝ) (k : ℕ) : ℝ := Real.exp (-t) * t ^ k / k.factorial

/-- (2): the one-increment return density of the jump law. -/
noncomputable def hJ (a σ lam μJ η Δ r : ℝ) : ℝ :=
  ∑' k : ℕ, wP (lam * Δ) k *
    gaussianPDFReal (a * Δ + k * μJ) (σ ^ 2 * Δ + k * η ^ 2).toNNReal r

/-- (2) truncated at `k ≤ K`. -/
noncomputable def hJK (K : ℕ) (a σ lam μJ η Δ r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), wP (lam * Δ) k *
    gaussianPDFReal (a * Δ + k * μJ) (σ ^ 2 * Δ + k * η ^ 2).toNNReal r

/-- The jump price density `g_J` for `θ = (a_J, σ_J, λ_J, μ_J, η_J)`, with the trapped extension. -/
noncomputable def gJ (Δ : Fin n → ℝ) (θ : ℝ × ℝ × ℝ × ℝ × ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  open Classical in
  if PosPath y0 y then
    ∏ j, hJ θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2 (Δ j) (ret y0 y j) / y j
  else if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0

/-- (1): the jump family `Θ_J` with floor `σmin` and intensity cap `Λ ∈ [0, ∞]`. -/
def ThetaJ (σmin : ℝ) (Λ : ℝ≥0∞) (θ : ℝ × ℝ × ℝ × ℝ × ℝ) : Prop :=
  σmin ≤ θ.2.1 ∧ 0 ≤ θ.2.2.1 ∧ ENNReal.ofReal θ.2.2.1 ≤ Λ ∧ 0 < θ.2.2.2.2

/-- (4): the per-step density ceiling `M_J`. -/
noncomputable def MJ (σmin : ℝ) (Δ : Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∏ j, 1 / (y j * σmin * Real.sqrt (2 * π * Δ j))

/-- (4): `ρ_J = 1 − exp(−Λ τ_e)`, and `1` at `Λ = ∞`. -/
noncomputable def ρJ (Λ : ℝ≥0∞) (τ : ℝ) : ℝ :=
  open Classical in
  if Λ = ⊤ then 1 else 1 - Real.exp (-(Λ.toReal * τ))

/-- (4): the envelope `U_J`, with the direct zero/trapped values off the positive stratum. -/
noncomputable def UJ (σmin : ℝ) (Λ : ℝ≥0∞) (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  open Classical in
  if PosPath y0 y then
    ENNReal.ofReal (1 - ρJ Λ (∑ j, Δ j)) * min (DG Δ y0 y) (ENNReal.ofReal (MJ σmin Δ y)) +
      ENNReal.ofReal (ρJ Λ (∑ j, Δ j)) * ENNReal.ofReal (MJ σmin Δ y)
  else if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0

/-- Parts 1 and 3 for the envelope (4). -/
def envelope : Prop :=
  ∀ (n : ℕ) (Δ : Fin n → ℝ) (σmin : ℝ) (Λ : ℝ≥0∞), 0 < n → (∀ j, 0 < Δ j) → 0 < σmin →
    -- Part 1: every jump law in `Θ_J` is dominated by `U_J`, on every array.
    (∀ θ, ThetaJ σmin Λ θ → ∀ y0 y, 0 ≤ gJ Δ θ y0 y ∧
      ENNReal.ofReal (gJ Δ θ y0 y) ≤ UJ σmin Λ Δ y0 y) ∧
    -- `U_J` is finite and measurable everywhere, and strictly positive on the positive stratum.
    (∀ y0 y, UJ σmin Λ Δ y0 y < ⊤) ∧
    Measurable (fun x : ℝ × (Fin n → ℝ) => UJ σmin Λ Δ x.1 x.2) ∧
    (∀ y0 y, PosPath y0 y → 0 < UJ σmin Λ Δ y0 y) ∧
    -- Part 3: raising the cap or lowering the floor raises `U_J`.
    (∀ Λ' : ℝ≥0∞, Λ ≤ Λ' → ∀ y0 y, UJ σmin Λ Δ y0 y ≤ UJ σmin Λ' Δ y0 y) ∧
    (∀ σ' : ℝ, 0 < σ' → σ' ≤ σmin → ∀ y0 y, UJ σmin Λ Δ y0 y ≤ UJ σ' Λ Δ y0 y) ∧
    -- Cap zero: `U_J ≤ D_G`. Cap infinity: `U_J = M_J` on positive prices.
    (Λ = 0 → ∀ y0 y, UJ σmin Λ Δ y0 y ≤ DG Δ y0 y) ∧
    (Λ = ⊤ → ∀ y0 y, PosPath y0 y → UJ σmin Λ Δ y0 y = ENNReal.ofReal (MJ σmin Δ y)) ∧
    -- Off the positive stratum `U_J` agrees with `D_G`'s zero/trapped values.
    (∀ y0 y, ¬ PosPath y0 y → UJ σmin Λ Δ y0 y = DG Δ y0 y) ∧
    -- The nonzero example: returns `R_j = (j + 1) Δ_j` have positive residual when `n ≥ 2`.
    (2 ≤ n → ∀ y0 y, PosPath y0 y → (∀ j : Fin n, ret y0 y j = ((j : ℕ) + 1) * Δ j) →
      0 < QG Δ y0 y)

/-- Part 4, (7): the truncation bounds for one increment. -/
def truncation : Prop :=
  ∀ (a σ lam μJ η Δ σmin r : ℝ) (K : ℕ), 0 < Δ → 0 < σmin → σmin ≤ σ → 0 ≤ lam → 0 < η →
    0 ≤ hJK K a σ lam μJ η Δ r ∧ hJK K a σ lam μJ η Δ r ≤ hJ a σ lam μJ η Δ r ∧
    hJ a σ lam μJ η Δ r ≤ hJK K a σ lam μJ η Δ r +
      1 / (σmin * Real.sqrt (2 * π * Δ)) * (1 - ∑ k ∈ Finset.range (K + 1), wP (lam * Δ) k)

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated
  Standalone.D3CatalogueCalibration

/-- The constant Gaussian parameters `(b, κ)` with `κ > 0`. -/
def GPar : Type := {p : ℝ × ℝ // 0 < p.2}

instance : MeasurableSpace GPar := Subtype.instMeasurableSpace

/-- The jump parameters `Θ_J`. -/
def JPar (σmin : ℝ) (Λ : ℝ≥0∞) : Type := {θ : ℝ × ℝ × ℝ × ℝ × ℝ // ThetaJ σmin Λ θ}

instance (σmin : ℝ) (Λ : ℝ≥0∞) : MeasurableSpace (JPar σmin Λ) := Subtype.instMeasurableSpace

open Classical in
/-- Claim 060 on claim 054's design: the score (5) and parts 1–3 for one name. -/
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
    let μm : Measure (Fin m → NNR) := Measure.pi fun _ : Fin m => muCEV
    let gJN := fun (θ : ℝ × ℝ × ℝ × ℝ × ℝ) (u : Fin (k + 1) → NNR) (v : Fin m → NNR) =>
      gJ Δe θ (u (Fin.last k) : ℝ) fun l => (v l : ℝ)
    let DJ := fun (σ' : ℝ) (Λ' : ℝ≥0∞) (u : Fin (k + 1) → NNR) (v : Fin m → NNR) =>
      max (Dmax Δe pw g u v) (UJ σ' Λ' Δe (u (Fin.last k) : ℝ) fun l => (v l : ℝ))
    let EJ := fun (σ' : ℝ) (Λ' : ℝ≥0∞) u v => Edrift (g (sel u) u v) (DJ σ' Λ' u v)
    let ED := fun u v => Edrift (g (sel u) u v) (Dmax Δe pw g u v)
    let E := EJ σmin Λ
    -- Part 1: the denominator dominates every jump law in `Θ_J`.
    (∀ θ, ThetaJ σmin Λ θ → ∀ u v, ENNReal.ofReal (gJN θ u v) ≤ DJ σmin Λ u v) ∧
    -- The score is measurable and finite; only `D_G` can make the denominator infinite, and
    -- those arrays are `μ_CEV^m`-null.
    Measurable (Function.uncurry E) ∧ (∀ u v, E u v < ⊤) ∧
    (∀ u v, DJ σmin Λ u v = ⊤ → DG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) = ⊤) ∧
    (∀ u, μm {v | DJ σmin Λ u v = ⊤} = 0) ∧
    -- Part 2, under the mixture premise (3).
    (∀ (ν : ProbabilityTheory.Kernel (Fin (k + 1) → NNR)
        ({ϑ : Fin c // pw ϑ ≤ 1} ⊕ (GPar ⊕ JPar σmin Λ))) [ProbabilityTheory.IsMarkovKernel ν]
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z =>
        μm.withDensity fun v => ENNReal.ofReal
          (Sum.elim (fun ϑ => g ϑ.1 u v)
            (Sum.elim (fun p : GPar => gGN Δe p.1.1 p.1.2 u v)
              (fun θ : JPar σmin Λ => gJN θ.1 u v)) z)) →
      P {ω | DJ σmin Λ (U ω) (V ω) = ⊤} = 0 ∧
      (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a) ∧
    -- Part 3: `E^J ≤ E^drift ≤ E`.
    (∀ u v, E u v ≤ ED u v ∧ ED u v ≤ Ecomp pw (fun ϑ => g ϑ u v) (sel u)) ∧
    -- Raising the cap, or lowering the floor, weakly decreases the score.
    (∀ Λ' : ℝ≥0∞, Λ ≤ Λ' → ∀ u v, EJ σmin Λ' u v ≤ E u v) ∧
    (∀ σ' : ℝ, 0 < σ' → σ' ≤ σmin → ∀ u v, EJ σ' Λ u v ≤ E u v) ∧
    -- Cap zero recovers claim 055's score; cap infinity uses the ceiling `M_J`.
    (Λ = 0 → ∀ u v, E u v = ED u v) ∧
    (Λ = ⊤ → ∀ u v, PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) →
      E u v = Edrift (g (sel u) u v)
        (max (Dmax Δe pw g u v) (ENNReal.ofReal (MJ σmin Δe fun l => (v l : ℝ))))) ∧
    -- The nonzero example: positive residual and positive numerator give a positive score.
    (∀ u v, PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) →
      0 < QG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) → 0 < g (sel u) u v → 0 < E u v) ∧
    -- Off the positive stratum (absorbed arrays) the score is claim 055's.
    (∀ u v, ¬ PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) → E u v = ED u v)

/-- The panel: claim 026's union bound and e-BH (lower scores, masks), and e-BH never selects a
score `≤ 1`. -/
def panel : Prop :=
  Standalone.D14JumpRobustness.panel ∧
  ∀ {ι : Type} [Fintype ι] (q : ℝ) (x : ι → ℝ), 0 < q → q < 1 →
    ∀ i ∈ Standalone.D12CatalogueFDR.rej q x, 1 < x i

/-- Claim 060. -/
def statement : Prop := envelope ∧ truncation ∧ score ∧ panel

end Standalone.D15JumpEnvelope
