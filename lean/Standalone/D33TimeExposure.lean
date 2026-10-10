import Standalone.D33ExposureSchedules
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Basic

/-!
# Claim 075 (D33): bounded time-varying exposure with an auxiliary-law energy bound

Statement only; the proof is `Novel/D33TimeExposureProof.lean`. Source claim:
`claims/075-d33-bounded-time-exposure.md`.

`statement := D33ExposureSchedules.statement ∧ part1 ∧ part2`. The deterministic parts (the energy
bounds, part 2's schedules and part 3) are `Standalone/D33ExposureSchedules.lean`.

**The canonical space.** `Canon Ω` is [ruf2015martingale]'s canonical space for `E = (0, ∞)`: a
coordinate `X`, a cemetery time `ζ` and a filtration. Every path is positive and continuous on
`[0, ζ)` (`pos`, `cont`), and `ζ` is a stopping time (`ζ_stop`). Values of `X` at and after `ζ` are
the cemetery and are never used: the coefficients are zero there. The statement holds for every such
space, the source's own included.

**AX-64, restated** (`AX64`). It is model-indexed: for a probability `Q`, covariance `a`, exponential
integrand `μ_R`, closed exhaustion `E_n` and exponential `Z`, the fields are:
* Definition 2.1's exhaustion conditions for `Q` and Assumption 2.3 (`noJump`);
* the source's construction facts: `τ_n` are stopping times, and `Z` is a nonnegative local
  martingale;
* Proposition 3.1: some auxiliary law `Q_aux` with `IsSol Q_aux` (the shifted problem) and the
  stopped-density identities `Q_aux(B) = ∫_B (Z stopped at τ_n)_∞ dQ` for `B` in the stopped σ-field
  at `τ_n`;
* Theorem 3.3's two equivalences for every such `Q_aux`, with Mathlib's `Martingale` and
  `UniformIntegrable`.

The energies `A_t = ∫₀^(t∧θ) μ_R a μ_R` and `A_∞` are extended nonnegative, and `θ`, `θ_n`, `τ̃_n`, `τ_n`
and `ρ_{E_n}` are defined exactly as in the source §2.2. Two primitives are not defined here: the
stochastic exponential `Z` is a field, and so is the shifted generalized martingale problem `IsSol`,
because Mathlib has no stochastic integral. The claim's proof uses `IsSol` only as the class of
auxiliary laws. The statement holds for every class for which the fields hold, so in particular for
the source's. `Novel/D33TimeExposureBridge.lean` derives `AX64` from AX-64's Upstream structure
`Upstream.AuxiliaryLawCriterion` (`ax64_of_upstream`). The restatement is satisfiable:
`Novel/D33TimeExposureModel.lean` builds the ledger's degenerate instance, a constant path with zero
exposure.

**The model.** Zero drift, covariance `a = σ(X)²` and integrand `μ_R = π/X`, both zero at and after
`ζ` (`aR`, `μR`). `σ` satisfies claim 001's assumption 1 (`VolHyp`), and `|π| ≤ M` everywhere. The
wealth is `V = v₀ Z`. `edens` is the energy density `μ_R a μ_R`. Part 1 checks the substitution (4):
it equals `π² σ(x)²/x²` before `ζ`.

**Part 1.** If `h_exp ≥ 0` is Borel, integrable on every `[0, t]`, and (1) holds for every path and
a.e. `s < θ`, then `V` is a `Q`-martingale. If also `∫₀^∞ h_exp < ∞`, `V` is a uniformly
integrable `Q`-martingale.

**Part 2.** `σ(x) = κx` with `κ > 0`, and `E_n = [1/(n+1), n+1]`.
* **AX-55 enters as `Q(ζ < ∞) = 0`.** The original law has no finite exit. This is all the proof
  uses of the geometric law, so the statement covers any `Q` with that property.
* **Conclusions.**
  - The exhaustion is admissible, and Assumption 2.3 holds on every path.
  - `θ = ζ` on every path.
  - Every auxiliary law satisfying Proposition 3.1 has `Q_aux(ζ < ∞) = 0`.
  - `V` is a martingale.
  - (2): `V` is uniformly integrable iff `Q_aux(∫₀^∞ π² < ∞) = 1`.
  - (3): for a deterministic schedule `π = p`, `V` is uniformly integrable iff `∫₀^∞ p² < ∞`.
  - The examples `e^(−t)`, `1` and `(1 + t)^(−γ)`.

Time is `ℝ≥0`. Integrals in time are over `(0, ∞) ⊂ ℝ`, with the integrand evaluated at
`s.toNNReal`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Standalone.D33TimeExposure

open Standalone.D1TwoEndpoint Standalone.D33ExposureSchedules

/-! ## The canonical space -/

/-- [ruf2015martingale]'s canonical space for `E = (0, ∞)`: coordinate `X`, cemetery time `ζ` and
the filtration `𝓕` (the right-continuous natural filtration). -/
structure Canon (Ω : Type) [mΩ : MeasurableSpace Ω] where
  𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ
  X : ℝ≥0 → Ω → ℝ
  ζ : Ω → ℝ≥0∞
  pos : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < ζ ω → 0 < X t ω
  cont : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < ζ ω → ContinuousOn (fun s => X s ω) (Iic t)
  ζ_stop : ∀ T : ℝ≥0, MeasurableSet[𝓕 T] {ω | ζ ω ≤ T}

variable {Ω : Type} [MeasurableSpace Ω]

/-- `ρ_F = inf{t ≥ 0 : X_t ∉ F}`, the cemetery lying outside `F`. -/
noncomputable def rho (C : Canon Ω) (F : Set ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : C.ζ ω ≤ s ∨ C.X s ω ∉ F), (s : ℝ≥0∞)

/-- `∫₀^(t∧η) e(s) ds`, in `[0, ∞]`. -/
noncomputable def energyUpTo (e : ℝ≥0 → Ω → ℝ≥0∞) (η : Ω → ℝ≥0∞) (t : ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Ioi (0 : ℝ),
    if (s.toNNReal : ℝ≥0∞) < t ∧ (s.toNNReal : ℝ≥0∞) < η ω then e s.toNNReal ω else 0

/-- `inf{t ≥ 0 : f(t) > n}`. -/
noncomputable def hit (f : ℝ≥0 → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : (n : ℝ≥0∞) < f t), (t : ℝ≥0∞)

/-- The energy density `μ_R a μ_R`, zero at and after `ζ`. -/
noncomputable def edens (C : Canon Ω) (a μ : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  if (s : ℝ≥0∞) < C.ζ ω then ENNReal.ofReal (μ s ω * a s ω * μ s ω) else 0

section Localization

variable (C : Canon Ω) (a μ : ℝ≥0 → Ω → ℝ) (E : ℕ → Set ℝ)

/-- The unlocalized energy `∫₀^(t∧ζ) μ_R a μ_R`. -/
noncomputable def Atil (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ := energyUpTo (edens C a μ) (fun _ => ⊤) t ω

/-- `θ_n = τ̃_n ∧ ρ_(E_n) ∧ n`. -/
noncomputable def thetaN (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  min (min (hit (fun t => Atil C a μ t ω) n) (rho C (E n) ω)) n

/-- `θ = lim θ_n`. -/
noncomputable def theta (ω : Ω) : ℝ≥0∞ := ⨆ n, thetaN C a μ E n ω

/-- The localized energy `A_t = ∫₀^(t∧θ) μ_R a μ_R`; `t = ∞` gives `A_∞`. -/
noncomputable def Aloc (t : ℝ≥0∞) (ω : Ω) : ℝ≥0∞ := energyUpTo (edens C a μ) (theta C a μ E) t ω

/-- `τ_n = inf{t ≥ 0 : A_t > n}`. -/
noncomputable def tau (n : ℕ) (ω : Ω) : ℝ≥0∞ := hit (fun t => Aloc C a μ E t ω) n

end Localization

/-- `(Z stopped at τ)_∞`. -/
noncomputable def Zterm (Z : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞) (ω : Ω) : ℝ :=
  if τ ω = ⊤ then Filter.limUnder Filter.atTop (fun t => Z t ω) else Z (τ ω).toNNReal ω

/-- `B` lies in the stopped σ-field at `τ`. -/
def InStopped (𝓕 : MeasureTheory.Filtration ℝ≥0 ‹MeasurableSpace Ω›) (τ : Ω → ℝ≥0∞) (B : Set Ω) :
    Prop :=
  MeasurableSet B ∧ ∀ t : ℝ≥0, MeasurableSet[𝓕 t] (B ∩ {ω | τ ω ≤ t})

/-- `f` jumps to `∞`: it is infinite at some time and bounded before it. -/
def JumpsToTop (f : ℝ≥0 → ℝ≥0∞) : Prop := ∃ t, f t = ⊤ ∧ ∃ c : ℝ≥0, ∀ s < t, f s ≤ c

/-- Proposition 3.1's stopped-density identities, for `n ≥ 1`. -/
def DensityId (C : Canon Ω) (a μ : ℝ≥0 → Ω → ℝ) (E : ℕ → Set ℝ) (Q : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ) (Qa : Measure Ω) : Prop :=
  ∀ (n : ℕ) (B : Set Ω), InStopped C.𝓕 (tau C a μ E (n + 1)) B →
    Qa B = ∫⁻ ω in B, ENNReal.ofReal (Zterm Z (tau C a μ E (n + 1)) ω) ∂Q

/-- AX-64 ([ruf2015martingale] Proposition 3.1 and Theorem 3.3), restated for one model. -/
structure AX64 (C : Canon Ω) (Q : Measure Ω) (a μ : ℝ≥0 → Ω → ℝ) (E : ℕ → Set ℝ)
    (Z : ℝ≥0 → Ω → ℝ) where
  prob : IsProbabilityMeasure Q
  E_closed : ∀ n, IsClosed (E n)
  E_mono : Monotone E
  E_cover : ⋃ n, E n = Ioi 0
  E_noexit : ∀ n, Q {ω | rho C (E n) ω = C.ζ ω ∧ C.ζ ω < ⊤} = 0
  /-- Assumption 2.3. -/
  noJump : ∀ᵐ ω ∂Q, ¬ JumpsToTop fun t => Atil C a μ t ω
  tau_stop : ∀ (n : ℕ) (t : ℝ≥0), MeasurableSet[C.𝓕 t] {ω | tau C a μ E n ω ≤ t}
  Z_nonneg : ∀ᵐ ω ∂Q, ∀ t, 0 ≤ Z t ω
  Z_local : IsLocalMartingale Z C.𝓕 Q
  /-- Definition 2.1's generalized local martingale problem for `(E, x₀, a, b + aμ_R)` on
  `[[0, θ[[`. -/
  IsSol : Measure Ω → Prop
  /-- Proposition 3.1. -/
  exists_aux : ∃ Qa, IsSol Qa ∧ IsProbabilityMeasure Qa ∧ DensityId C a μ E Q Z Qa
  /-- Theorem 3.3, (3.1). -/
  mart_iff : ∀ Qa, IsSol Qa → IsProbabilityMeasure Qa → DensityId C a μ E Q Z Qa →
    (Martingale Z C.𝓕 Q ↔ ∀ t : ℝ≥0, Qa {ω | Aloc C a μ E t ω < ⊤} = 1)
  /-- Theorem 3.3, (3.2). -/
  ui_iff : ∀ Qa, IsSol Qa → IsProbabilityMeasure Qa → DensityId C a μ E Q Z Qa →
    (Martingale Z C.𝓕 Q ∧ UniformIntegrable Z 1 Q ↔ Qa {ω | Aloc C a μ E ⊤ ω < ⊤} = 1)

/-! ## The model -/

/-- `a = σ(X)²` before `ζ`, zero afterward. -/
noncomputable def aR (C : Canon Ω) (σ : ℝ → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  if (s : ℝ≥0∞) < C.ζ ω then σ (C.X s ω) ^ 2 else 0

/-- `μ_R = π/X` before `ζ`, zero afterward. -/
noncomputable def μR (C : Canon Ω) (π : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  if (s : ℝ≥0∞) < C.ζ ω then π s ω / C.X s ω else 0

/-- `E_n = [1/(n+1), n+1]`. -/
def Egeo (n : ℕ) : Set ℝ := Icc (1 / (n + 1)) (n + 1)

/-- A uniformly integrable martingale. -/
def UIMart (C : Canon Ω) (V : ℝ≥0 → Ω → ℝ) (Q : Measure Ω) : Prop :=
  Martingale V C.𝓕 Q ∧ UniformIntegrable V 1 Q

/-- Part 1. -/
def part1 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (C : Canon Ω) (Q : Measure Ω) (σ : ℝ → ℝ)
    (π : ℝ≥0 → Ω → ℝ) (M v₀ : ℝ) (E : ℕ → Set ℝ) (Z : ℝ≥0 → Ω → ℝ),
    AX64 C Q (aR C σ) (μR C π) E Z → VolHyp σ → (∀ (s : ℝ≥0) ω, |π s ω| ≤ M) → 0 < v₀ →
    -- (4).
    (∀ (s : ℝ≥0) ω, (s : ℝ≥0∞) < C.ζ ω → edens C (aR C σ) (μR C π) s ω =
      ENNReal.ofReal (π s ω ^ 2 * σ (C.X s ω) ^ 2 / C.X s ω ^ 2)) ∧
    ∀ h : ℝ → ℝ, Measurable h → (∀ s, 0 ≤ h s) → (∀ t : ℝ, IntegrableOn h (Icc 0 t)) →
      -- (1).
      (∀ ω, ∀ᵐ s : ℝ, 0 < s → (s.toNNReal : ℝ≥0∞) < theta C (aR C σ) (μR C π) E ω →
        edens C (aR C σ) (μR C π) s.toNNReal ω ≤ ENNReal.ofReal (h s)) →
      Martingale (fun t ω => v₀ * Z t ω) C.𝓕 Q ∧
        (IntegrableOn h (Ioi 0) → UIMart C (fun t ω => v₀ * Z t ω) Q)

/-- Part 2. -/
def part2 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (C : Canon Ω) (Q : Measure Ω) (κ : ℝ) (π : ℝ≥0 → Ω → ℝ)
    (M v₀ : ℝ) (Z : ℝ≥0 → Ω → ℝ) (S : AX64 C Q (aR C fun x => κ * x) (μR C π) Egeo Z),
    0 < κ → (∀ (s : ℝ≥0) ω, |π s ω| ≤ M) → 0 < v₀ →
    -- AX-55: the original geometric law has no finite exit.
    Q {ω | C.ζ ω < ⊤} = 0 →
    -- The exhaustion is admissible, and Assumption 2.3 holds on every path.
    ((∀ n, IsClosed (Egeo n)) ∧ Monotone Egeo ∧ ⋃ n, Egeo n = Ioi 0 ∧
      (∀ n, Q {ω | rho C (Egeo n) ω = C.ζ ω ∧ C.ζ ω < ⊤} = 0) ∧
      ∀ ω, ¬ JumpsToTop fun t => Atil C (aR C fun x => κ * x) (μR C π) t ω) ∧
    -- `θ = ζ` on every path.
    (∀ ω, theta C (aR C fun x => κ * x) (μR C π) Egeo ω = C.ζ ω) ∧
    -- Auxiliary nonexit, for every auxiliary law of Proposition 3.1.
    (∀ Qa, S.IsSol Qa → IsProbabilityMeasure Qa →
      DensityId C (aR C fun x => κ * x) (μR C π) Egeo Q Z Qa → Qa {ω | C.ζ ω < ⊤} = 0) ∧
    -- Finite-horizon martingality.
    Martingale (fun t ω => v₀ * Z t ω) C.𝓕 Q ∧
    -- (2).
    (∀ Qa, S.IsSol Qa → IsProbabilityMeasure Qa →
      DensityId C (aR C fun x => κ * x) (μR C π) Egeo Q Z Qa →
      (UIMart C (fun t ω => v₀ * Z t ω) Q ↔
        Qa {ω | ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (π s.toNNReal ω ^ 2) < ⊤} = 1)) ∧
    -- (3), for a deterministic schedule `p`.
    (∀ p : ℝ → ℝ, (∀ (s : ℝ≥0) ω, π s ω = p s) →
      (UIMart C (fun t ω => v₀ * Z t ω) Q ↔ energy p < ⊤)) ∧
    -- The examples.
    ((∀ (s : ℝ≥0) ω, π s ω = Real.exp (-(s : ℝ))) → UIMart C (fun t ω => v₀ * Z t ω) Q) ∧
    ((∀ (s : ℝ≥0) ω, π s ω = 1) → ¬ UIMart C (fun t ω => v₀ * Z t ω) Q) ∧
    ∀ γ : ℝ, 0 ≤ γ → (∀ (s : ℝ≥0) ω, π s ω = powSched γ s) →
      (UIMart C (fun t ω => v₀ * Z t ω) Q ↔ 1 / 2 < γ)

/-- Claim 075. -/
def statement : Prop := Standalone.D33ExposureSchedules.statement ∧ part1 ∧ part2

end Standalone.D33TimeExposure
