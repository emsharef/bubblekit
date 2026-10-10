import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.LocalProperty

/-!
# Claim 001 (D1): conditional two-endpoint criterion for constant-proportion wealth

Statement only; the proof is `Novel/D1TwoEndpointProof.lean`. Source claim:
`claims/001-d1-two-endpoint-criterion.md`.

`S` solves `dS = σ(S) dW` on `(0, ∞)`, absorbed at `0`. The exposure is `π > 0`, the integrand is
`bπ(x) = πσ(x)/x`, `Zπ` is its stochastic exponential, and the wealth is `Vπ = v₀ Zπ` (the
representation (W) of the claim).

Mathlib cannot express a weak solution or a stochastic exponential, and statements here may import
Mathlib only. So the statement has four parts:

* **(A) Deterministic core, unconditional.** For every `σ` satisfying assumption 1, every `π > 0` and
  every reference point `c > 0`: the martingale condition of [mijatovic2010martingale] Theorem 2.1
  (ledger AX-01) for drift `0`, volatility `σ` and integrand `bπ` holds iff **not**
  `(0 < π < 1/2 and I₀ < ∞) or (π > 1/2 and I∞ < ∞)`. The condition is written out below with the
  source's own functions: `ρ`, `s` and `v` in its normalization, `ṽ` for the auxiliary drift `bπσ`,
  and goodness (24)/(26) with the original scale.
* **(B) Classification, conditional on AX-01 at this instance.** On a probability space, let `Z` be any process that is a
  nonnegative continuous local martingale and that, on every `[0, T]` with `T > 0`, is a martingale
  exactly when the condition in (A) holds. That is what AX-01 asserts of `Zπ`. Then `v₀ Z` is a
  nonnegative continuous local martingale, and for every `T > 0` it is a strict local martingale on
  `[0, T]` iff `(0 < π < 1/2 and I₀ < ∞) or (π > 1/2 and I∞ < ∞)`. Equivalently, it is a martingale
  on `[0, T]` iff not. This is (1) and the table of the claim.
* **(C) The counterexample's numbers.** For `σ ≡ 1` and `π = 1/4`, the strict case holds
  (`I₀ = ∫_0^1 x dx = 1/2 < ∞`) and `I∞ = ∞`.
* **(D) Scope of the correction.** If `I₀ = ∞`, the right-hand side of (1) is the charter's
  `π > 1/2 and I∞ < ∞`. If `I₀ < ∞` and `0 < π < 1/2`, it holds while the charter's conjunction
  fails.

That AX-01 does supply the premise of (B) for `Zπ`, and that AX-03 classifies `S`, is proved from
the hypothesis structures `Upstream.MartingaleCriterion` and `Upstream.DriftlessIntegralCriterion`
in `Novel/D1TwoEndpointProof.lean` (`wealth_classification`). Those structures have only vacuous
instances; every stochastic conclusion is conditional on them and on (W).

`I₀ < ∞` is `∫_0^x y/σ²(y) dy < ∞` for some `x > 0`, and `I∞ < ∞` is `∫_x^∞ y/σ²(y) dy < ∞` for some
`x > 0` (as integrability); the cutoff does not matter.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace Standalone.D1TwoEndpoint

universe u

/-! ## Coefficients and the deterministic functions of [mijatovic2010martingale] -/

/-- Assumption 1: `σ` Borel, `σ(x) ≠ 0` for `x > 0`, and `1/σ²` integrable on every compact
subinterval of `(0, ∞)`. -/
structure VolHyp (σ : ℝ → ℝ) : Prop where
  measurable : Measurable σ
  ne_zero : ∀ x, 0 < x → σ x ≠ 0
  locInt : ∀ a b, 0 < a → 0 < b → IntegrableOn (fun x => 1 / σ x ^ 2) (Icc a b)

/-- `bπ(x) = π σ(x) / x`. -/
noncomputable def bPi (π : ℝ) (σ : ℝ → ℝ) (x : ℝ) : ℝ := π * σ x / x

/-- `ρ(x) = exp(−∫_c^x 2m/σ²)` for drift `m`, source (16). -/
noncomputable def scaleDensity (m σ : ℝ → ℝ) (c x : ℝ) : ℝ :=
  Real.exp (-∫ y in c..x, 2 * m y / σ y ^ 2)

/-- `s(x) = ∫_c^x ρ`, source (18). -/
noncomputable def scale (m σ : ℝ → ℝ) (c x : ℝ) : ℝ :=
  ∫ y in c..x, scaleDensity m σ c y

/-- `v(x) = ∫_c^x (s(x) − s(y)) / (ρ(y) σ²(y)) dy`, source p. 7 (no factor 2). -/
noncomputable def fellerV (m σ : ℝ → ℝ) (c x : ℝ) : ℝ :=
  ∫ y in c..x, (scale m σ c x - scale m σ c y) / (scaleDensity m σ c y * σ y ^ 2)

/-- Auxiliary drift `μ + bπ σ` with original drift `μ = 0`, source (15). -/
noncomputable def auxDrift (π : ℝ) (σ : ℝ → ℝ) : ℝ → ℝ := fun x => 0 + bPi π σ x * σ x

/-- `f` has a finite limit along `F`. -/
def HasFiniteLimit (f : ℝ → ℝ) (F : Filter ℝ) : Prop := ∃ L : ℝ, Tendsto f F (𝓝 L)

/-- `∞` is good, source (24), original drift `0`. -/
def GoodAtInfty (π : ℝ) (σ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ sr : ℝ, Tendsto (scale (fun _ => 0) σ c) atTop (𝓝 sr) ∧
    ∃ x, 0 < x ∧ IntegrableOn (fun y => (sr - scale (fun _ => 0) σ c y) * bPi π σ y ^ 2 /
      (scaleDensity (fun _ => 0) σ c y * σ y ^ 2)) (Ioi x)

/-- `0` is good, source (26), original drift `0`. -/
def GoodAtZero (π : ℝ) (σ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ sl : ℝ, Tendsto (scale (fun _ => 0) σ c) (𝓝[>] 0) (𝓝 sl) ∧
    ∃ x, 0 < x ∧ IntegrableOn (fun y => (scale (fun _ => 0) σ c y - sl) * bPi π σ y ^ 2 /
      (scaleDensity (fun _ => 0) σ c y * σ y ^ 2)) (Ioo 0 x)

/-- The condition of [mijatovic2010martingale] Theorem 2.1 on `J = (0, ∞)`: [the auxiliary diffusion
does not exit at `∞` (`ṽ(∞) = ∞`) or `∞` is good] and [it does not exit at `0` (`ṽ(0) = ∞`) or `0`
is good]. -/
def MUCondition (π : ℝ) (σ : ℝ → ℝ) (c : ℝ) : Prop :=
  (¬ HasFiniteLimit (fellerV (auxDrift π σ) σ c) atTop ∨ GoodAtInfty π σ c) ∧
    (¬ HasFiniteLimit (fellerV (auxDrift π σ) σ c) (𝓝[>] 0) ∨ GoodAtZero π σ c)

/-- `I₀ < ∞`. -/
def I0Finite (σ : ℝ → ℝ) : Prop := ∃ x, 0 < x ∧ IntegrableOn (fun y => y / σ y ^ 2) (Ioo 0 x)

/-- `I∞ < ∞`. -/
def IInftyFinite (σ : ℝ → ℝ) : Prop := ∃ x, 0 < x ∧ IntegrableOn (fun y => y / σ y ^ 2) (Ioi x)

/-- The right-hand side of (1): `(0 < π < 1/2 and I₀ < ∞) or (π > 1/2 and I∞ < ∞)`. -/
def StrictCase (π : ℝ) (σ : ℝ → ℝ) : Prop :=
  (π < 1 / 2 ∧ I0Finite σ) ∨ (1 / 2 < π ∧ IInftyFinite σ)

/-! ## Martingale vocabulary -/

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- The process stopped at the deterministic time `T`. -/
def stopAt (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t => X (min t T)

/-- Local martingale (Mathlib's localization of the martingale property). -/
def IsLocalMartingale (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  Locally (fun Y => Martingale Y 𝓕 P) 𝓕 X P

/-- Martingale on `[0, T]`. -/
def MartingaleOn (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  Martingale (stopAt T X) 𝓕 P

/-- Strict local martingale on `[0, T]`. -/
def IsStrictLocalMartingaleOn (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  IsLocalMartingale (stopAt T X) 𝓕 P ∧ ¬ MartingaleOn T X 𝓕 P

/-! ## The statement -/

/-- Claim 001. (A) the deterministic endpoint classification; (B) the classification of wealth,
given AX-01's conclusion at this instance as a premise; (C) the counterexample's numbers; (D) the
scope of the correction. -/
def statement : Prop :=
  (∀ (σ : ℝ → ℝ) (π c : ℝ), VolHyp σ → 0 < π → 0 < c →
      (MUCondition π σ c ↔ ¬ StrictCase π σ)) ∧
  (∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
      (Z : ℝ≥0 → Ω → ℝ) (σ : ℝ → ℝ) (π c v₀ : ℝ),
      VolHyp σ → 0 < π → 0 < c → 0 < v₀ → IsProbabilityMeasure P →
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ Z t ω) → (∀ᵐ ω ∂P, Continuous fun t => Z t ω) →
      IsLocalMartingale Z 𝓕 P →
      (∀ T : ℝ≥0, 0 < T → (MartingaleOn T Z 𝓕 P ↔ MUCondition π σ c)) →
      ((∀ᵐ ω ∂P, ∀ t, 0 ≤ v₀ * Z t ω) ∧ (∀ᵐ ω ∂P, Continuous fun t => v₀ * Z t ω) ∧
        IsLocalMartingale (fun t ω => v₀ * Z t ω) 𝓕 P) ∧
      ∀ T : ℝ≥0, 0 < T →
        (IsStrictLocalMartingaleOn T (fun t ω => v₀ * Z t ω) 𝓕 P ↔ StrictCase π σ) ∧
        (MartingaleOn T (fun t ω => v₀ * Z t ω) 𝓕 P ↔ ¬ StrictCase π σ)) ∧
  (StrictCase (1 / 4) (fun _ => 1) ∧ I0Finite (fun _ => 1) ∧ ¬ IInftyFinite (fun _ => 1) ∧
    (∫ y in (0 : ℝ)..1, y / (1 : ℝ) ^ 2) = 1 / 2) ∧
  (∀ (σ : ℝ → ℝ) (π : ℝ), 0 < π → ¬ I0Finite σ →
      (StrictCase π σ ↔ 1 / 2 < π ∧ IInftyFinite σ)) ∧
  (∀ (σ : ℝ → ℝ) (π : ℝ), 0 < π → π < 1 / 2 → I0Finite σ →
      StrictCase π σ ∧ ¬ (1 / 2 < π ∧ IInftyFinite σ))

end Standalone.D1TwoEndpoint
