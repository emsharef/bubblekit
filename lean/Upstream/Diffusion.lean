import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Shared vocabulary for the D1 stochastic inputs (ledger AX-01, AX-02, AX-03)

This file is infrastructure for `Upstream/MartingaleCriterion.lean` (AX-01), `Upstream/FellerTest.lean`
(AX-02) and `Upstream/DriftlessIntegralCriterion.lean` (AX-03). It holds no cited theorem.

**Deterministic side (concrete).** The state interval `J = (l, r)` with `−∞ ≤ l < r ≤ ∞`; the
Engelbert–Schmidt coefficient conditions (5)–(6) and condition (8) of [mijatovic2010martingale]; the
functions ρ, s, v of its (16), (18) and the display after (19), in the source normalization (no
factor 2 in v); endpoint values as one-sided limits; goodness (24)/(26); the scale forms (21)/(23).

**Stochastic side.** Mathlib (at the pinned revision) defines Brownian motion, martingales and
localization (`Locally`), but has no stochastic integral and does not construct a Brownian motion.
So "S is a weak solution of dS = μ(S)dt + σ(S)dW" and "Z is the stochastic exponential (7)" cannot be
defined here. They enter as two opaque relations bundled in `SDEPrimitives`, each tied by a field to
the concrete path conventions of the sources, which are defined here in full:

* exit (source p. 4): `ζ` finite and `S_t → e` (in `EReal`) as `t ↑ ζ`, for `e ∈ {l, r}`;
  "exits at r" means this event has positive probability;
* absorption: after an exit at a *finite* endpoint `a`, `S_t = a` for `t ≥ ζ`. A real-valued path
  cannot sit at `±∞`; after an exit at an infinite endpoint the values of `S` are unconstrained;
* stochastic exponential (source (7) and the sentence after it): `Z_0 = 1`, `Z > 0` before `ζ`;
  after a finite exit with finite accumulated `∫_0^ζ b(S_u)² du`, `Z` keeps its (positive) exit value;
  after a finite exit with infinite accumulated integral, `Z = 0`.

All path conventions are almost-sure, simultaneously in `t`.

`SDEPrimitives.conventional` is a *degenerate* model of `SDEPrimitives`: it takes every path obeying
the conventions as a "solution". It is a genuine model of that structure's two fields; it is not
the weak-solution relation, which Mathlib cannot express. See the per-entry files for how the three
hypothesis structures are instantiated (vacuously, through the Brownian premise) and for the
convention checks.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Upstream.Diffusion

/-! ## The state interval -/

/-- The open state interval `J = (l, r)`, `−∞ ≤ l < r ≤ ∞`. -/
structure StateInterval where
  l : EReal
  r : EReal
  lt : l < r

namespace StateInterval

variable (J : StateInterval)

/-- `x ∈ J`. -/
def Mem (x : ℝ) : Prop := J.l < (x : EReal) ∧ (x : EReal) < J.r

/-- The approach `x ↑ r` from inside `J`; for `r = ∞` this is `x → ∞` (`toRight_top`). -/
noncomputable def toRight : Filter ℝ := comap (fun x : ℝ => (x : EReal)) (𝓝[<] J.r)

/-- The approach `x ↓ l` from inside `J`; for `l = −∞` this is `x → −∞` (`toLeft_bot`). -/
noncomputable def toLeft : Filter ℝ := comap (fun x : ℝ => (x : EReal)) (𝓝[>] J.l)

/-- `(x, r)`. -/
def rightTail (x : ℝ) : Set ℝ := {y | x < y ∧ (y : EReal) < J.r}

/-- `(l, x)`. -/
def leftTail (x : ℝ) : Set ℝ := {y | J.l < (y : EReal) ∧ y < x}

/-- `f ∈ L¹_loc(J)`: integrable on every compact `[a, b]` with `a, b ∈ J` (source p. 4). -/
def LocInt (f : ℝ → ℝ) : Prop := ∀ a b, J.Mem a → J.Mem b → IntegrableOn f (Icc a b)

/-- `f ∈ L¹_loc(r−)`: `∫_x^r |f| < ∞` for some `x ∈ J` (source p. 7). -/
def IntegrableNearRight (f : ℝ → ℝ) : Prop := ∃ x, J.Mem x ∧ IntegrableOn f (J.rightTail x)

/-- `f ∈ L¹_loc(l+)`: `∫_l^x |f| < ∞` for some `x ∈ J` (source p. 7). -/
def IntegrableNearLeft (f : ℝ → ℝ) : Prop := ∃ x, J.Mem x ∧ IntegrableOn f (J.leftTail x)

end StateInterval

/-! ## Coefficient hypotheses -/

/-- Borel coefficients and the Engelbert–Schmidt conditions (5)–(6) of [mijatovic2010martingale]:
`σ ≠ 0` on `J`, and `1/σ²`, `μ/σ²` locally integrable on `J`. Only the values on `J` matter; asking
`μ`, `σ` to be Borel on all of `ℝ` restricts the premise, never strengthens a conclusion. -/
structure CoeffHyp (J : StateInterval) (μ σ : ℝ → ℝ) : Prop where
  measurable_drift : Measurable μ
  measurable_vol : Measurable σ
  vol_ne_zero : ∀ x, J.Mem x → σ x ≠ 0
  locInt_inv_sq : J.LocInt (fun x => 1 / σ x ^ 2)
  locInt_drift : J.LocInt (fun x => μ x / σ x ^ 2)

/-- Condition (8) of [mijatovic2010martingale] on the integrand `b`, with `b` Borel. -/
structure IntegrandHyp (J : StateInterval) (σ b : ℝ → ℝ) : Prop where
  measurable : Measurable b
  locInt : J.LocInt (fun x => b x ^ 2 / σ x ^ 2)

/-! ## Scale density, scale function and Feller's `v` (source normalization) -/

/-- `ρ(x) = exp(−∫_c^x 2μ/σ²(y) dy)`, source (16). Oriented integral. -/
noncomputable def scaleDensity (μ σ : ℝ → ℝ) (c x : ℝ) : ℝ :=
  Real.exp (-∫ y in c..x, 2 * μ y / σ y ^ 2)

/-- `s(x) = ∫_c^x ρ(y) dy`, source (18). -/
noncomputable def scale (μ σ : ℝ → ℝ) (c x : ℝ) : ℝ :=
  ∫ y in c..x, scaleDensity μ σ c y

/-- `v(x) = ∫_c^x (s(x) − s(y)) / (ρ(y) σ²(y)) dy`, the display after source (19); equal to the
`w` of [karatzas2015distribution] (7.1). **No factor 2.** -/
noncomputable def fellerV (μ σ : ℝ → ℝ) (c x : ℝ) : ℝ :=
  ∫ y in c..x, (scale μ σ c x - scale μ σ c y) / (scaleDensity μ σ c y * σ y ^ 2)

/-- Drift `μ + bσ` of the auxiliary diffusion (15). Its scale density is the source's `ρ̃` of (17)
(`scaleDensity_auxDrift`), so `fellerV (auxDrift μ σ b) σ c` is the source's `ṽ`. -/
def auxDrift (μ σ b : ℝ → ℝ) : ℝ → ℝ := fun x => μ x + b x * σ x

/-- `f` has a finite limit along `F`. With `F = J.toRight`, `HasFiniteLimit v F` is the source's
"`v(r) < ∞`" (the limit `v(r) := lim_{x↑r} v(x)` exists in `[0, ∞]` by monotonicity, source p. 7). -/
def HasFiniteLimit (f : ℝ → ℝ) (F : Filter ℝ) : Prop := ∃ L : ℝ, Tendsto f F (𝓝 L)

/-- Scale form (21) of the right exit test: `s(r) < ∞` and `(s(r) − s)/(ρσ²) ∈ L¹_loc(r−)`. -/
def ScaleExitRight (J : StateInterval) (μ σ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ sr : ℝ, Tendsto (scale μ σ c) J.toRight (𝓝 sr) ∧
    J.IntegrableNearRight (fun y => (sr - scale μ σ c y) / (scaleDensity μ σ c y * σ y ^ 2))

/-- Scale form (23) of the left exit test: `s(l) > −∞` and `(s − s(l))/(ρσ²) ∈ L¹_loc(l+)`. -/
def ScaleExitLeft (J : StateInterval) (μ σ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ sl : ℝ, Tendsto (scale μ σ c) J.toLeft (𝓝 sl) ∧
    J.IntegrableNearLeft (fun y => (scale μ σ c y - sl) / (scaleDensity μ σ c y * σ y ^ 2))

/-- `r` is good, (24): `s(r) < ∞` and `(s(r) − s) b²/(ρσ²) ∈ L¹_loc(r−)`, with the scale of the
*original* diffusion. -/
def GoodRight (J : StateInterval) (μ σ b : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ sr : ℝ, Tendsto (scale μ σ c) J.toRight (𝓝 sr) ∧
    J.IntegrableNearRight
      (fun y => (sr - scale μ σ c y) * b y ^ 2 / (scaleDensity μ σ c y * σ y ^ 2))

/-- `l` is good, (26): `s(l) > −∞` and `(s − s(l)) b²/(ρσ²) ∈ L¹_loc(l+)`. -/
def GoodLeft (J : StateInterval) (μ σ b : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ sl : ℝ, Tendsto (scale μ σ c) J.toLeft (𝓝 sl) ∧
    J.IntegrableNearLeft
      (fun y => (scale μ σ c y - sl) * b y ^ 2 / (scaleDensity μ σ c y * σ y ^ 2))

/-! ## Probabilistic vocabulary -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `W` is an `(𝓕, P)`-Brownian motion on a probability space: Brownian (Mathlib's
`IsBrownianReal`), adapted, with `W_t − W_s` independent of `𝓕_s` for `s ≤ t`. -/
def IsFBrownian (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop :=
  IsProbabilityMeasure P ∧ IsBrownianReal W P ∧ Adapted 𝓕 W ∧
    ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance) (𝓕 s) P

/-- The usual conditions: `𝓕` right-continuous and `𝓕 0` contains every `P`-null set. -/
def UsualConditions (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  𝓕.IsRightContinuous ∧ ∀ s : Set Ω, P s = 0 → MeasurableSet[𝓕 0] s

/-- Along `ω`, the path exits at the endpoint `e`: `ζ(ω) < ∞` and `S_t(ω) → e` as `t ↑ ζ(ω)`. -/
def ExitsAtPath (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (e : EReal) (ω : Ω) : Prop :=
  ∃ z : ℝ≥0, ζ ω = z ∧ Tendsto (fun t => (S t ω : EReal)) (𝓝[<] z) (𝓝 e)

/-- "`S` exits `J` at `r`": `P(ζ < ∞, lim_{t↑ζ} S_t = r) > 0` (source p. 4). -/
def ExitsRight (P : Measure Ω) (J : StateInterval) (S : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → WithTop ℝ≥0) : Prop :=
  0 < P {ω | ExitsAtPath S ζ J.r ω}

/-- "`S` exits `J` at `l`". -/
def ExitsLeft (P : Measure Ω) (J : StateInterval) (S : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → WithTop ℝ≥0) : Prop :=
  0 < P {ω | ExitsAtPath S ζ J.l ω}

/-- Path conventions of a `J`-valued diffusion started at `s₀` with exit time `ζ`, absorbed at the
endpoint where it exits (source p. 4). Almost surely, simultaneously in `t`. -/
structure ExitConventions (P : Measure Ω) (J : StateInterval) (s₀ : ℝ) (S : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → WithTop ℝ≥0) : Prop where
  start : ∀ᵐ ω ∂P, S 0 ω = s₀
  exitTime_pos : ∀ᵐ ω ∂P, 0 < ζ ω
  mem_before : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < ζ ω → J.Mem (S t ω)
  continuousOn_before : ∀ᵐ ω ∂P, ContinuousOn (fun t => S t ω) {t | (t : WithTop ℝ≥0) < ζ ω}
  exits_at_endpoint : ∀ᵐ ω ∂P, ∀ z : ℝ≥0, ζ ω = z →
    ExitsAtPath S ζ J.l ω ∨ ExitsAtPath S ζ J.r ω
  absorbed : ∀ᵐ ω ∂P, ∀ (z : ℝ≥0) (a : ℝ), ζ ω = z →
    Tendsto (fun t => (S t ω : EReal)) (𝓝[<] z) (𝓝 (a : EReal)) → ∀ t, z ≤ t → S t ω = a

/-- `∫_0^z b²(S_u(ω)) du ∈ [0, ∞]`, the accumulated quadratic variation of `∫ b(S) dW` up to `z`. -/
noncomputable def accumulated (b : ℝ → ℝ) (S : ℝ≥0 → Ω → ℝ) (ω : Ω) (z : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ u in Ico (0 : ℝ) z, ENNReal.ofReal (b (S u.toNNReal ω) ^ 2)

/-- Conventions of the stochastic exponential (7) of [mijatovic2010martingale], p. 4. Almost surely,
simultaneously in `t`. -/
structure StochExpConventions (P : Measure Ω) (b : ℝ → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → WithTop ℝ≥0) (Z : ℝ≥0 → Ω → ℝ) : Prop where
  start : ∀ᵐ ω ∂P, Z 0 ω = 1
  pos_before : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < ζ ω → 0 < Z t ω
  frozen : ∀ᵐ ω ∂P, ∀ z : ℝ≥0, ζ ω = z → accumulated b S ω z < ∞ →
    0 < Z z ω ∧ ∀ t, z ≤ t → Z t ω = Z z ω
  killed : ∀ᵐ ω ∂P, ∀ z : ℝ≥0, ζ ω = z → accumulated b S ω z = ∞ → ∀ t, z ≤ t → Z t ω = 0

/-- The process stopped at the deterministic time `T`. `Martingale (stopAt T X)` is "`X` is a
martingale on `[0, T]`". -/
def stopAt (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t => X (min t T)

/-- Local martingale: Mathlib's localization of the martingale property. -/
def IsLocalMartingale (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  Locally (fun Y => Martingale Y 𝓕 P) 𝓕 X P

/-- Martingale on `[0, T]`. -/
def MartingaleOn (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  Martingale (stopAt T X) 𝓕 P

/-- Strict local martingale: a local martingale that is not a martingale. -/
def IsStrictLocalMartingale (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  IsLocalMartingale X 𝓕 P ∧ ¬ Martingale X 𝓕 P

/-- Strict local martingale on `[0, T]`. -/
def IsStrictLocalMartingaleOn (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  IsLocalMartingale (stopAt T X) 𝓕 P ∧ ¬ MartingaleOn T X 𝓕 P

/-! ## The undefinable primitives -/

/-- The two notions Mathlib cannot define, on a fixed base `(Ω, P, 𝓕, W)`:

* `Solves J μ σ s₀ S ζ`: `S` is a weak solution of `dS = μ(S) dt + σ(S) dW`, `S_0 = s₀`, on `J`,
  driven by `W`, with exit time `ζ`, absorbed at its exit endpoint (source (4) and p. 4);
* `StochExp b S ζ Z`: `Z` is the stochastic exponential (7) of `∫ b(S) dW`.

Each is tied to the concrete conventions it must obey. The intended model is the weak-solution
relation and the stochastic exponential of the sources; every theorem using a hypothesis structure
over `X : SDEPrimitives P 𝓕 W` is conditional on `X` being that model. -/
structure SDEPrimitives (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) where
  Solves : StateInterval → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop
  StochExp : (ℝ → ℝ) → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → (ℝ≥0 → Ω → ℝ) → Prop
  solves_conventions : ∀ {J μ σ s₀ S ζ}, Solves J μ σ s₀ S ζ → ExitConventions P J s₀ S ζ
  stochExp_conventions : ∀ {b S ζ Z}, StochExp b S ζ Z → StochExpConventions P b S ζ Z

/-- Degenerate model of `SDEPrimitives`: every convention-respecting path counts. A genuine model of
both fields; not the weak-solution relation. -/
def SDEPrimitives.conventional (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) :
    SDEPrimitives P 𝓕 W where
  Solves J _ _ s₀ S ζ := ExitConventions P J s₀ S ζ
  StochExp b S ζ Z := StochExpConventions P b S ζ Z
  solves_conventions h := h
  stochExp_conventions h := h


/-! ## Convention checks

Rule 6 asks the file of a vacuously instantiated structure to exercise the conventions its fields
rely on. The conventions shared by AX-01–AX-03 are exercised here; each entry's file adds the checks
specific to its fields.

* `not_isFBrownian_const`: the Brownian premise fails for a constant `W` (this is what makes the
  instances in the entry files vacuous).
* Endpoint approach: `toRight_top`, `toLeft_bot`, `toRight_coe`, `toLeft_coe`.
* Source normalization: `fellerV_zero_one` (`v(x) = (x − c)²/2` for `μ = 0, σ = 1`; no factor 2);
  `scaleDensity_auxDrift` (our `ρ̃` is the source's (17)).
* Premises hold in a degenerate case: `coeffHyp_zero_one`, `integrandHyp_rampIntegrand`.
* Exit and absorption: `exitConventions_ramp` (a path exiting at the finite endpoint `r = 1` at time
  `1` and absorbed there), `exitsRight_ramp`, `not_exitsLeft_ramp`; `exitConventions_const`,
  `not_exitsRight_const`, `not_exitsLeft_const` (no exit).
* Stochastic exponential: `stochExpConventions_one` (finite accumulated integral, frozen positive
  value); `accumulated_ramp` and `stochExpConventions_rampKilled` (infinite accumulated integral,
  killed to `0`).
* Martingale vocabulary: `isLocalMartingale_of_martingale`, `not_isStrictLocalMartingale_of_martingale`,
  `stopAt_of_le`, `stopAt_of_ge`; `StrictExample.isStrictLocalMartingale_X` shows
  `IsStrictLocalMartingale` is inhabited (a time-constant, non-integrable `X` on `ℕ`).
-/

section ConventionChecks

theorem not_isBrownianReal_const (P : Measure Ω) [IsProbabilityMeasure P] (a : ℝ) :
    ¬ IsBrownianReal (fun _ _ => a) P := by
  intro h
  have hm := (h.toIsPreBrownianReal.hasLaw_eval 1).map_eq
  rw [Measure.map_const, measure_univ, one_smul] at hm
  have h1 : (Measure.dirac a) {a} = 1 := by simp
  rw [hm] at h1
  have : NullSingletonClass (gaussianReal 0 (1 : ℝ≥0)) := nullSingletonClass_gaussianReal one_ne_zero
  simp at h1

theorem not_isFBrownian_const (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (a : ℝ) :
    ¬ IsFBrownian 𝓕 (fun _ _ => a) P := fun ⟨_, h, _⟩ => not_isBrownianReal_const P a h

namespace StateInterval

theorem toRight_top {l : EReal} (h : l < ⊤) : (⟨l, ⊤, h⟩ : StateInterval).toRight = atTop := by
  have : 𝓝[<] (⊤ : EReal) = 𝓝[≠] ⊤ := by
    congr 1; ext x; simp [lt_top_iff_ne_top]
  simp only [toRight, this, EReal.nhdsWithin_top]
  exact comap_map (fun _ _ h => EReal.coe_injective h)

theorem toLeft_bot {r : EReal} (h : ⊥ < r) : (⟨⊥, r, h⟩ : StateInterval).toLeft = atBot := by
  have : 𝓝[>] (⊥ : EReal) = 𝓝[≠] ⊥ := by
    congr 1; ext x; simp [bot_lt_iff_ne_bot]
  simp only [toLeft, this, EReal.nhdsWithin_bot]
  exact comap_map (fun _ _ h => EReal.coe_injective h)

theorem toRight_coe {l : EReal} {a : ℝ} (h : l < a) :
    (⟨l, a, h⟩ : StateInterval).toRight = 𝓝[<] a := by
  simp only [toRight, nhdsWithin, comap_inf, comap_principal,
    ← EReal.isEmbedding_coe.isInducing.nhds_eq_comap]
  congr 2
  ext x; simp

theorem toLeft_coe {r : EReal} {a : ℝ} (h : (a : EReal) < r) :
    (⟨a, r, h⟩ : StateInterval).toLeft = 𝓝[>] a := by
  simp only [toLeft, nhdsWithin, comap_inf, comap_principal,
    ← EReal.isEmbedding_coe.isInducing.nhds_eq_comap]
  congr 2
  ext x; simp

end StateInterval

theorem scaleDensity_zero_one (c x : ℝ) : scaleDensity (fun _ => 0) (fun _ => 1) c x = 1 := by
  simp [scaleDensity]

theorem scale_zero_one (c x : ℝ) : scale (fun _ => 0) (fun _ => 1) c x = x - c := by
  simp [scale, scaleDensity_zero_one]

/-- Source normalization of `v`: for `μ = 0`, `σ = 1`, `v(x) = (x − c)²/2` (no factor 2). -/
theorem fellerV_zero_one (c x : ℝ) :
    fellerV (fun _ => 0) (fun _ => 1) c x = (x - c) ^ 2 / 2 := by
  simp only [fellerV, scale_zero_one, scaleDensity_zero_one, one_pow, mul_one, div_one]
  have : ∀ y : ℝ, x - c - (y - c) = x - y := fun y => by ring
  simp only [this]
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem StateInterval.mem_of_mem_uIcc {J : StateInterval} {c x y : ℝ} (hc : J.Mem c) (hx : J.Mem x)
    (hy : y ∈ uIcc c x) : J.Mem y := by
  rcases hy with ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · rcases min_choice c x with h | h <;> rw [h] at h1
    · exact hc.1.trans_le (EReal.coe_le_coe_iff.2 h1)
    · exact hx.1.trans_le (EReal.coe_le_coe_iff.2 h1)
  · rcases max_choice c x with h | h <;> rw [h] at h2
    · exact (EReal.coe_le_coe_iff.2 h2).trans_lt hc.2
    · exact (EReal.coe_le_coe_iff.2 h2).trans_lt hx.2

theorem StateInterval.LocInt.intervalIntegrable {J : StateInterval} {f : ℝ → ℝ} (hf : J.LocInt f)
    {c x : ℝ} (hc : J.Mem c) (hx : J.Mem x) : IntervalIntegrable f volume c x := by
  rw [intervalIntegrable_iff']
  rcases le_total c x with h | h
  · rw [uIcc_of_le h]; exact hf c x hc hx
  · rw [uIcc_of_ge h]; exact hf x c hx hc

theorem coeffHyp_zero_one (J : StateInterval) : CoeffHyp J (fun _ => 0) (fun _ => 1) where
  measurable_drift := measurable_const
  measurable_vol := measurable_const
  vol_ne_zero _ _ := one_ne_zero
  locInt_inv_sq _ _ _ _ := by simp
  locInt_drift _ _ _ _ := by simp

/-- The auxiliary scale density is the source's `ρ̃ = ρ · exp(−∫_c^x 2b/σ)`, (17). -/
theorem scaleDensity_auxDrift {J : StateInterval} {μ σ b : ℝ → ℝ} (hμσ : CoeffHyp J μ σ)
    (hb : IntegrandHyp J σ b) {c x : ℝ} (hc : J.Mem c) (hx : J.Mem x) :
    scaleDensity (auxDrift μ σ b) σ c x =
      scaleDensity μ σ c x * Real.exp (-∫ y in c..x, 2 * b y / σ y) := by
  have hμ : IntervalIntegrable (fun y => 2 * μ y / σ y ^ 2) volume c x := by
    have := (hμσ.locInt_drift.intervalIntegrable hc hx).const_mul 2
    simpa [mul_div_assoc] using this
  have hbσ : IntervalIntegrable (fun y => 2 * b y / σ y) volume c x := by
    have hg : IntervalIntegrable (fun y => b y ^ 2 / σ y ^ 2 + 1) volume c x :=
      (hb.locInt.intervalIntegrable hc hx).add intervalIntegrable_const
    refine (hg.mono_fun' ?_ ?_)
    · exact ((measurable_const.mul hb.measurable).div hμσ.measurable_vol).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      simp only [Real.norm_eq_abs]
      rw [abs_div, abs_mul, abs_two]
      have h0 : 0 ≤ (|b y| / |σ y| - 1) ^ 2 := sq_nonneg _
      have hsq : b y ^ 2 / σ y ^ 2 = (|b y| / |σ y|) ^ 2 := by
        rw [div_pow, sq_abs, sq_abs]
      rw [hsq, mul_div_assoc]
      nlinarith
  have hcongr : ∫ y in c..x, 2 * auxDrift μ σ b y / σ y ^ 2 =
      ∫ y in c..x, (2 * μ y / σ y ^ 2 + 2 * b y / σ y) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hσ := hμσ.vol_ne_zero y (StateInterval.mem_of_mem_uIcc hc hx hy)
    simp only [auxDrift]
    field_simp
  rw [scaleDensity, scaleDensity, hcongr, intervalIntegral.integral_add hμ hbσ, neg_add,
    Real.exp_add]

/-- `J = (−∞, 1)`. -/
noncomputable def rampInterval : StateInterval := ⟨⊥, (1 : ℝ), EReal.bot_lt_coe 1⟩

/-- Deterministic path `t ↦ min t 1` from `0`: reaches `r = 1` at time `1`, stays there. -/
def ramp : ℝ≥0 → Unit → ℝ := fun t _ => min (t : ℝ) 1

/-- Its exit time, `ζ = 1`. -/
def rampExit : Unit → WithTop ℝ≥0 := fun _ => ((1 : ℝ≥0) : WithTop ℝ≥0)

theorem ramp_tendsto :
    Tendsto (fun t : ℝ≥0 => (ramp t () : EReal)) (𝓝[<] (1 : ℝ≥0)) (𝓝 ((1 : ℝ) : EReal)) := by
  have hc : Continuous (fun t : ℝ≥0 => (ramp t () : EReal)) :=
    continuous_coe_real_ereal.comp (NNReal.continuous_coe.min continuous_const)
  have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
  simpa [ramp] using this

instance : (𝓝[<] (1 : ℝ≥0)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, zero_lt_one⟩

theorem ramp_limit_eq {e : EReal}
    (h : Tendsto (fun t : ℝ≥0 => (ramp t () : EReal)) (𝓝[<] (1 : ℝ≥0)) (𝓝 e)) :
    e = (1 : ℝ) :=
  tendsto_nhds_unique h ramp_tendsto

theorem exitConventions_ramp :
    ExitConventions (Measure.dirac ()) rampInterval 0 ramp rampExit where
  start := Eventually.of_forall fun _ => by simp [ramp]
  exitTime_pos := Eventually.of_forall fun _ => by simp [rampExit]
  mem_before := Eventually.of_forall fun _ t ht => by
    have ht : t < 1 := WithTop.coe_lt_coe.1 ht
    have ht' : (t : ℝ) < 1 := by exact_mod_cast ht
    refine ⟨EReal.bot_lt_coe _, ?_⟩
    simp only [rampInterval, ramp, min_eq_left ht'.le]
    exact_mod_cast ht'
  continuousOn_before := Eventually.of_forall fun _ =>
    (NNReal.continuous_coe.min continuous_const).continuousOn
  exits_at_endpoint := Eventually.of_forall fun ω z _ => by
    cases ω
    exact Or.inr ⟨1, rfl, ramp_tendsto⟩
  absorbed := Eventually.of_forall fun ω z a hz ha t ht => by
    cases ω
    have hz : z = 1 := (WithTop.coe_inj.1 hz).symm
    subst hz
    have ha : a = 1 := by exact_mod_cast ramp_limit_eq ha
    have ht : (1 : ℝ) ≤ t := by exact_mod_cast ht
    simp [ramp, ha, ht]

theorem exitsAtPath_ramp_iff (e : EReal) : ExitsAtPath ramp rampExit e () ↔ e = (1 : ℝ) := by
  constructor
  · rintro ⟨z, hz, h⟩
    have hz : z = 1 := (WithTop.coe_inj.1 hz).symm
    subst hz
    exact ramp_limit_eq h
  · rintro rfl
    exact ⟨1, rfl, ramp_tendsto⟩

/-- The ramp exits at `r = 1`. -/
theorem exitsRight_ramp : ExitsRight (Measure.dirac ()) rampInterval ramp rampExit := by
  have : {ω | ExitsAtPath ramp rampExit rampInterval.r ω} = univ := by
    ext ω; cases ω; simp [exitsAtPath_ramp_iff, rampInterval]
  simp [ExitsRight, this]

/-- The ramp does not exit at `l = −∞`. -/
theorem not_exitsLeft_ramp : ¬ ExitsLeft (Measure.dirac ()) rampInterval ramp rampExit := by
  have : {ω | ExitsAtPath ramp rampExit rampInterval.l ω} = ∅ := by
    ext ω; cases ω
    simp only [exitsAtPath_ramp_iff, rampInterval, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact (EReal.bot_lt_coe 1).ne
  simp [ExitsLeft, this]

/-- A constant path with `ζ = ∞`. -/
theorem exitConventions_const {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {J : StateInterval}
    {s₀ : ℝ} (hs₀ : J.Mem s₀) : ExitConventions P J s₀ (fun _ _ => s₀) (fun _ => ⊤) where
  start := Eventually.of_forall fun _ => rfl
  exitTime_pos := Eventually.of_forall fun _ => WithTop.coe_lt_top 0
  mem_before := Eventually.of_forall fun _ _ _ => hs₀
  continuousOn_before := Eventually.of_forall fun _ => continuousOn_const
  exits_at_endpoint := Eventually.of_forall fun _ _ hz => absurd hz.symm (WithTop.coe_ne_top)
  absorbed := Eventually.of_forall fun _ _ _ hz => absurd hz.symm (WithTop.coe_ne_top)

theorem not_exitsAtPath_const {Ω : Type*} {s₀ : ℝ} (e : EReal) (ω : Ω) :
    ¬ ExitsAtPath (fun _ _ => s₀) (fun _ => (⊤ : WithTop ℝ≥0)) e ω :=
  fun ⟨_, hz, _⟩ => WithTop.coe_ne_top hz.symm

theorem not_exitsRight_const {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (J : StateInterval)
    (s₀ : ℝ) : ¬ ExitsRight P J (fun _ _ => s₀) (fun _ => ⊤) := by
  simp [ExitsRight, not_exitsAtPath_const]

theorem not_exitsLeft_const {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (J : StateInterval)
    (s₀ : ℝ) : ¬ ExitsLeft P J (fun _ _ => s₀) (fun _ => ⊤) := by
  simp [ExitsLeft, not_exitsAtPath_const]

/-- `Z ≡ 1` for `b = 0`: accumulated integral `0`, frozen at the positive value `1` after an exit. -/
theorem stochExpConventions_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) :
    StochExpConventions P (fun _ => 0) S ζ (fun _ _ => 1) where
  start := Eventually.of_forall fun _ => rfl
  pos_before := Eventually.of_forall fun _ _ _ => one_pos
  frozen := Eventually.of_forall fun _ _ _ _ => ⟨one_pos, fun _ _ => rfl⟩
  killed := Eventually.of_forall fun _ _ _ h => by simp [accumulated] at h

theorem isLocalMartingale_of_martingale {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} (h : Martingale X 𝓕 P) :
    IsLocalMartingale X 𝓕 P :=
  Locally.of_prop h

theorem not_isStrictLocalMartingale_of_martingale {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} (h : Martingale X 𝓕 P) :
    ¬ IsStrictLocalMartingale X 𝓕 P :=
  fun h' => h'.2 h

theorem stopAt_of_le {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) {T t : ℝ≥0} (h : t ≤ T) :
    stopAt T X t = X t := by simp [stopAt, h]

theorem stopAt_of_ge {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) {T t : ℝ≥0} (h : T ≤ t) :
    stopAt T X t = X T := by simp [stopAt, h]

/-- `b(x) = 1/(1 − x)`, singular at the exit endpoint `r = 1`. -/
noncomputable def rampIntegrand : ℝ → ℝ := fun x => (1 - x)⁻¹

theorem integrandHyp_rampIntegrand : IntegrandHyp rampInterval (fun _ => 1) rampIntegrand where
  measurable := (measurable_const.sub measurable_id).inv
  locInt a b _ hb := by
    have hb : b < 1 := by have := hb.2; simp only [rampInterval] at this; exact_mod_cast this
    refine ContinuousOn.integrableOn_Icc ?_
    refine ContinuousOn.div_const (ContinuousOn.pow ?_ 2) _
    refine ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) fun x hx => ?_
    exact sub_ne_zero.2 (ne_of_gt (hx.2.trans_lt hb))

/-- Along the ramp, `∫_0^1 b(S_u)² du = ∞`. -/
theorem accumulated_ramp : accumulated rampIntegrand ramp () 1 = ∞ := by
  by_contra hne
  have hlt : accumulated rampIntegrand ramp () 1 < ∞ := lt_top_iff_ne_top.2 hne
  have hle : ∫⁻ u in Ico (0 : ℝ) 1, ‖(u - 1)⁻¹‖ₑ ≤ accumulated rampIntegrand ramp () 1 := by
    refine setLIntegral_mono' measurableSet_Ico fun u hu => ?_
    have hu0 : (u.toNNReal : ℝ) = u := Real.coe_toNNReal u hu.1
    have hpos : 0 < 1 - u := sub_pos.2 hu.2
    have hx : 1 ≤ (1 - u)⁻¹ := one_le_inv₀ hpos |>.2 (by linarith [hu.1])
    simp only [ramp, hu0, min_eq_left hu.2.le, rampIntegrand]
    rw [Real.enorm_eq_ofReal_abs, show u - 1 = -(1 - u) by ring, inv_neg, abs_neg,
      abs_of_pos (inv_pos.2 hpos)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hint : IntegrableOn (fun u : ℝ => (u - 1)⁻¹) (Ico 0 1) :=
    ⟨(measurable_id.sub measurable_const).inv.aestronglyMeasurable, hle.trans_lt hlt⟩
  have hii : IntervalIntegrable (fun u : ℝ => (u - 1)⁻¹) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
      ← integrableOn_Icc_iff_integrableOn_Ioc (by simp)]
    exact (integrableOn_Icc_iff_integrableOn_Ico (by simp)).2 hint
  rcases intervalIntegrable_sub_inv_iff.1 hii with h | h
  · exact zero_ne_one h
  · exact h (by simp)

/-- The killed stochastic exponential along the ramp: `Z_t = 1 − t` before `ζ = 1`, `0` after. -/
noncomputable def rampKilled : ℝ≥0 → Unit → ℝ := fun t _ => if t < 1 then 1 - t else 0

theorem stochExpConventions_rampKilled :
    StochExpConventions (Measure.dirac ()) rampIntegrand ramp rampExit rampKilled where
  start := Eventually.of_forall fun _ => by simp [rampKilled]
  pos_before := Eventually.of_forall fun _ t ht => by
    have ht : t < 1 := WithTop.coe_lt_coe.1 ht
    simp only [rampKilled, ht, ↓reduceIte]
    exact sub_pos.2 (by exact_mod_cast ht)
  frozen := Eventually.of_forall fun ω z hz h => by
    cases ω
    have hz : z = 1 := (WithTop.coe_inj.1 hz).symm
    subst hz
    exact absurd accumulated_ramp h.ne
  killed := Eventually.of_forall fun _ z hz _ t ht => by
    have hz : z = 1 := (WithTop.coe_inj.1 hz).symm
    subst hz
    simp [rampKilled, not_lt.2 ht]

namespace StrictExample

/-- `P{n} = 2^{-(n+1)}` on `ℕ`. -/
noncomputable def P : Measure ℕ := Measure.sum fun n => ((2 : ℝ≥0∞)⁻¹ ^ (n + 1)) • Measure.dirac n

instance : IsProbabilityMeasure P := by
  constructor
  simp only [P, Measure.sum_apply_of_countable, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  simp_rw [pow_succ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- `A(n) = 2^{n+1}`: `P`-a.s. finite, not integrable. -/
noncomputable def A : ℕ → ℝ := fun n => 2 ^ (n + 1)

theorem not_integrable_A : ¬ Integrable A P := by
  intro h
  have hfin := h.hasFiniteIntegral
  rw [HasFiniteIntegral, P, lintegral_sum_measure] at hfin
  simp_rw [lintegral_smul_measure] at hfin
  simp only [lintegral_dirac, smul_eq_mul] at hfin
  have h1 : ∀ i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (i + 1) * ‖A i‖ₑ = 1 := fun i => by
    rw [A, enorm_pow, show ‖(2 : ℝ)‖ₑ = 2 by rw [Real.enorm_eq_ofReal zero_le_two]; simp, ← mul_pow,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  simp only [h1, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero] at hfin
  exact lt_irrefl _ hfin

/-- Constant filtration: everything is known at time `0`. -/
def 𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace ℕ) :=
  ⟨fun _ => ⊤, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

/-- The process `X_t = A` for all `t`. -/
noncomputable def X : ℝ≥0 → ℕ → ℝ := fun _ => A

/-- `τ_n = ∞` on `{A ≤ n}`, `0` elsewhere. -/
noncomputable def τ : ℕ → ℕ → WithTop ℝ≥0 := fun n ω => if A ω ≤ n then ⊤ else ⊥

theorem isLocalizingSequence_τ : IsLocalizingSequence 𝓕 τ P where
  isStoppingTime _ _ := MeasurableSpace.measurableSet_top
  mono := Eventually.of_forall fun ω n m hnm => by
    simp only [τ]
    split_ifs with h1 h2 <;> simp_all
    exact absurd (h1.trans (Nat.cast_le.2 hnm)) (not_le.2 h2)
  tendsto_top := Eventually.of_forall fun ω => by
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_ge (A ω)
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [τ, hN.trans (Nat.cast_le.2 hn)]

/-- `X` is a strict local martingale: a local martingale that is not a martingale. This shows the
predicate `IsStrictLocalMartingale` is inhabited. -/
theorem isStrictLocalMartingale_X : IsStrictLocalMartingale X 𝓕 P := by
  refine ⟨⟨τ, isLocalizingSequence_τ, fun n => ?_⟩, fun h => not_integrable_A (h.integrable 0)⟩
  have hY : stoppedProcess (fun i => {ω | ⊥ < τ n ω}.indicator (X i)) (τ n) =
      fun _ => {ω | A ω ≤ n}.indicator A := by
    ext t ω
    simp only [stoppedProcess, X, τ, indicator, mem_ofPred_eq]
    split_ifs <;> simp_all
  rw [hY]
  have hm : ∀ f : ℕ → ℝ, Measurable[⊤] f := fun _ _ _ => MeasurableSpace.measurableSet_top
  refine martingale_const_fun 𝓕 P (hm _).stronglyMeasurable ?_
  refine Integrable.of_bound (C := n) (hm _).stronglyMeasurable.aestronglyMeasurable ?_
  refine Eventually.of_forall fun ω => ?_
  simp only [indicator, mem_ofPred_eq]
  split_ifs with h
  · exact (Real.norm_of_nonneg (by unfold A; positivity)).le.trans h
  · simp

end StrictExample

/-! ### The degenerate base used by the vacuous instances

One point, Dirac mass, the right-continuous trivial filtration, `W ≡ 0`. The usual conditions hold
(`usualConditions_unit`); the Brownian premise fails (`not_isFBrownian_unit`). A non-degenerate base
would need a Brownian motion, which Mathlib defines but does not construct. -/

/-- The right continuation of the trivial filtration on `Unit` (right-continuous by construction). -/
noncomputable def unitFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit) :=
  Filtration.rightCont ⊥

/-- `W ≡ 0`. -/
def unitW : ℝ≥0 → Unit → ℝ := fun _ _ => 0

theorem usualConditions_unit : UsualConditions unitFiltration (Measure.dirac ()) := by
  refine ⟨by unfold unitFiltration; infer_instance, fun s hs => ?_⟩
  have : s = ∅ := by
    ext ω; cases ω
    simp only [mem_empty_iff_false, iff_false]
    intro h
    rw [Measure.dirac_apply_of_mem h] at hs
    exact one_ne_zero hs
  rw [this]; exact @MeasurableSet.empty _ (unitFiltration 0)

theorem not_isFBrownian_unit : ¬ IsFBrownian unitFiltration unitW (Measure.dirac ()) :=
  not_isFBrownian_const _ _ 0

end ConventionChecks

end Upstream.Diffusion
