import Upstream.MartingaleCriterion

/-!
# AX-05  Sin's stochastic-volatility model has both kinds of pricing measure

Ledger entry AX-05 (`ledger/AXIOMS.md`). Source: [sin1995complications], Theorem 3.2, printed p. 4,
and Theorem 3.6 with its preceding nonparallel-vectors qualification, printed p. 5; Section 2 and
Assumptions 2.3, 3.1, printed pp. 2–4.

## Setting

The model is `dS = S v^α γ · dW`, `S₀ = s₀ > 0`, and `dv = v a · dW + κ(L − v) dt`, `v₀ = 1`, under
`Q` (the source's `Qˢ`), driven by a two-dimensional `(𝓕, Q)`-Brownian motion `W = (W₁, W₂)`. The
filtration satisfies the usual conditions, and `𝓕₀` is trivial. Parameters are `α, κ, L > 0`, nonzero
`γ, a ∈ ℝ²` and `s₀ > 0` (`SinParams.Valid`). Euclidean quantities are written out: `a · γ` is
`dot`, and nonparallel `|a · γ| < |a||γ|` is `(a · γ)² < |a|²|γ|²` (`Nonparallel`).

"`(S, v)` solves Sin's system" cannot be defined without stochastic integration, so it is the opaque
relation `SinPrimitives.Solves`. It is tied to concrete conventions (`SinConventions`): adapted,
every path continuous, the initial values, and `S > 0` on every path. The solution is taken in a
version with all paths continuous and positive, which the source's construction allows (`S` is a
stochastic exponential). Claim 003's admissible models need every path continuous.

## Fields

* `localMartingale`: `S` is a local martingale under `Q`;
* `martingale_iff`, Theorem 3.2: `S` is a martingale (on every finite horizon) iff `a · γ ≤ 0`;
* `equivalent_martingale_measure`, Theorem 3.6: if `a · γ > 0` and the vectors are nonparallel,
  then for every `T > 0` there is a probability `Qᵐ` equivalent to `Q` on `𝓕_T` (`EquivOn`) under
  which `S` is a martingale on `[0, T]`.

The `Qᵐ`-dynamics of `v` are not a field (no use needs them). Neither are horizon-specific measures
equivalent on an infinite-horizon σ-field. `exists_strict_horizon` derives from Theorem 3.2 that
`a · γ > 0` gives some finite `T₀` on which `S` is not a martingale. It is not strengthened to every
horizon.

## Instance: VACUOUS

`SinPricingMeasures.vacuousInstance` is on the one-point base with `W₁ = W₂ ≡ 0`. Every field is
discharged by refuting the Brownian premise (`not_isFBrownian_unit`). No degenerate non-vacuous model
is within reach: a model needs a two-dimensional Brownian motion, which Mathlib does not construct.
Also, a constant process cannot witness the strictness conclusion, as the ledger notes.

## Convention checks (`sin_parameter_check`, `sin_conventions_check`, `sin_conclusion_check`)

* the D8 choice `α = κ = L = 1`, `γ = (1, 0)`, `a = (1, 1)` is valid, with `a · γ = 1 > 0` and
  nonparallel `1 < 2`;
* the conventions hold for constant paths on the one-point base;
* `EquivOn` is reflexive;
* every conclusion predicate is inhabited on both sides: a martingale, a non-martingale (the killed
  exponential of `Upstream/MartingaleCriterion.lean`), and martingales on `[0, T]`.

These catch a mis-stated convention, not a premise contradiction.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace Upstream

open Diffusion

namespace Sin

/-- `a · γ` in `ℝ²`. -/
def dot (a γ : ℝ × ℝ) : ℝ := a.1 * γ.1 + a.2 * γ.2

/-- `|a|²` in `ℝ²` (Euclidean). -/
def sqNorm (a : ℝ × ℝ) : ℝ := a.1 ^ 2 + a.2 ^ 2

/-- Nonparallel: `|a · γ| < |a||γ|`, written as `(a · γ)² < |a|²|γ|²`. -/
def Nonparallel (a γ : ℝ × ℝ) : Prop := dot a γ ^ 2 < sqNorm a * sqNorm γ

/-- Parameters of Sin's model (the source's `σ`, `ρ` renamed `γ`, `κ`). -/
structure SinParams where
  α : ℝ
  κ : ℝ
  L : ℝ
  γ : ℝ × ℝ
  a : ℝ × ℝ
  s₀ : ℝ

/-- The source's restrictions with constant coefficients (Section 2, Assumption 3.1). -/
def SinParams.Valid (p : SinParams) : Prop :=
  0 < p.α ∧ 0 < p.κ ∧ 0 < p.L ∧ p.γ ≠ 0 ∧ p.a ≠ 0 ∧ 0 < p.s₀

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `(W₁, W₂)` is a two-dimensional `(𝓕, Q)`-Brownian motion. -/
def IsFBrownian2 (𝓕 : Filtration ℝ≥0 mΩ) (W₁ W₂ : ℝ≥0 → Ω → ℝ) (Q : Measure Ω) : Prop :=
  IsFBrownian 𝓕 W₁ Q ∧ IsFBrownian 𝓕 W₂ Q ∧
    IndepFun (fun ω t => W₁ t ω) (fun ω t => W₂ t ω) Q ∧
    ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => (W₁ t ω - W₁ s ω, W₂ t ω - W₂ s ω)) inferInstance)
        (𝓕 s) Q

/-- `Q₁` and `Q₂` are equivalent on `𝓕_T`. -/
def EquivOn (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (Q₁ Q₂ : Measure Ω) : Prop :=
  Q₁.trim (𝓕.le T) ≪ Q₂.trim (𝓕.le T) ∧ Q₂.trim (𝓕.le T) ≪ Q₁.trim (𝓕.le T)

/-- Concrete conventions of a solution: adapted, continuous, initial values, `S > 0`. -/
structure SinConventions (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (p : SinParams)
    (S v : ℝ≥0 → Ω → ℝ) : Prop where
  adapted_S : Adapted 𝓕 S
  adapted_v : Adapted 𝓕 v
  start : ∀ ω, S 0 ω = p.s₀ ∧ v 0 ω = 1
  cont : ∀ ω, Continuous (fun t => S t ω) ∧ Continuous (fun t => v t ω)
  pos : ∀ ω, ∀ t, 0 < S t ω

/-- The undefinable notion: `(S, v)` solves Sin's system driven by `(W₁, W₂)`. -/
structure SinPrimitives (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W₁ W₂ : ℝ≥0 → Ω → ℝ) where
  Solves : SinParams → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop
  solves_conventions : ∀ {p S v}, Solves p S v → SinConventions Q 𝓕 p S v

/-- Degenerate model of `SinPrimitives`: every convention-respecting pair counts. -/
def SinPrimitives.conventional (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W₁ W₂ : ℝ≥0 → Ω → ℝ) :
    SinPrimitives Q 𝓕 W₁ W₂ where
  Solves p S v := SinConventions Q 𝓕 p S v
  solves_conventions h := h

/-- The setting premises shared by all fields. -/
def Setting (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W₁ W₂ : ℝ≥0 → Ω → ℝ) : Prop :=
  IsFBrownian2 𝓕 W₁ W₂ Q ∧ UsualConditions 𝓕 Q ∧
    ∀ s : Set Ω, MeasurableSet[𝓕 0] s → Q s = 0 ∨ Q s = 1

end Sin

open Sin

/-- AX-05, Sin's model. -/
structure SinPricingMeasures {Ω : Type*} {mΩ : MeasurableSpace Ω} (Q : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (W₁ W₂ : ℝ≥0 → Ω → ℝ) (X : SinPrimitives Q 𝓕 W₁ W₂) : Prop where
  /-- `S` is a nonnegative continuous local martingale under `Q`. -/
  localMartingale : ∀ (p : SinParams) (S v : ℝ≥0 → Ω → ℝ),
    Setting Q 𝓕 W₁ W₂ → p.Valid → X.Solves p S v → IsLocalMartingale S 𝓕 Q
  /-- Theorem 3.2: `S` is a martingale iff `a · γ ≤ 0`. -/
  martingale_iff : ∀ (p : SinParams) (S v : ℝ≥0 → Ω → ℝ),
    Setting Q 𝓕 W₁ W₂ → p.Valid → X.Solves p S v → (Martingale S 𝓕 Q ↔ dot p.a p.γ ≤ 0)
  /-- Theorem 3.6: for `a · γ > 0` and nonparallel vectors, an equivalent martingale measure on
  every finite horizon. -/
  equivalent_martingale_measure : ∀ (p : SinParams) (S v : ℝ≥0 → Ω → ℝ),
    Setting Q 𝓕 W₁ W₂ → p.Valid → X.Solves p S v → 0 < dot p.a p.γ → Nonparallel p.a p.γ →
    ∀ T : ℝ≥0, 0 < T → ∃ Qm : Measure Ω, IsProbabilityMeasure Qm ∧ EquivOn 𝓕 T Qm Q ∧
      MartingaleOn T S 𝓕 Qm

namespace Sin

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {Q : Measure Ω}

/-- If `S` is a martingale on every `[0, T]`, `T > 0`, it is a martingale. -/
theorem martingale_of_forall_martingaleOn {S : ℝ≥0 → Ω → ℝ}
    (h : ∀ T : ℝ≥0, 0 < T → MartingaleOn T S 𝓕 Q) : Martingale S 𝓕 Q := by
  refine ⟨fun t => ?_, fun i j hij => ?_⟩
  · have := (h (t + 1) (by positivity)).1 t
    simpa [stopAt, min_eq_left (le_add_of_nonneg_right zero_le_one)] using this
  · have := (h (j + 1) (by positivity)).2 i j hij
    simpa [stopAt, min_eq_left (le_add_of_nonneg_right zero_le_one),
      min_eq_left (hij.trans (le_add_of_nonneg_right zero_le_one))] using this

/-- From Theorem 3.2: `a · γ > 0` gives some finite horizon on which `S` is not a martingale. -/
theorem exists_strict_horizon {W₁ W₂ : ℝ≥0 → Ω → ℝ} {X : SinPrimitives Q 𝓕 W₁ W₂}
    (U : SinPricingMeasures Q 𝓕 W₁ W₂ X) {p : SinParams} {S v : ℝ≥0 → Ω → ℝ}
    (hset : Setting Q 𝓕 W₁ W₂) (hp : p.Valid) (hS : X.Solves p S v) (hdot : 0 < dot p.a p.γ) :
    ∃ T₀ : ℝ≥0, 0 < T₀ ∧ ¬ MartingaleOn T₀ S 𝓕 Q := by
  by_contra h
  push Not at h
  have := (U.martingale_iff p S v hset hp hS).1 (martingale_of_forall_martingaleOn h)
  linarith

end Sin

/-- **Vacuous** instance on the one-point base: every field is discharged by refuting the Brownian
premise. See the file header. -/
theorem SinPricingMeasures.vacuousInstance :
    SinPricingMeasures (Measure.dirac ()) unitFiltration unitW unitW
      (SinPrimitives.conventional (Measure.dirac ()) unitFiltration unitW unitW) where
  localMartingale _ _ _ h := absurd h.1.1 not_isFBrownian_unit
  martingale_iff _ _ _ h := absurd h.1.1 not_isFBrownian_unit
  equivalent_martingale_measure _ _ _ h := absurd h.1.1 not_isFBrownian_unit

/-! ## Convention checks -/

namespace Sin

/-- D8's parameters: `α = κ = L = 1`, `γ = (1, 0)`, `a = (1, 1)`, any `s₀ > 0`. -/
def d8Params (s₀ : ℝ) : SinParams := ⟨1, 1, 1, (1, 0), (1, 1), s₀⟩

theorem sin_parameter_check {s₀ : ℝ} (hs₀ : 0 < s₀) :
    (d8Params s₀).Valid ∧ dot (d8Params s₀).a (d8Params s₀).γ = 1 ∧
      Nonparallel (d8Params s₀).a (d8Params s₀).γ := by
  refine ⟨⟨one_pos, one_pos, one_pos, by simp [d8Params], by simp [d8Params], hs₀⟩, ?_, ?_⟩
  · simp [dot, d8Params]
  · simp [Nonparallel, dot, sqNorm, d8Params]

/-- The conventions hold for constant paths on the one-point base; `EquivOn` is reflexive. -/
theorem sin_conventions_check {s₀ : ℝ} (hs₀ : 0 < s₀) (T : ℝ≥0) :
    SinConventions (Measure.dirac ()) unitFiltration (d8Params s₀) (fun _ _ => s₀) (fun _ _ => 1) ∧
      EquivOn unitFiltration T (Measure.dirac ()) (Measure.dirac ()) :=
  ⟨⟨fun _ => measurable_const, fun _ => measurable_const, fun _ => ⟨rfl, rfl⟩,
    fun _ => ⟨continuous_const, continuous_const⟩, fun _ _ => hs₀⟩, ⟨le_rfl.absolutelyContinuous, le_rfl.absolutelyContinuous⟩⟩

/-- Every conclusion predicate is inhabited on both sides on the one-point base. -/
theorem sin_conclusion_check {s₀ : ℝ} (T : ℝ≥0) :
    IsLocalMartingale (fun _ _ => s₀) unitFiltration (Measure.dirac ()) ∧
      Martingale (fun _ _ => s₀) unitFiltration (Measure.dirac ()) ∧
      MartingaleOn T (fun _ _ => s₀) unitFiltration (Measure.dirac ()) ∧
      ¬ Martingale rampKilled unitFiltration (Measure.dirac ()) ∧
      ¬ MartingaleOn 2 rampKilled unitFiltration (Measure.dirac ()) :=
  ⟨isLocalMartingale_of_martingale (martingale_const _ _ _), martingale_const _ _ _,
    martingale_const _ _ _, MartingaleCriterion.mu_killed_check.1,
    MartingaleCriterion.mu_killed_check.2⟩

end Sin

end Upstream
