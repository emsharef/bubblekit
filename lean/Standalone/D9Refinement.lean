import Standalone.D9FiniteGrid
import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Claim 007 (D9): grid refinement, the stochastic-exponential limit before zero

Statement only; the proof is `Novel/D9RefinementProof.lean`. Source claim:
`claims/007-d9-refinement.md`.

**Inputs.** The statement is conditional on AX-06 (claim 004's restatement), AX-10, AX-11 and AX-14,
restated below because a statement may import only Mathlib and other statements. The proof file
derives the restated `AX10`, `AX11` and `AX14` from `Upstream.EmeryStability`,
`Upstream.ContinuousHittingTimes` and `Upstream.StochasticIntegration`.
* The stochastic integral and the bracket cannot be defined in Mathlib. They are relations
  `Integral K X I` ("`I = ∫ K dX`") and `Bracket L A` ("`A = ⟨L⟩`"), quantified over; `AX14` and
  `AX10` are the cited properties of such a pair.
* AX-08's identification of the finite gain sum with an elementary integral is `AX14.elementary`,
  as in the Upstream structure.

**Setting.** Claim 004's `Setting` under `Q`, with `X` held constant after `T`, and any real
exposure `π`.
* `Grids`: finite deterministic grids `g n 0 = 0 < … < g n (N n) = T`, whose mesh tends to `0`.
  They need not be nested.
* `W n = gridWealth π X (N n) (g n)` is the recursion (1) (claims 004–005), with continuous
  interpolation and a freeze in cash at a zero-price rebalance.
* `rho X T m = min(inf{t : X_t ∈ (−∞, 1/m) ∪ (m, ∞)}, T)` is (2), entry into an open set.
  `Xm X T m` is `X` stopped there, and `stoppedW` is `W n` read at `t ∧ ρ_m`.
* `expo π L A = exp(πL − π²A/2)` is (3), for `L` an integral of `1/Xᵐ` against `Xᵐ` and `A` its
  bracket.
* `PathConv` is (6), for bounded measurable functionals of the path on `[0, T]` that are Lipschitz
  in the uniform norm on continuous paths. Asking `G` to be defined and measurable on all paths
  costs nothing: a function measurable on continuous paths, with the trace σ-algebra, extends
  measurably, and a bounded one stays bounded after truncation.
* `UIConv` is (7), under the stated uniform-integrability hypothesis.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D9Refinement

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-! ## Stochastic-integration vocabulary (AX-14) -/

/-- A continuous local martingale, in a version with every path continuous. -/
structure ContLocMart (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) : Prop where
  adapted : Adapted 𝓕 X
  cont : ∀ ω, Continuous fun t => X t ω
  localMart : IsLocalMartingale X 𝓕 Q

/-- An admissible integrand: progressively measurable and pathwise locally bounded. -/
structure Integrand (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (K : ℝ≥0 → Ω → ℝ) : Prop where
  progressive : IsStronglyProgressive 𝓕 K
  locBdd : ∀ᵐ ω ∂Q, ∀ T : ℝ≥0, ∃ C, ∀ t ≤ T, |K t ω| ≤ C

/-- The left-continuous step integrand on the grid `g 0 = 0 < … < g N`: `h i` on `(g i, g (i+1)]`,
`h N` after `g N`, and `h 0` at `0`. -/
noncomputable def elemIntegrand (g : ℕ → ℝ≥0) (N : ℕ) (h : ℕ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  open Classical in h (Nat.findGreatest (fun i => g i < t) N) ω

/-- The finite predictable sum `Σ_{i<N} hᵢ (M_{t∧gᵢ₊₁} − M_{t∧gᵢ}) + h_N (M_t − M_{t∧g_N})`. -/
def elemGain (M : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) (N : ℕ) (h : ℕ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, h i ω * (M (min t (g (i + 1))) ω - M (min t (g i)) ω) +
    h N ω * (M t ω - M (min t (g N)) ω)

/-- `exp(πL − π²A/2)`. -/
noncomputable def expo (π : ℝ) (L A : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (π * L t ω - π ^ 2 / 2 * A t ω)

/-- AX-14 restated ([etheridge2018continuous] §§6–7, as specialized in the ledger), for relations
`Integral K X I` ("`I = ∫ K dX`") and `Bracket L A` ("`A = ⟨L⟩`") on one base. -/
structure AX14 (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop)
    (Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop) : Prop where
  integral_zero : ∀ {K X I}, Integral K X I → ∀ ω, I 0 ω = 0
  bracket_conventions : ∀ {L A}, Bracket L A → Adapted 𝓕 A ∧ (∀ ω, A 0 ω = 0) ∧
    (∀ ω, Continuous fun t => A t ω) ∧ ∀ ω, Monotone fun t => A t ω
  bracket_congr : ∀ {L L' A}, Bracket L A → (∀ᵐ ω ∂Q, ∀ t, L t ω = L' t ω) → Bracket L' A
  integral_exists : ∀ (K X : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q →
    UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → Integrand Q 𝓕 K → ∃ L, Integral K X L
  integral_contLocMart : ∀ (K X L : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q →
    UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → Integrand Q 𝓕 K → Integral K X L →
    ContLocMart Q 𝓕 L
  integral_unique : ∀ (K X L L' : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q →
    UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → Integrand Q 𝓕 K → Integral K X L →
    Integral K X L' → ∀ᵐ ω ∂Q, ∀ t, L t ω = L' t ω
  bracket_exists : ∀ (L : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q → UsualConditions 𝓕 Q →
    ContLocMart Q 𝓕 L → ∃ A, Bracket L A
  bracket_unique : ∀ (L A A' : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q →
    UsualConditions 𝓕 Q → ContLocMart Q 𝓕 L → Bracket L A → Bracket L A' →
    ∀ᵐ ω ∂Q, ∀ t, A t ω = A' t ω
  bracket_density : ∀ (K X L b : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q →
    UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → Integrand Q 𝓕 K →
    (∀ ω, Continuous fun t => b t ω) → (∀ t ω, 0 ≤ b t ω) →
    Bracket X (fun t ω => ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal ω) → Integral K X L →
    ∃ A, Bracket L A ∧ ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      A t ω = ∫ s in (0 : ℝ)..(t : ℝ), K s.toNNReal ω ^ 2 * b s.toNNReal ω
  stop_contLocMart : ∀ (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0), IsProbabilityMeasure Q →
    UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → IsStoppingTime 𝓕 τ →
    ContLocMart Q 𝓕 (stoppedProcess X τ)
  stop_integral : ∀ (K X L : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0), IsProbabilityMeasure Q →
    UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → Integrand Q 𝓕 K → IsStoppingTime 𝓕 τ →
    Integral K X L → Integral K (stoppedProcess X τ) (stoppedProcess L τ)
  stop_local : ∀ (K K' X L L' : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0), IsProbabilityMeasure Q →
    UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → Integrand Q 𝓕 K → Integrand Q 𝓕 K' →
    IsStoppingTime 𝓕 τ → (∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω → K t ω = K' t ω) →
    Integral K X L → Integral K' X L' →
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω → L t ω = L' t ω
  stop_bracket : ∀ (L A : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0), IsProbabilityMeasure Q →
    UsualConditions 𝓕 Q → ContLocMart Q 𝓕 L → IsStoppingTime 𝓕 τ → Bracket L A →
    Bracket (stoppedProcess L τ) (stoppedProcess A τ)
  assoc : ∀ (H K X L I : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q → UsualConditions 𝓕 Q →
    ContLocMart Q 𝓕 X → Integrand Q 𝓕 K → Integrand Q 𝓕 H → Integral K X L → Integral H L I →
    Integral (fun t ω => H t ω * K t ω) X I
  exponential : ∀ (L A : ℝ≥0 → Ω → ℝ) (π : ℝ), IsProbabilityMeasure Q →
    UsualConditions 𝓕 Q → ContLocMart Q 𝓕 L → (∀ ω, L 0 ω = 0) → Bracket L A →
    ContLocMart Q 𝓕 (expo π L A) ∧
      Integral (fun t ω => π * expo π L A t ω) L (fun t ω => expo π L A t ω - 1)
  elementary : ∀ (M : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) (N : ℕ) (h : ℕ → Ω → ℝ),
    IsProbabilityMeasure Q → UsualConditions 𝓕 Q → ContLocMart Q 𝓕 M → StrictMono g →
    g 0 = 0 → (∀ i ≤ N, Measurable[𝓕 (g i)] (h i)) →
    Integral (elemIntegrand g N h) M (elemGain M g N h)

/-! ## Stability vocabulary (AX-10) -/

/-- Émery's `D`: adapted processes with càdlàg paths. -/
structure IsD (𝓕 : Filtration ℝ≥0 mΩ) (U : ℝ≥0 → Ω → ℝ) : Prop where
  adapted : Adapted 𝓕 U
  cadlag : ∀ ω, IsCadlag fun t => U t ω

/-- Convergence uniformly on compacts in probability. -/
def TendstoUCP (Q : Measure Ω) (U : ℕ → ℝ≥0 → Ω → ℝ) (V : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ (T : ℝ≥0) (ε : ℝ), 0 < ε →
    Tendsto (fun n => Q {ω | ∃ t ≤ T, ε < |U n t ω - V t ω|}) atTop (𝓝 0)

/-- The left-limit process `t ↦ Z_{t−}`. -/
noncomputable def leftLimProc (Z : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Function.leftLim (fun s => Z s ω) t

/-- An operator maps `D` to `D`. -/
def MapsD (𝓕 : Filtration ℝ≥0 mΩ) (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ U, IsD 𝓕 U → IsD 𝓕 (F U)

/-- Nonanticipation, for inputs in `D`. -/
def Nonanticipating (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ (U V : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0), IsD 𝓕 U → IsD 𝓕 V → IsStoppingTime 𝓕 τ →
    (∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < τ ω → U t ω = V t ω) →
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < τ ω → F U t ω = F V t ω

/-- Lip(a), in the global-supremum form, for inputs in `D`. -/
def LipOp (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (a : ℝ)
    (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ U V, IsD 𝓕 U → IsD 𝓕 V → ∀ᵐ ω ∂Q, ∀ C : ℝ, (∀ s, |U s ω - V s ω| ≤ C) →
    ∀ t, |F U t ω - F V t ω| ≤ a * C

/-- The premises shared by the operators of an equation. -/
structure OpAdmissible (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (a : ℝ)
    (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) : Prop where
  mapsD : MapsD 𝓕 F
  nonanticipating : Nonanticipating Q 𝓕 F
  lip : LipOp Q 𝓕 a F

/-- AX-10 restated ([emery1979lipschitz] Theorem 0(a) and Theorem 2, as specialized in the
ledger): existence, uniqueness and ucp stability of `U = H + ∫ F(U)_{s−} dM`. -/
structure AX10 (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop) : Prop where
  exists_solution : ∀ (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) (a : ℝ) (H M : ℝ≥0 → Ω → ℝ),
    IsProbabilityMeasure Q → UsualConditions 𝓕 Q → 0 < a → OpAdmissible Q 𝓕 a F →
    IsD 𝓕 H → ContLocMart Q 𝓕 M →
    ∃ U, IsD 𝓕 U ∧ Integral (leftLimProc (F U)) M (fun t ω => U t ω - H t ω)
  unique_solution : ∀ (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) (a : ℝ) (H M U U' : ℝ≥0 → Ω → ℝ),
    IsProbabilityMeasure Q → UsualConditions 𝓕 Q → 0 < a → OpAdmissible Q 𝓕 a F →
    IsD 𝓕 H → ContLocMart Q 𝓕 M → IsD 𝓕 U → IsD 𝓕 U' →
    Integral (leftLimProc (F U)) M (fun t ω => U t ω - H t ω) →
    Integral (leftLimProc (F U')) M (fun t ω => U' t ω - H t ω) →
    ∀ᵐ ω ∂Q, ∀ t, U t ω = U' t ω
  stable : ∀ (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) (Fn : ℕ → (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ)
    (a : ℝ) (H M U : ℝ≥0 → Ω → ℝ) (Un : ℕ → ℝ≥0 → Ω → ℝ),
    IsProbabilityMeasure Q → UsualConditions 𝓕 Q → 0 < a → OpAdmissible Q 𝓕 a F →
    (∀ n, OpAdmissible Q 𝓕 a (Fn n)) → IsD 𝓕 H → ContLocMart Q 𝓕 M →
    IsD 𝓕 U → Integral (leftLimProc (F U)) M (fun t ω => U t ω - H t ω) →
    (∀ n, IsD 𝓕 (Un n) ∧
      Integral (leftLimProc (Fn n (Un n))) M (fun t ω => Un n t ω - H t ω)) →
    TendstoUCP Q (fun n => Fn n U) (F U) → TendstoUCP Q Un U

/-! ## Hitting times (AX-11) -/

/-- First entry into a set, with `inf ∅ = ∞`. -/
noncomputable def openHitTime (S : ℝ≥0 → Ω → ℝ) (Γ : Set ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf ((fun t : ℝ≥0 => (t : WithTop ℝ≥0)) '' {t | S t ω ∈ Γ})

/-- AX-11 restated ([etheridge2018continuous] Exercise 4.5(i), continuous case), on one
filtration. -/
def AX11 (𝓕 : Filtration ℝ≥0 mΩ) : Prop :=
  ∀ S : ℝ≥0 → Ω → ℝ, 𝓕.IsRightContinuous → Adapted 𝓕 S → (∀ ω, Continuous fun t => S t ω) →
    ∀ Γ : Set ℝ, IsOpen Γ → IsStoppingTime 𝓕 (openHitTime S Γ)

/-! ## The objects of the claim -/

/-- Finite deterministic grids `0 = g n 0 < … < g n (N n) = T` whose mesh tends to `0`. -/
def Grids (T : ℝ≥0) (g : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ) : Prop :=
  (∀ n, g n 0 = 0 ∧ StrictMono (g n) ∧ g n (N n) = T) ∧
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ i < N n, ((g n (i + 1) : ℝ) - g n i) < δ

/-- The open band complement `(−∞, 1/m) ∪ (m, ∞)`. -/
def band (m : ℕ) : Set ℝ := {x | x < 1 / (m : ℝ) ∨ (m : ℝ) < x}

/-- `ρ_m`, (2). -/
noncomputable def rho (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (m : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  min (openHitTime X (band m) ω) T

/-- `Xᵐ_t = X_{t∧ρ_m}`, (2). -/
noncomputable def Xm (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (m : ℕ) : ℝ≥0 → Ω → ℝ :=
  stoppedProcess X (rho X T m)

/-- The recursion read at `t ∧ ρ_m`. -/
noncomputable def stoppedW (π : ℝ) (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (m : ℕ) (g : ℕ → ℕ → ℝ≥0)
    (N : ℕ → ℕ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  gridWealth π X (N n) (g n) (min (t : WithTop ℝ≥0) (rho X T m ω)).untopA ω

/-- (6): bounded functionals of the path on `[0, T]`, Lipschitz in the uniform norm on continuous
paths, converge in expectation. -/
def PathConv (Q : Measure Ω) (T : ℝ≥0) (U : ℕ → ℝ≥0 → Ω → ℝ) (V : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ (G : (Icc (0 : ℝ≥0) T → ℝ) → ℝ) (B C : ℝ), Measurable G → (∀ x, |G x| ≤ B) →
    (∀ x y : Icc (0 : ℝ≥0) T → ℝ, Continuous x → Continuous y → ∀ D : ℝ,
      (∀ t, |x t - y t| ≤ D) → |G x - G y| ≤ C * D) →
    Tendsto (fun n => ∫ ω, G (fun t => U n t.1 ω) ∂Q) atTop
      (𝓝 (∫ ω, G (fun t => V t.1 ω) ∂Q))

/-- (7): under uniform integrability of the terminal values, `L¹` and defect convergence. -/
def UIConv (Q : Measure Ω) (T : ℝ≥0) (U : ℕ → ℝ≥0 → Ω → ℝ) (V : ℝ≥0 → Ω → ℝ) : Prop :=
  UniformIntegrable (fun n ω => U n T ω) 1 Q →
    Tendsto (fun n => ∫ ω, |U n T ω - V T ω| ∂Q) atTop (𝓝 0) ∧
      Tendsto (fun n => 1 - ∫ ω, U n T ω ∂Q) atTop (𝓝 (1 - ∫ ω, V T ω ∂Q))

/-- Claim 007. -/
def statement : Prop :=
  AX06.{u} →
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop)
    (Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop),
    AX14 Q 𝓕 Integral Bracket → AX10 Q 𝓕 Integral → AX11 𝓕 →
  ∀ (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (g : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ) (π : ℝ),
    Setting Q 𝓕 X T → 0 < T → (∀ t ω, X t ω = X (min t T) ω) → Grids T g N →
    -- (2)–(4), (6), (7) for the stopped recursion, every `m > 1`.
    (∀ m : ℕ, 1 < m →
      IsStoppingTime 𝓕 (rho X T m) ∧
      (∀ t ω, 1 / (m : ℝ) ≤ Xm X T m t ω ∧ Xm X T m t ω ≤ m) ∧
      (∃ L A, Integral (fun t ω => 1 / Xm X T m t ω) (Xm X T m) L ∧ Bracket L A) ∧
      ∀ L A, Integral (fun t ω => 1 / Xm X T m t ω) (Xm X T m) L → Bracket L A →
        (∀ ε : ℝ, 0 < ε → Tendsto (fun n => Q {ω | ∃ t ≤ T,
          ε < |stoppedW π X T m g N n t ω - expo π L A t ω|}) atTop (𝓝 0)) ∧
        PathConv Q T (stoppedW π X T m g N) (expo π L A) ∧
        UIConv Q T (stoppedW π X T m g N) (expo π L A)) ∧
    -- (5), the breach limit, (6), (7) and the D1 identification, under strict positivity.
    ((∀ᵐ ω ∂Q, ∀ t ≤ T, 0 < X t ω) →
      (∃ L A, Integral (fun t ω => 1 / X t ω) X L ∧ Bracket L A) ∧
      ∀ L A, Integral (fun t ω => 1 / X t ω) X L → Bracket L A →
        (∀ ε : ℝ, 0 < ε → Tendsto (fun n => Q {ω | ∃ t ≤ T,
          ε < |gridWealth π X (N n) (g n) t ω - expo π L A t ω|}) atTop (𝓝 0)) ∧
        Tendsto (fun n => Q {ω | ∃ t ≤ T, gridWealth π X (N n) (g n) t ω ≤ 0}) atTop (𝓝 0) ∧
        PathConv Q T (fun n => gridWealth π X (N n) (g n)) (expo π L A) ∧
        UIConv Q T (fun n => gridWealth π X (N n) (g n)) (expo π L A) ∧
        ∀ (σ : ℝ → ℝ) (Wb : ℝ≥0 → Ω → ℝ), Measurable σ →
          (∀ a b : ℝ, 0 < a → ∃ C, ∀ x ∈ Icc a b, |σ x| ≤ C) →
          ContLocMart Q 𝓕 Wb → Bracket Wb (fun t _ => (t : ℝ)) →
          Integral (fun t ω => if t ≤ T then σ (X t ω) else 0) Wb (fun t ω => X t ω - 1) →
          (∃ J, Integral (fun t ω => if t ≤ T then bPi π σ (X t ω) else 0) Wb J ∧
            ∀ᵐ ω ∂Q, ∀ t, J t ω = π * L t ω) ∧
          ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, π ^ 2 * A t ω = ∫ s in (0 : ℝ)..(t : ℝ),
            (if s.toNNReal ≤ T then bPi π σ (X s.toNNReal ω) else 0) ^ 2)

end Standalone.D9Refinement
