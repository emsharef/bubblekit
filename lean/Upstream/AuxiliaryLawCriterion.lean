import Upstream.Diffusion
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# AX-64  Auxiliary-law energy criterion for stochastic exponentials

Ledger entry AX-64 (`ledger/AXIOMS.md`). Source: [ruf2015martingale], Definition 2.1,
Assumptions 2.2–2.3, the construction of §2.2 including (2.1), Proposition 3.1 and Theorem 3.3
(printed pp. 2–5), with Remarks 3.2 and 3.5. Our notation: the source's original law `P` is `Q`, its
auxiliary `Q` is `Q_aux`, and its `b` and `µ` are `b_R` and `μ_R`.

## The canonical space (concrete)

`CanonicalSpace d E Ω`, for `E ⊆ ℝ^d`: a coordinate `X`, a cemetery time `ζ` and the filtration `𝓕`.
Every path lies in `E` and is continuous on `[0, ζ)` (`mem_before`, `cont_before`), and `ζ` is a
stopping time. Values at and after `ζ` stand for the cemetery `∆` and are never read: membership in
a closed `F ⊆ E` fails there by definition (`rho`). The space is a structure, so the source's own
canonical space is one model; the fields hold for it. Paths that never reach the cemetery are not
the whole space: `ζ` may be finite.

## §2.2, defined in full

Over coefficients `a` (matrices), `b_R` and `μ_R` (vectors), and a closed exhaustion `(E_n)`:
* the energy density `μ_Rᵀ a μ_R` (`edens`) and the integrals `∫₀^(t∧η)` in `[0, ∞]`
  (`energyUpTo`);
* `ρ_F` (`rho`);
* `τ̃_n = inf{t : ∫₀^t μ_Rᵀ a μ_R > n}`, with the unlocalized integral (`Atil`);
* `θ_n = τ̃_n ∧ ρ_(E_n) ∧ n` and `θ = lim θ_n`;
* `⟨M⟩_t = ∫₀^(t∧θ) μ_Rᵀ a μ_R` (`Aloc`; `t = ∞` gives `A_∞`) and `τ_n = inf{t : ⟨M⟩_t > n}`;
* the stopped σ-field (`InStopped`) and `(Z stopped at τ_n)_∞` (`Zterm`);
* Proposition 3.1's density identities (`DensityId`) and Assumption 2.3 (`NoJump`, with
  `∫₀^(t∧ζ)`).

## The undefinable primitives

Mathlib has no stochastic integral, so three notions are opaque relations in `MPPrimitives`. Each is
tied by a field to the conventions it must obey:
* `Solves Q x₀ a b (E_n)`: Definition 2.1, first bullet. The conventions are `Q(X₀ = x₀) = 1`,
  `(E_n)` closed, nondecreasing and exhausting `E`, and `Q(ρ_(E_n) = ζ < ∞) = 0` (`SolvesConventions`).
  The generator local-martingale clause stays opaque.
* `SolvesOn Q x₀ a b η`: Definition 2.1, second bullet, on `[[0, η[[`. It is opaque.
* `StochExp Q a b μ (E_n) Z`: `Z` is (2.1). The conventions (`ExpConventions`) are:
  - `Z₀ = 1`, `Z ≥ 0`, and `Z > 0` before `θ`;
  - `Z` is continuous, and frozen at its value at `θ` afterward, which is the source's left limit;
  - `Z` is a local martingale, each `Z^(τ_n)` is a uniformly integrable martingale, and each `τ_n`
    is a stopping time.

  All of these are almost sure, simultaneously in `t`, except the stopping-time property.

## Fields

For a probability `Q`, a start `x₀ ∈ E`, coefficients satisfying the source's measurability and
positivity (`CoeffHyp`), `Solves`, Assumption 2.3 and `StochExp`:
* `exists_aux`, Proposition 3.1: some `Q_aux` solves the shifted problem `(a, b_R + aμ_R)` on
  `[[0, θ[[` and satisfies the density identities for every `n ≥ 1`;
* `mart_iff` and `ui_iff`, Theorem 3.3, for **every** such `Q_aux`, as Remark 3.5 allows: `Z` is a
  martingale iff `Q_aux(⟨M⟩_t < ∞) = 1` for all `t`; and `Z` is a uniformly integrable martingale
  iff `Q_aux(⟨M⟩_θ < ∞) = 1`. These use Mathlib's `Martingale` and `UniformIntegrable`.

Neither energy finiteness nor any application conclusion is a premise. Corollary 3.4 is not a field.

## Instance: degenerate, NOT vacuous

`degenerateInstance` uses the ledger's model.
* **The model.** `E = ℝ^d`, one constant path at `0` with `ζ = ∞`, the Dirac law and closed balls
  `E_n`.
* **The primitives (`degeneratePrimitives`).** They accept only zero coefficients (`a = 0`,
  `b_R = 0`) and `Z = 1`. This is a sub-relation of the true one on this space: the constant path
  solves Definition 2.1 for zero coefficients. It is not the true relation.
* **Why every field holds.** The energy vanishes, `τ_n = ∞`, `Z = 1` and `Q_aux = Q`. Both sides of
  each equivalence are true.
* **Non-vacuous.** `premises_sat` shows the field premises are satisfiable on this instance.

## Convention checks

* `degenerate_theta`: `θ = ∞` on the constant path. All `θ_n = n` are finite while their limit is
  not, so `θ_n` are not `τ_n`.
* `energy_top_check`: a unit density has infinite energy up to `∞` and finite energy up to any finite
  time. So `⟨M⟩_∞ < ∞` is a real condition, not a type-level triviality.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal

namespace Upstream.AuxLaw

open Diffusion

/-! ## The canonical space -/

/-- [ruf2015martingale]'s canonical space for `E ⊆ ℝ^d`: coordinate `X`, cemetery time `ζ`, and the
right-continuous natural filtration `𝓕`. -/
structure CanonicalSpace (d : ℕ) (E : Set (Fin d → ℝ)) (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  𝓕 : Filtration ℝ≥0 mΩ
  X : ℝ≥0 → Ω → (Fin d → ℝ)
  ζ : Ω → ℝ≥0∞
  mem_before : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < ζ ω → X t ω ∈ E
  cont_before : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < ζ ω → ContinuousOn (fun s => X s ω) (Iic t)
  ζ_stop : ∀ T : ℝ≥0, MeasurableSet[𝓕 T] {ω | ζ ω ≤ T}

variable {d : ℕ} {E : Set (Fin d → ℝ)} {Ω : Type*} [MeasurableSpace Ω]

/-! ## §2.2 -/

/-- `ρ_F = inf{t ≥ 0 : X_t ∉ F}`; the cemetery lies outside `F`. -/
noncomputable def rho (C : CanonicalSpace d E Ω) (F : Set (Fin d → ℝ)) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : C.ζ ω ≤ s ∨ C.X s ω ∉ F), (s : ℝ≥0∞)

/-- `∫₀^(t∧η) e(s) ds ∈ [0, ∞]`. -/
noncomputable def energyUpTo (e : ℝ≥0 → Ω → ℝ≥0∞) (η : Ω → ℝ≥0∞) (t : ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Ioi (0 : ℝ),
    if (s.toNNReal : ℝ≥0∞) < t ∧ (s.toNNReal : ℝ≥0∞) < η ω then e s.toNNReal ω else 0

/-- `inf{t ≥ 0 : f(t) > n}`. -/
noncomputable def hit (f : ℝ≥0 → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : (n : ℝ≥0∞) < f t), (t : ℝ≥0∞)

/-- The energy density `μ_Rᵀ a μ_R`. -/
noncomputable def edens (a : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (μ : ℝ≥0 → Ω → (Fin d → ℝ))
    (s : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (μ s ω ⬝ᵥ (a s ω *ᵥ μ s ω))

section Localization

variable (C : CanonicalSpace d E Ω) (a : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
  (μ : ℝ≥0 → Ω → (Fin d → ℝ)) (En : ℕ → Set (Fin d → ℝ))

/-- `∫₀^t μ_Rᵀ a μ_R`, the integral defining `τ̃_n`. -/
noncomputable def Atil (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ := energyUpTo (edens a μ) (fun _ => ⊤) t ω

/-- `∫₀^(t∧ζ) μ_Rᵀ a μ_R`, the integral of Assumption 2.3. -/
noncomputable def AtilZ (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ := energyUpTo (edens a μ) C.ζ t ω

/-- `θ_n = τ̃_n ∧ ρ_(E_n) ∧ n`. -/
noncomputable def thetaN (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  min (min (hit (fun t => Atil a μ t ω) n) (rho C (En n) ω)) n

/-- `θ = lim θ_n`. -/
noncomputable def theta (ω : Ω) : ℝ≥0∞ := ⨆ n, thetaN C a μ En n ω

/-- `⟨M⟩_t = ∫₀^(t∧θ) μ_Rᵀ a μ_R`; `t = ∞` gives `⟨M⟩_θ`. -/
noncomputable def Aloc (t : ℝ≥0∞) (ω : Ω) : ℝ≥0∞ := energyUpTo (edens a μ) (theta C a μ En) t ω

/-- `τ_n = inf{t ≥ 0 : ⟨M⟩_t > n}`. -/
noncomputable def tau (n : ℕ) (ω : Ω) : ℝ≥0∞ := hit (fun t => Aloc C a μ En t ω) n

end Localization

/-- `(Z stopped at τ)_∞`: `Z_τ` where `τ` is finite, and `lim_(t→∞) Z_t` where it is not. -/
noncomputable def Zterm (Z : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞) (ω : Ω) : ℝ :=
  if τ ω = ⊤ then limUnder atTop (fun t => Z t ω) else Z (τ ω).toNNReal ω

/-- `Z` stopped at `τ`. -/
noncomputable def stoppedAt (Z : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if τ ω ≤ t then Z (τ ω).toNNReal ω else Z t ω

/-- `B` lies in the stopped σ-field at `τ`. -/
def InStopped (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (τ : Ω → ℝ≥0∞) (B : Set Ω) : Prop :=
  MeasurableSet B ∧ ∀ t : ℝ≥0, MeasurableSet[𝓕 t] (B ∩ {ω | τ ω ≤ t})

/-- `f` jumps to `∞`: infinite at some time and bounded before it. -/
def JumpsToTop (f : ℝ≥0 → ℝ≥0∞) : Prop := ∃ t, f t = ⊤ ∧ ∃ c : ℝ≥0, ∀ s < t, f s ≤ c

/-- Assumption 2.3. -/
def NoJump (C : CanonicalSpace d E Ω) (Q : Measure Ω) (a : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (μ : ℝ≥0 → Ω → (Fin d → ℝ)) : Prop :=
  ∀ᵐ ω ∂Q, ¬ JumpsToTop fun t => AtilZ C a μ t ω

/-- Proposition 3.1's stopped-density identities, for `n ≥ 1`. -/
def DensityId (C : CanonicalSpace d E Ω) (a : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (μ : ℝ≥0 → Ω → (Fin d → ℝ)) (En : ℕ → Set (Fin d → ℝ)) (Q : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ) (Qa : Measure Ω) : Prop :=
  ∀ (n : ℕ) (B : Set Ω), InStopped C.𝓕 (tau C a μ En (n + 1)) B →
    Qa B = ∫⁻ ω in B, ENNReal.ofReal (Zterm Z (tau C a μ En (n + 1)) ω) ∂Q

/-- The shifted drift `b̂ = b_R + a μ_R`. -/
def bhat (a : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (b μ : ℝ≥0 → Ω → (Fin d → ℝ)) :
    ℝ≥0 → Ω → (Fin d → ℝ) :=
  fun t ω => b t ω + a t ω *ᵥ μ t ω

/-- Progressive measurability of `a, b_R, μ_R` (entrywise), and `a` symmetric positive
semidefinite. -/
structure CoeffHyp (C : CanonicalSpace d E Ω) (a : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (b μ : ℝ≥0 → Ω → (Fin d → ℝ)) : Prop where
  a_prog : ∀ i j, IsStronglyProgressive C.𝓕 fun t ω => a t ω i j
  b_prog : ∀ i, IsStronglyProgressive C.𝓕 fun t ω => b t ω i
  μ_prog : ∀ i, IsStronglyProgressive C.𝓕 fun t ω => μ t ω i
  a_psd : ∀ t ω, (a t ω).PosSemidef

/-! ## Conventions and primitives -/

/-- The concrete part of Definition 2.1 for `Q` with exhaustion `(E_n)`. -/
structure SolvesConventions (C : CanonicalSpace d E Ω) (Q : Measure Ω) (x₀ : Fin d → ℝ)
    (En : ℕ → Set (Fin d → ℝ)) : Prop where
  start : ∀ᵐ ω ∂Q, C.X 0 ω = x₀ ∧ 0 < C.ζ ω
  closed : ∀ n, IsClosed (En n)
  mono : Monotone En
  cover : ⋃ n, En n = E
  noexit : ∀ n, Q {ω | rho C (En n) ω = C.ζ ω ∧ C.ζ ω < ⊤} = 0

/-- Conventions of the exponential (2.1) and of the source's facts about it (p. 4). -/
structure ExpConventions (C : CanonicalSpace d E Ω) (Q : Measure Ω)
    (a : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (μ : ℝ≥0 → Ω → (Fin d → ℝ))
    (En : ℕ → Set (Fin d → ℝ)) (Z : ℝ≥0 → Ω → ℝ) : Prop where
  start : ∀ᵐ ω ∂Q, Z 0 ω = 1
  nonneg : ∀ᵐ ω ∂Q, ∀ t, 0 ≤ Z t ω
  pos_before : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : ℝ≥0∞) < theta C a μ En ω → 0 < Z t ω
  continuous : ∀ᵐ ω ∂Q, Continuous fun t => Z t ω
  frozen : ∀ᵐ ω ∂Q, ∀ z : ℝ≥0, theta C a μ En ω = z → ∀ t, z ≤ t → Z t ω = Z z ω
  localMartingale : IsLocalMartingale Z C.𝓕 Q
  stopped_ui : ∀ n : ℕ, Martingale (stoppedAt Z (tau C a μ En (n + 1))) C.𝓕 Q ∧
    UniformIntegrable (stoppedAt Z (tau C a μ En (n + 1))) 1 Q
  tau_stop : ∀ (n : ℕ) (t : ℝ≥0), MeasurableSet[C.𝓕 t] {ω | tau C a μ En n ω ≤ t}

/-- The three notions Mathlib cannot define, on a canonical space:
* `Solves Q x₀ a b (E_n)`: `Q` solves Definition 2.1's generalized local martingale problem for
  `(E, x₀, a, b)` with exhaustion `(E_n)`;
* `SolvesOn Q x₀ a b η`: the same on `[[0, η[[` (Definition 2.1, second bullet);
* `StochExp Q a b μ (E_n) Z`: `Z` is (2.1) for `μ` under `Q`, localized by `(E_n)`.

The intended model is the source's. Every theorem over `X : MPPrimitives C` is conditional on `X`
being that model. -/
structure MPPrimitives (C : CanonicalSpace d E Ω) where
  Solves : Measure Ω → (Fin d → ℝ) → (ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) →
    (ℝ≥0 → Ω → (Fin d → ℝ)) → (ℕ → Set (Fin d → ℝ)) → Prop
  SolvesOn : Measure Ω → (Fin d → ℝ) → (ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) →
    (ℝ≥0 → Ω → (Fin d → ℝ)) → (Ω → ℝ≥0∞) → Prop
  StochExp : Measure Ω → (ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) → (ℝ≥0 → Ω → (Fin d → ℝ)) →
    (ℝ≥0 → Ω → (Fin d → ℝ)) → (ℕ → Set (Fin d → ℝ)) → (ℝ≥0 → Ω → ℝ) → Prop
  solves_conventions : ∀ {Q x₀ a b En}, Solves Q x₀ a b En → SolvesConventions C Q x₀ En
  stochExp_conventions : ∀ {Q a b μ En Z}, StochExp Q a b μ En Z → ExpConventions C Q a μ En Z

end Upstream.AuxLaw

namespace Upstream

open AuxLaw

/-- AX-64, [ruf2015martingale] Proposition 3.1 and Theorem 3.3. -/
structure AuxiliaryLawCriterion {d : ℕ} {E : Set (Fin d → ℝ)} {Ω : Type*} [MeasurableSpace Ω]
    (C : CanonicalSpace d E Ω) (X : MPPrimitives C) : Prop where
  /-- Proposition 3.1. -/
  exists_aux : ∀ (Q : Measure Ω) (x₀ : Fin d → ℝ) (a : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
      (b μ : ℝ≥0 → Ω → (Fin d → ℝ)) (En : ℕ → Set (Fin d → ℝ)) (Z : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure Q → x₀ ∈ E → CoeffHyp C a b μ → X.Solves Q x₀ a b En →
      NoJump C Q a μ → X.StochExp Q a b μ En Z →
      ∃ Qa, IsProbabilityMeasure Qa ∧ X.SolvesOn Qa x₀ a (bhat a b μ) (theta C a μ En) ∧
        DensityId C a μ En Q Z Qa
  /-- Theorem 3.3, (3.1), for every law of Proposition 3.1. -/
  mart_iff : ∀ (Q : Measure Ω) (x₀ : Fin d → ℝ) (a : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
      (b μ : ℝ≥0 → Ω → (Fin d → ℝ)) (En : ℕ → Set (Fin d → ℝ)) (Z : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure Q → x₀ ∈ E → CoeffHyp C a b μ → X.Solves Q x₀ a b En →
      NoJump C Q a μ → X.StochExp Q a b μ En Z →
      ∀ Qa, IsProbabilityMeasure Qa → X.SolvesOn Qa x₀ a (bhat a b μ) (theta C a μ En) →
        DensityId C a μ En Q Z Qa →
        (Martingale Z C.𝓕 Q ↔ ∀ t : ℝ≥0, Qa {ω | Aloc C a μ En t ω < ⊤} = 1)
  /-- Theorem 3.3, (3.2), for every law of Proposition 3.1. -/
  ui_iff : ∀ (Q : Measure Ω) (x₀ : Fin d → ℝ) (a : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
      (b μ : ℝ≥0 → Ω → (Fin d → ℝ)) (En : ℕ → Set (Fin d → ℝ)) (Z : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure Q → x₀ ∈ E → CoeffHyp C a b μ → X.Solves Q x₀ a b En →
      NoJump C Q a μ → X.StochExp Q a b μ En Z →
      ∀ Qa, IsProbabilityMeasure Qa → X.SolvesOn Qa x₀ a (bhat a b μ) (theta C a μ En) →
        DensityId C a μ En Q Z Qa →
        (Martingale Z C.𝓕 Q ∧ UniformIntegrable Z 1 Q ↔ Qa {ω | Aloc C a μ En ⊤ ω < ⊤} = 1)

namespace AuxiliaryLawCriterion

/-! ## The degenerate instance -/

/-- One constant path at `0` in `ℝ^d`, never reaching the cemetery. -/
def degenerateSpace (d : ℕ) : CanonicalSpace d univ Unit where
  𝓕 := ⊤
  X := fun _ _ => 0
  ζ := fun _ => ⊤
  mem_before := fun _ _ _ => mem_univ _
  cont_before := fun _ _ _ => continuousOn_const
  ζ_stop := fun _ => Subsingleton.measurableSet

/-- Primitives accepting only zero coefficients and `Z = 1`, with the conventions. A sub-relation of
the source's on this space, not the source's relation. -/
def degeneratePrimitives (d : ℕ) : MPPrimitives (degenerateSpace d) where
  Solves Q x₀ a b En := SolvesConventions (degenerateSpace d) Q x₀ En ∧ a = 0 ∧ b = 0
  SolvesOn _ _ a b _ := a = 0 ∧ b = 0
  StochExp Q a _ μ En Z := ExpConventions (degenerateSpace d) Q a μ En Z ∧ a = 0 ∧ Z = 1
  solves_conventions h := h.1
  stochExp_conventions h := h.1

theorem edens_zero (μ : ℝ≥0 → Unit → (Fin d → ℝ)) : edens (0 : ℝ≥0 → Unit → Matrix _ _ ℝ) μ = 0 := by
  funext s ω
  simp [edens]

theorem energyUpTo_zero (η : Unit → ℝ≥0∞) (t : ℝ≥0∞) (ω : Unit) :
    energyUpTo (0 : ℝ≥0 → Unit → ℝ≥0∞) η t ω = 0 := by
  simp [energyUpTo]

theorem hit_zero (n : ℕ) : hit (fun _ => (0 : ℝ≥0∞)) n = ⊤ := by
  simp [hit]

theorem degenerate_tau (μ : ℝ≥0 → Unit → (Fin d → ℝ)) (En : ℕ → Set (Fin d → ℝ)) (n : ℕ)
    (ω : Unit) : tau (degenerateSpace d) 0 μ En n ω = ⊤ := by
  simp only [tau, Aloc, edens_zero, energyUpTo_zero, hit_zero]

theorem degenerate_Aloc (μ : ℝ≥0 → Unit → (Fin d → ℝ)) (En : ℕ → Set (Fin d → ℝ)) (t : ℝ≥0∞)
    (ω : Unit) : Aloc (degenerateSpace d) 0 μ En t ω = 0 := by
  simp only [Aloc, edens_zero, energyUpTo_zero]

theorem degenerate_density (Q : Measure Unit) (μ : ℝ≥0 → Unit → (Fin d → ℝ))
    (En : ℕ → Set (Fin d → ℝ)) : DensityId (degenerateSpace d) 0 μ En Q 1 Q := by
  intro n B _
  have hZ : ∀ ω, Zterm (1 : ℝ≥0 → Unit → ℝ) (tau (degenerateSpace d) 0 μ En (n + 1)) ω = 1 := by
    intro ω
    simp only [Zterm, degenerate_tau, ite_true]
    exact tendsto_const_nhds.limUnder_eq
  simp only [hZ, ENNReal.ofReal_one, setLIntegral_const, one_mul]

theorem degenerate_mart (Q : Measure Unit) [IsProbabilityMeasure Q] :
    Martingale (1 : ℝ≥0 → Unit → ℝ) (degenerateSpace d).𝓕 Q ∧
      UniformIntegrable (1 : ℝ≥0 → Unit → ℝ) 1 Q :=
  ⟨martingale_const _ _ (1 : ℝ),
    uniformIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const (1 : ℝ))⟩

/-- The degenerate instance: every field holds, with satisfiable premises (`premises_sat`). -/
theorem degenerateInstance (d : ℕ) :
    AuxiliaryLawCriterion (degenerateSpace d) (degeneratePrimitives d) where
  exists_aux Q x₀ a b μ En Z _ _ _ hsol _ hexp := by
    obtain ⟨_, rfl, rfl⟩ := hsol
    obtain ⟨_, -, rfl⟩ := hexp
    refine ⟨Q, inferInstance, ⟨rfl, ?_⟩, degenerate_density Q μ En⟩
    funext t ω
    simp [bhat]
  mart_iff Q x₀ a b μ En Z _ _ _ hsol _ hexp Qa _ _ _ := by
    obtain ⟨_, rfl, rfl⟩ := hsol
    obtain ⟨_, -, rfl⟩ := hexp
    exact iff_of_true (degenerate_mart Q).1 fun t => by simp [degenerate_Aloc]
  ui_iff Q x₀ a b μ En Z _ _ _ hsol _ hexp Qa _ _ _ := by
    obtain ⟨_, rfl, rfl⟩ := hsol
    obtain ⟨_, -, rfl⟩ := hexp
    exact iff_of_true (degenerate_mart Q) (by simp [degenerate_Aloc])

/-- Closed balls exhaust `ℝ^d`. -/
theorem balls_cover : ⋃ n : ℕ, Metric.closedBall (0 : Fin d → ℝ) n = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.mpr ?_
  obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
  exact ⟨n, mem_closedBall_zero_iff.mpr hn⟩

/-- The field premises hold together on the instance: the Dirac law with closed balls, zero
coefficients and `Z = 1`. -/
theorem premises_sat (d : ℕ) :
    IsProbabilityMeasure (Measure.dirac ()) ∧ (0 : Fin d → ℝ) ∈ (univ : Set (Fin d → ℝ)) ∧
    CoeffHyp (degenerateSpace d) 0 0 0 ∧
    (degeneratePrimitives d).Solves (Measure.dirac ()) 0 0 0
      (fun n => Metric.closedBall 0 n) ∧
    NoJump (degenerateSpace d) (Measure.dirac ()) 0 0 ∧
    (degeneratePrimitives d).StochExp (Measure.dirac ()) 0 0 0
      (fun n => Metric.closedBall 0 n) 1 := by
  have hA : ∀ t ω, AtilZ (degenerateSpace d) (0 : ℝ≥0 → Unit → Matrix _ _ ℝ) 0 t ω = 0 :=
    fun t ω => by simp only [AtilZ, edens_zero, energyUpTo_zero]
  refine ⟨inferInstance, mem_univ _, ⟨fun _ _ => ?_, fun _ => ?_, fun _ => ?_, fun _ _ => ?_⟩,
    ⟨⟨?_, fun _ => Metric.isClosed_closedBall, fun _ _ h => Metric.closedBall_subset_closedBall
      (by exact_mod_cast h), balls_cover, fun _ => by simp [degenerateSpace]⟩, rfl, rfl⟩,
    ae_of_all _ fun ω ⟨t, ht, _⟩ => by simp [hA] at ht, ⟨?_, rfl, rfl⟩⟩
  · exact isStronglyProgressive_const _ _
  · exact isStronglyProgressive_const _ _
  · exact isStronglyProgressive_const _ _
  · simpa using PosSemidef.zero
  · exact ae_of_all _ fun _ => ⟨rfl, by simp [degenerateSpace]⟩
  · have hm := degenerate_mart (d := d) (Measure.dirac ())
    have hstop : ∀ n, stoppedAt (1 : ℝ≥0 → Unit → ℝ)
        (tau (degenerateSpace d) 0 0 (fun n => Metric.closedBall 0 n) (n + 1)) = 1 := fun n => by
      funext t ω
      simp [stoppedAt]
    exact
      { start := ae_of_all _ fun _ => rfl
        nonneg := ae_of_all _ fun _ _ => zero_le_one
        pos_before := ae_of_all _ fun _ _ _ => one_pos
        continuous := ae_of_all _ fun _ => continuous_const
        frozen := ae_of_all _ fun _ _ _ _ _ => rfl
        localMartingale := ProbabilityTheory.Locally.of_prop hm.1
        stopped_ui := fun n => by rw [hstop]; exact hm
        tau_stop := fun _ _ => Subsingleton.measurableSet }

/-! ## Convention checks -/

/-- `θ = ∞` on the constant path, though every `θ_n = n` is finite. -/
theorem degenerate_theta (n : ℕ) (ω : Unit) :
    thetaN (degenerateSpace d) 0 0 (fun n => Metric.closedBall 0 n) n ω = n ∧
      theta (degenerateSpace d) 0 0 (fun n => Metric.closedBall 0 n) ω = ⊤ := by
  have hrho : ∀ n : ℕ, rho (degenerateSpace d) (Metric.closedBall 0 n) ω = ⊤ := fun n => by
    simp [rho, degenerateSpace]
  have hN : ∀ n, thetaN (degenerateSpace d) 0 0 (fun n => Metric.closedBall 0 n) n ω = n :=
    fun n => by simp only [thetaN, Atil, edens_zero, energyUpTo_zero, hit_zero, hrho, min_self,
      min_eq_right le_top]
  refine ⟨hN n, ?_⟩
  simp only [theta, hN]
  exact ENNReal.iSup_natCast

/-- A unit density has infinite energy up to `∞` and finite energy up to a finite `t`. -/
theorem energy_top_check (ω : Unit) (t : ℝ≥0) :
    energyUpTo (fun _ _ => (1 : ℝ≥0∞)) (fun _ => ⊤) ⊤ ω = ⊤ ∧
      energyUpTo (fun _ _ => (1 : ℝ≥0∞)) (fun _ => ⊤) t ω < ⊤ := by
  constructor
  · simp [energyUpTo]
  · calc _ ≤ ∫⁻ s in Ioi (0 : ℝ), (Iio (t : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) s := by
          refine lintegral_mono fun s => ?_
          split_ifs with h
          · have hst : s < t := (Real.le_coe_toNNReal s).trans_lt
              (NNReal.coe_lt_coe.mpr (ENNReal.coe_lt_coe.mp h.1))
            rw [indicator_of_mem (show s ∈ Iio (t : ℝ) from hst)]
          · exact zero_le
      _ = volume (Iio (t : ℝ) ∩ Ioi 0) := by
          rw [lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
            one_mul]
      _ < ⊤ := by
          rw [Iio_inter_Ioi, Real.volume_Ioo]
          exact ENNReal.ofReal_lt_top

end AuxiliaryLawCriterion

end Upstream
