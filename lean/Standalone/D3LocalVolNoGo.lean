import Mathlib.MeasureTheory.Constructions.Pi
import Standalone.D8TailCompletions
import Standalone.D1TwoEndpoint

/-!
# Claim 006 (D3): local volatility alone cannot give power above uniform null size

Statement only; the proof is `Novel/D3LocalVolNoGoProof.lean`. Source claim:
`claims/006-d3-local-vol-no-go.md`.

**Inputs.** The statement is conditional on AX-09's stopped uniqueness in law, restated as `AX09`
because a statement may import only Mathlib and other statements. The proof file derives it from
`Upstream.StoppedUniqueness`. The pricing laws themselves are a **premise** (`PricingFamily`), not a
construction. That premise is a relation `Law σ μ` ("μ is the pricing path law ν_σ on `[0, T]` of the
weak solution of `dS = σ(S) dW`, `S₀ = s₀`, absorbed at zero"), with three requirements:

* a law exists for every admissible `σ` (AX-09's weak existence, with no exit at infinity by AX-02);
* each law is a probability;
* almost every path is in `E_T`, absorbed at zero.

This is the reduced formal scope the claim's formalization notes ask to disclose: weak existence and
non-explosion are assumed in this form, not derived from the Upstream structures. AX-03 is not used
here: `H₀` and `H₁` are defined by `I∞`, as in the claim, and AX-03's martingale reading of them is
commentary.

**Encodings.**

* **Paths and tests.** `Path T` is the space of continuous real paths on `[0, T]`, with the trace of
  the product σ-algebra, which for continuous paths is the Borel σ-algebra of the uniform topology
  (claim 003). Pricing laws are supported on `E_T` (nonnegative paths from `s₀`), absorbed at zero.
  `k` paths are observed. A test (`IsTest`) is Borel on `Path Tᵏ`, with values in `[0, 1]`.
* **The coefficient class `Σ`.** Claim 002's `Admissible`: Borel, nowhere zero on `(0, ∞)`, with
  `1/σ²` locally integrable there. `I∞ < ∞` is claim 001's `IInftyFinite`.
* **The two restrictions.** The flag `cont` restricts `Σ` to positive coefficients continuous on
  `(0, ∞)`. The flag `pricing` restricts the physical law to `P = ν_σ`. Each restriction applies to
  alternatives and nulls alike, and both can be imposed together.
* **The null completion.** `σ_n` of (2) is claim 002's `completion σ n 1`.
* **The events.** `A n = {w : max w < n}`. `stopExit n` stops a path at its first time outside
  `(0, n)` (the claim's `Hₙ` of (4)). It is measurable (proved in the proof file), so in `AX09`
  `μ.map (stopExit n)` is the law of the stopped path.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D3LocalVolNoGo

open Standalone.D8TailCompletions (Admissible completion)
open Standalone.D1TwoEndpoint (IInftyFinite)

/-- Continuous real paths on `[0, T]`. -/
abbrev Path (T : ℝ≥0) : Type := {w : Icc (0 : ℝ≥0) T → ℝ // Continuous w}

variable {T : ℝ≥0}

/-- First time in `[0, T]` at which `w` is outside `(0, n)`; `T` if there is none. -/
noncomputable def exitIcc (n : ℝ) (w : Path T) : ℝ≥0 :=
  open Classical in
  if (Subtype.val '' {t | w.1 t ∉ Ioo 0 n}).Nonempty then
    sInf (Subtype.val '' {t | w.1 t ∉ Ioo 0 n})
  else T

/-- `Hₙ` of (4): the path stopped at its first time outside `(0, n)`. -/
noncomputable def stopExit (n : ℝ) (w : Path T) : Path T :=
  ⟨fun t => w.1 ⟨min t.1 (exitIcc n w), bot_le, (min_le_left _ _).trans t.2.2⟩,
    w.2.comp ((continuous_subtype_val.min continuous_const).subtype_mk _)⟩

/-- A path of `E_T` (nonnegative, from `s₀`), absorbed at zero. -/
structure AbsorbedPath (s₀ : ℝ) (w : Path T) : Prop where
  nonneg : ∀ t, 0 ≤ w.1 t
  start : w.1 ⟨0, le_rfl, bot_le⟩ = s₀
  absorbed : ∀ t u, t ≤ u → w.1 t = 0 → w.1 u = 0

/-- The pricing-law premise (see the header). -/
structure PricingFamily (s₀ : ℝ) (T : ℝ≥0) (Law : (ℝ → ℝ) → Measure (Path T) → Prop) : Prop where
  exists_law : ∀ σ, Admissible σ → ∃ μ, Law σ μ
  prob : ∀ σ μ, Law σ μ → IsProbabilityMeasure μ
  paths : ∀ σ μ, Law σ μ → ∀ᵐ w ∂μ, AbsorbedPath s₀ w

/-- AX-09 restated ([karatzas2015distribution] Proposition 9.1, as specialized in the ledger): two
admissible coefficients that agree on `(0, n)`, with `s₀ < n`, give the same law of the path
stopped at its first exit from `(0, n)`. -/
def AX09 (s₀ : ℝ) (T : ℝ≥0) (Law : (ℝ → ℝ) → Measure (Path T) → Prop) : Prop :=
  ∀ (σ σ' : ℝ → ℝ) (n : ℝ) (μ μ' : Measure (Path T)), Admissible σ → Admissible σ' → s₀ < n →
    (∀ x, 0 < x → x < n → σ x = σ' x) → Law σ μ → Law σ' μ' →
    μ.map (stopExit n) = μ'.map (stopExit n)

/-- A test: Borel on `k` paths, with values in `[0, 1]`. -/
structure IsTest {k : ℕ} (φ : (Fin k → Path T) → ℝ) : Prop where
  measurable : Measurable φ
  nonneg : ∀ x, 0 ≤ φ x
  le_one : ∀ x, φ x ≤ 1

/-- The coefficient class: `Σ`, or (with `cont`) its positive coefficients continuous on `(0, ∞)`. -/
def InClass (cont : Bool) (σ : ℝ → ℝ) : Prop :=
  Admissible σ ∧ (cont = true → (∀ x, 0 < x → 0 < σ x) ∧ ContinuousOn σ (Ioi 0))

/-- A model `(σ, P)` with pricing law `μ`: `σ` in the class, `μ` its pricing law, and `P` a
physical probability equivalent to `μ` (with `pricing`, equal to it). -/
def IsModel (Law : (ℝ → ℝ) → Measure (Path T) → Prop) (cont pricing : Bool) (σ : ℝ → ℝ)
    (μ P : Measure (Path T)) : Prop :=
  InClass cont σ ∧ Law σ μ ∧ IsProbabilityMeasure P ∧ P ≪ μ ∧ μ ≪ P ∧ (pricing = true → P = μ)

/-- `E_{P^⊗k}[φ]`. -/
noncomputable def testExp (k : ℕ) (P : Measure (Path T)) (φ : (Fin k → Path T) → ℝ) : ℝ :=
  ∫ x, φ x ∂(Measure.pi fun _ : Fin k => P)

/-- Uniform null size: the supremum over models in `H₀` (`I∞ = ∞`) of the family. -/
noncomputable def size (Law : (ℝ → ℝ) → Measure (Path T) → Prop) (cont pricing : Bool) (k : ℕ)
    (φ : (Fin k → Path T) → ℝ) : ℝ :=
  sSup {e | ∃ g μ P, IsModel Law cont pricing g μ P ∧ ¬ IInftyFinite g ∧ e = testExp k P φ}

/-- `Aₙ = {w : max_[0,T] w < n}`. -/
def A (n : ℝ) : Set (Path T) := {w | ∀ t, w.1 t < n}

/-- Claim 006. -/
def statement : Prop :=
  ∀ (s₀ : ℝ) (T : ℝ≥0) (Law : (ℝ → ℝ) → Measure (Path T) → Prop), 0 < s₀ →
    PricingFamily s₀ T Law → AX09 s₀ T Law → ∀ cont pricing : Bool,
    -- (1): power at most uniform null size, at every alternative of the family.
    (∀ (k : ℕ) (φ : (Fin k → Path T) → ℝ) (σ : ℝ → ℝ) (μ P : Measure (Path T)), IsTest φ →
      IsModel Law cont pricing σ μ P → IInftyFinite σ →
      testExp k P φ ≤ size Law cont pricing k φ) ∧
    -- (2), (6), (7) and (3): the null completion, its pricing law, the physical null, the bound.
    (∀ (σ : ℝ → ℝ) (μ P : Measure (Path T)) (n : ℕ), IsModel Law cont pricing σ μ P → s₀ < n →
      InClass cont (completion σ n 1) ∧ ¬ IInftyFinite (completion σ n 1) ∧
      ∀ μn, Law (completion σ n 1) μn →
        (∀ B, MeasurableSet B → μ (B ∩ A n) = μn (B ∩ A n)) ∧
        ∃ Pn, IsModel Law cont pricing (completion σ n 1) μn Pn ∧
          (∀ B, MeasurableSet B → Pn (B ∩ A n) = P (B ∩ A n)) ∧
          ∀ (k : ℕ) (φ : (Fin k → Path T) → ℝ), IsTest φ →
            |testExp k P φ - testExp k Pn φ| ≤ 1 - (1 - (P (A n)ᶜ).toReal) ^ k ∧
            1 - (1 - (P (A n)ᶜ).toReal) ^ k ≤ k * (P (A n)ᶜ).toReal) ∧
    -- `pₙ → 0`.
    (∀ (σ : ℝ → ℝ) (μ P : Measure (Path T)), IsModel Law cont pricing σ μ P →
      Tendsto (fun n : ℕ => (P (A n)ᶜ).toReal) atTop (𝓝 0)) ∧
    -- Sharpness: the constant test has size and power `ε`.
    (∀ (k : ℕ) (ε : ℝ), size Law cont pricing k (fun _ => ε) = ε ∧
      ∀ P : Measure (Path T), IsProbabilityMeasure P → testExp k P (fun _ => ε) = ε) ∧
    -- The asymptotic consequence.
    (∀ (φ : ∀ k : ℕ, (Fin k → Path T) → ℝ) (σ : ℝ → ℝ) (μ P : Measure (Path T)),
      (∀ k, IsTest (φ k)) → IsModel Law cont pricing σ μ P → IInftyFinite σ →
      limsup (fun k => testExp k P (φ k)) atTop ≤
        limsup (fun k => size Law cont pricing k (φ k)) atTop)

end Standalone.D3LocalVolNoGo
