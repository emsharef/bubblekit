import Standalone.D3LocalVolNoGo
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Claim 013 (D3): identification from two compact integrals under a declared power tail

Statement only; the proof is `Novel/D3PowerTailProof.lean`. Source claim:
`claims/013-d3-power-tail-identification.md`.

**Parts 1–2 are deterministic and unconditional.** Part 3 is a probabilistic implication whose
premises are **claim 012's conclusion** on each block and **AX-51's** event convergence; neither is
derived here (claim 012 is approved but not formalized). Part 4 is unconditional at the coefficient
level and, for tests, conditional on claim 006's premises (`PricingFamily`, `AX09`), exactly as
claim 006. The binary label's reading as strict/true local martingale is conditional on AX-03 and is
commentary here (claim 002's `theta_interpretation`).

**Encodings.**
* `PowTail R σ`: `σ(x) = κ x^p` for every `x ≥ R`, some `κ > 0`, `p ∈ ℝ` (rpow), the onset `R`
  declared. `CPow R σ` adds claim 002's `Admissible` (Borel, nonzero on `(0, ∞)`, `1/σ²` locally
  integrable there), positivity and continuity on `(0, ∞)`: the class `C_pow(R)`.
* `B1 = ∫_R^{Rr} x/σ²`, `B2 = ∫_{Rr}^{Rr²} x/σ²`. `I_R` is claim 002's `F R σ = ∫⁻_{(R,∞)} x/σ²`
  (in `[0, ∞]`) and `θ` is claim 002's `θ R σ` (`1` iff `I_R < ∞`).
* `bandSet`: the set of `θ` over `C_pow(R)` with `B_i ∈ [L_i, U_i]`.
* Part 3. `TightOn P B̂ B D` is "`n^{1/3}(B̂ₙ − B) 1_{Dₙ} = O_P(1)`": for each `ε > 0` some `K` has
  `P(Dₙ ∩ {K < n^{1/3}|B̂ₙ − B|}) ≤ ε` eventually. This is claim 012's conclusion on block `i`, with
  `Dᵢₙ = D_{Aᵢ}^n(w)`. `Ds n = D_*^n` is contained in both block events, and AX-51 gives
  `P(D_*^n Δ D_*) → 0`. `reject` is the event `{φₙ = 1} = D_*^n ∩ {B̂₁ₙ − B̂₂ₙ > hₙ}`, (5). A null
  model has `θ = 0`, an alternative `θ = 1`.
* Part 4. `EventuallyPower σ`: `σ(x) = κ x^p` for all `x ≥ H`, some unknown `H > 0`, `κ ≠ 0`
  (`κ > 0` when `σ` is positive), `p ∈ ℝ`. `sizePow` is claim 006's uniform null size with the null
  models further restricted to eventually power coefficients.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D3PowerTail

open Standalone.D8TailCompletions (Admissible Compatible F θ completion)
open Standalone.D1TwoEndpoint (IInftyFinite)
open Standalone.D3LocalVolNoGo

/-- (1): `σ(x) = κ x^p` for every `x ≥ R`. -/
def PowTail (R : ℝ) (σ : ℝ → ℝ) : Prop := ∃ κ p : ℝ, 0 < κ ∧ ∀ x, R ≤ x → σ x = κ * x ^ p

/-- `C_pow(R)`. -/
def CPow (R : ℝ) (σ : ℝ → ℝ) : Prop :=
  Admissible σ ∧ (∀ x, 0 < x → 0 < σ x) ∧ ContinuousOn σ (Ioi 0) ∧ PowTail R σ

/-- `B₁ = ∫_R^{Rr} x/σ(x)² dx`. -/
noncomputable def B1 (R r : ℝ) (σ : ℝ → ℝ) : ℝ := ∫ x in R..R * r, x / σ x ^ 2

/-- `B₂ = ∫_{Rr}^{Rr²} x/σ(x)² dx`. -/
noncomputable def B2 (R r : ℝ) (σ : ℝ → ℝ) : ℝ := ∫ x in R * r..R * r ^ 2, x / σ x ^ 2

/-- The identified set of `θ` under the bands `B_i ∈ [L_i, U_i]`. -/
def bandSet (R r L1 U1 L2 U2 : ℝ) : Set ℕ :=
  {n | ∃ σ, CPow R σ ∧ B1 R r σ ∈ Icc L1 U1 ∧ B2 R r σ ∈ Icc L2 U2 ∧ θ R σ = n}

/-- `n^{1/3} (B̂ₙ − B) 1_{Dₙ} = O_P(1)`. -/
def TightOn {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Bh : ℕ → Ω → ℝ) (B : ℝ)
    (D : ℕ → Set Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ᶠ n in atTop,
    P.real {ω | ω ∈ D n ∧ K < (n : ℝ) ^ (1 / 3 : ℝ) * |Bh n ω - B|} ≤ ε

/-- `{φₙ = 1} = D_*^n ∩ {B̂₁ₙ − B̂₂ₙ > hₙ}`, (5). -/
def reject {Ω : Type*} (Bh1 Bh2 : ℕ → Ω → ℝ) (h : ℕ → ℝ) (Ds : ℕ → Set Ω) (n : ℕ) : Set Ω :=
  {ω | ω ∈ Ds n ∧ h n < Bh1 n ω - Bh2 n ω}

/-- `σ(x) = κ x^p` beyond some unknown onset `H`. -/
def EventuallyPower (σ : ℝ → ℝ) : Prop :=
  ∃ H κ p : ℝ, 0 < H ∧ κ ≠ 0 ∧ ∀ x, H ≤ x → σ x = κ * x ^ p

/-- Claim 006's uniform null size, nulls restricted to eventually power coefficients. -/
noncomputable def sizePow {T : ℝ≥0} (Law : (ℝ → ℝ) → Measure (Path T) → Prop) (cont pricing : Bool)
    (k : ℕ) (φ : (Fin k → Path T) → ℝ) : ℝ :=
  sSup {e | ∃ g μ P, IsModel Law cont pricing g μ P ∧ EventuallyPower g ∧ ¬ IInftyFinite g ∧
    e = testExp k P φ}

/-- Claim 013. -/
def statement : Prop :=
  -- Part 1: (2) for every coefficient of the class.
  (∀ (R r : ℝ) (σ : ℝ → ℝ), 0 < R → 1 < r → CPow R σ →
    0 < B1 R r σ ∧ 0 < B2 R r σ ∧
    (∀ κ p : ℝ, 0 < κ → (∀ x, R ≤ x → σ x = κ * x ^ p) →
      B2 R r σ / B1 R r σ = r ^ (2 - 2 * p) ∧
      p = 1 - Real.log (B2 R r σ / B1 R r σ) / (2 * Real.log r)) ∧
    (B2 R r σ / B1 R r σ < 1 →
      F R σ = ENNReal.ofReal (B1 R r σ / (1 - B2 R r σ / B1 R r σ))) ∧
    (1 ≤ B2 R r σ / B1 R r σ → F R σ = ∞) ∧
    θ R σ = if B2 R r σ < B1 R r σ then 1 else 0) ∧
  -- Part 1: every positive pair is attained.
  (∀ (R r b1 b2 : ℝ), 0 < R → 1 < r → 0 < b1 → 0 < b2 →
    ∃ σ, CPow R σ ∧ B1 R r σ = b1 ∧ B2 R r σ = b2) ∧
  -- The two labels on nonzero examples: `σ = x` (`θ = 0`) and `σ = x²` (`θ = 1`).
  (∀ R : ℝ, 0 < R → CPow R (fun x => x) ∧ θ R (fun x => x) = 0 ∧
    CPow R (fun x => x ^ 2) ∧ θ R (fun x => x ^ 2) = 1) ∧
  -- Part 2: (3), nonemptiness, and the conditional size bound (4).
  (∀ (R r L1 U1 L2 U2 : ℝ), 0 < R → 1 < r → 0 < L1 → L1 ≤ U1 → 0 < L2 → L2 ≤ U2 →
    (0 ∈ bandSet R r L1 U1 L2 U2 ↔ L1 ≤ U2) ∧ (1 ∈ bandSet R r L1 U1 L2 U2 ↔ L2 < U1) ∧
    (bandSet R r L1 U1 L2 U2).Nonempty ∧ bandSet R r L1 U1 L2 U2 ⊆ {0, 1}) ∧
  (∀ (R r : ℝ) (σ : ℝ → ℝ), 0 < R → 1 < r → CPow R σ → θ R σ = 0 →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (L1 U1 L2 U2 : Ω → ℝ) (α : ℝ), Measurable L1 → Measurable U1 → Measurable L2 →
      Measurable U2 →
      1 - α ≤ P.real {ω | B1 R r σ ∈ Icc (L1 ω) (U1 ω) ∧ B2 R r σ ∈ Icc (L2 ω) (U2 ω)} →
      P.real {ω | U2 ω < L1 ω} ≤ α) ∧
  -- Part 3: the pointwise rule (5)–(6), given claim 012 on both blocks and AX-51.
  (∀ (R r : ℝ) (σ : ℝ → ℝ), 0 < R → 1 < r → CPow R σ →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Bh1 Bh2 : ℕ → Ω → ℝ) (D1 D2 Ds : ℕ → Set Ω) (D : Set Ω) (h : ℕ → ℝ),
      (∀ n, Measurable (Bh1 n)) → (∀ n, Measurable (Bh2 n)) → (∀ n, MeasurableSet (Ds n)) →
      MeasurableSet D → (∀ n, Ds n ⊆ D1 n) → (∀ n, Ds n ⊆ D2 n) →
      TightOn P Bh1 (B1 R r σ) D1 → TightOn P Bh2 (B2 R r σ) D2 →
      Tendsto (fun n => P (symmDiff (Ds n) D)) atTop (𝓝 0) →
      Tendsto h atTop (𝓝 0) → Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * h n) atTop atTop →
      (θ R σ = 0 → Tendsto (fun n => P.real (reject Bh1 Bh2 h Ds n)) atTop (𝓝 0)) ∧
      (θ R σ = 1 →
        Tendsto (fun n => P.real (reject Bh1 Bh2 h Ds n)) atTop (𝓝 (P.real D)) ∧
        (0 < P.real D → Tendsto (fun n => P.real (reject Bh1 Bh2 h Ds n) / P.real (Ds n))
          atTop (𝓝 1)) ∧
        (P.real D = 0 → Tendsto (fun n => P.real (reject Bh1 Bh2 h Ds n)) atTop (𝓝 0)))) ∧
  -- Part 3: `hₙ = n^{−1/4}` meets both threshold conditions.
  (Tendsto (fun n : ℕ => (n : ℝ) ^ (-1 / 4 : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-1 / 4 : ℝ)) atTop atTop) ∧
  -- Part 4: unknown onset, coefficient level: `{0, 1}` after observing `σ` on `(0, R₀]`.
  (∀ (σ : ℝ → ℝ) (c R₀ : ℝ), Admissible σ → (∀ x, 0 < x → 0 < σ x) →
    ContinuousOn σ (Ioi 0) → 0 < c → c < R₀ →
    {n | ∃ g, Compatible σ R₀ g ∧ EventuallyPower g ∧ (∀ x, 0 < x → 0 < g x) ∧
      ContinuousOn g (Ioi 0) ∧ θ c g = n} = {0, 1}) ∧
  -- Part 4: claim 006's null completions are eventually power, and the test bound survives.
  (∀ (σ : ℝ → ℝ) (n : ℝ), Admissible σ → 0 < n → EventuallyPower (completion σ n 1)) ∧
  (∀ (s₀ : ℝ) (T : ℝ≥0) (Law : (ℝ → ℝ) → Measure (Path T) → Prop), 0 < s₀ →
    PricingFamily s₀ T Law → AX09 s₀ T Law → ∀ cont pricing : Bool,
    ∀ (k : ℕ) (φ : (Fin k → Path T) → ℝ) (σ : ℝ → ℝ) (μ P : Measure (Path T)), IsTest φ →
      IsModel Law cont pricing σ μ P → EventuallyPower σ → IInftyFinite σ →
      testExp k P φ ≤ sizePow Law cont pricing k φ)

end Standalone.D3PowerTail
