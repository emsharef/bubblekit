import Standalone.PriceChain
import Standalone.SplitLikelihoodSupport
import Standalone.D1TwoEndpoint
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Claim 054, deterministic part: CEV kernels, supports, scores and blocks

Statement only; the proof is `Novel/CEVSupportProof.lean`. Source claim:
`claims/054-d13-cev-catalogue.md`, the finite-array steps of parts 1, 2 and 4, and the
coefficient side of part 3. No probability enters.

**Vocabulary** (shared, with identical bodies, with `Upstream.CEVKernel`):
* `NNR = [0, ∞)`, with `muCEV = Lebesgue + δ₀`;
* `besselI` and `upperGamma` (by their formulas);
* the CEV density `fcev` and atom `acev`;
* `chainN f Δ x₀ y = ∏ⱼ f(Δⱼ, y_{j−1}, yⱼ)` on `[0, ∞)^n`.

The claim's kernel `Kc p κ` uses AX-55's `f1` for `p = 1` and AX-56's `fcev`/`acev` otherwise. At a
zero state it is trapped (`1` at `0`, `0` elsewhere). From a positive state it has no atom when
`p ≥ 1`.

**Statement.** It is stated for arbitrary nonnegative arrays, not only model-possible paths.
* **Support.** Assume `fcev > 0` for positive arguments when `p' ≠ 1`, a cited AX-56 fact taken
  here as a hypothesis. Then for `p > 1` a positive chain forces either a positive start with all positive
  coordinates, or a zero start with all-zero coordinates. In both cases every `p ≤ 1` chain is
  positive.
* **Absorbed arrays.**
  - From a zero start, the chain is `1` on the all-zero array.
  - From a positive start with some zero coordinate, every `p ≥ 1` chain vanishes.
* **Composite score (1).** For a finite catalogue with nonempty null `{p ≤ 1}`, densities `g ≥ 0`, a
  selected index, and the support property (some null density is positive when `Ĝ` is):
  - `E = min_{null} R₊(Ĝ, gϑ)` is finite;
  - `E = 0` if `Ĝ = 0`, and `E = Ĝ/G₀` with `G₀ = max_{null} g > 0` if `Ĝ > 0`;
  - if the selected index is null, `E ≤ 1`.
* **Blocks.** For `σ = κx^p`, the blocks are `b₁ = R^η(r^η − 1)/(κ²η)` (`p ≠ 1`, `η = 2 − 2p`) or
  `log r/κ²` (`p = 1`), with `b₂ = r^η b₁`.
* **Coefficient side of the labels.** `I∞(κx^p) < ∞` iff `p > 1`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Standalone.CEVSupport

open Standalone.PriceChain Standalone.SplitLikelihoodSupport

/-- `[0, ∞)`. -/
abbrev NNR := {x : ℝ // 0 ≤ x}

instance : PolishSpace NNR := (isClosed_le continuous_const continuous_id).polishSpace

instance : Nonempty NNR := ⟨⟨0, le_rfl⟩⟩

/-- The point `0`. -/
def zero : NNR := ⟨0, le_rfl⟩

/-- `max x 0`. -/
noncomputable def toNNR (x : ℝ) : NNR := ⟨max x 0, le_max_right _ _⟩

/-- Lebesgue measure on `[0, ∞)`. -/
noncomputable def lebNN : Measure NNR := Measure.comap Subtype.val volume

/-- The CEV reference measure. -/
noncomputable def muCEV : Measure NNR := lebNN + Measure.dirac zero

/-- The modified Bessel function of the first kind, by its series (for `z ≥ 0`). -/
noncomputable def besselI (ν z : ℝ) : ℝ :=
  (∑' k : ℕ, ENNReal.ofReal ((z / 2) ^ (2 * (k : ℝ) + ν) /
    ((k.factorial : ℝ) * Real.Gamma ((k : ℝ) + ν + 1)))).toReal

/-- The upper incomplete gamma function. -/
noncomputable def upperGamma (ν z : ℝ) : ℝ := ∫ t in Ioi z, t ^ (ν - 1) * Real.exp (-t)

/-- The CEV density on `(0, ∞)` (AX-56). -/
noncomputable def fcev (p κ Δ x y : ℝ) : ℝ :=
  x ^ (1 / 2 : ℝ) * y ^ (1 / 2 - 2 * p) / (κ ^ 2 * |p - 1| * Δ) *
    Real.exp (-(x ^ (2 - 2 * p) + y ^ (2 - 2 * p)) / (2 * (κ ^ 2 * |p - 1| ^ 2 * Δ))) *
    besselI (1 / (2 * |p - 1|)) (x ^ (1 - p) * y ^ (1 - p) / (κ ^ 2 * |p - 1| ^ 2 * Δ))

/-- The absorption atom (AX-56). -/
noncomputable def acev (p κ Δ x : ℝ) : ℝ :=
  if p < 1 then
    upperGamma (1 / (2 * |p - 1|)) (x ^ (2 - 2 * p) / (2 * (κ ^ 2 * |p - 1| ^ 2 * Δ))) /
      Real.Gamma (1 / (2 * |p - 1|))
  else 0

/-- AX-56's kernel on `[0, ∞)` with the trapped extension (`p ≠ 1`). -/
noncomputable def K (p κ Δ x y : ℝ) : ℝ :=
  if x = 0 then (if y = 0 then 1 else 0) else if y = 0 then acev p κ Δ x else fcev p κ Δ x y

/-- The claim's kernel: AX-55's lognormal for `p = 1` (no atom from a positive state), else `K`. -/
noncomputable def Kc (p κ Δ x y : ℝ) : ℝ :=
  open Classical in
  if p = 1 then (if x = 0 then (if y = 0 then 1 else 0) else if y = 0 then 0 else f1 κ Δ x y)
  else K p κ Δ x y

/-- The previous coordinate, `x₀` before the first. -/
def prevN {n : ℕ} (x₀ : ℝ) (y : Fin n → NNR) (j : Fin n) : ℝ :=
  if h : (j : ℕ) = 0 then x₀ else (y ⟨j - 1, by omega⟩ : ℝ)

/-- The chain density on `[0, ∞)^n`. -/
noncomputable def chainN {n : ℕ} (f : ℝ → ℝ → ℝ → ℝ) (Δ : Fin n → ℝ) (x₀ : ℝ)
    (y : Fin n → NNR) : ℝ :=
  ∏ j : Fin n, f (Δ j) (prevN x₀ y j) (y j)

/-- The composite null score `E = min_{ϑ : p ϑ ≤ 1} R₊(Ĝ, g ϑ)`. -/
noncomputable def Ecomp {c : ℕ} (pw : Fin c → ℝ) (g : Fin c → ℝ) (sel : Fin c) : ℝ≥0∞ :=
  ⨅ ϑ ∈ {ϑ | pw ϑ ≤ 1}, Rplus (g sel) (g ϑ)

/-- `b₁ = ∫_R^{Rr} x/σ(x)² dx` for `σ = κx^p`, in closed form. -/
noncomputable def blk1 (R r p κ : ℝ) : ℝ :=
  if p = 1 then Real.log r / κ ^ 2 else R ^ (2 - 2 * p) * (r ^ (2 - 2 * p) - 1) / (κ ^ 2 * (2 - 2 * p))

/-- The deterministic part of claim 054. -/
def statement : Prop :=
  -- Support: a positive `p > 1` chain forces every `p ≤ 1` chain to be positive.
  (∀ (m : ℕ) (Δ : Fin m → ℝ) (p p' κ κ' : ℝ) (x₀ : ℝ) (v : Fin m → NNR),
    (∀ j, 0 < Δ j) → 0 ≤ x₀ → 1 < p → 0 < p' → p' ≤ 1 → 0 < κ' →
    (p' ≠ 1 → ∀ Δ' x y : ℝ, 0 < Δ' → 0 < x → 0 < y → 0 < fcev p' κ' Δ' x y) →
    0 < chainN (Kc p κ) Δ x₀ v → 0 < chainN (Kc p' κ') Δ x₀ v) ∧
  -- Absorbed arrays.
  (∀ (m : ℕ) (Δ : Fin m → ℝ) (p κ : ℝ), chainN (Kc p κ) Δ 0 (fun _ => zero) = 1) ∧
  (∀ (m : ℕ) (Δ : Fin m → ℝ) (p κ x₀ : ℝ) (v : Fin m → NNR), 1 ≤ p → 0 < x₀ →
    (∃ l, (v l : ℝ) = 0) → chainN (Kc p κ) Δ x₀ v = 0) ∧
  -- The composite score (1).
  (∀ (c : ℕ) (pw : Fin c → ℝ) (g : Fin c → ℝ) (sel : Fin c), (∀ ϑ, 0 ≤ g ϑ) →
    (∃ ϑ, pw ϑ ≤ 1) → (0 < g sel → ∃ ϑ, pw ϑ ≤ 1 ∧ 0 < g ϑ) →
    Ecomp pw g sel < ⊤ ∧ (g sel = 0 → Ecomp pw g sel = 0) ∧
    (0 < g sel → ∃ G₀ : ℝ, 0 < G₀ ∧ (∀ ϑ, pw ϑ ≤ 1 → g ϑ ≤ G₀) ∧ (∃ ϑ, pw ϑ ≤ 1 ∧ g ϑ = G₀) ∧
      Ecomp pw g sel = ENNReal.ofReal (g sel / G₀)) ∧
    (pw sel ≤ 1 → Ecomp pw g sel ≤ 1)) ∧
  -- Blocks.
  (∀ (R r p κ : ℝ), 0 < R → 1 < r → 0 < κ →
    Standalone.D3PowerTail.B1 R r (fun x => κ * x ^ p) = blk1 R r p κ ∧
    Standalone.D3PowerTail.B2 R r (fun x => κ * x ^ p) = r ^ (2 - 2 * p) * blk1 R r p κ ∧
    0 < blk1 R r p κ) ∧
  -- The coefficient side of AX-03's labels.
  (∀ p κ : ℝ, 0 < κ → (Standalone.D1TwoEndpoint.IInftyFinite (fun x => κ * x ^ p) ↔ 1 < p))

end Standalone.CEVSupport
