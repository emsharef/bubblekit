import Standalone.D9FiniteGrid
import Standalone.D9Refinement
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Claim 009 (D9): terminal L¹ convergence when continuous wealth is a true martingale

Statement only; the proof is `Novel/D9TrueLimitProof.lean`. Source claim:
`claims/009-d9-true-limit-ui.md`.

**Inputs.** The statement is conditional on AX-06 and AX-08 (claims 004 and 005's restatements,
`AX06`, `AX08`) and on AX-10, AX-11 and AX-14 (claim 007's restatements, `AX10`, `AX11`, `AX14`),
through claims 005 and 007, whose proved statements it applies. AX-16 is **not** a premise: its two
parts, specialized as the claim uses them, are proved in the proof file from Mathlib's
dominated-convergence theorem and the subsequence lemma for convergence in measure. Reverse Vitali
is Mathlib's `unifIntegrable_of_tendsto_Lp`.

**Setting.** Claim 007's: claim 004's `Setting` under `Q`, `X` held constant after `T > 0`,
`Grids T g N` (finite deterministic grids, mesh to zero, not necessarily nested), and in addition
`Q(X_t > 0 for every t ≤ T) = 1`. The exposure is `0 ≤ π ≤ 1`.

* `termW π X T g N n = W⁽ⁿ⁾_T`, claim 005's grid wealth at `T` on the `n`-th grid;
* `expo π L A T = Vπ_T = exp(πL_T − π²⟨L⟩_T/2)`, claim 007's continuous exponential, for `L` an
  integral of `1/X` against `X` (`Integral (1/X) X L`) and `A` its bracket. These exist by claim 007;
  the statement holds for every such pair.
* `PayoffConv`: for every globally Lipschitz `f : ℝ → ℝ`, the payoffs `f(W⁽ⁿ⁾_T)` and `f(Vπ_T)` are
  integrable and their expectations converge, (2).
* `TrueLimitConv`: (1), uniform integrability of `{W⁽ⁿ⁾_T}` (Mathlib's `UniformIntegrable` at
  `p = 1`, which includes the `L¹` bound), and (2).
* `EndpointConv`: the terminal `L¹` distance is zero for every `n`, uniform integrability, and (2).

**Parts.**
1. Basic facts: nonnegativity, terminal integrability, means at most one, and convergence of
   `W⁽ⁿ⁾_T` to `Vπ_T` in `Q`-probability.
2. Part 1–2 of the claim: if `E_Q[Vπ_T] = 1`, then `TrueLimitConv`. A true martingale on `[0, T]`
   (`MartingaleOn T`) has `E_Q[Vπ_T] = 1`, so "`Vπ` true" may be read either way.
3. Part 3, the D1 regimes, **conditional on AX-01 at this instance**: for `σ` satisfying claim 001's
   assumption 1 (`VolHyp`), `I₀ = ∞` (`¬ I0Finite σ`), `0 < π` and (`π ≤ 1/2` or `I∞ = ∞`), and the
   premise that `Vπ` is a martingale on `[0, T]` exactly when [mijatovic2010martingale]'s condition
   holds. That premise is what AX-01 asserts of the stochastic exponential of `∫ bπ(X) dW`; claim 007's
   D1 identification (its statement, under locally bounded `σ` and `dX = σ(X) dW`) shows that `Vπ`
   has exactly that exponent, and claim 001's representation (W) identifies it with the wealth. As in
   claim 001's statement (B), AX-01 and (W) enter as this premise and are not proved.
4. The endpoints: `π = 0` gives `W⁽ⁿ⁾ = V⁰ = 1` everywhere; `π = 1` gives `W⁽ⁿ⁾_T = V¹_T = X_T`
   almost surely, whether or not `X` is true, with common defect `1 − E_Q[X_T]`.
5. Part 4 of the claim, with no true-limit hypothesis: `limsup_n (1 − E W⁽ⁿ⁾_T) ≤ 1 − E Vπ_T`,
   written as "for every `ε > 0`, eventually `1 − E W⁽ⁿ⁾_T ≤ 1 − E Vπ_T + ε`".
6. Calls `(x − K)⁺` and puts `(K − x)⁺` are 1-Lipschitz, so `PayoffConv` covers them (the first
   conjunct of `statement`).

No reverse inequality in part 5, and no conclusion for a strict `Vπ` with `1/2 < π < 1`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D9TrueLimit

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9FiniteGrid
  Standalone.D9Refinement

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- `W⁽ⁿ⁾_T`, the grid wealth at `T` on the `n`-th grid. -/
noncomputable def termW (π : ℝ) (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (g : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ)
    (n : ℕ) (ω : Ω) : ℝ :=
  gridWealth π X (N n) (g n) T ω

/-- (2): every globally Lipschitz terminal payoff is integrable and its expectation converges. -/
def PayoffConv (Q : Measure Ω) (W : ℕ → Ω → ℝ) (V : Ω → ℝ) : Prop :=
  ∀ (f : ℝ → ℝ) (C : ℝ≥0), LipschitzWith C f →
    (∀ n, Integrable (fun ω => f (W n ω)) Q) ∧ Integrable (fun ω => f (V ω)) Q ∧
      Tendsto (fun n => ∫ ω, f (W n ω) ∂Q) atTop (𝓝 (∫ ω, f (V ω) ∂Q))

/-- (1), terminal uniform integrability, and (2). -/
def TrueLimitConv (Q : Measure Ω) (W : ℕ → Ω → ℝ) (V : Ω → ℝ) : Prop :=
  Tendsto (fun n => ∫ ω, |W n ω - V ω| ∂Q) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ ω, W n ω ∂Q) atTop (𝓝 1) ∧
    Tendsto (fun n => 1 - ∫ ω, W n ω ∂Q) atTop (𝓝 0) ∧
    UniformIntegrable W 1 Q ∧ PayoffConv Q W V

/-- Zero terminal `L¹` distance for every `n`, uniform integrability, and (2). -/
def EndpointConv (Q : Measure Ω) (W : ℕ → Ω → ℝ) (V : Ω → ℝ) : Prop :=
  (∀ n, ∫ ω, |W n ω - V ω| ∂Q = 0) ∧ UniformIntegrable W 1 Q ∧ PayoffConv Q W V

/-- Claim 009. The first conjunct is item 6 (calls and puts); the second is items 1–5. -/
def statement : Prop :=
  (∀ K : ℝ, LipschitzWith 1 (fun x : ℝ => max (x - K) 0) ∧
    LipschitzWith 1 (fun x : ℝ => max (K - x) 0)) ∧
  (AX06.{u} → AX08.{u} →
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop)
    (Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop),
    AX14 Q 𝓕 Integral Bracket → AX10 Q 𝓕 Integral → AX11 𝓕 →
  ∀ (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (g : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ) (π : ℝ),
    Setting Q 𝓕 X T → 0 < T → (∀ t ω, X t ω = X (min t T) ω) → Grids T g N →
    (∀ᵐ ω ∂Q, ∀ t ≤ T, 0 < X t ω) → 0 ≤ π → π ≤ 1 →
  ∀ L A : ℝ≥0 → Ω → ℝ, Integral (fun t ω => 1 / X t ω) X L → Bracket L A →
    -- 1. Nonnegativity, integrability, means at most one, convergence in probability.
    ((∀ n ω, 0 ≤ termW π X T g N n ω) ∧ (∀ ω, 0 < expo π L A T ω) ∧
      (∀ n, Integrable (termW π X T g N n) Q) ∧ Integrable (expo π L A T) Q ∧
      (∀ n, ∫ ω, termW π X T g N n ω ∂Q ≤ 1) ∧ ∫ ω, expo π L A T ω ∂Q ≤ 1 ∧
      TendstoInMeasure Q (termW π X T g N) atTop (expo π L A T)) ∧
    -- 2. Parts 1–2: a true continuous limit.
    (∫ ω, expo π L A T ω ∂Q = 1 → TrueLimitConv Q (termW π X T g N) (expo π L A T)) ∧
    (MartingaleOn T (expo π L A) 𝓕 Q → ∫ ω, expo π L A T ω ∂Q = 1) ∧
    -- 3. Part 3: the D1 regimes, given AX-01's conclusion at this instance.
    (∀ (σ : ℝ → ℝ) (c : ℝ), VolHyp σ → 0 < c → 0 < π → ¬ I0Finite σ →
      (π ≤ 1 / 2 ∨ ¬ IInftyFinite σ) →
      (MartingaleOn T (expo π L A) 𝓕 Q ↔ MUCondition π σ c) →
      MartingaleOn T (expo π L A) 𝓕 Q ∧ TrueLimitConv Q (termW π X T g N) (expo π L A T)) ∧
    -- 4. Part 3: the endpoints.
    (π = 0 → (∀ n ω, termW π X T g N n ω = 1) ∧ (∀ ω, expo π L A T ω = 1) ∧
      EndpointConv Q (termW π X T g N) (expo π L A T)) ∧
    (π = 1 → (∀ n, termW π X T g N n =ᵐ[Q] X T) ∧ expo π L A T =ᵐ[Q] X T ∧
      EndpointConv Q (termW π X T g N) (expo π L A T) ∧
      ∀ n, 1 - ∫ ω, termW π X T g N n ω ∂Q = 1 - ∫ ω, X T ω ∂Q) ∧
    -- 5. Part 4: the one-sided defect limit, with no true-limit hypothesis.
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      1 - ∫ ω, termW π X T g N n ω ∂Q ≤ 1 - ∫ ω, expo π L A T ω ∂Q + ε))

end Standalone.D9TrueLimit
