import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Claim 002 (D8): exact identified sets of the JKP integral under bounded coefficient information

Statement only; the proof is `Novel/D8TailCompletionsProof.lean`. Source claim:
`claims/002-d8-tail-completions.md`.

The observation is the exact restriction of the coefficient `σ` to `(0, R]`. `C_R(σ)` is the class
of admissible coefficients `g` (Borel, nonzero on `(0, ∞)`, `1/g²` locally integrable there) with
`g = σ` on `(0, R]`, including at `R`. Coefficients are functions `ℝ → ℝ`, and only their values on
`(0, ∞)` enter.

For `0 < c < R`:

* `J = ∫_c^R x/σ²(x) dx` (a real number);
* `F_c(g) = ∫_c^∞ x/g²(x) dx ∈ [0, ∞]`, a Lebesgue integral of a nonnegative function;
* `θ(g) = 1` if `F_c(g) < ∞`, else `0`.

The statement:

1. `{F_c(g) : g ∈ C_R(σ)} = {J + a : 0 < a < ∞} ∪ {∞}`, claim (1);
2. `{θ(g) : g ∈ C_R(σ)} = {0, 1}`, claim (2);
3. the lower endpoint `J` is not attained: `J < F_c(g)` for every compatible `g`;
4. the explicit completions `g_p(x) = σ(x)` for `x ≤ R` and `σ(R)(x/R)^p` for `x > R`, `p ≥ 1`, are
   compatible, with `F_c(g_1) = ∞` and `F_c(g_p) = J + R²/(2(p−1)σ(R)²)` for `p > 1`;
5. if `σ` is positive and continuous on `(0, ∞)`, so is every `g_p`.

These are deterministic and unconditional. The claim's bubble interpretation (θ = 1 labels a
strict local martingale, θ = 0 a martingale) is conditional on AX-03. It is proved from
`Upstream.DriftlessIntegralCriterion` in the proof file (`theta_interpretation`,
`both_labels_compatible`).
-/

open MeasureTheory Set
open scoped ENNReal

namespace Standalone.D8TailCompletions

/-- Admissible coefficient: Borel, nonzero on `(0, ∞)`, `1/g²` integrable on every compact
`[a, b] ⊂ (0, ∞)`. -/
structure Admissible (g : ℝ → ℝ) : Prop where
  measurable : Measurable g
  ne_zero : ∀ x, 0 < x → g x ≠ 0
  locInt : ∀ a b, 0 < a → 0 < b → IntegrableOn (fun x => 1 / g x ^ 2) (Icc a b)

/-- `g ∈ C_R(σ)`: admissible and equal to `σ` on `(0, R]`. -/
def Compatible (σ : ℝ → ℝ) (R : ℝ) (g : ℝ → ℝ) : Prop :=
  Admissible g ∧ ∀ x, 0 < x → x ≤ R → g x = σ x

/-- `F_c(g) = ∫_c^∞ x/g²(x) dx ∈ [0, ∞]`. -/
noncomputable def F (c : ℝ) (g : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioi c, ENNReal.ofReal (x / g x ^ 2)

/-- `J_cR = ∫_c^R x/σ²(x) dx`. -/
noncomputable def J (c R : ℝ) (σ : ℝ → ℝ) : ℝ := ∫ x in c..R, x / σ x ^ 2

/-- `θ(g) = 1` if `F_c(g) < ∞`, else `0`. -/
noncomputable def θ (c : ℝ) (g : ℝ → ℝ) : ℕ := if F c g < ∞ then 1 else 0

/-- The power completion `g_p`. -/
noncomputable def completion (σ : ℝ → ℝ) (R p : ℝ) : ℝ → ℝ :=
  fun x => if x ≤ R then σ x else σ R * (x / R) ^ p

/-- Claim 002. -/
def statement : Prop :=
  ∀ (σ : ℝ → ℝ) (c R : ℝ), Admissible σ → 0 < c → c < R →
    {y | ∃ g, Compatible σ R g ∧ F c g = y} =
        {y | ∃ a : ℝ, 0 < a ∧ y = ENNReal.ofReal (J c R σ + a)} ∪ {∞} ∧
    {n | ∃ g, Compatible σ R g ∧ θ c g = n} = {0, 1} ∧
    (∀ g, Compatible σ R g → ENNReal.ofReal (J c R σ) < F c g) ∧
    (∀ p, 1 ≤ p → Compatible σ R (completion σ R p)) ∧
    F c (completion σ R 1) = ∞ ∧
    (∀ p, 1 < p → F c (completion σ R p) =
      ENNReal.ofReal (J c R σ + R ^ 2 / (2 * (p - 1) * σ R ^ 2))) ∧
    ((ContinuousOn σ (Ioi 0) ∧ ∀ x, 0 < x → 0 < σ x) →
      ∀ p, 1 ≤ p → ContinuousOn (completion σ R p) (Ioi 0) ∧
        ∀ x, 0 < x → 0 < completion σ R p x)

end Standalone.D8TailCompletions
