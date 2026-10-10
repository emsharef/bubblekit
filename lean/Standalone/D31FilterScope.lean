import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Claim 043 (D31): replacing flagged returns by zero does not preserve Gaussian calibration

Statement only; the proof is `Novel/D31FilterScopeProof.lean`. Source claim:
`claims/043-d31-filter-scope.md`.

**Structure.** `statement := law ∧ counterexample ∧ corrected`.
* `law`: part 1. The jump-removal map `H_a` pushes a Lebesgue density `f` forward to the density
  `f_a` with respect to `ν_a` = Lebesgue on `{0 < |y| ≤ a}` plus a Dirac mass at `0`; the result has
  total mass one. For a strictly positive density `p`:
  - `P(Y = 0) = ρ_p(a) ∈ (0, 1)`;
  - the law of `Y` is not absolutely continuous with respect to Lebesgue, so it is no nondegenerate
    Gaussian;
  - changing `p` at the single point `0` leaves the atom's mass unchanged.
* `counterexample`: part 2, with `R` standard normal (claim 042's null `b = 1/2` with one
  return and `Δ = v = w = 1`):
  - the profiled denominator is `sup_b φ(r; b − 1/2, 1) = 1/√(2π)`, attained;
  - the scores are `E(r) = ε⁻¹ exp(−r²/(2ε²))`;
  - `E[E(R)] = 1/√(1+ε²)`, while `E[E_naive(Y)] ≥ ρ/ε`;
  - `ε = ρ/2` gives a filtered mean at least `2`;
  - `α = ρ/2` and `ε = ρ/4` give rejection probability at least `ρ = 2α > α`;
  - for every `0 < α < 1` some cutoff `a > 0` has `ρ > α`, and then every `0 < ε < α` violates
    level `α`.
* `corrected`: part 3. Transform a family of densities containing the actual `p`. A measurable
  positive `D_a` dominating every transformed density on the support of `ν_a` gives
  `E[E_correct(Y)] ≤ 1`, AX-58's step proved directly with the supplied density. With `D_a = p_a`
  the mean is exactly one and the ratio at zero is `ρ_q(a)/ρ_p(a)`.

**Encodings.** Densities are real, measurable and nonnegative with Lebesgue integral one (as
`∫⁻ ofReal`). `ρ_f(a)` is the real value of `∫_(|r|>a) f`. Means are lower integrals of the
(nonnegative) scores. The prices `1, exp R` and `1, exp Y` are positive trivially and are not
restated.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Standalone.D31FilterScope

/-- The jump-removal map: `H_a(r) = r` if `|r| ≤ a`, and `0` otherwise. -/
noncomputable def Ha (a r : ℝ) : ℝ := if |r| ≤ a then r else 0

/-- `ρ_f(a) = ∫_(|r|>a) f`. -/
noncomputable def rho (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  (∫⁻ r in {r | a < |r|}, ENNReal.ofReal (f r)).toReal

/-- The retained set `{0 < |y| ≤ a}`. -/
def kept (a : ℝ) : Set ℝ := {y | 0 < |y| ∧ |y| ≤ a}

/-- `ν_a`: Lebesgue on the retained set plus a Dirac mass at `0`. -/
noncomputable def nu (a : ℝ) : Measure ℝ := volume.restrict (kept a) + Measure.dirac 0

/-- The transformed density `f_a`. -/
noncomputable def fa (f : ℝ → ℝ) (a : ℝ) (y : ℝ) : ℝ :=
  open Classical in if y = 0 then rho f a else if |y| ≤ a then f y else 0

/-- A Lebesgue probability density. -/
def IsDensity (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (∀ r, 0 ≤ f r) ∧ ∫⁻ r, ENNReal.ofReal (f r) = 1

/-- The law with density `f`. -/
noncomputable def lawOf (f : ℝ → ℝ) : Measure ℝ := volume.withDensity fun r => ENNReal.ofReal (f r)

/-- Part 1. -/
def law : Prop :=
  ∀ (a : ℝ), 0 < a →
    -- Pushforward of any density.
    (∀ f, IsDensity f →
      (lawOf f).map (Ha a) = (nu a).withDensity (fun y => ENNReal.ofReal (fa f a y)) ∧
      ∫⁻ y, ENNReal.ofReal (fa f a y) ∂(nu a) = 1) ∧
    -- The atom, for a strictly positive density and the actual observation.
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (R : Ω → ℝ) (p : ℝ → ℝ),
      IsDensity p → (∀ r, 0 < p r) → Measurable R → P.map R = lawOf p →
      P.map (fun ω => Ha a (R ω)) = (nu a).withDensity (fun y => ENNReal.ofReal (fa p a y)) ∧
      P {ω | Ha a (R ω) = 0} = ENNReal.ofReal (rho p a) ∧ 0 < rho p a ∧ rho p a < 1 ∧
      ¬ P.map (fun ω => Ha a (R ω)) ≪ volume ∧
      (∀ (μ : ℝ) (v : ℝ≥0), v ≠ 0 → P.map (fun ω => Ha a (R ω)) ≠ gaussianReal μ v) ∧
      ∀ c : ℝ, rho (Function.update p 0 c) a = rho p a

/-- Part 2's profiled denominator `sup_b φ(r; b − 1/2, 1)`. -/
noncomputable def Dprof (r : ℝ) : ℝ := ⨆ b : ℝ, gaussianPDFReal (b - 1 / 2) 1 r

/-- Part 2's score with the forecast `φ(·; 0, ε²)`. -/
noncomputable def score (ε r : ℝ) : ℝ := gaussianPDFReal 0 (ε ^ 2).toNNReal r / Dprof r

/-- Part 2. -/
def counterexample : Prop :=
  -- The profiled denominator and the scores.
  (∀ r : ℝ, Dprof r = 1 / Real.sqrt (2 * Real.pi) ∧ gaussianPDFReal (r + 1 / 2 - 1 / 2) 1 r = Dprof r) ∧
  (∀ ε r : ℝ, 0 < ε → score ε r = ε⁻¹ * Real.exp (-r ^ 2 / (2 * ε ^ 2))) ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (R : Ω → ℝ) (a : ℝ),
    Measurable R → P.map R = gaussianReal 0 1 → 0 < a →
    let ρ := rho (gaussianPDFReal 0 1) a
    (∀ ε : ℝ, 0 < ε →
      ∫⁻ ω, ENNReal.ofReal (score ε (R ω)) ∂P = ENNReal.ofReal (1 / Real.sqrt (1 + ε ^ 2)) ∧
      ENNReal.ofReal (ρ / ε) ≤ ∫⁻ ω, ENNReal.ofReal (score ε (Ha a (R ω))) ∂P) ∧
    -- `ε = ρ/2`: the filtered mean is at least two.
    2 ≤ ∫⁻ ω, ENNReal.ofReal (score (ρ / 2) (Ha a (R ω))) ∂P ∧
    -- `α = ρ/2`, `ε = ρ/4`: rejection probability at least `ρ = 2α > α`.
    (ENNReal.ofReal ρ ≤ P {ω | 1 / (ρ / 2) < score (ρ / 4) (Ha a (R ω))} ∧ ρ / 2 < ρ) ∧
    -- Any level, with a small cutoff.
    ∀ α : ℝ, 0 < α → α < 1 → ∃ a' : ℝ, 0 < a' ∧ α < rho (gaussianPDFReal 0 1) a' ∧
      ∀ ε : ℝ, 0 < ε → ε < α →
        ENNReal.ofReal (rho (gaussianPDFReal 0 1) a') ≤
          P {ω | 1 / α < score ε (Ha a' (R ω))}

/-- The support of `ν_a`. -/
def supp (a : ℝ) : Set ℝ := {y | y = 0 ∨ y ∈ kept a}

/-- Part 3's corrected score `q_a/D_a` on the support, zero elsewhere. -/
noncomputable def Ecorr (q : ℝ → ℝ) (a : ℝ) (D : ℝ → ℝ) (y : ℝ) : ℝ :=
  open Classical in if y ∈ supp a then fa q a y / D y else 0

/-- Part 3. -/
def corrected : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (R : Ω → ℝ)
    {Θ : Type} (pθ : Θ → ℝ → ℝ) (θ₀ : Θ) (q D : ℝ → ℝ) (a : ℝ), 0 < a →
    (∀ θ, IsDensity (pθ θ)) → (∀ θ r, 0 < pθ θ r) → IsDensity q →
    Measurable R → P.map R = lawOf (pθ θ₀) →
    Measurable D → (∀ y ∈ supp a, 0 < D y) → (∀ θ, ∀ y ∈ supp a, fa (pθ θ) a y ≤ D y) →
    ∫⁻ ω, ENNReal.ofReal (Ecorr q a D (Ha a (R ω))) ∂P ≤ 1 ∧
    -- Against the single actual density: the exact ratio, mean one, and its value at zero.
    ∫⁻ ω, ENNReal.ofReal (Ecorr q a (fa (pθ θ₀) a) (Ha a (R ω))) ∂P = 1 ∧
    Ecorr q a (fa (pθ θ₀) a) 0 = rho q a / rho (pθ θ₀) a

/-- Claim 043. -/
def statement : Prop := law ∧ counterexample ∧ corrected

end Standalone.D31FilterScope
