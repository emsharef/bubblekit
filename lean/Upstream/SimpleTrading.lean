import Upstream.Diffusion

/-!
# AX-08: finite predictable gains preserve continuous local martingales

Cited input: [etheridge2018continuous], (33)--(34), Theorem 7.11, Definition 7.12,
the elementary-integral formula and Proposition 7.14 on p. 56. For unbounded
finite coefficients, the finite-sum identification uses Proposition 7.14 on
bounded coefficient truncations, as detailed in AX-08. The finite sum is concrete; the
stochastic closure theorem is a hypothesis, not reconstructed here.

`constantInstance` is DEGENERATE, not vacuous: the integrator is the nonzero
constant process 1, so every gain is zero. Its hypotheses are satisfiable
(`constant_premises`). This gives no model of a stochastic price or a strict
local martingale, and proves no D9 classification.
-/

open MeasureTheory
open scoped NNReal

namespace Upstream.SimpleTrading

def gain {Ω : Type*} {N : ℕ} (X : ℝ≥0 → Ω → ℝ)
    (times : Fin (N + 1) → ℝ≥0) (holdings : Fin N → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin N, holdings i ω *
    (X (min t (times i.succ)) ω - X (min t (times i.castSucc)) ω)

end Upstream.SimpleTrading

namespace Upstream

structure SimpleTrading {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) : Prop where
  gains_local : ∀ (N : ℕ) (times : Fin (N + 1) → ℝ≥0)
    (holdings : Fin N → Ω → ℝ),
    IsProbabilityMeasure P → Diffusion.UsualConditions 𝓕 P →
    StrictMono times →
    (∀ i, Measurable[𝓕 (times i.castSucc)] (holdings i)) →
    Integrable (X 0) P →
    (∀ᵐ ω ∂P, Continuous fun t => X t ω) →
    Diffusion.IsLocalMartingale X 𝓕 P →
    (∀ᵐ ω ∂P, Continuous fun t => SimpleTrading.gain X times holdings t ω) ∧
    Diffusion.IsLocalMartingale (SimpleTrading.gain X times holdings) 𝓕 P

namespace SimpleTrading

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) [IsProbabilityMeasure P]

theorem constant_premises :
    Integrable (fun _ : Ω => (1 : ℝ)) P ∧
    (∀ᵐ _ω ∂P, Continuous fun _ : ℝ≥0 => (1 : ℝ)) ∧
    Diffusion.IsLocalMartingale (fun _ : ℝ≥0 => fun _ : Ω => (1 : ℝ)) 𝓕 P := by
  exact ⟨integrable_const 1, Filter.Eventually.of_forall (fun _ => continuous_const),
    Diffusion.isLocalMartingale_of_martingale (martingale_const 𝓕 P 1)⟩

def constantInstance : SimpleTrading P 𝓕 (fun _ _ => (1 : ℝ)) where
  gains_local N times holdings _ _ _ _ _ _ _ := by
    have hg : gain (fun (_ : ℝ≥0) (_ : Ω) => (1 : ℝ)) times holdings =
        (fun _ : ℝ≥0 => fun _ : Ω => (0 : ℝ)) := by
      funext t ω
      simp [gain]
    rw [hg]
    exact ⟨Filter.Eventually.of_forall (fun _ => continuous_const),
      Diffusion.isLocalMartingale_of_martingale (martingale_const 𝓕 P 0)⟩

/-- The instance has a base satisfying the usual-conditions premise. -/
theorem unit_usual_conditions :
    Diffusion.UsualConditions Diffusion.unitFiltration (Measure.dirac ()) :=
  Diffusion.usualConditions_unit

/-- Nonzero holdings are allowed in the degenerate model. -/
theorem one_holdings_measurable (N : ℕ) (times : Fin (N + 1) → ℝ≥0) :
    ∀ i : Fin N, Measurable[𝓕 (times i.castSucc)] (fun _ : Ω => (1 : ℝ)) := by
  intro i
  exact measurable_const

end SimpleTrading
end Upstream
