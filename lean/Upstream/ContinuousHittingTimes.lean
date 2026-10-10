import Upstream.BoundedStopping

/-!
# AX-11: continuous adapted processes hit open sets at stopping times

Source: [etheridge2018continuous], equation (14) and Exercise 4.5(i), p. 24.
The source states the right-continuous-path result for the right-continuation
of the filtration. We restrict to continuous paths and a right-continuous
filtration. The textbook stopping-time theorem is a hypothesis field, not
reconstructed here. No martingale, Brownian motion or positivity is required.

`degenerateInstance` is genuine and DEGENERATE, not vacuous: on the one-point
base every time-valued random variable is a stopping time. Its field holds for
every continuous adapted process there. `constant_premises`, `constant_hit`
and `constant_miss` exercise admissible inputs and the zero/infinity conventions.
This provides no stochastic price model and does not formalize claim 003's
canonical-measure argument by itself.
-/

open MeasureTheory Set
open scoped NNReal

namespace Upstream

namespace ContinuousHittingTimes

/-- First entry into a set, with the infimum taken in the extended time order. -/
noncomputable def openHitTime {Ω : Type*} (S : ℝ≥0 → Ω → ℝ)
    (Γ : Set ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf ((fun t : ℝ≥0 => (t : WithTop ℝ≥0)) '' {t | S t ω ∈ Γ})

end ContinuousHittingTimes

/-- AX-11, on a fixed filtration. The probability does not enter this input. -/
structure ContinuousHittingTimes {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration ℝ≥0 mΩ) : Prop where
  hit_open : 𝓕.IsRightContinuous → ∀ (S : ℝ≥0 → Ω → ℝ),
    Adapted 𝓕 S → (∀ ω, Continuous fun t => S t ω) →
    ∀ Γ : Set ℝ, IsOpen Γ →
    IsStoppingTime 𝓕 (ContinuousHittingTimes.openHitTime S Γ)

namespace ContinuousHittingTimes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- AX-04's concrete exit time is entry into the open set outside [-n,n]. -/
theorem exitTime_stopping (input : ContinuousHittingTimes 𝓕)
    (h𝓕 : 𝓕.IsRightContinuous) (S : ℝ≥0 → Ω → ℝ)
    (hS : Adapted 𝓕 S) (hc : ∀ ω, Continuous fun t => S t ω) (n : ℝ) :
    IsStoppingTime 𝓕 (Stopping.exitTime S n) := by
  exact input.hit_open h𝓕 S hS hc {x | n < |x|}
    (isOpen_lt continuous_const continuous_abs)

/-- The one-point model satisfies the field for all processes, not an empty class. -/
def degenerateInstance : ContinuousHittingTimes Diffusion.unitFiltration where
  hit_open _ S _ _ Γ _ t := by
    have h : openHitTime S Γ = (fun _ : Unit => openHitTime S Γ ()) := by
      funext ω
      cases ω
      rfl
    rw [h]
    exact MeasurableSet.const _

theorem constant_premises :
    Diffusion.unitFiltration.IsRightContinuous ∧
    Adapted Diffusion.unitFiltration (fun _ : ℝ≥0 => fun _ : Unit => (1 : ℝ)) ∧
    (∀ _ω : Unit, Continuous fun _ : ℝ≥0 => (1 : ℝ)) := by
  exact ⟨Diffusion.usualConditions_unit.1, fun _ => measurable_const,
    fun _ => continuous_const⟩

/-- A path already in the target has hitting time zero. -/
theorem constant_hit {Γ : Set ℝ} {c : ℝ} (hc : c ∈ Γ) (ω : Ω) :
    openHitTime (fun _ _ => c) Γ ω = 0 := by
  apply le_antisymm
  · exact sInf_le ⟨0, hc, rfl⟩
  · exact bot_le

/-- A constant path outside the target has hitting time infinity. -/
theorem constant_miss {Γ : Set ℝ} {c : ℝ} (hc : c ∉ Γ) (ω : Ω) :
    openHitTime (fun _ _ => c) Γ ω = ⊤ := by
  have h : {t : ℝ≥0 | (fun _ _ => c) t ω ∈ Γ} = ∅ := by
    simp [hc]
  rw [openHitTime, h, Set.image_empty, sInf_empty]

end ContinuousHittingTimes
end Upstream
