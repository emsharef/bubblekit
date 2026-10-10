import Novel.D20ClockConfidenceStage

/-!
# Claim 067, parts 2 and 3

* **Pointwise.** `D^sel = max(G₀, D_G, max_(v ∈ C) D_v)` dominates every retained CEV null, and
  each clock-Gaussian law whose clock is retained. It is positive where the forecast is, so the
  score is finite. `C ⊆ 𝒱` gives `D^sel ≤ D^all`, hence (5). The safe score is at most
  `c/(1 + (c − 1)δ)`, which gives the necessary condition for strict rejection.
* **The covered moment.** Given `((A, Z), W)`, the tested law is the component's. When its clock
  is retained (or the component is a CEV null) the raw score has mean at most one (AX-58's
  pointwise step), and Markov's inequality bounds its size.
* **The failure-event correction.** Given `(A, Z)` on a Gaussian component, integrate over the
  references. On the covered event the clipped score has mean `≤ 1` and the raw rejection
  probability is `≤ α`; on the failure event, of probability `p ≤ δ` by (3), they are `≤ c` and
  `≤ 1`. So `E[min(E, c)] ≤ 1 + (c − 1)δ` and `P(E > 1/α) ≤ α + (1 − α)δ`. `cond_bound` then
  removes the latent component.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal

namespace Novel.D20ClockConfidence

open Standalone.D20ClockConfidence Standalone.CEVSupport Standalone.D13CEVCatalogue
  Standalone.D13DriftNull Standalone.D17ClockDrift Standalone.SplitLikelihoodDominated
  Standalone.D15JumpEnvelope

/-- Markov's inequality from a mean at most one. -/
theorem markov_lt {α' : Type} [MeasurableSpace α'] {L : Measure α'} {E : α' → ℝ≥0∞}
    (hE : Measurable E) (hm : ∫⁻ y, E y ∂L ≤ 1) {α : ℝ} (hα : 0 < α) :
    L {y | ENNReal.ofReal (1 / α) < E y} ≤ ENNReal.ofReal α := by
  have hmk := mul_meas_ge_le_lintegral₀ (μ := L) hE.aemeasurable (ENNReal.ofReal (1 / α))
  have hsub : {y | ENNReal.ofReal (1 / α) < E y} ⊆ {y | ENNReal.ofReal (1 / α) ≤ E y} :=
    fun y (h : _ < E y) => show _ ≤ E y from le_of_lt h
  have hle : ENNReal.ofReal (1 / α) * L {y | ENNReal.ofReal (1 / α) < E y} ≤ 1 :=
    (mul_le_mul_right (measure_mono hsub) _).trans (hmk.trans hm)
  have hinv : (ENNReal.ofReal (1 / α))⁻¹ = ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
  rw [← hinv, ENNReal.le_inv_iff_mul_le, mul_comm]
  exact hle

/-- The normalizer `1 + (c − 1)δ` is at least one. -/
theorem norm_ge_one {δ c : ℝ} (hδ : 0 < δ) (hc : 1 ≤ c) : 1 ≤ 1 + (c - 1) * δ := by nlinarith

theorem Esafe_le_self {δ c : ℝ} (hδ : 0 < δ) (hc : 1 ≤ c) (E : ℝ≥0∞) : Esafe δ c E ≤ E := by
  unfold Esafe
  refine ENNReal.div_le_of_le_mul ((min_le_left _ _).trans ?_)
  calc E = 1 * E := (one_mul E).symm
    _ ≤ ENNReal.ofReal (1 + (c - 1) * δ) * E := by
        gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (norm_ge_one hδ hc)
    _ = E * ENNReal.ofReal (1 + (c - 1) * δ) := mul_comm _ _

theorem Esafe_le_cap {δ c : ℝ} (hδ : 0 < δ) (hc : 1 ≤ c) (E : ℝ≥0∞) :
    Esafe δ c E ≤ ENNReal.ofReal (c / (1 + (c - 1) * δ)) := by
  unfold Esafe
  rw [ENNReal.ofReal_div_of_pos (by linarith [norm_ge_one hδ hc])]
  gcongr
  exact min_le_right _ _

theorem Esafe_mono {δ c : ℝ} {E E' : ℝ≥0∞} (h : E ≤ E') : Esafe δ c E ≤ Esafe δ c E' := by
  unfold Esafe; gcongr

/-- The necessary condition for strict rejection of the safe score. -/
theorem reject_cond {δ c α : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hc : 1 ≤ c) (hα : 0 < α) {E : ℝ≥0∞}
    (h : ENNReal.ofReal (1 / α) < Esafe δ c E) : δ < α ∧ (1 - δ) / (α - δ) < c := by
  have hN := norm_ge_one hδ hc
  have h' := h.trans_le (Esafe_le_cap hδ hc E)
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h'
  rw [div_lt_div_iff₀ hα (by linarith)] at h'
  have hkey : 1 - δ < c * (α - δ) := by nlinarith
  have hαδ : δ < α := by
    by_contra hle; push Not at hle
    nlinarith
  refine ⟨hαδ, ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  linarith

end Novel.D20ClockConfidence
