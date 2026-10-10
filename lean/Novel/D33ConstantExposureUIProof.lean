import Standalone.D33ConstantExposureUI
import Novel.D1TwoEndpointProof
import Upstream.UniformIntegrabilityCriterion

/-!
# Claim 074: the proof

* **Part 1.** For `π = 0` the integrand vanishes, so (A) holds. For `π > 0`:
  - (A) fails, since `bπ(x) = πσ(x)/x ≠ 0` on all of `(0, ∞)`, a set of positive (infinite)
    Lebesgue measure;
  - `∞` is bad because the original scale `x − c` is unbounded, and `0` is bad because the goodness
    integrand is `π²/x`. Both are claim 001's lemmas (`not_goodAtInfty`, `not_goodAtZero`), reused;
  - (B), (C) and (D) each need a good endpoint.
* **Part 2.** Multiplication by `v₀ > 0` preserves and reflects martingality (claim 001's
  `martingale_const_mul_iff`) and uniform integrability (`uniformIntegrable_const_mul_iff`, since
  every `L¹` seminorm scales by `|v₀|`).
* **Part 3.** At `π = 0`, a martingale stopped at `T` is a martingale (claim 001's
  `martingale_stopAt`). For `π > 0`, claim 001's part (B) gives the finite-horizon rows.
* **The conditional form** (`ui_classification`) derives the premises from
  `Upstream.UniformIntegrabilityCriterion` (AX-63) and `Upstream.MartingaleCriterion` (AX-01) for a
  weak solution and its stochastic exponential.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Novel.D33ConstantExposureUI

open Standalone.D1TwoEndpoint Standalone.D33ConstantExposureUI Novel.D1TwoEndpoint

variable {σ : ℝ → ℝ} {p : ℝ}

/-! ## Part 1 -/

theorem zeroIntegrand_iff (hσ : VolHyp σ) (hp : 0 ≤ p) : ZeroIntegrand p σ ↔ p = 0 := by
  constructor
  · intro h
    by_contra hne
    have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hne)
    have h0 : volume {x : ℝ | ¬ (0 < x → bPi p σ x = 0)} = 0 := ae_iff.1 h
    have hsub : Ioi (0 : ℝ) ⊆ {x | ¬ (0 < x → bPi p σ x = 0)} := fun x hx => by
      simp only [mem_ofPred_eq, not_imp]
      refine ⟨hx, ?_⟩
      unfold bPi
      exact div_ne_zero (mul_ne_zero hp'.ne' (hσ.ne_zero x hx)) (ne_of_gt hx)
    have := measure_mono_null hsub h0
    simp at this
  · rintro rfl
    exact Eventually.of_forall fun x _ => by simp [bPi]

theorem uiCondition_iff (hσ : VolHyp σ) (hp : 0 ≤ p) (c : ℝ) : UICondition p σ c ↔ p = 0 := by
  rcases eq_or_lt_of_le hp with rfl | hp'
  · simp only [iff_true]
    exact Or.inl ((zeroIntegrand_iff hσ le_rfl).2 rfl)
  · have hne : p ≠ 0 := hp'.ne'
    simp only [hne, iff_false]
    rintro (h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact hne ((zeroIntegrand_iff hσ hp).1 h)
    · exact not_goodAtInfty c h
    · exact not_goodAtZero hσ hp' c h
    · exact not_goodAtZero hσ hp' c h

/-! ## Scaling -/

theorem uniformIntegrable_const_mul {ι α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ι → α → ℝ} {q : ℝ≥0∞} (h : UniformIntegrable f q μ) (c : ℝ) :
    UniformIntegrable (fun i x => c * f i x) q μ := by
  obtain ⟨hu, C, hC⟩ := h
  have e : ∀ i (μ' : Measure α), eLpNorm (fun x => c * f i x) q μ' = ‖c‖ₑ * eLpNorm (f i) q μ' :=
    fun i μ' => by rw [show (fun x => c * f i x) = c • f i from rfl, eLpNorm_const_smul]
  refine ⟨?_, ⟨‖c‖₊ * C, fun i => ?_⟩⟩
  · unfold UnifIntegrable at hu ⊢
    simp_rw [e, ← ENNReal.mul_iSup]
    have := ENNReal.Tendsto.const_mul hu (Or.inr (enorm_ne_top (x := c)))
    rwa [mul_zero] at this
  · rw [e, ENNReal.coe_mul]
    exact mul_le_mul' le_rfl (hC i)

theorem uniformIntegrable_const_mul_iff {ι α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ι → α → ℝ} {q : ℝ≥0∞} {c : ℝ} (hc : c ≠ 0) :
    UniformIntegrable (fun i x => c * f i x) q μ ↔ UniformIntegrable f q μ := by
  refine ⟨fun h => ?_, fun h => uniformIntegrable_const_mul h c⟩
  have := uniformIntegrable_const_mul h c⁻¹
  convert this using 1
  ext i x; field_simp

theorem uiMartingale_const_mul_iff {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {Z : ℝ≥0 → Ω → ℝ} {v : ℝ} (hv : v ≠ 0) :
    UIMartingale (fun t ω => v * Z t ω) 𝓕 P ↔ UIMartingale Z 𝓕 P :=
  and_congr (martingale_const_mul_iff hv) (uniformIntegrable_const_mul_iff hv)

/-! ## Parts 2 and 3 -/

theorem part2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω}
    {Z : ℝ≥0 → Ω → ℝ} {c v₀ : ℝ} (hσ : VolHyp σ) (hp : 0 ≤ p) (hv : 0 < v₀)
    (hUI : UIMartingale Z 𝓕 P ↔ UICondition p σ c) :
    UIMartingale (fun t ω => v₀ * Z t ω) 𝓕 P ↔ p = 0 := by
  rw [uiMartingale_const_mul_iff hv.ne', hUI, uiCondition_iff hσ hp]

theorem part3_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ℝ≥0 → Ω → ℝ} {c v₀ : ℝ} (hσ : VolHyp σ) (hv : 0 < v₀)
    (hUI : UIMartingale Z 𝓕 P ↔ UICondition 0 σ c) :
    UIMartingale (fun t ω => v₀ * Z t ω) 𝓕 P ∧
      ∀ T : ℝ≥0, MartingaleOn T (fun t ω => v₀ * Z t ω) 𝓕 P := by
  have h := (part2 hσ le_rfl hv hUI).2 rfl
  exact ⟨h, fun T => martingale_stopAt h.1 T⟩

theorem strictCase_iff_not :
    ¬ StrictCase p σ ↔ (p < 1 / 2 → ¬ I0Finite σ) ∧ (1 / 2 < p → ¬ IInftyFinite σ) := by
  unfold StrictCase; tauto

theorem part3_pos {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω}
    (hP : IsProbabilityMeasure P) {Z : ℝ≥0 → Ω → ℝ} {c v₀ : ℝ} (hσ : VolHyp σ) (hp : 0 < p)
    (hc : 0 < c) (hv : 0 < v₀) (hUI : UIMartingale Z 𝓕 P ↔ UICondition p σ c)
    (hnn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ Z t ω) (hcont : ∀ᵐ ω ∂P, Continuous fun t => Z t ω)
    (hlm : IsLocalMartingale Z 𝓕 P)
    (hMU : ∀ T : ℝ≥0, 0 < T → (MartingaleOn T Z 𝓕 P ↔ MUCondition p σ c)) :
    ¬ UIMartingale (fun t ω => v₀ * Z t ω) 𝓕 P ∧
      ∀ T : ℝ≥0, 0 < T → (MartingaleOn T (fun t ω => v₀ * Z t ω) 𝓕 P ↔
        (p < 1 / 2 → ¬ I0Finite σ) ∧ (1 / 2 < p → ¬ IInftyFinite σ)) := by
  refine ⟨fun h => hp.ne' ((part2 hσ hp.le hv hUI).1 h), fun T hT => ?_⟩
  rw [((partB P 𝓕 Z hσ hp hc hv hP hnn hcont hlm hMU).2 T hT).2, strictCase_iff_not]

theorem statement_holds : Standalone.D33ConstantExposureUI.statement.{u} :=
  ⟨fun _ _ c hσ hp _ => uiCondition_iff hσ hp c,
    fun _ _ _ _ _ _ _ hσ hp _ hv _ hUI => part2 hσ hp hv hUI,
    fun _ _ _ _ _ _ hσ _ hv hP hUI => by have := hP; exact part3_zero hσ hv hUI,
    fun _ _ _ _ _ _ _ hσ hp hc hv hP hUI hnn hcont hlm hMU =>
      part3_pos hP hσ hp hc hv hUI hnn hcont hlm hMU⟩

/-! ## The conditional form, from the hypothesis structures -/

section Upstream

open Upstream Upstream.Diffusion Upstream.DriftlessIntegralCriterion

/-- AX-63's condition at this instance is the condition restated in the statement. -/
theorem uiCondition_upstream_iff (c : ℝ) :
    Upstream.UICondition halfLine (fun _ => 0) σ (bPi p σ) c ↔
      Standalone.D33ConstantExposureUI.UICondition p σ c := by
  simp only [Upstream.UICondition, Standalone.D33ConstantExposureUI.UICondition, ZeroIntegrand,
    GoodRight, GoodLeft, GoodAtInfty, GoodAtZero, StateInterval.IntegrableNearRight,
    StateInterval.IntegrableNearLeft, halfLine_toLeft, halfLine_toRight, halfLine_rightTail,
    halfLine_leftTail, halfLine_mem_iff]
  exact Iff.rfl

/-- **Claim 074, conditional form.** Under the hypothesis structures for AX-63 and AX-01, for a weak
solution `S` of `dS = σ(S) dW` on `(0, ∞)` from `s₀ > 0` and the stochastic exponential `Z` of
`∫ bπ(S) dW`, `π ≥ 0`, the wealth `V = v₀ Z` is a uniformly integrable martingale on `[0, ∞)` iff
`π = 0`; for `π > 0` it is a martingale on `[0, T]`, `T > 0`, iff `I₀ = ∞` when `π < 1/2` and
`I∞ = ∞` when `π > 1/2`. -/
theorem ui_classification {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {X : SDEPrimitives P 𝓕 W}
    (U63 : UniformIntegrabilityCriterion P 𝓕 W X) (U1 : MartingaleCriterion P 𝓕 W X)
    {s₀ v₀ c : ℝ} {S : ℝ≥0 → Ω → ℝ} {ζ : Ω → WithTop ℝ≥0} {Z : ℝ≥0 → Ω → ℝ}
    (hW : IsFBrownian 𝓕 W P) (hσ : VolHyp σ) (hp : 0 ≤ p) (hc : 0 < c) (hv : 0 < v₀)
    (hs₀ : 0 < s₀) (hS : X.Solves halfLine (fun _ => 0) σ s₀ S ζ)
    (hZ : X.StochExp (bPi p σ) S ζ Z) :
    (UIMartingale (fun t ω => v₀ * Z t ω) 𝓕 P ↔ p = 0) ∧
      (0 < p → ∀ T : ℝ≥0, 0 < T →
        (Standalone.D1TwoEndpoint.MartingaleOn T (fun t ω => v₀ * Z t ω) 𝓕 P ↔
        (p < 1 / 2 → ¬ I0Finite σ) ∧ (1 / 2 < p → ¬ IInftyFinite σ))) := by
  have hco := coeffHyp_of_volHyp hσ
  have hin := integrandHyp_bPi (p := p) hσ
  have hs₀' : halfLine.Mem s₀ := (halfLine_mem_iff s₀).2 hs₀
  have hc' : halfLine.Mem c := (halfLine_mem_iff c).2 hc
  have hUI : UIMartingale Z 𝓕 P ↔ Standalone.D33ConstantExposureUI.UICondition p σ c :=
    (U63.ui_iff _ _ _ _ _ _ _ _ _ hW hco hin hs₀' hc' hS hZ).trans (uiCondition_upstream_iff c)
  refine ⟨part2 hσ hp hv hUI, fun hp' T hT => ?_⟩
  obtain ⟨hnn, hcont, hlm⟩ :=
    U1.nonneg_continuous_localMartingale _ _ _ _ _ _ _ _ hW hco hin hs₀' hS hZ
  have hMU : ∀ T : ℝ≥0, 0 < T →
      (Standalone.D1TwoEndpoint.MartingaleOn T Z 𝓕 P ↔ Standalone.D1TwoEndpoint.MUCondition p σ c) :=
    fun T hT => (U1.martingaleOn_iff _ _ _ _ _ _ _ _ _ hW hco hin hs₀' hc' hS hZ T hT).trans
      (muCondition_upstream_iff c)
  exact (part3_pos hW.1 hσ hp' hc hv hUI hnn hcont hlm hMU).2 T hT

end Upstream

end Novel.D33ConstantExposureUI
