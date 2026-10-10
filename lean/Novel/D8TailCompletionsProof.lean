import Standalone.D8TailCompletions
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Piecewise
import Upstream.DriftlessIntegralCriterion

/-!
# Proof of claim 002 (D8): exact identified sets of the JKP integral

Proves `Standalone.D8TailCompletions.statement` (`statement_holds`).

* `F_split` is (3): `F_c(g) = J_cR + ∫_R^∞ x/g²`.
* `T_pos`: the tail is strictly positive, so `J_cR` is not attained (`J_lt_F`), and every
  compatible value lies in `{J + a : a > 0} ∪ {∞}` (`F_mem`).
* `compatible_completion`: the power completions `g_p` are admissible and agree with `σ` on `(0, R]`.
* `tail_integrand` is (5).
* `T_completion_one`: the `p = 1` tail is infinite, by Mathlib's `integrableOn_Ioi_rpow_iff`.
* `T_completion` is (6), via `integral_Ioi_rpow_of_lt`. The choice `p = 1 + R²/(2k²a)` realizes
  `J + a` (`image_F`).
* `image_θ` is (2), and `completion_pos_continuous` is the continuity remark.

The bubble interpretation is conditional on AX-03: `theta_interpretation` and
`both_labels_compatible` assume `Upstream.DriftlessIntegralCriterion`, whose only instance is
vacuous. `jkpIntegrable_iff_F` identifies AX-03's tail-integrability with `F_c(g) < ∞`.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Novel.D8TailCompletions

open Standalone.D8TailCompletions

variable {σ g : ℝ → ℝ} {c R : ℝ}

theorem jkp_integrableOn_Icc (hg : Admissible g) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x => x / g x ^ 2) (Icc a b) :=
  IntegrableOn.congr_fun ((hg.locInt a b ha hb).continuousOn_mul continuousOn_id isCompact_Icc)
    (fun x _ => mul_one_div x (g x ^ 2)) measurableSet_Icc

theorem jkp_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x / g x ^ 2 := div_nonneg hx (sq_nonneg _)

theorem measurable_jkp (hg : Admissible g) : Measurable fun x => ENNReal.ofReal (x / g x ^ 2) :=
  ENNReal.measurable_ofReal.comp (measurable_id.div (hg.measurable.pow_const 2))

theorem J_nonneg (hc : 0 < c) (hcR : c < R) : 0 ≤ J c R σ :=
  intervalIntegral.integral_nonneg hcR.le fun _ hx => jkp_nonneg (hc.le.trans hx.1)

theorem ofReal_J (hσ : Admissible σ) (hc : 0 < c) (hcR : c < R) :
    ENNReal.ofReal (J c R σ) = ∫⁻ x in Ioc c R, ENNReal.ofReal (x / σ x ^ 2) := by
  rw [J, intervalIntegral.integral_of_le hcR.le]
  refine ofReal_integral_eq_lintegral_ofReal
    ((jkp_integrableOn_Icc hσ hc (hc.trans hcR)).mono_set Ioc_subset_Icc_self) ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx =>
    jkp_nonneg (hc.le.trans hx.1.le))

/-- The tail `∫_R^∞ x/g²`. -/
noncomputable def T (R : ℝ) (g : ℝ → ℝ) : ℝ≥0∞ := ∫⁻ x in Ioi R, ENNReal.ofReal (x / g x ^ 2)

/-- (3): `F_c(g) = J_cR + ∫_R^∞ x/g²`. -/
theorem F_split (hσ : Admissible σ) (hc : 0 < c) (hcR : c < R) (hg : Compatible σ R g) :
    F c g = ENNReal.ofReal (J c R σ) + T R g := by
  rw [F, ← Ioc_union_Ioi_eq_Ioi hcR.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same,
    ofReal_J hσ hc hcR, T]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  rw [hg.2 x (hc.trans hx.1) hx.2]

/-- The tail is strictly positive. -/
theorem T_pos (hg : Admissible g) (hR : 0 < R) : 0 < T R g := by
  rw [T, lintegral_pos_iff_support (measurable_jkp hg)]
  refine lt_of_lt_of_le ?_ (measure_mono (μ := volume.restrict (Ioi R)) (s := Ioi R) fun x hx => ?_)
  · rw [Measure.restrict_apply_self, Real.volume_Ioi]; exact ENNReal.zero_lt_top
  · have hx0 : 0 < x := hR.trans hx
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact div_pos hx0 (by have := hg.ne_zero x hx0; positivity)

/-- The lower endpoint `J` is not attained. -/
theorem J_lt_F (hσ : Admissible σ) (hc : 0 < c) (hcR : c < R) (hg : Compatible σ R g) :
    ENNReal.ofReal (J c R σ) < F c g := by
  rw [F_split hσ hc hcR hg]
  exact ENNReal.lt_add_right ENNReal.ofReal_ne_top (T_pos hg.1 (hc.trans hcR)).ne'

/-- Every compatible value lies in `{J + a : a > 0} ∪ {∞}`. -/
theorem F_mem (hσ : Admissible σ) (hc : 0 < c) (hcR : c < R) (hg : Compatible σ R g) :
    F c g ∈ {y | ∃ a : ℝ, 0 < a ∧ y = ENNReal.ofReal (J c R σ + a)} ∪ {∞} := by
  rw [F_split hσ hc hcR hg]
  by_cases hT : T R g = ∞
  · right; rw [hT, add_top]; rfl
  · left
    have hpos := T_pos hg.1 (hc.trans hcR)
    refine ⟨(T R g).toReal, ENNReal.toReal_pos hpos.ne' hT, ?_⟩
    rw [ENNReal.ofReal_add (J_nonneg hc hcR) ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hT]

/-! ## The power completions -/

theorem completion_of_le {p x : ℝ} (hx : x ≤ R) : completion σ R p x = σ x := by
  simp [completion, hx]

theorem completion_of_gt {p x : ℝ} (hx : R < x) : completion σ R p x = σ R * (x / R) ^ p := by
  simp [completion, not_le.2 hx]

theorem completion_eq_tail (hR : 0 < R) {p x : ℝ} (hx : R ≤ x) :
    completion σ R p x = σ R * (x / R) ^ p := by
  rcases hx.lt_or_eq with h | h
  · exact completion_of_gt h
  · subst h; rw [completion_of_le le_rfl, div_self hR.ne', Real.one_rpow, mul_one]

theorem compatible_completion (hσ : Admissible σ) (hR : 0 < R) (p : ℝ) :
    Compatible σ R (completion σ R p) := by
  have hk : σ R ≠ 0 := hσ.ne_zero R hR
  refine ⟨⟨?_, fun x hx => ?_, fun a b ha hb => ?_⟩, fun x _ hx => completion_of_le hx⟩
  · exact Measurable.ite measurableSet_Iic hσ.measurable
      (measurable_const.mul ((measurable_id.div_const R).pow_const p))
  · rcases le_or_gt x R with h | h
    · rw [completion_of_le h]; exact hσ.ne_zero x hx
    · rw [completion_of_gt h]
      exact mul_ne_zero hk (Real.rpow_pos_of_pos (div_pos hx hR) p).ne'
  · set M := max R b
    have h1 : IntegrableOn (fun x => 1 / completion σ R p x ^ 2) (Icc a R) :=
      IntegrableOn.congr_fun (hσ.locInt a R ha hR)
        (fun x hx => by simp only [completion_of_le hx.2]) measurableSet_Icc
    have hcont : ContinuousOn (fun x : ℝ => 1 / (σ R * (x / R) ^ p) ^ 2) (Icc R M) := by
      refine continuousOn_const.div ((continuousOn_const.mul ?_).pow 2) fun x hx => ?_
      · exact (continuousOn_id.div_const R).rpow_const fun x hx =>
          Or.inl (div_pos (hR.trans_le hx.1) hR).ne'
      · exact pow_ne_zero _ (mul_ne_zero hk (Real.rpow_pos_of_pos
          (div_pos (hR.trans_le hx.1) hR) p).ne')
    have h2 : IntegrableOn (fun x => 1 / completion σ R p x ^ 2) (Icc R M) :=
      IntegrableOn.congr_fun hcont.integrableOn_Icc
        (fun x hx => by simp only [completion_eq_tail hR hx.1]) measurableSet_Icc
    refine (h1.union h2).mono_set fun x hx => ?_
    rcases le_or_gt x R with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h.le, hx.2.trans (le_max_right _ _)⟩

/-- The tail integrand of `g_p`: `x/g_p² = (R^{2p}/k²) x^{1−2p}` for `x > R`. -/
theorem tail_integrand (hσ : Admissible σ) (hR : 0 < R) {p x : ℝ} (hx : R < x) :
    x / completion σ R p x ^ 2 = R ^ (2 * p) / σ R ^ 2 * x ^ (1 - 2 * p) := by
  have hx0 : 0 < x := hR.trans hx
  have hk : σ R ≠ 0 := hσ.ne_zero R hR
  rw [completion_of_gt hx, mul_pow, ← Real.rpow_natCast ((x / R) ^ p), ← Real.rpow_mul
    (div_pos hx0 hR).le, Real.div_rpow hx0.le hR.le, Real.rpow_sub hx0, Real.rpow_one]
  push_cast
  have h1 : 0 < x ^ (p * 2) := Real.rpow_pos_of_pos hx0 _
  have h2 : 0 < R ^ (p * 2) := Real.rpow_pos_of_pos hR _
  rw [show 2 * p = p * 2 by ring]
  field_simp

theorem tail_integrableOn_iff (hσ : Admissible σ) (hR : 0 < R) (p : ℝ) :
    IntegrableOn (fun x => x / completion σ R p x ^ 2) (Ioi R) ↔
      IntegrableOn (fun x : ℝ => x ^ (1 - 2 * p)) (Ioi R) := by
  have hk : σ R ≠ 0 := hσ.ne_zero R hR
  have hK : R ^ (2 * p) / σ R ^ 2 ≠ 0 := div_ne_zero (Real.rpow_pos_of_pos hR _).ne' (pow_ne_zero _ hk)
  rw [integrableOn_congr_fun (s := Ioi R) (fun x (hx : x ∈ Ioi R) => tail_integrand hσ hR hx)
    measurableSet_Ioi]
  refine ⟨fun h => ?_, fun h => h.const_mul _⟩
  exact (h.const_mul (R ^ (2 * p) / σ R ^ 2)⁻¹).congr
    (ae_of_all _ fun x => by simp only; rw [← mul_assoc, inv_mul_cancel₀ hK, one_mul])

/-- For a nonnegative measurable integrand, the lintegral is finite iff the function is integrable. -/
theorem lintegral_lt_top_iff (hg : Admissible g) (hR : 0 ≤ R) :
    T R g < ∞ ↔ IntegrableOn (fun x => x / g x ^ 2) (Ioi R) := by
  have h0 : 0 ≤ᵐ[volume.restrict (Ioi R)] fun x => x / g x ^ 2 :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx =>
      jkp_nonneg (hR.trans (le_of_lt hx)))
  exact ⟨fun hT => ⟨(measurable_id.div (hg.measurable.pow_const 2)).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal h0).2 hT⟩, fun h => (hasFiniteIntegral_iff_ofReal h0).1 h.2⟩

theorem T_completion_one (hσ : Admissible σ) (hR : 0 < R) : T R (completion σ R 1) = ∞ := by
  by_contra h
  have hI := (lintegral_lt_top_iff (compatible_completion hσ hR 1).1 hR.le).1 (lt_top_iff_ne_top.2 h)
  rw [tail_integrableOn_iff hσ hR, integrableOn_Ioi_rpow_iff hR] at hI
  norm_num at hI

theorem T_completion (hσ : Admissible σ) (hR : 0 < R) {p : ℝ} (hp : 1 < p) :
    T R (completion σ R p) = ENNReal.ofReal (R ^ 2 / (2 * (p - 1) * σ R ^ 2)) := by
  have hk : σ R ≠ 0 := hσ.ne_zero R hR
  have ha : 1 - 2 * p < -1 := by linarith
  have hI : IntegrableOn (fun x => x / completion σ R p x ^ 2) (Ioi R) :=
    (tail_integrableOn_iff hσ hR p).2 (integrableOn_Ioi_rpow_of_lt ha hR)
  rw [T, ← ofReal_integral_eq_lintegral_ofReal hI ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun x hx => jkp_nonneg (hR.trans hx).le))]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x (hx : x ∈ Ioi R) => tail_integrand hσ hR hx),
    integral_const_mul, integral_Ioi_rpow_of_lt ha hR]
  have hRR : R ^ (2 * p) * R ^ (1 - 2 * p + 1) = R ^ 2 := by
    rw [← Real.rpow_add hR, show 2 * p + (1 - 2 * p + 1) = ((2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have hp1 : p - 1 ≠ 0 := by linarith
  have hq : 1 - 2 * p + 1 ≠ 0 := by linarith
  rw [show R ^ (2 * p) / σ R ^ 2 * (-R ^ (1 - 2 * p + 1) / (1 - 2 * p + 1)) =
    (R ^ (2 * p) * R ^ (1 - 2 * p + 1)) / (σ R ^ 2 * (2 * (p - 1))) by field_simp; ring, hRR]
  ring

/-- (1) -/
theorem image_F (hσ : Admissible σ) (hc : 0 < c) (hcR : c < R) :
    {y | ∃ g, Compatible σ R g ∧ F c g = y} =
      {y | ∃ a : ℝ, 0 < a ∧ y = ENNReal.ofReal (J c R σ + a)} ∪ {∞} := by
  have hR : 0 < R := hc.trans hcR
  have hk : σ R ≠ 0 := hσ.ne_zero R hR
  ext y
  refine ⟨fun ⟨g, hg, hy⟩ => hy ▸ F_mem hσ hc hcR hg, fun hy => ?_⟩
  rcases hy with ⟨a, ha, rfl⟩ | hy
  · set p := 1 + R ^ 2 / (2 * σ R ^ 2 * a)
    have hp : 1 < p := by
      have : 0 < R ^ 2 / (2 * σ R ^ 2 * a) := by positivity
      linarith
    refine ⟨completion σ R p, compatible_completion hσ hR p, ?_⟩
    rw [F_split hσ hc hcR (compatible_completion hσ hR p), T_completion hσ hR hp,
      ← ENNReal.ofReal_add (J_nonneg hc hcR) (by positivity)]
    congr 2
    simp only [p, add_sub_cancel_left]
    field_simp
  · refine ⟨completion σ R 1, compatible_completion hσ hR 1, ?_⟩
    rw [F_split hσ hc hcR (compatible_completion hσ hR 1), T_completion_one hσ hR, add_top]
    exact hy.symm

theorem F_completion_one (hσ : Admissible σ) (hc : 0 < c) (hcR : c < R) :
    F c (completion σ R 1) = ∞ := by
  rw [F_split hσ hc hcR (compatible_completion hσ (hc.trans hcR) 1),
    T_completion_one hσ (hc.trans hcR), add_top]

theorem F_completion (hσ : Admissible σ) (hc : 0 < c) (hcR : c < R) {p : ℝ} (hp : 1 < p) :
    F c (completion σ R p) = ENNReal.ofReal (J c R σ + R ^ 2 / (2 * (p - 1) * σ R ^ 2)) := by
  have hR := hc.trans hcR
  have hp1 : 0 < p - 1 := by linarith
  rw [F_split hσ hc hcR (compatible_completion hσ hR p), T_completion hσ hR hp,
    ← ENNReal.ofReal_add (J_nonneg hc hcR) (by positivity)]

/-- (2) -/
theorem image_θ (hσ : Admissible σ) (hc : 0 < c) (hcR : c < R) :
    {n | ∃ g, Compatible σ R g ∧ θ c g = n} = {0, 1} := by
  have hR := hc.trans hcR
  ext n
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun ⟨g, _, hn⟩ => ?_, fun hn => ?_⟩
  · rw [← hn, θ]; split_ifs <;> simp
  · rcases hn with rfl | rfl
    · refine ⟨completion σ R 1, compatible_completion hσ hR 1, ?_⟩
      simp [θ, F_completion_one hσ hc hcR]
    · refine ⟨completion σ R 2, compatible_completion hσ hR 2, ?_⟩
      simp [θ, F_completion hσ hc hcR (by norm_num : (1 : ℝ) < 2)]

/-- If `σ` is positive and continuous on `(0, ∞)`, so is every completion. -/
theorem completion_pos_continuous (hR : 0 < R) (hcont : ContinuousOn σ (Ioi 0))
    (hpos : ∀ x, 0 < x → 0 < σ x) (p : ℝ) :
    ContinuousOn (completion σ R p) (Ioi 0) ∧ ∀ x, 0 < x → 0 < completion σ R p x := by
  have hk : 0 < σ R := hpos R hR
  refine ⟨?_, fun x hx => ?_⟩
  · have heq : completion σ R p = (Iic R).piecewise σ (fun x => σ R * (x / R) ^ p) := by
      funext x
      simp only [completion, Set.piecewise, mem_Iic]
    rw [heq]
    refine ContinuousOn.piecewise (fun x hx => ?_) (hcont.mono inter_subset_left) ?_
    · rw [frontier_Iic] at hx
      have := mem_singleton_iff.1 hx.2
      subst this
      rw [div_self hR.ne', Real.one_rpow, mul_one]
    · rw [compl_Iic, closure_Ioi]
      refine continuousOn_const.mul ((continuousOn_id.div_const R).rpow_const fun x hx => ?_)
      exact Or.inl (div_pos (hR.trans_le hx.2) hR).ne'
  · rcases le_or_gt x R with h | h
    · rw [completion_of_le h]; exact hpos x hx
    · rw [completion_of_gt h]; exact mul_pos hk (Real.rpow_pos_of_pos (div_pos hx hR) p)

theorem statement_holds : Standalone.D8TailCompletions.statement := by
  intro σ c R hσ hc hcR
  have hR := hc.trans hcR
  exact ⟨image_F hσ hc hcR, image_θ hσ hc hcR, fun g hg => J_lt_F hσ hc hcR hg,
    fun p _ => compatible_completion hσ hR p, F_completion_one hσ hc hcR,
    fun p hp => F_completion hσ hc hcR hp,
    fun ⟨hcont, hpos⟩ p _ => completion_pos_continuous hR hcont hpos p⟩

/-! ## The bubble interpretation, conditional on AX-03 -/

section Upstream

open Upstream Upstream.Diffusion Upstream.DriftlessIntegralCriterion
open scoped NNReal

theorem coeffHyp_of_admissible (hg : Admissible g) : CoeffHyp halfLine (fun _ => 0) g where
  measurable_drift := measurable_const
  measurable_vol := hg.measurable
  vol_ne_zero x hx := hg.ne_zero x ((halfLine_mem_iff x).1 hx)
  locInt_inv_sq a b ha hb := hg.locInt a b ((halfLine_mem_iff a).1 ha) ((halfLine_mem_iff b).1 hb)
  locInt_drift _ _ _ _ := by simp

/-- AX-03's tail-integrability notion is `F_c(g) < ∞`, for any cutoff `c > 0`. -/
theorem jkpIntegrable_iff_F (hg : Admissible g) (hc : 0 < c) : JKPIntegrable g ↔ F c g < ∞ := by
  rw [F, show (∫⁻ x in Ioi c, ENNReal.ofReal (x / g x ^ 2)) = T c g from rfl,
    lintegral_lt_top_iff hg hc.le]
  simp only [JKPIntegrable, StateInterval.IntegrableNearRight, halfLine_rightTail, halfLine_mem_iff]
  refine ⟨fun ⟨x, hx, h⟩ => ?_, fun h => ⟨c, hc, h⟩⟩
  rcases le_total x c with hxc | hcx
  · exact h.mono_set (Ioi_subset_Ioi hxc)
  · refine ((jkp_integrableOn_Icc hg hc hx).union h).mono_set fun y hy => ?_
    rcases le_or_gt y x with hyx | hyx
    · exact Or.inl ⟨(mem_Ioi.1 hy).le, hyx⟩
    · exact Or.inr hyx

/-- **Interpretation, conditional on AX-03.** For a compatible coefficient `g` and a weak solution
`S` of `dS = g(S) dW` on `(0, ∞)` (absorbed at `0`) accepted by the primitives, `θ(g) = 1` gives a
strict local martingale and `θ(g) = 0` a martingale that is not uniformly integrable. -/
theorem theta_interpretation {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {X : SDEPrimitives P 𝓕 W}
    (U3 : DriftlessIntegralCriterion P 𝓕 W X) (hW : IsFBrownian 𝓕 W P)
    (hg : Compatible σ R g) (hc : 0 < c) {s₀ : ℝ} (hs₀ : 0 < s₀) {S : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → WithTop ℝ≥0} (hS : X.Solves halfLine (fun _ => 0) g s₀ S ζ) :
    (θ c g = 1 → Diffusion.IsStrictLocalMartingale S 𝓕 P) ∧
      (θ c g = 0 → Martingale S 𝓕 P ∧ ¬ UniformIntegrable S 1 P) := by
  have hco := coeffHyp_of_admissible hg.1
  have hs₀' := (halfLine_mem_iff s₀).2 hs₀
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hF : F c g < ∞ := by by_contra hF; simp [θ, hF] at h
    exact U3.strict_of_integrable _ _ _ _ hW hco hs₀' hS ((jkpIntegrable_iff_F hg.1 hc).2 hF)
  · have hF : ¬ F c g < ∞ := by intro hF; simp [θ, hF] at h
    exact U3.martingale_of_not_integrable _ _ _ _ hW hco hs₀' hS
      ((jkpIntegrable_iff_F hg.1 hc).not.2 hF)

/-- **Both labels are compatible with the observation, conditional on AX-03.** The completions `g_1`
and `g_2` agree with `σ` on `(0, R]`; any accepted solution with coefficient `g_1` is a martingale,
and any with coefficient `g_2` is a strict local martingale. -/
theorem both_labels_compatible {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {X : SDEPrimitives P 𝓕 W}
    (U3 : DriftlessIntegralCriterion P 𝓕 W X) (hW : IsFBrownian 𝓕 W P)
    (hσ : Admissible σ) (hc : 0 < c) (hcR : c < R) {s₀ : ℝ} (hs₀ : 0 < s₀)
    {S₁ S₂ : ℝ≥0 → Ω → ℝ} {ζ₁ ζ₂ : Ω → WithTop ℝ≥0}
    (hS₁ : X.Solves halfLine (fun _ => 0) (completion σ R 1) s₀ S₁ ζ₁)
    (hS₂ : X.Solves halfLine (fun _ => 0) (completion σ R 2) s₀ S₂ ζ₂) :
    Compatible σ R (completion σ R 1) ∧ Compatible σ R (completion σ R 2) ∧
      Martingale S₁ 𝓕 P ∧ Diffusion.IsStrictLocalMartingale S₂ 𝓕 P := by
  have hR := hc.trans hcR
  have h1 := compatible_completion hσ hR 1
  have h2 := compatible_completion hσ hR 2
  refine ⟨h1, h2, ((theta_interpretation U3 hW h1 hc hs₀ hS₁).2 ?_).1,
    (theta_interpretation U3 hW h2 hc hs₀ hS₂).1 ?_⟩
  · simp [θ, F_completion_one hσ hc hcR]
  · simp [θ, F_completion hσ hc hcR (by norm_num : (1 : ℝ) < 2)]

end Upstream

end Novel.D8TailCompletions
