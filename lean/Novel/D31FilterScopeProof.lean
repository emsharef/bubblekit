import Standalone.D31FilterScope
import Novel.D31FilterScopeCounter

/-!
# Claim 043: part 3 and the proof

Part 3 checks AX-58's hypotheses for the transformed law and proves its step directly:
* by part 1 the observation has density `p_a` with respect to `ν_a`, and the transformed forecast `q_a`
  integrates to one there;
* on the support of `ν_a`, `D_a ≥ p_a > 0` gives `(q_a/D_a) p_a ≤ q_a`, and the score is zero
  elsewhere, so the mean is at most `∫ q_a dν_a = 1`;
* with `D_a = p_a` the inequality is an equality off a set where `q_a` vanishes too, so the mean is
  one, and the ratio at zero is `ρ_q(a)/ρ_p(a)`.

`law`: `Novel/D31FilterScopeLaw.lean`; `counterexample`: `Novel/D31FilterScopeCounter.lean`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Novel.D31FilterScope

open Standalone.D31FilterScope

theorem measurableSet_supp (a : ℝ) : MeasurableSet (supp a) :=
  (measurableSet_singleton 0).union (measurableSet_kept a)

theorem measurable_Ecorr {q D : ℝ → ℝ} (hq : Measurable q) (hD : Measurable D) (a : ℝ) :
    Measurable (Ecorr q a D) := by
  classical
  unfold Ecorr
  exact Measurable.ite (measurableSet_supp a) ((measurable_fa hq a).div hD) measurable_const

/-- The mean of a function of the filtered return, against `ν_a`. -/
theorem mean_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {R : Ω → ℝ} {p : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hp : IsDensity p) (hR : Measurable R) (hlaw : P.map R = lawOf p) {g : ℝ → ℝ}
    (hg : Measurable g) :
    ∫⁻ ω, ENNReal.ofReal (g (Ha a (R ω))) ∂P =
      ∫⁻ y, ENNReal.ofReal (fa p a y) * ENNReal.ofReal (g y) ∂(nu a) := by
  rw [← lintegral_map (f := fun y => ENNReal.ofReal (g y)) hg.ennreal_ofReal
    (show Measurable (fun ω => Ha a (R ω)) from (measurable_Ha a).comp hR),
    show (fun ω => Ha a (R ω)) = Ha a ∘ R from rfl, ← Measure.map_map (measurable_Ha a) hR, hlaw,
    map_Ha ha hp, lintegral_withDensity_eq_lintegral_mul _ (measurable_fa hp.1 a).ennreal_ofReal
      hg.ennreal_ofReal]
  rfl

theorem fa_pos {p : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hp : IsDensity p) (hpos : ∀ r, 0 < p r)
    {y : ℝ} (hy : y ∈ supp a) : 0 < fa p a y := by
  classical
  rcases hy with rfl | hk
  · simp only [fa, ↓reduceIte]; exact (rho_pos_lt ha hp hpos).1
  · have hy0 : y ≠ 0 := fun h => by rw [h] at hk; simp [kept] at hk
    simp only [fa, hy0, ↓reduceIte, if_pos hk.2]; exact hpos y

theorem fa_off {f : ℝ → ℝ} {a y : ℝ} (hy : y ∉ supp a) : fa f a y = 0 := by
  classical
  have hy0 : y ≠ 0 := fun h => hy (Or.inl h)
  have hk : ¬ |y| ≤ a := fun h => hy (Or.inr ⟨abs_pos.2 hy0, h⟩)
  simp only [fa, hy0, ↓reduceIte, if_neg hk]

theorem corrected_holds : Standalone.D31FilterScope.corrected := by
  classical
  intro Ω _ P _ R Θ pθ θ₀ q D a ha hpθ hpos hq hR hlaw hDm hDpos hDom
  have hp := hpθ θ₀
  have hpa : ∀ y, ENNReal.ofReal (fa (pθ θ₀) a y) * ENNReal.ofReal (Ecorr q a D y) ≤
      ENNReal.ofReal (fa q a y) := fun y => by
    rw [← ENNReal.ofReal_mul (fa_nonneg hp a y)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold Ecorr
    split_ifs with hy
    · have hD := hDpos y hy
      rw [show fa (pθ θ₀) a y * (fa q a y / D y) = fa q a y * (fa (pθ θ₀) a y / D y) by ring]
      exact mul_le_of_le_one_right (fa_nonneg hq a y) ((div_le_one hD).2 (hDom θ₀ y hy))
    · rw [mul_zero]; exact fa_nonneg hq a y
  have hexact : ∀ y, ENNReal.ofReal (fa (pθ θ₀) a y) *
      ENNReal.ofReal (Ecorr q a (fa (pθ θ₀) a) y) = ENNReal.ofReal (fa q a y) := fun y => by
    rw [← ENNReal.ofReal_mul (fa_nonneg hp a y)]
    congr 1
    unfold Ecorr
    split_ifs with hy
    · have := fa_pos ha hp (hpos θ₀) hy
      field_simp
    · rw [mul_zero, fa_off hy]
  refine ⟨?_, ?_, ?_⟩
  · rw [mean_eq ha hp hR hlaw (measurable_Ecorr hq.1 hDm a)]
    exact (lintegral_mono hpa).trans (mass_fa ha hq).le
  · rw [mean_eq ha hp hR hlaw (measurable_Ecorr hq.1 (measurable_fa hp.1 a) a)]
    simp_rw [hexact]
    exact mass_fa ha hq
  · simp [Ecorr, supp, fa]

theorem statement_holds : Standalone.D31FilterScope.statement :=
  ⟨law_holds, counterexample_holds, corrected_holds⟩

end Novel.D31FilterScope
