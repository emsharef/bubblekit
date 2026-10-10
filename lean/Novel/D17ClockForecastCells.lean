import Novel.D17ClockForecastLabels
import Novel.D17ClockCellsProof

/-!
# Claim 035, parts 2 and 3 on claim 034's design

* The CEV label forecast (4) is positive and normalized (`labels_holds`). A training-only blend with
  a normalized baseline is nonnegative and normalized: the masses are `λ · 1 + (1 − λ) · 1`.
* Claim 034's validity holds for any nonnegative normalized numerator with its denominator
  unchanged (`Novel.D17ClockCells.validity_holds`), so both scores inherit all of its conclusions.
* (5) is linearity of `q ↦ q / D` with `0 < D ≤ 1` (claim 034's `covers`). The log protection
  follows from its floor.
* On an all-zero suffix from a zero quote, claim 034's `boundary` gives `D = 1`. Each numerator is
  a single mass of a normalized forecast, so it is at most one.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D17ClockForecast

open Standalone.D17ClockForecast

theorem cells_holds : Standalone.D17ClockForecast.cells := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW k n r _ δ pf κf vT vE qb lam Δ 𝒱 ℬ hδ hpf hκf hvE
    hqb0 hqb1 hlam hΔ h𝒱 h𝒱pos hℬ qC qM D
  have hC := fun u => (labels_holds P' 𝓕 Wb Solves h55 h56 hW).2 k n r δ pf κf vT vE hδ hpf hκf
    hvE u
  have hl0 : ∀ u, 0 ≤ lam u := fun u => (hlam u).1.le
  have hl1 : ∀ u, 0 ≤ 1 - lam u := fun u => by linarith [(hlam u).2]
  have hqC0 : ∀ u w, 0 ≤ qC u w := fun u w => ((hC u).1 w).le
  have hqC1 : ∀ u, ∑' w, ENNReal.ofReal (qC u w) = 1 := fun u => by
    rw [← ENNReal.ofReal_tsum_of_nonneg (hqC0 u) (hC u).2.1.summable, (hC u).2.1.tsum_eq,
      ENNReal.ofReal_one]
  have hqM0 : ∀ u w, 0 ≤ qM u w := fun u w =>
    add_nonneg (mul_nonneg (hl0 u) (hqb0 u w)) (mul_nonneg (hl1 u) (hqC0 u w))
  have hofM : ∀ u w, ENNReal.ofReal (qM u w) = ENNReal.ofReal (lam u) * ENNReal.ofReal (qb u w) +
      ENNReal.ofReal (1 - lam u) * ENNReal.ofReal (qC u w) := fun u w => by
    rw [ENNReal.ofReal_add (mul_nonneg (hl0 u) (hqb0 u w)) (mul_nonneg (hl1 u) (hqC0 u w)),
      ENNReal.ofReal_mul (hl0 u), ENNReal.ofReal_mul (hl1 u)]
  have hqM1 : ∀ u, ∑' w, ENNReal.ofReal (qM u w) = 1 := fun u => by
    rw [tsum_congr (hofM u), ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hqb1,
      hqC1, mul_one, mul_one, ← ENNReal.ofReal_add (hl0 u) (hl1 u), add_sub_cancel,
      ENNReal.ofReal_one]
  have hD : ∀ h ℓ u w, 0 < D h ℓ u w ∧ D h ℓ u w ≤ 1 := fun h ℓ u w => by
    have := (Novel.D17ClockCells.covers_holds).2.2.2.2 δ ℬ h ℓ n Δ 𝒱 (u (Fin.last k)) w hδ hℬ hΔ
      h𝒱 h𝒱pos
    exact ⟨this.1, this.2.1⟩
  refine ⟨fun q hq => ?_, fun h ℓ u w => ?_, fun h ℓ u hu => ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · refine ⟨hqC0, hqC1, ?_⟩
      intro Ω _ P _ U X₀ Vc Bp R Hv Lv hU hX hVc hBp hR hcov hg
      exact Novel.D17ClockCells.validity_holds P k n δ Δ 𝒱 ℬ U X₀ Vc Bp R qC Hv Lv hδ hΔ h𝒱 h𝒱pos
        hℬ hU hX hVc hBp hR hqC0 hqC1 hcov hg
    · refine ⟨hqM0, hqM1, ?_⟩
      intro Ω _ P _ U X₀ Vc Bp R Hv Lv hU hX hVc hBp hR hcov hg
      exact Novel.D17ClockCells.validity_holds P k n δ Δ 𝒱 ℬ U X₀ Vc Bp R qM Hv Lv hδ hΔ h𝒱 h𝒱pos
        hℬ hU hX hVc hBp hR hqM0 hqM1 hcov hg
  · intro EB EC EM
    have hblend : EM = ENNReal.ofReal (lam u) * EB + ENNReal.ofReal (1 - lam u) * EC := by
      simp only [EM, EB, EC]
      rw [hofM, ENNReal.add_div, mul_div_assoc, mul_div_assoc]
    have hge : ENNReal.ofReal (lam u) * EB ≤ EM := by rw [hblend]; exact le_self_add
    refine ⟨hblend, hge, fun hEB => ?_⟩
    have hDp := (hD h ℓ u w).1
    have hfB : EB < ⊤ := ENNReal.div_lt_top ENNReal.ofReal_ne_top hDp.ne'
    have hfM : EM < ⊤ := ENNReal.div_lt_top ENNReal.ofReal_ne_top hDp.ne'
    have hBr : 0 < EB.toReal := ENNReal.toReal_pos hEB.ne' hfB.ne
    have hge' : lam u * EB.toReal ≤ EM.toReal := by
      have := ENNReal.toReal_mono hfM.ne hge
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hl0 u)] at this
    refine Real.log_le_log (hlam u).1 ?_
    rw [le_div_iff₀ hBr]; exact hge'
  · have hD1 : D h ℓ u (fun _ => 0) = 1 := by
      show Standalone.D17ClockCells.Dclock δ ℬ h ℓ Δ 𝒱 (u (Fin.last k)) (fun _ => 0) = 1
      rw [hu]
      exact (Novel.D17ClockCells.boundary_holds.2.1 δ ℬ h ℓ n Δ 𝒱 0 hδ hℬ hΔ h𝒱 h𝒱pos le_rfl
        zero_le_one).1
    have hb1 : ENNReal.ofReal (qb u fun _ => 0) ≤ 1 :=
      (hqb1 u) ▸ ENNReal.le_tsum (f := fun w => ENNReal.ofReal (qb u w)) _
    have hc1 : ENNReal.ofReal (qC u fun _ => 0) ≤ 1 :=
      (hqC1 u) ▸ ENNReal.le_tsum (f := fun w => ENNReal.ofReal (qC u w)) _
    refine ⟨hD1, ?_, ?_⟩
    · rw [hD1, div_one]; exact hc1
    · rw [hD1, div_one, hofM]
      calc ENNReal.ofReal (lam u) * ENNReal.ofReal (qb u fun _ => 0) +
            ENNReal.ofReal (1 - lam u) * ENNReal.ofReal (qC u fun _ => 0)
          ≤ ENNReal.ofReal (lam u) * 1 + ENNReal.ofReal (1 - lam u) * 1 := by gcongr
        _ = 1 := by
          rw [mul_one, mul_one, ← ENNReal.ofReal_add (hl0 u) (hl1 u), add_sub_cancel,
            ENNReal.ofReal_one]

end Novel.D17ClockForecast
