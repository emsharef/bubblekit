import Novel.D19CenteredQuadratureTensor

/-!
# Claim 038, part 1: the two-sided relative integration bound

The label mass is the path integral over the cell product (`walk_path`), which splits over the
tensor subcells (`lintegral_cellBox`). On each subcell the midpoint path lies in the observed
cells, so the subcell bounds (`box_lower`, `box_upper`) hold with the allowances `ε^−` and `ε^+`
(`quadT_le`, `G_sum_le`). Summing, the midpoint terms add up to claim 036's `Q_J` (`Qs_eq`, `Wt_eq`).
Intersecting with claim 036's (6) gives (3).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D19CenteredQuadrature

open Standalone.D19CenteredQuadrature Standalone.D19FilteredLikelihood Standalone.D19CondSensitivity
  Standalone.D17ClockCells Standalone.D14FixedTick Novel.D19FilteredLikelihood Novel.D19CondSensitivity

variable {δ s : ℝ} {M m : ℕ}

theorem tv_in (hδ : 0 < δ) (hM : 0 < M) {z : Fin m → ℕ} (hz : ∀ j, 1 ≤ z j) (L : Fin m → Fin M) :
    InCl δ s z (tv δ M z L) := fun k => by
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [aP, dP]
  · simp only [aP, dP, Fin.cons_succ, tv]
    exact tMid_mem hδ hM (hz j) (L j).isLt

theorem Wt_nonneg (hδ : 0 < δ) (μ σ : Fin m → ℝ) {z : Fin m → ℕ} (hz : ∀ j, 1 ≤ z j)
    (L : Fin m → Fin M) : 0 ≤ Wt δ s M μ σ z L :=
  Finset.prod_nonneg fun j _ => mul_nonneg
    (div_nonneg (sub_nonneg.2 (lA_lt_lD hδ (hz j)).le) (Nat.cast_nonneg _))
    (gaussianPDFReal_nonneg _ _ _)

theorem epsMinus_nonneg {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) {B : Box} (hB : B.Valid)
    (z : Fin m → ℕ) : 0 ≤ epsMinus δ M v B z :=
  Finset.sum_nonneg fun j _ => by have := hv j; have := hB.2.1; positivity

theorem epsPlus_nonneg (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) : 0 ≤ epsPlus δ s M Δ v B z :=
  Finset.sum_nonneg fun i _ => by positivity

/-- (2) for the label mass, as extended reals. -/
theorem walk_bounds (hδ : 0 < δ) (hs : 0 < s) (hM : 0 < M) (Δ : Fin m → ℝ) (hΔ : ∀ j, 0 < Δ j)
    {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) {B : Box} (hB : B.Valid) {b w : ℝ} (hbw : B.Mem (b, w))
    {z : Fin m → ℕ} (hz : ∀ j, 1 ≤ z j) :
    ENNReal.ofReal (Real.exp (-epsMinus δ M v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z) ≤
      walkM δ (muF Δ v b w) (sdF v w) s {z} ∧
    walkM δ (muF Δ v b w) (sdF v w) s {z} ≤
      ENNReal.ofReal (Real.exp (epsPlus δ s M Δ v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z) := by
  have hw : 0 < w := hB.2.1.trans_le hbw.2.1
  have hW := Wt_nonneg (s := s) hδ (muF Δ v b w) (sdF v w) hz (M := M)
  rw [walk_path hδ hs Δ hv b hw hz, lintegral_cellBox hδ hM hz, Qs_eq hM,
    Finset.mul_sum, Finset.mul_sum,
    ENNReal.ofReal_sum_of_nonneg fun L _ => mul_nonneg (Real.exp_pos _).le (hW L),
    ENNReal.ofReal_sum_of_nonneg fun L _ => mul_nonneg (Real.exp_pos _).le (hW L)]
  have hrv : ∀ i, rv δ M z i = hP δ M z i.succ / 2 := rv_eq z
  constructor
  · refine Finset.sum_le_sum fun L _ => ?_
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, Wt_eq Δ hv b hw z hz hδ, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm (Real.exp _)]
    exact box_lower Δ hv b hw _ _ _ fun u hu =>
      quadT_le M hv hB hbw.2.1 z (hP_nonneg hδ hz) fun i => (hu i).trans_eq (hrv i)
  · refine Finset.sum_le_sum fun L _ => ?_
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, Wt_eq Δ hv b hw z hz hδ, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm (Real.exp _)]
    refine (box_upper Δ hv b hw _ _ _ _ (linT_eq Δ v b w _ _)).trans ?_
    gcongr
    · exact pdens_nonneg _ _ _ _ _ _
    · have := G_sum_le (s := s) M Δ v hΔ hv hB hbw (tv_in (s := s) hδ hM hz L)
      simp only [← hrv] at this
      exact this

theorem centered_holds : Standalone.D19CenteredQuadrature.centered := by
  intro δ s m M Δ v B b w z hδ hs hM hΔ hv hB hbw hz
  have hwb := walk_bounds hδ hs hM Δ hΔ hv hB hbw hz
  have hfin := walk_ne_top (δ := δ) (muF Δ v b w) (sdF v w) s z
  have hQ0 : 0 ≤ Qs δ s M (muF Δ v b w) (sdF v w) z := by
    rw [Qs_eq hM]; exact Finset.sum_nonneg fun L _ => Wt_nonneg hδ _ _ hz L
  have hlo : Real.exp (-epsMinus δ M v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z ≤
      Lz δ s (muF Δ v b w) (sdF v w) z := (ENNReal.ofReal_le_iff_le_toReal hfin).1 hwb.1
  have hup : Lz δ s (muF Δ v b w) (sdF v w) z ≤
      Real.exp (epsPlus δ s M Δ v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hwb.2
  have q := quad_holds δ s m M Δ v B b w z hδ hs hM hΔ hv hB hbw hz
  refine ⟨epsMinus_nonneg hv hB z, epsPlus_nonneg Δ v B z, hlo, hup, ?_, ?_⟩
  · unfold epsMinusH
    rcases min_choice (epsQ δ s M Δ v B z) (epsMinus δ M v B z) with h | h <;> rw [h]
    · exact q.2.1
    · exact hlo
  · unfold epsPlusH
    rcases min_choice (epsQ δ s M Δ v B z) (epsPlus δ s M Δ v B z) with h | h <;> rw [h]
    · exact q.2.2
    · exact hup

end Novel.D19CenteredQuadrature
