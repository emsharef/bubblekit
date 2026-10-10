import Standalone.D34ScreenCalibration
import Novel.D34ScreenCalibrationFlag
import Novel.D34ScreenCalibrationExample
import Novel.D14MisspecificationProof

/-!
# Claim 045 (D34): proof

Proves `Standalone.D34ScreenCalibration.statement` (`statement_holds`).
* `part1_holds`. AX-65 at the exchangeable reference bounds its flag probability by `α`, and the
  eventwise TV comparison moves the bound to the actual law.
* `part1w_holds`. A common measurable map commutes with every coordinate permutation, so the
  pushforward of an exchangeable window law is exchangeable.
* `part2_holds`:
  - (2) is `Measure.compProd_apply`.
  - (5): on the kernel's full-measure set, `K_D(u)(tail) ≤ R_cal(C_D(u)) + ρ`. Claim 023's
    bounded-function TV comparison (`Novel.D14Misspecification.lintegral_le_tv`) moves `∫ R_cal`
    from `law C_D` to `ν^n` within `η`. That integral is `ν^(n+1)(flag)` (`pi_flag`), which AX-65
    bounds by `α`, the iid law being exchangeable (`permInvariant_pi`).
  - (7): AX-66 bounds `ν^n(G)` by `δ`, the TV premise moves this to `law C_D` within `η`, and
    `{R_D > E + ρ} ⊆ {C_D ∈ G}` on the kernel's full-measure set.
  - (8): `R_D ≤ b + (1 − b)·1{R_D > b}` pointwise, and `μ_D{R_D > b} ≤ d` by (7) when `b < 1`.
* Part 3 is `Novel/D34ScreenCalibrationExample.lean`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Novel.D34ScreenCalibration

open Standalone.D34ScreenCalibration

/-- An upper TV comparison as an `ℝ≥0∞` inequality. -/
theorem le_add_of_tv {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {A : Set X} {ρ : ℝ} (hρ : 0 ≤ ρ) (h : μ.real A - ν.real A ≤ ρ) :
    μ A ≤ ν A + ENNReal.ofReal ρ := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ A), ← ENNReal.ofReal_toReal (measure_ne_top ν A),
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg hρ]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [measureReal_def] at h
  linarith

theorem part1_holds : part1 := by
  intro n α ε LD Lref hn hα hα1 hε hD hR hperm hax hTV
  have hF := measurableSet_flag (n := n) hα1
  have hRef : Lref.real (Standalone.D34ScreenCalibration.Flag n α) ≤ α :=
    ENNReal.toReal_le_of_le_ofReal hα.le (hax hR hn hperm α hα hα1)
  have h1 := (abs_le.mp (hTV _ hF)).2
  exact le_min measureReal_le_one (by linarith)

theorem part1w_holds : part1w := by
  intro n α W _ Wlaw s hn hα hα1 hW hs hperm
  have hS : Measurable fun (w : Fin (n + 1) → W) (i : Fin (n + 1)) => s (w i) :=
    measurable_pi_iff.mpr fun i => hs.comp (measurable_pi_apply i)
  have hperm' : PermInvariantLaw (Wlaw.map fun w i => s (w i)) := by
    intro σ
    have hσ : Measurable fun (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) => v (σ i) :=
      measurable_pi_iff.mpr fun _ => measurable_pi_apply _
    have hσW : Measurable fun (w : Fin (n + 1) → W) (i : Fin (n + 1)) => w (σ i) :=
      measurable_pi_iff.mpr fun _ => measurable_pi_apply _
    have h1 : (Wlaw.map fun w i => s (w i)).map (fun v i => v (σ i)) =
        (Wlaw.map fun w i => w (σ i)).map fun w i => s (w i) := by
      rw [Measure.map_map hσ hS, Measure.map_map hS hσW]
      rfl
    rw [h1, hperm σ]
    have hidW : (Wlaw.map fun (w : Fin (n + 1) → W) (i : Fin (n + 1)) => w i) = Wlaw :=
      Measure.map_id
    have hidR : ((Wlaw.map fun w i => s (w i)).map
        fun (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) => v i) = Wlaw.map fun w i => s (w i) :=
      Measure.map_id
    rw [hidW, hidR]
  refine ⟨hperm', fun hax => ?_⟩
  have hP : IsProbabilityMeasure (Wlaw.map fun w i => s (w i)) := by
    have := hS.aemeasurable (μ := Wlaw)
    infer_instance
  exact ENNReal.toReal_le_of_le_ofReal hα.le (hax hP hn hperm' α hα hα1)

theorem part2_holds : part2 := by
  intro n α 𝒰 _ _ μD C K ν η ρ hn hα hα1 hμ hK hν hC hη hρ hax65 hax66 hTVc hTVk
  set A : 𝒰 → Set ℝ := fun u => {s | qcal n α (C u) < (s : WithTop ℝ)}
  have hA : ∀ u, MeasurableSet (A u) := fun u => measurableSet_tail hα1 (C u)
  have hFD := measurableSet_flagD (α := α) hα1 hC
  have hcomp : (μD ⊗ₘ K) (FlagD C α) = ∫⁻ u, K u (A u) ∂μD := by
    rw [Measure.compProd_apply hFD]
    rfl
  have hRDm := measurable_RD hα1 hC K
  have hKreal : ∀ u, K u (A u) = ENNReal.ofReal (RD C K α u) := fun u =>
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hRD1 : ∀ u, RD C K α u ≤ 1 := fun u => measureReal_le_one
  have hRD0 : ∀ u, 0 ≤ RD C K α u := fun u => measureReal_nonneg
  -- (2).
  have h2 : (μD ⊗ₘ K).real (FlagD C α) = ∫ u, RD C K α u ∂μD := by
    rw [measureReal_def, hcomp, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hRD0)
      hRDm.aestronglyMeasurable]
    simp only [hKreal]
  -- The kernel comparison on the full-measure set.
  have hk : ∀ᵐ u ∂μD, K u (A u) ≤ Rcal ν n α (C u) + ENNReal.ofReal ρ := by
    filter_upwards [hTVk] with u hu
    exact le_add_of_tv hρ (abs_le.mp (hu _ (hA u))).2
  have hRcal1 : ∀ c, Rcal ν n α c ≠ ⊤ := fun c => measure_ne_top _ _
  have : IsProbabilityMeasure (μD.map C) := by
    have := hC.aemeasurable (μ := μD)
    infer_instance
  -- (5).
  have h5 : (μD ⊗ₘ K) (FlagD C α) ≤ ENNReal.ofReal (α + η + ρ) := by
    have htv := Novel.D14Misspecification.lintegral_le_tv (H := μD.map C)
      (G := Measure.pi fun _ : Fin n => ν) (Y := fun c => (Rcal ν n α c).toReal) (c := 1)
      (measurable_Rcal hα1).ennreal_toReal (fun _ => ENNReal.toReal_nonneg)
      (fun c => ENNReal.toReal_le_of_le_ofReal zero_le_one (by
        rw [ENNReal.ofReal_one]; exact prob_le_one)) zero_le_one hη hTVc
    simp only [ENNReal.ofReal_toReal (hRcal1 _), one_mul] at htv
    have hα65 := hax65 inferInstance hn (permInvariant_pi ν) α hα hα1
    rw [pi_flag hα1 ν] at hα65
    calc (μD ⊗ₘ K) (FlagD C α) = ∫⁻ u, K u (A u) ∂μD := hcomp
      _ ≤ ∫⁻ u, (Rcal ν n α (C u) + ENNReal.ofReal ρ) ∂μD := lintegral_mono_ae hk
      _ = ∫⁻ c, Rcal ν n α c ∂(μD.map C) + ENNReal.ofReal ρ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_map (measurable_Rcal hα1) hC]
      _ ≤ ∫⁻ c, Rcal ν n α c ∂(Measure.pi fun _ : Fin n => ν) + ENNReal.ofReal η +
            ENNReal.ofReal ρ := by gcongr
      _ ≤ ENNReal.ofReal α + ENNReal.ofReal η + ENNReal.ofReal ρ := by gcongr
      _ = ENNReal.ofReal (α + η + ρ) := by
          rw [ENNReal.ofReal_add (by linarith) hρ, ENNReal.ofReal_add hα.le hη]
  refine ⟨h2, le_min measureReal_le_one
    (ENNReal.toReal_le_of_le_ofReal (by linarith) h5), ?_, fun E δ hE hE1 hδ hδ1 hB => ?_⟩
  · have := Upstream.sub_rcal_eq_kcal (n := n) hα1
    rw [← rcal_eq, ← kcal_eq] at this
    omega
  set G : Set (Fin n → ℝ) := {c | ENNReal.ofReal E < Rcal ν n α c}
  have hG : MeasurableSet G := measurableSet_lt measurable_const (measurable_Rcal hα1)
  have hpiG : (Measure.pi fun _ : Fin n => ν).real G ≤ δ :=
    ENNReal.toReal_le_of_le_ofReal hδ.le (hax66 hν hn α E δ hα hα1 hE hE1 hδ hδ1 hB)
  have hmapG : μD.real (C ⁻¹' G) ≤ δ + η := by
    have := (abs_le.mp (hTVc G hG)).2
    rw [map_measureReal_apply hC hG] at this
    linarith
  have hsub : {u | E + ρ < RD C K α u} ≤ᵐ[μD] C ⁻¹' G := by
    filter_upwards [hTVk] with u hu
    intro hlt
    have h1 := (abs_le.mp (hu _ (hA u))).2
    show ENNReal.ofReal E < Rcal ν n α (C u)
    rw [ENNReal.ofReal_lt_iff_lt_toReal hE.le (hRcal1 _)]
    have : RD C K α u = (K u).real (A u) := rfl
    rw [Rcal, ← measureReal_def]
    linarith
  have h7 : μD.real {u | E + ρ < RD C K α u} ≤ min 1 (δ + η) :=
    le_min measureReal_le_one
      ((ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans hmapG)
  refine ⟨h7, ?_⟩
  -- (8).
  set b := min 1 (E + ρ)
  set d := min 1 (δ + η)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hd0 : 0 ≤ d := le_min zero_le_one (by linarith)
  have hBm : MeasurableSet {u | b < RD C K α u} := measurableSet_lt measurable_const hRDm
  have hm : μD.real {u | b < RD C K α u} ≤ d := by
    by_cases hEr : E + ρ ≤ 1
    · have : b = E + ρ := min_eq_right hEr
      rw [this]
      exact h7
    · have : {u | b < RD C K α u} = ∅ := by
        ext u
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        have : b = 1 := min_eq_left (by linarith)
        rw [this]
        exact hRD1 u
      rw [this, measureReal_empty]
      exact hd0
  have hint : Integrable (RD C K α) μD :=
    Integrable.of_bound hRDm.aestronglyMeasurable 1
      (ae_of_all _ fun u => by rw [Real.norm_of_nonneg (hRD0 u)]; exact hRD1 u)
  have hpt : ∀ u, RD C K α u ≤ b + (1 - b) * ({u | b < RD C K α u}.indicator (fun _ => (1 : ℝ)) u) := by
    intro u
    by_cases h : b < RD C K α u
    · rw [indicator_of_mem (show u ∈ {u | b < RD C K α u} from h)]
      linarith [hRD1 u]
    · rw [indicator_of_notMem (show u ∉ {u | b < RD C K α u} from h)]
      linarith [not_lt.mp h]
  have hint2 : Integrable (fun u => b + (1 - b) * ({u | b < RD C K α u}.indicator (fun _ => (1 : ℝ)) u)) μD :=
    (integrable_const b).add (((integrable_const (1 : ℝ)).indicator hBm).const_mul (1 - b))
  rw [h2]
  calc ∫ u, RD C K α u ∂μD
      ≤ ∫ u, (b + (1 - b) * ({u | b < RD C K α u}.indicator (fun _ => (1 : ℝ)) u)) ∂μD :=
        integral_mono hint hint2 hpt
    _ = b + (1 - b) * μD.real {u | b < RD C K α u} := by
        rw [integral_add (integrable_const b)
          (((integrable_const (1 : ℝ)).indicator hBm).const_mul (1 - b)), integral_const,
          integral_const_mul, integral_indicator_const (1 : ℝ) hBm, probReal_univ, one_smul,
          smul_eq_mul, mul_one]
    _ ≤ b + (1 - b) * d := by
        have := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hb1)
        linarith

theorem statement_holds : Standalone.D34ScreenCalibration.statement :=
  ⟨part1_holds, part1w_holds, part2_holds, part3_holds⟩

end Novel.D34ScreenCalibration
