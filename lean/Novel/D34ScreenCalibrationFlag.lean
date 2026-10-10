import Standalone.D34ScreenCalibration
import Upstream.IIDCalibrationRisk

/-!
# Claim 045: the flag event

Deterministic and measure-theoretic facts about the rank rule (1), used by the proof.
* `kcal_eq`, `qcal_eq`, `Rcal_eq`, `rcal_eq`, `Bcal_eq`: the statement's restated definitions are
  AX-65's and AX-66's, so their lemmas apply.
* `measurableSet_qcal_lt`: `{x : q_cal(f x) < g x}` is measurable for measurable `f, g`. In the
  finite branch `q_cal` is the measurable order statistic `Upstream.ostat`. In the infinite branch
  the set is empty.
* `measurable_RD`: `R_D` is measurable.
* `permInvariant_pi`: an iid law is exchangeable.
* `pi_flag`: `ν^(n+1)(flag) = ∫ R_cal dν^n`, by splitting off the last coordinate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Novel.D34ScreenCalibration

open Standalone.D34ScreenCalibration

theorem kcal_eq : kcal = Upstream.kcal := rfl
theorem sortedCal_eq {n : ℕ} : (sortedCal : (Fin n → ℝ) → List ℝ) = Upstream.sortedCal := rfl
theorem qcal_eq : qcal = Upstream.qcal := rfl
theorem Rcal_eq : Rcal = Upstream.Rcal := rfl
theorem rcal_eq : rcal = Upstream.rcal := rfl
theorem Bcal_eq : Bcal = Upstream.Bcal := rfl

/-- In the finite branch the cutoff is the real order statistic `Upstream.ostat`. -/
theorem qcal_finite {n : ℕ} {α : ℝ} (hα1 : α < 1) (h : kcal n α ≤ n) (c : Fin n → ℝ) :
    qcal n α c = ((Upstream.ostat (kcal n α) c : ℝ) : WithTop ℝ) := by
  obtain ⟨hi, hq⟩ := Upstream.qcal_eq_coe hα1 h c
  rw [qcal_eq, hq, Upstream.ostat, kcal_eq, List.getD_eq_getElem _ _ hi]

theorem qcal_infinite {n : ℕ} {α : ℝ} (h : ¬ kcal n α ≤ n) (c : Fin n → ℝ) : qcal n α c = ⊤ :=
  Upstream.qcal_top h c

theorem measurableSet_qcal_lt {X : Type*} [MeasurableSpace X] {n : ℕ} {α : ℝ} (hα1 : α < 1)
    {f : X → Fin n → ℝ} {g : X → ℝ} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | qcal n α (f x) < ((g x : ℝ) : WithTop ℝ)} := by
  by_cases h : kcal n α ≤ n
  · have : {x | qcal n α (f x) < ((g x : ℝ) : WithTop ℝ)} =
        {x | Upstream.ostat (kcal n α) (f x) < g x} := by
      ext x
      simp only [mem_ofPred_eq, qcal_finite hα1 h, WithTop.coe_lt_coe]
    rw [this]
    exact measurableSet_lt ((Upstream.measurable_ostat (Upstream.one_le_kcal hα1) h).comp hf) hg
  · have : {x | qcal n α (f x) < ((g x : ℝ) : WithTop ℝ)} = ∅ := by
      ext x
      simp [qcal_infinite h]
    rw [this]
    exact MeasurableSet.empty

theorem measurableSet_flag {n : ℕ} {α : ℝ} (hα1 : α < 1) :
    MeasurableSet (Standalone.D34ScreenCalibration.Flag n α) :=
  measurableSet_qcal_lt hα1 (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)
    (measurable_pi_apply _)

theorem measurableSet_flagD {𝒰 : Type*} [MeasurableSpace 𝒰] {n : ℕ} {α : ℝ} (hα1 : α < 1)
    {C : 𝒰 → Fin n → ℝ} (hC : Measurable C) : MeasurableSet (FlagD C α) :=
  measurableSet_qcal_lt hα1 (hC.comp measurable_fst) measurable_snd

theorem measurableSet_tail {n : ℕ} {α : ℝ} (hα1 : α < 1) (c : Fin n → ℝ) :
    MeasurableSet {s : ℝ | qcal n α c < (s : WithTop ℝ)} :=
  measurableSet_qcal_lt (f := fun _ : ℝ => c) (g := id) hα1 measurable_const measurable_id

theorem measurable_Rcal {ν : Measure ℝ} {n : ℕ} {α : ℝ} (hα1 : α < 1) :
    Measurable (Rcal ν n α) :=
  Upstream.measurable_Rcal ν n hα1

theorem measurable_RD {𝒰 : Type*} [MeasurableSpace 𝒰] {n : ℕ} {α : ℝ} (hα1 : α < 1)
    {C : 𝒰 → Fin n → ℝ} (hC : Measurable C) (K : Kernel 𝒰 ℝ) [IsSFiniteKernel K] :
    Measurable (RD C K α) := by
  have := Kernel.measurable_kernel_prodMk_left (κ := K) (measurableSet_flagD hα1 hC)
  exact this.ennreal_toReal

/-- An iid law is exchangeable. -/
theorem permInvariant_pi {m : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    PermInvariantLaw (Measure.pi fun _ : Fin m => ν) := by
  intro σ
  have hg : Measurable fun (v : Fin m → ℝ) (i : Fin m) => v (σ i) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (σ i)
  have hid : (Measure.pi fun _ : Fin m => ν).map (fun v i => v i) =
      Measure.pi fun _ : Fin m => ν := Measure.map_id
  rw [hid]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hg (MeasurableSet.univ_pi hs)]
  have hpre : (fun (v : Fin m → ℝ) (i : Fin m) => v (σ i)) ⁻¹' univ.pi s =
      univ.pi fun j => s (σ.symm j) := by
    ext v
    simp only [mem_preimage, mem_univ_pi]
    exact ⟨fun h j => by simpa using h (σ.symm j), fun h i => by simpa using h (σ i)⟩
  rw [hpre, Measure.pi_pi]
  exact Fintype.prod_equiv σ.symm _ _ fun _ => rfl

/-- `ν^(n+1)(flag) = ∫ R_cal dν^n`. -/
theorem pi_flag {n : ℕ} {α : ℝ} (hα1 : α < 1) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : Fin (n + 1) => ν) (Standalone.D34ScreenCalibration.Flag n α) =
      ∫⁻ c, Rcal ν n α c ∂(Measure.pi fun _ : Fin n => ν) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) (Fin.last n)
  set S : Set (ℝ × (Fin n → ℝ)) := {p | qcal n α p.2 < ((p.1 : ℝ) : WithTop ℝ)}
  have hS : MeasurableSet S := measurableSet_qcal_lt hα1 measurable_snd measurable_fst
  have hpre : Standalone.D34ScreenCalibration.Flag n α =
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n) ⁻¹' S := by
    ext v
    have hv : MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n) v =
        (v (Fin.last n), fun j => v j.castSucc) := by
      simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.removeNth_last]
      rfl
    simp only [Standalone.D34ScreenCalibration.Flag, S, mem_ofPred_eq, mem_preimage, hv]
  rw [hpre, hmp.measure_preimage hS.nullMeasurableSet, Measure.prod_apply_symm hS]
  rfl

end Novel.D34ScreenCalibration
