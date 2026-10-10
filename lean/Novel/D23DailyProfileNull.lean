import Novel.D23DailyProfileSep

/-!
# Claim 068, part 1: measurability, the singular set and scale

* A block's start depends only on the other blocks (`start_congr`), so splitting off block `d`, each
  section of its singular set is claim 033's singular set at a fixed start, which is null when
  `n_d ≥ 2` (`singular_null`). A finite union over blocks is null.
* Claim 033's scale invariance of each `D_u` gives that of `P_day`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23DailyProfile

open Standalone.D23DailyProfile Standalone.D17ClockDrift Standalone.D13DriftNull Standalone.CEVSupport
  Novel.D17ClockDrift

variable {D : ℕ} {n : Fin D → ℕ}

theorem measurable_toR (d : Fin D) : Measurable fun y : Arr n => toR y d :=
  measurable_pi_iff.2 fun j => measurable_subtype_coe.comp ((measurable_pi_apply j).comp
    (measurable_pi_apply d))

theorem measurable_flat : Measurable fun y : Arr n => flatR (toR y) :=
  measurable_pi_iff.2 fun _ => measurable_subtype_coe.comp
    ((measurable_pi_apply _).comp (measurable_pi_apply _))

theorem measurable_start (d : Fin D) : Measurable fun x : ℝ × Arr n => start x.1 x.2 d := by
  by_cases h : off n d < ∑ d, n d + 1
  · have he : (fun x : ℝ × Arr n => start x.1 x.2 d) =
        fun x => (Fin.cons x.1 (flatR (toR x.2)) : Fin (∑ d, n d + 1) → ℝ) ⟨off n d, h⟩ := by
      funext x; simp [start, h]
    rw [he]
    generalize (⟨off n d, h⟩ : Fin (∑ d, n d + 1)) = k
    refine Fin.cases ?_ (fun k' => ?_) k
    · simp only [Fin.cons_zero]; exact measurable_fst
    · simp only [Fin.cons_succ]; exact (measurable_pi_apply k').comp (measurable_flat.comp measurable_snd)
  · have he : (fun x : ℝ × Arr n => start x.1 x.2 d) = fun x => x.1 := by
      funext x; simp [start, h]
    rw [he]; exact measurable_fst

theorem measurable_block (d : Fin D) :
    Measurable fun x : ℝ × Arr n => (start x.1 x.2 d, toR x.2 d) :=
  (measurable_start d).prodMk ((measurable_toR d).comp measurable_snd)

theorem measurable_Pday {Δ : (d : Fin D) → Fin (n d) → ℝ} {𝒰 : (d : Fin D) → Finset (Fin (n d) → ℝ)}
    (h𝒰 : ∀ d, (𝒰 d).Nonempty) : Measurable (fun x : ℝ × Arr n => Pday 𝒰 Δ x.1 x.2) := by
  unfold Pday
  refine Finset.measurable_prod _ fun d _ => ?_
  unfold Pd
  simp_rw [← Finset.sup'_eq_sup (h𝒰 d)]
  convert Finset.measurable_sup' (h𝒰 d) fun u _ =>
    (measurable_Dv (Δ := Δ (d)) (v := u)).comp (measurable_block d) using 1
  funext x
  rw [Finset.sup'_apply]
  rfl

/-- A block's start depends only on the other blocks. -/
theorem start_congr (s : ℝ) {y y' : Arr n} (d : Fin D) (h : ∀ d', d' ≠ d → y d' = y' d') :
    start s y d = start s y' d := by
  unfold start
  split_ifs with hlt
  · generalize hk : (⟨off n d, hlt⟩ : Fin (∑ d, n d + 1)) = k
    revert hk
    refine Fin.cases (fun _ => ?_) (fun k' hk => ?_) k
    · simp
    · simp only [Fin.cons_succ]
      have hv : (k' : ℕ) + 1 = off n d := by
        have := congrArg Fin.val hk; simp at this; omega
      obtain ⟨⟨d', j⟩, rfl⟩ := (finSigmaFinEquiv (n := n)).surjective k'
      have hd : d' ≠ d := by
        rintro rfl
        rw [e_val] at hv; omega
      rw [flatR_e, flatR_e]
      simp only [toR, h d' hd]
  · rfl

theorem measurableSet_sing (Δ : (d : Fin D) → Fin (n d) → ℝ) (s : ℝ) (d : Fin D) :
    MeasurableSet {y : Arr n | PosPath (start s y d) (toR y d) ∧ Sing Δ s y d} := by
  have hb : Measurable fun y : Arr n => (start s y d, toR y d) :=
    (measurable_block d).comp (measurable_const.prodMk measurable_id)
  have : {y : Arr n | Sing Δ s y d} = ⋂ j, ⋂ j', {y | ret (start s y d) (toR y d) j / Δ d j =
      ret (start s y d) (toR y d) j' / Δ d j'} := by
    ext y; simp [Sing]
  have hSing : MeasurableSet {y : Arr n | Sing Δ s y d} := by
    rw [this]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun j' => measurableSet_eq_fun
      (((Novel.D13DriftNull.measurable_ret j).comp hb).div_const _)
      (((Novel.D13DriftNull.measurable_ret j').comp hb).div_const _)
  exact (Novel.D13DriftNull.measurableSet_pos.preimage hb).inter hSing

/-- With every `n_d ≥ 2`, the singular positive arrays are null. -/
theorem sing_null {Δ : (d : Fin D) → Fin (n d) → ℝ} (hΔ : ∀ d j, 0 < Δ d j) (h2 : ∀ d, 2 ≤ n d)
    (s : ℝ) : refM n {y | AllPos s y ∧ ∃ d, Sing Δ s y d} = 0 := by
  have hn : ∀ d, 0 < n d := fun d => by have := h2 d; omega
  refine measure_mono_null (t := ⋃ d, {y : Arr n | PosPath (start s y d) (toR y d) ∧ Sing Δ s y d})
    (fun y ⟨hy, d, hd⟩ => mem_iUnion.2 ⟨d, posPath_block hy hn d, hd⟩) (measure_iUnion_null fun d => ?_)
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by have := d.pos; omega⟩
  set S := {y : Arr n | PosPath (start s y d) (toR y d) ∧ Sing Δ s y d}
  have hS := measurableSet_sing Δ s d
  let X := fun d : Fin (D' + 1) => Fin (n d) → NNR
  let μ := fun d : Fin (D' + 1) => Measure.pi fun _ : Fin (n d) => muCEV
  let e := MeasurableEquiv.piFinSuccAbove X d
  have hmp := measurePreserving_piFinSuccAbove μ d
  have h1 : refM n S = ((μ d).prod (Measure.pi fun i => μ (d.succAbove i))) (e.symm ⁻¹' S) := by
    unfold refM
    rw [← hmp.measure_preimage (e.symm.measurable hS).nullMeasurableSet]
    congr 1
    ext v
    simp only [mem_preimage]
    rw [show e.symm (e v) = v from e.symm_apply_apply v]
  rw [h1, Measure.prod_apply_symm (e.symm.measurable hS)]
  refine (lintegral_eq_zero_iff' (Measurable.aemeasurable ?_)).2 (Filter.Eventually.of_forall fun w => ?_)
  · exact measurable_measure_prodMk_right (e.symm.measurable hS)
  -- The section at the other blocks `w`.
  set y0 := start s (e.symm (fun _ => 0, w)) d
  have hy0 : ∀ x, start s (e.symm (x, w)) d = y0 := fun x =>
    start_congr s d fun d' hd' => by
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hd'
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_apply_succAbove]
  have hxd : ∀ x, toR (e.symm (x, w)) d = fun j => (x j : ℝ) := fun x => by
    funext j; simp [e, toR, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_apply_same]
  refine measure_mono_null (fun x hx => ?_) (singular_null (hΔ d) (hΔ d) (h2 d) y0)
  change PosPath (start s (e.symm (x, w)) d) (toR (e.symm (x, w)) d) ∧ Sing Δ s (e.symm (x, w)) d at hx
  rw [hy0, hxd] at hx
  refine ⟨hx.1, ?_⟩
  unfold Sing at hx
  rw [hy0, hxd] at hx
  exact (Qv_zero_iff (hn d) (hΔ d) (hΔ d) y0 _).2 hx.2

/-- Rescaling each block's shapes leaves `P_day` unchanged. -/
theorem Pday_scale {Δ : (d : Fin D) → Fin (n d) → ℝ} {𝒰 : (d : Fin D) → Finset (Fin (n d) → ℝ)}
    (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) (hu : ∀ d, ∀ u ∈ 𝒰 d, ∀ j, 0 < u j)
    (c : Fin D → ℝ) (hc : ∀ d, 0 < c d) (s : ℝ) (y : Arr n) :
    Pday (fun d => (𝒰 d).image fun u => c d • u) Δ s y = Pday 𝒰 Δ s y := by
  unfold Pday Pd
  refine Finset.prod_congr rfl fun d _ => ?_
  rw [Finset.sup_image]
  exact Finset.sup_congr rfl fun u hud => Dv_scale (hn d) (hΔ d) (hu d u hud) (hc d) _ _

theorem profile_holds : Standalone.D23DailyProfile.profile := by
  intro D n Δ 𝒰 hn hΔ h𝒰 hu
  refine ⟨measurable_Pday h𝒰, fun s y hy => ⟨fun d => Pd_pos hn hΔ h𝒰 hu hy d,
    Pday_pos hn hΔ h𝒰 hu hy, jointSup_eq hn hΔ h𝒰 hu hy, fun hns => ⟨fun d u hud => ?_, ?_,
    attained hn hΔ h𝒰 hu hy hns⟩, fun d hd => ?_, fun d h1 => ?_⟩,
    fun h2 s _ => sing_null hΔ h2 s, fun c hc s y => Pday_scale hn hΔ hu c hc s y⟩
  · exact Dv_fin (posPath_block hy hn d) ((Qd_pos_iff hn hΔ hu s y d hud).2 (hns d))
  · obtain ⟨ch, hch, he⟩ := attained hn hΔ h𝒰 hu hy hns
    rw [← he]
    exact ENNReal.prod_lt_top fun d _ => ENNReal.ofReal_lt_top
  · obtain ⟨h1, h2⟩ := singular_top hn hΔ h𝒰 hu hy hd
    refine ⟨h1, h2, fun q => ?_⟩
    unfold Eday
    simp only [hy, ↓reduceIte, h2, ENNReal.div_top]
  · have : Subsingleton (Fin (n d)) := by rw [h1]; infer_instance
    intro j j'
    rw [Subsingleton.elim j j']

end Novel.D23DailyProfile
