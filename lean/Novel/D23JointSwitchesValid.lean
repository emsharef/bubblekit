import Novel.D23JointSwitchesRec

/-!
# Claim 070, (8): calibration under the actual kernel mixture

Every admissible component density is at most its shape's `P_joint`, hence at most the catalogue
maximum; integrating against the probability kernel keeps the bound (`mixDens_le`). So the score times
the actual density is at most the forecast, and AX-58's step gives the conditional and unconditional
bounds once for the whole evaluation array; Markov gives the size.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23JointSwitches

open Standalone.D23JointSwitches Standalone.D23DailyProfile Standalone.D17ClockDrift
  Standalone.D13DriftNull Standalone.CEVSupport Novel.D17ClockDrift Novel.D23DailyProfile

variable {D : ℕ} {n : Fin D → ℕ}

theorem measurable_finset_sup {α ι : Type*} [MeasurableSpace α] (S : Finset ι) {f : ι → α → ℝ≥0∞}
    (hf : ∀ i ∈ S, Measurable (f i)) : Measurable fun x => S.sup fun i => f i x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sup_empty]; exact measurable_const
  | insert a S ha ih =>
    simp only [Finset.sup_insert]
    exact (hf a (Finset.mem_insert_self _ _)).sup (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The catalogue denominator. -/
noncomputable def Pcat (Δ : Fam n) (𝒰 : Finset (Fam n)) (K : ℕ) (s : ℝ) (y : Arr n) : ℝ≥0∞ :=
  𝒰.sup fun u => Pjoint Δ u K s y

theorem mixDens_le {T : Type} [MeasurableSpace T] (Δ : Fam n) (𝒰 : Finset (Fam n)) (K : ℕ)
    (ν : Kernel T (𝒰 × (Fin D → ℝ) × (Fin D → ℝ))) [IsMarkovKernel ν] (s : T → ℝ)
    (hν : ∀ t, ν t {θ | ¬ ((∀ d, 0 < θ.2.2 d) ∧ countPair θ.2.1 θ.2.2 ≤ K)} = 0) (t : T) (y : Arr n) :
    mixDens Δ 𝒰 ν s t y ≤ Pcat Δ 𝒰 K (s t) y := by
  unfold mixDens
  have hae : ∀ᵐ θ ∂(ν t), (∀ d, 0 < θ.2.2 d) ∧ countPair θ.2.1 θ.2.2 ≤ K := ae_iff.2 (hν t)
  calc ∫⁻ θ, G Δ θ.1.1 θ.2.1 θ.2.2 (s t) y ∂(ν t) ≤ ∫⁻ _θ, Pcat Δ 𝒰 K (s t) y ∂(ν t) := by
        refine lintegral_mono_ae (hae.mono fun θ hθ => ?_)
        exact (le_iSup₂_of_le θ.2.1 θ.2.2 (le_iSup (fun _ : ((∀ d, 0 < θ.2.2 d) ∧
          countPair θ.2.1 θ.2.2 ≤ K) => G Δ θ.1 θ.2.1 θ.2.2 (s t) y) hθ)).trans
          (Finset.le_sup (f := fun u => Pjoint Δ u K (s t) y) θ.1.2)
    _ = Pcat Δ 𝒰 K (s t) y := by simp

theorem Pcat_pos {Δ : Fam n} {𝒰 : Finset (Fam n)} (hD : 0 < D) (hn : ∀ d, 0 < n d)
    (hΔ : ∀ d j, 0 < Δ d j) (h𝒰 : 𝒰.Nonempty) (hu : ∀ u ∈ 𝒰, ∀ d j, 0 < u d j) (K : ℕ) {s : ℝ}
    {y : Arr n} (hy : AllPos s y) : 0 < Pcat Δ 𝒰 K s y := by
  obtain ⟨u, hu𝒰⟩ := h𝒰
  exact lt_of_lt_of_le ((budget_holds D n Δ u hD hn hΔ (hu u hu𝒰) K).2 s y hy).1
    (Finset.le_sup (f := fun u => Pjoint Δ u K s y) hu𝒰)

theorem measurable_Pcat {Δ : Fam n} {𝒰 : Finset (Fam n)} (hD : 0 < D) (hn : ∀ d, 0 < n d)
    (hΔ : ∀ d j, 0 < Δ d j) (hu : ∀ u ∈ 𝒰, ∀ d j, 0 < u d j) (K : ℕ) :
    Measurable ({x : ℝ × Arr n | AllPos x.1 x.2}.indicator fun x => Pcat Δ 𝒰 K x.1 x.2) := by
  have he : {x : ℝ × Arr n | AllPos x.1 x.2}.indicator (fun x => Pcat Δ 𝒰 K x.1 x.2) =
      fun x => 𝒰.sup fun u => {x : ℝ × Arr n | AllPos x.1 x.2}.indicator
        (fun x => Pjoint Δ u K x.1 x.2) x := by
    funext x
    by_cases hx : AllPos x.1 x.2
    · simp only [Set.indicator_of_mem (show x ∈ {x : ℝ × Arr n | AllPos x.1 x.2} from hx), Pcat]
    · simp only [Set.indicator_of_notMem (show x ∉ {x : ℝ × Arr n | AllPos x.1 x.2} from hx)]
      exact (Finset.sup_bot 𝒰).symm
  rw [he]
  exact measurable_finset_sup 𝒰 fun u hu𝒰 => (budget_holds D n Δ u hD hn hΔ (hu u hu𝒰) K).1

open Classical in
theorem calibration_holds : Standalone.D23JointSwitches.calibration := by
  intro T _ _ Ω _ P _ D n Δ 𝒰 K s q ν _ U V hD hn hΔ h𝒰 hu hs hspos hq hq0 hq1 hU hV hν hpm hpfin hlaw E
  have : IsProbabilityMeasure (P.map U) :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  have hsy : Measurable fun p : T × Arr n => (s p.1, p.2) := (hs.comp measurable_fst).prodMk measurable_snd
  have hA : MeasurableSet {p : T × Arr n | AllPos (s p.1) p.2} := measurableSet_allPos.preimage hsy
  -- `P_cat` on the positive domain, as a measurable function.
  set F : T × Arr n → ℝ≥0∞ := fun p =>
    {x : ℝ × Arr n | AllPos x.1 x.2}.indicator (fun x => Pcat Δ 𝒰 K x.1 x.2) (s p.1, p.2)
  have hFm : Measurable F := (measurable_Pcat hD hn hΔ hu K).comp hsy
  have hEm : Measurable (Function.uncurry E) := by
    have he : Function.uncurry E = fun p : T × Arr n =>
        if AllPos (s p.1) p.2 then ENNReal.ofReal (q p.1 p.2) * (F p)⁻¹ else 0 := by
      funext p
      show Escore _ _ _ _ = _
      unfold Escore
      split_ifs with hp
      · simp only [F, Set.indicator_of_mem (show (s p.1, p.2) ∈ {x : ℝ × Arr n | AllPos x.1 x.2} from hp)]
        rfl
      · rfl
    rw [he]
    exact Measurable.ite hA (hq.ennreal_ofReal.mul hFm.inv) measurable_const
  have hfin : ∀ t y, E t y < ⊤ := fun t y => by
    show Escore _ _ _ _ < ⊤
    unfold Escore
    split_ifs with hy
    · exact ENNReal.div_lt_top ENNReal.ofReal_ne_top (Pcat_pos hD hn hΔ h𝒰 hu K hy).ne'
    · exact ENNReal.zero_lt_top
  have hkey : ∀ t y, mixDens Δ 𝒰 ν s t y * E t y ≤ ENNReal.ofReal (q t y) := fun t y => by
    show _ * Escore _ _ _ _ ≤ _
    unfold Escore
    split_ifs with hy
    · calc mixDens Δ 𝒰 ν s t y * (ENNReal.ofReal (q t y) / Pcat Δ 𝒰 K (s t) y)
          ≤ Pcat Δ 𝒰 K (s t) y * (ENNReal.ofReal (q t y) / Pcat Δ 𝒰 K (s t) y) :=
            mul_le_mul_left (mixDens_le Δ 𝒰 K ν s hν t y) _
        _ ≤ _ := ENNReal.mul_div_le
    · rw [mul_zero]; exact bot_le
  have hcond : ∀ᵐ t ∂(P.map U), ∫⁻ y, E t y ∂(condDistrib V U P t) ≤ 1 := by
    filter_upwards [hlaw] with t ht
    have hpm' : Measurable fun y => mixDens Δ 𝒰 ν s t y := hpm.comp measurable_prodMk_left
    have hEt : Measurable fun y => E t y := hEm.comp measurable_prodMk_left
    rw [ht, lintegral_withDensity_eq_lintegral_mul _ hpm' hEt]
    calc ∫⁻ y, ((fun y => mixDens Δ 𝒰 ν s t y) * E t) y ∂(refM n)
        ≤ ∫⁻ y, ENNReal.ofReal (q t y) ∂(refM n) := lintegral_mono fun y => hkey t y
      _ = 1 := hq1 t
  have huncond : ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 := by
    rw [show (∫⁻ ω, E (U ω) (V ω) ∂P) = ∫⁻ ω, Function.uncurry E (U ω, V ω) ∂P from rfl,
      Novel.D14SupportRobustness.disint hU hV hEm]
    calc ∫⁻ t, ∫⁻ y, Function.uncurry E (t, y) ∂(condDistrib V U P t) ∂(P.map U)
        ≤ ∫⁻ _t, 1 ∂(P.map U) := lintegral_mono_ae hcond
      _ = 1 := by simp
  have hEω : Measurable fun ω => E (U ω) (V ω) := hEm.comp (hU.prodMk hV)
  refine ⟨hfin, hEm, hcond, huncond, fun α hα _ => ?_, fun F' _ hF => (lintegral_mono hF).trans huncond⟩
  refine le_trans (measure_mono fun ω hω => ?_) (Novel.D18SignNoise.size_ge hEω huncond hα)
  exact (show ENNReal.ofReal (1 / α) < E (U ω) (V ω) from hω).le

end Novel.D23JointSwitches
