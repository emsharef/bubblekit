import Novel.D18ClockNoiseState

/-!
# Claim 066: the denominators (4), the domination (5) and AX-58's consequences

* `DstC`, `DsupC` and their minimum are in `(0, 1]`, decrease with the state level (parent bounds)
  and under any refining set of child boxes (`UsW_mono_W`/`Usup_mono` with `Wclock_mono`).
* **Domination for one latent state.** From `(x₀, h₀, v, b, w)` with `(b, w)` in a box of the
  cover and `v ∈ 𝒱`, the label probability under (2) is
  - at most the state bound: it is claim 065's `Qg` (`jointLawG_labels`), bounded by `Qg_le_UsW`
    with `W = Wclock B`;
  - at most the support bound: on the label event every latent price lies in its expanded
    interval, the returns' marginal is the Gaussian product (`lintegral_jointLawG_fst`), and the
    box event is bounded by `Qh_le_Bsup`.
* **The conditional law** (`dom_gen`): disintegrate over `(U, X₀, H₀, V, B)`, as in claim 065, for
  any bound function of the training record. So a cover and level selected from `(U, Z)` keep (5).
* **AX-58** with counting measure, disintegration and Markov.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18ClockNoise

open Standalone.D18ClockNoise Standalone.D17ClockCells Standalone.D18SignNoise
  Standalone.D18BoundedNoise Standalone.D14FixedTick Novel.D17ClockCells Novel.D18SignNoise
  Novel.D18BoundedNoise Novel.D14FixedTick

variable {δ a ρ β : ℝ} {n : ℕ} {Δ : Fin n → ℝ} {𝒱 : Finset (Fin n → ℝ)}

/-! ## The state maximum -/

theorem DstC_bounds (hδ : 0 < δ) (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {C : Finset Box}
    (hC : C.Nonempty) (hCv : ∀ B ∈ C, B.Valid) (hΔ : ∀ j, 0 < Δ j) (h𝒱 : 𝒱.Nonempty)
    (hv : ∀ vc ∈ 𝒱, ∀ j, 0 < vc j) (ℓ z₀ : ℕ) (v : Fin n → ℕ) :
    0 < DstC δ a ρ β C ℓ Δ 𝒱 z₀ v ∧ DstC δ a ρ β C ℓ Δ 𝒱 z₀ v ≤ 1 := by
  obtain ⟨vc, hvc⟩ := h𝒱
  obtain ⟨B, hB⟩ := hC
  refine ⟨lt_of_lt_of_le (ENNReal.ofReal_pos.2 (UsW_pos (β := β) hδ ha hρ0 hρ1 n ℓ Δ vc z₀ v false 0
    (fun j => Wclock_ok (hCv B hB) (hΔ j) (hv vc hvc j)) (feas_false hδ ha z₀)))
    (le_iSup₂_of_le B hB (le_iSup₂_of_le vc hvc (le_iSup₂_of_le false (false_mem_feasT hδ ha z₀)
      (le_iSup₂_of_le 0 (mem_range_pow ℓ) le_rfl)))), ?_⟩
  exact iSup₂_le fun _ _ => iSup₂_le fun _ _ => iSup₂_le fun _ _ => iSup₂_le fun _ _ =>
    ENNReal.ofReal_le_one.2 (UsW_le_one _ _ _ _ _ _ _ _)

theorem DstC_ℓ_succ (C : Finset Box) (ℓ z₀ : ℕ) (v : Fin n → ℕ) :
    DstC δ a ρ β C (ℓ + 1) Δ 𝒱 z₀ v ≤ DstC δ a ρ β C ℓ Δ 𝒱 z₀ v := by
  refine iSup₂_le fun B hB => iSup₂_le fun vc hvc => iSup₂_le fun h hh => iSup₂_le fun d hd => ?_
  have hd2 : d / 2 < 2 ^ ℓ := by have := Finset.mem_range.1 hd; rw [pow_succ] at this; omega
  exact (ENNReal.ofReal_le_ofReal (UsW_parent ℓ _ _ z₀ v h d)).trans (le_iSup₂_of_le B hB
    (le_iSup₂_of_le vc hvc (le_iSup₂_of_le h hh (le_iSup₂_of_le (d / 2) (Finset.mem_range.2 hd2)
      le_rfl))))

theorem DstC_refine (hδ : 0 < δ) (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {C C' : Finset Box}
    (hCv : ∀ B ∈ C, B.Valid) (hC' : Refines C' C) (hΔ : ∀ j, 0 < Δ j)
    (hv : ∀ vc ∈ 𝒱, ∀ j, 0 < vc j) (ℓ z₀ : ℕ) (v : Fin n → ℕ) :
    DstC δ a ρ β C' ℓ Δ 𝒱 z₀ v ≤ DstC δ a ρ β C ℓ Δ 𝒱 z₀ v := by
  refine iSup₂_le fun B' hB' => iSup₂_le fun vc hvc => iSup₂_le fun h hh => iSup₂_le fun d hd => ?_
  obtain ⟨hv', B, hB, hsub⟩ := hC' B' hB'
  refine le_iSup₂_of_le B hB (le_iSup₂_of_le vc hvc (le_iSup₂_of_le h hh (le_iSup₂_of_le d hd
    (ENNReal.ofReal_le_ofReal ?_))))
  exact UsW_mono_W hδ ha hρ0 hρ1 n ℓ Δ vc z₀ v h d (fun j => Wclock_ok hv' (hΔ j) (hv vc hvc j))
    (fun j _ _ _ _ ha' hab hc hcd => Wclock_mono (hCv B hB) hv' hsub ha' hab hc hcd (hΔ j)
      (hv vc hvc j)) (mem_feasT.1 hh)

/-! ## Domination for one latent state -/

/-- The label probability from one latent state is at most the state bound. -/
theorem joint_le_DstC (hδ : 0 < δ) (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {C : Finset Box}
    {B : Box} (hB : B ∈ C) (hBv : B.Valid) (hΔ : ∀ j, 0 < Δ j) {vc : Fin n → ℝ} (hvc : vc ∈ 𝒱)
    (hv : ∀ j, 0 < vc j) {bp : ℝ × ℝ} (hbp : B.Mem bp) {z₀ : ℕ} {h₀ : Bool} {x₀ : ℝ}
    (hx : x₀ ∈ Ico (ilo δ a z₀ h₀) (ihi δ a z₀ h₀)) (ℓ : ℕ) (v : Fin n → ℕ) :
    jointLawG ρ β (muC Δ vc bp) (sdC vc bp) x₀ h₀ {p | labelsOf δ a x₀ p = v} ≤
      DstC δ a ρ β C ℓ Δ 𝒱 z₀ v := by
  rw [jointLawG_labels hρ0 hρ1]
  have hf : Feas δ a z₀ h₀ := hx.1.trans_lt hx.2
  obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.1 (isub_cover hf ℓ hx)
  exact (Qg_le_UsW hδ ha hρ0 hρ1 n ℓ _ _ Δ vc z₀ v h₀ d (fun j => Wclock_ok hBv (hΔ j) (hv j))
    (fun j => Wclock_dom hBv hbp (hΔ j) (hv j)) hf x₀ hxd).trans (le_iSup₂_of_le B hB
      (le_iSup₂_of_le vc hvc (le_iSup₂_of_le h₀ (mem_feasT.2 hf) (le_iSup₂_of_le d hd le_rfl))))

/-- The label probability from one latent state is at most the support bound. -/
theorem joint_le_DsupC (hδ : 0 < δ) (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {C : Finset Box}
    {B : Box} (hB : B ∈ C) (hBv : B.Valid) (hΔ : ∀ j, 0 < Δ j) {vc : Fin n → ℝ} (hvc : vc ∈ 𝒱)
    (hv : ∀ j, 0 < vc j) {bp : ℝ × ℝ} (hbp : B.Mem bp) {z₀ : ℕ} {h₀ : Bool} {x₀ : ℝ}
    (hx : x₀ ∈ Ico (ilo δ a z₀ h₀) (ihi δ a z₀ h₀)) (ℓ : ℕ) (v : Fin n → ℕ) :
    jointLawG ρ β (muC Δ vc bp) (sdC vc bp) x₀ h₀ {p | labelsOf δ a x₀ p = v} ≤
      DsupC δ a C ℓ Δ 𝒱 z₀ v := by
  have hx0 : 0 ≤ x₀ := (ilo_nonneg _ _).trans hx.1
  have hΦ : Measurable fun ξ : Fin n → ℝ => ∏ j, ENNReal.ofReal (hbox δ a (v j) (lpath n x₀ ξ j)) :=
    Measurable.comp (g := fun q : ℝ × (Fin n → ℝ) => ∏ j, ENNReal.ofReal (hbox δ a (v j) (lpath n q.1 q.2 j)))
      (f := fun ξ : Fin n → ℝ => (x₀, ξ)) (measurable_prod_h (h := hbox δ a) hbox_meas v)
      (measurable_const.prodMk measurable_id)
  have hS : MeasurableSet {p : (Fin n → ℝ) × (Fin n → Bool) | labelsOf δ a x₀ p = v} :=
    measurableSet_eq_fun ((measurable_labelsOf δ a (n := n)).comp
      (measurable_const.prodMk measurable_id)) measurable_const
  calc jointLawG ρ β (muC Δ vc bp) (sdC vc bp) x₀ h₀ {p | labelsOf δ a x₀ p = v}
      = ∫⁻ p, {p | labelsOf δ a x₀ p = v}.indicator 1 p
          ∂(jointLawG ρ β (muC Δ vc bp) (sdC vc bp) x₀ h₀) := (lintegral_indicator_one hS).symm
    _ ≤ ∫⁻ p, (fun ξ => ∏ j, ENNReal.ofReal (hbox δ a (v j) (lpath n x₀ ξ j))) p.1
          ∂(jointLawG ρ β (muC Δ vc bp) (sdC vc bp) x₀ h₀) := lintegral_mono fun p => by
        by_cases hp : labelsOf δ a x₀ p = v
        · rw [indicator_of_mem (show p ∈ {p | labelsOf δ a x₀ p = v} from hp), Pi.one_apply]
          refine le_of_eq (Finset.prod_eq_one fun j _ => ?_).symm
          have hj : obs δ a (lpath n x₀ p.1 j) (p.2 j) = v j := congrFun hp j
          have hm := obs_mem (a := a) hδ (lpath_nonneg n p.1 hx0 j) (p.2 j)
          rw [hj] at hm
          simp [hbox, icell_sub_ecell hδ ha _ _ hm]
        · rw [indicator_of_notMem (show p ∉ {p | labelsOf δ a x₀ p = v} from hp)]
          exact bot_le
    _ = ∫⁻ ξ, (fun ξ => ∏ j, ENNReal.ofReal (hbox δ a (v j) (lpath n x₀ ξ j))) ξ
          ∂(gpi (muC Δ vc bp) (sdC vc bp)) :=
        lintegral_jointLawG_fst (f := fun ξ => ∏ j, ENNReal.ofReal (hbox δ a (v j) (lpath n x₀ ξ j)))
          hρ0 hρ1 _ _ x₀ h₀ hΦ
    _ = Qh (hbox δ a) (muC Δ vc bp) (sdC vc bp) v x₀ := rfl
    _ ≤ ENNReal.ofReal (Bsup δ a B ℓ Δ vc z₀ v) :=
        Qh_le_Bsup hδ ha hBv ℓ hΔ hv v hbp (icell_sub_ecell hδ ha z₀ h₀ hx)
    _ ≤ DsupC δ a C ℓ Δ 𝒱 z₀ v := le_iSup₂_of_le B hB (le_iSup₂_of_le vc hvc le_rfl)

/-- From one latent state covered by `C`, the label probability is at most (4). -/
theorem joint_le_Dcn (hδ : 0 < δ) (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {ℬ : Box}
    {C : Finset Box} (hC : Covers ℬ C) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ vc ∈ 𝒱, ∀ j, 0 < vc j)
    {vc : Fin n → ℝ} (hvc : vc ∈ 𝒱) {bp : ℝ × ℝ} (hbp : ℬ.Mem bp) {z₀ : ℕ} {h₀ : Bool} {x₀ : ℝ}
    (hx : x₀ ∈ Ico (ilo δ a z₀ h₀) (ihi δ a z₀ h₀)) (ℓ : ℕ) (v : Fin n → ℕ) :
    jointLawG ρ β (muC Δ vc bp) (sdC vc bp) x₀ h₀ {p | labelsOf δ a x₀ p = v} ≤
      Dcn δ a ρ β C ℓ Δ 𝒱 z₀ v := by
  obtain ⟨B, hB, hbB⟩ := hC.2 bp hbp
  exact le_min (joint_le_DstC hδ ha hρ0 hρ1 hB (hC.1 B hB) hΔ hvc (hv vc hvc) hbB hx ℓ v)
    (joint_le_DsupC hδ ha hρ0 hρ1 hB (hC.1 B hB) hΔ hvc (hv vc hvc) hbB hx ℓ v)

end Novel.D18ClockNoise
