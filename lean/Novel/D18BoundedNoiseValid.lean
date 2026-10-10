import Novel.D18BoundedNoiseWalk
import Novel.D14SupportRobustnessProof

/-!
# Claim 064: domination (6) and AX-58's consequences

* `dom_core`: both modes at once. Suppose that, for every label path `v` and measurable training
  set `A`, `P(U ∈ A, V = v) ≤ E[1_A(U) ∏_j h(v_j, X_j)]` along the latent path. Then for almost
  every `u` and all `v` and levels, `P(V = v | U = u) ≤ D`.
  The proof disintegrates over `(U, Θ, X₀)`. Given those, the inner expectation is `Qh` under
  `Θ`'s Gaussian law from `X₀ > 0`; from `X₀ = 0` the path is zero whatever the returns, so it is
  `Qh` at `0` again. `X₀` lies in the expanded last cell, so `Qh ≤ B ≤ D` (`Qh_le_Bn`). Comparing
  set integrals gives the conditional bound.
* **Support mode.** On `V = v`, each latent price lies in its expanded interval by (2), so the
  label event is contained in the latent box event: `h = 1_{I^a}`, with `M = 1`.
* **Uniform mode.** Given `(U, Θ, X₀, X)`, the label event has probability `∏ g_(v_j)(X_j)` exactly,
  by (1) and (3): `h = gnoise`, with `M = Mnoise`.
* `conclusions_of_dom`: AX-58's pointwise step with counting measure, disintegration and Markov,
  as in claim 031.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18BoundedNoise

open Standalone.D18BoundedNoise Standalone.D14FixedTick Standalone.D14Cell Novel.D14FixedTick

/-- (2): a label and a bounded error place the latent price in the expanded interval. -/
theorem expanded_holds {δ a x y : ℝ} (hδ : 0 < δ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : |y - x| ≤ a) :
    x ∈ ecell δ a (mlabel δ y) := by
  have hc := (mlabel_eq_iff hδ hy (mlabel δ y)).1 rfl
  rw [abs_le] at hxy
  exact ⟨max_le hx (by linarith [hc.1]), by unfold ehi; linarith [hc.2]⟩

section Cons

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {k n : ℕ}
  {U : Ω → Fin (k + 1) → ℕ} {V : Ω → Fin n → ℕ} {q : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ}
  {Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ} {D : ℕ → (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ≥0∞}

/-- AX-58's consequences from the domination and the bounds on `D`. -/
theorem conclusions_of_dom (hU : Measurable U) (hV : Measurable V)
    (hq1 : ∀ u, ∑' v, ENNReal.ofReal (q u v) = 1) (hD : ∀ ℓ u v, 0 < D ℓ u v ∧ D ℓ u v ≤ 1)
    (hdom : ∀ᵐ u ∂(P.map U), ∀ v ℓ, condDistrib V U P u {v} ≤ D ℓ u v) :
    conclusions P U V q Lv D := by
  unfold conclusions
  intro E
  have hDtop : ∀ ℓ u v, D ℓ u v ≠ ⊤ := fun ℓ u v => ((hD ℓ u v).2.trans_lt ENNReal.one_lt_top).ne
  have hfin : ∀ u v, E u v < ⊤ := fun u v =>
    ENNReal.div_lt_top ENNReal.ofReal_ne_top (hD _ u v).1.ne'
  have hcond : ∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1 := by
    filter_upwards [hdom] with u hu
    rw [lintegral_countable']
    calc ∑' v, E u v * condDistrib V U P u {v} ≤ ∑' v, ENNReal.ofReal (q u v) :=
          ENNReal.tsum_le_tsum fun v => by
            calc E u v * condDistrib V U P u {v} ≤ E u v * D (Lv u v) u v :=
                  mul_le_mul_right (hu v (Lv u v)) _
              _ = ENNReal.ofReal (q u v) := ENNReal.div_mul_cancel (hD _ u v).1.ne' (hDtop _ u v)
      _ = 1 := hq1 u
  have hEm : Measurable fun p : (Fin (k + 1) → ℕ) × (Fin n → ℕ) => E p.1 p.2 :=
    measurable_of_countable _
  have huncond : ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 := by
    rw [show (∫⁻ ω, E (U ω) (V ω) ∂P) =
      ∫⁻ ω, (fun p : (Fin (k + 1) → ℕ) × (Fin n → ℕ) => E p.1 p.2) (U ω, V ω) ∂P from rfl,
      Novel.D14SupportRobustness.disint hU hV hEm]
    have := (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 ‹_›
    calc ∫⁻ u, ∫⁻ v, E u v ∂(condDistrib V U P u) ∂(P.map U) ≤ ∫⁻ _u, 1 ∂(P.map U) :=
          lintegral_mono_ae hcond
      _ = 1 := by simp
  refine ⟨hD, hfin, hdom, hcond, huncond, fun α hα _ => ?_, fun F _ hF =>
    (lintegral_mono hF).trans huncond⟩
  have hT : Measurable fun ω => E (U ω) (V ω) := hEm.comp (hU.prodMk hV)
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hT.aemeasurable (ENNReal.ofReal (1 / α))
  have hsub : {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ⊆
      {ω | ENNReal.ofReal (1 / α) ≤ E (U ω) (V ω)} := fun ω (hω : _ < E (U ω) (V ω)) =>
    show _ ≤ E (U ω) (V ω) from le_of_lt hω
  have hle : ENNReal.ofReal (1 / α) * P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ 1 :=
    (mul_le_mul_right (measure_mono hsub) _).trans (hmk.trans huncond)
  have hinv : (ENNReal.ofReal (1 / α))⁻¹ = ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
  rw [← hinv, ENNReal.le_inv_iff_mul_le, mul_comm]
  exact hle

end Cons

section Dom

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {k n : ℕ}
  {δ a : ℝ} {Δ : Fin n → ℝ} {Γ : Finset (ℝ × ℝ)} {U : Ω → Fin (k + 1) → ℕ} {Θ : Ω → ℝ × ℝ}
  {X₀ Y₀ : Ω → ℝ} {R : Ω → Fin n → ℝ}

theorem Dn_bounds (hδ : 0 < δ) (ha : 0 ≤ a) (hΔ : ∀ j, 0 < Δ j) (hΓ : Γ.Nonempty)
    (hΓκ : ∀ θ ∈ Γ, 0 < θ.2) {M : ℕ → ℕ → ℕ → ℝ} (hM : ∀ ℓ z d, d < 2 ^ ℓ → 0 < M ℓ z d)
    (ℓ z₀ : ℕ) (v : Fin n → ℕ) : 0 < Dn δ a M ℓ Δ Γ z₀ v ∧ Dn δ a M ℓ Δ Γ z₀ v ≤ 1 := by
  obtain ⟨θ, hθ⟩ := hΓ
  refine ⟨(ENNReal.ofReal_pos.2 (Bn_bounds hδ ha hM ℓ (fun j => Novel.D14Cell.sθ_pos hΔ
    (hΓκ θ hθ) j) z₀ v).1).trans_le (le_iSup₂_of_le θ hθ le_rfl), iSup₂_le fun θ' h' => ?_⟩
  exact ENNReal.ofReal_le_one.2 (Bn_bounds hδ ha hM ℓ (fun j => Novel.D14Cell.sθ_pos hΔ
    (hΓκ θ' h') j) z₀ v).2

/-- The parameter lies in the catalogue and the endpoint in the expanded last cell. -/
theorem latent_ae (hδ : 0 < δ) (hU : Measurable U) (hΘ : Measurable Θ) (hX : Measurable X₀)
    (hlat : latent P δ a Δ Γ U Θ X₀ Y₀ R) :
    ∀ᵐ w ∂(P.map fun ω => (U ω, Θ ω, X₀ ω)),
      w.2.1 ∈ Γ ∧ w.2.2 ∈ ecell δ a (w.1 (Fin.last k)) := by
  have hW : Measurable fun ω => (U ω, Θ ω, X₀ ω) := hU.prodMk (hΘ.prodMk hX)
  have hl : Measurable fun w : (Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ => w.1 (Fin.last k) :=
    (measurable_pi_apply _).comp measurable_fst
  have hx : Measurable fun w : (Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ => w.2.2 :=
    measurable_snd.comp measurable_snd
  have hS : MeasurableSet {w : (Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ |
      w.2.1 ∈ Γ ∧ w.2.2 ∈ ecell δ a (w.1 (Fin.last k))} :=
    ((measurable_fst.comp measurable_snd) Γ.finite_toSet.measurableSet).inter
      ((measurableSet_le ((measurable_of_countable (elo δ a)).comp hl) hx).inter
        (measurableSet_lt hx ((measurable_of_countable (ehi δ a)).comp hl)))
  refine (ae_map_iff hW.aemeasurable hS).2 ?_
  filter_upwards [hlat.1] with ω ⟨hθ, hx0, hy0, hxy, hlast⟩
  refine ⟨hθ, ?_⟩
  show X₀ ω ∈ ecell δ a (U ω (Fin.last k))
  rw [hlast]; exact expanded_holds hδ hx0 hy0 hxy

/-- (6) from a bound on the label event by an emission product along the latent path. -/
theorem dom_core (hδ : 0 < δ) (ha : 0 ≤ a) (hΔ : ∀ j, 0 < Δ j) (hΓκ : ∀ θ ∈ Γ, 0 < θ.2)
    (hU : Measurable U) (hΘ : Measurable Θ) (hX : Measurable X₀) (hR : Measurable R)
    {V : Ω → Fin n → ℕ} (hV : Measurable V)
    {h : ℕ → ℝ → ℝ} (hhm : ∀ z, Measurable (h z)) (hh1 : ∀ z y, h z y ≤ 1)
    (hout : ∀ z y, 0 ≤ y → y ∉ ecell δ a z → h z y = 0)
    {M : ℕ → ℕ → ℕ → ℝ} (hM : ∀ ℓ z d, d < 2 ^ ℓ → 0 < M ℓ z d)
    (hhM : ∀ ℓ z d, d < 2 ^ ℓ → ∀ y ∈ esub δ a ℓ z d, h z y ≤ M ℓ z d)
    (hlat : latent P δ a Δ Γ U Θ X₀ Y₀ R)
    (hPV : ∀ (v : Fin n → ℕ) (A : Set (Fin (k + 1) → ℕ)), MeasurableSet A →
      P (U ⁻¹' A ∩ V ⁻¹' {v}) ≤ ∫⁻ ω, A.indicator 1 (U ω) *
        ∏ j, ENNReal.ofReal (h (v j) (lpath n (X₀ ω) (R ω) j)) ∂P) :
    ∀ᵐ u ∂(P.map U), ∀ v ℓ, condDistrib V U P u {v} ≤ Dn δ a M ℓ Δ Γ (u (Fin.last k)) v := by
  rw [ae_all_iff]; intro v
  rw [ae_all_iff]; intro ℓ
  have : IsProbabilityMeasure (P.map U) :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  set W := fun ω => (U ω, Θ ω, X₀ ω) with hWdef
  have hW : Measurable W := hU.prodMk (hΘ.prodMk hX)
  set Φ : ((Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ) × (Fin n → ℝ) → ℝ≥0∞ :=
    fun p => ∏ j, ENNReal.ofReal (h (v j) (lpath n p.1.2.2 p.2 j)) with hΦdef
  have hΦ : Measurable Φ := (measurable_prod_h hhm v).comp
    ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have hin : ∀ᵐ w ∂(P.map W), ∫⁻ r, Φ (w, r) ∂(condDistrib R W P w) ≤
      Dn δ a M ℓ Δ Γ (w.1 (Fin.last k)) v := by
    filter_upwards [latent_ae hδ hU hΘ hX hlat, hlat.2] with w hw hg
    obtain ⟨hθ, hx⟩ := hw
    have hx0 : 0 ≤ w.2.2 := (elo_nonneg _).trans hx.1
    have hq : ∫⁻ r, Φ (w, r) ∂(condDistrib R W P w) = Qh h (muθ Δ w.2.1) (sθ Δ w.2.1) v w.2.2 := by
      rcases hx0.lt_or_eq with hpos | hzero
      · rw [hg hpos]; rfl
      · have h0 : w.2.2 = 0 := hzero.symm
        unfold Qh
        simp only [hΦdef, h0, lpath_zero]
        rw [lintegral_const, lintegral_const, measure_univ, measure_univ]
    rw [hq]
    exact (Qh_le_Bn hhm hh1 hδ ha hout hM hhM ℓ (fun j => Novel.D14Cell.sθ_pos hΔ (hΓκ _ hθ) j) v
      hx).trans (le_iSup₂_of_le w.2.1 hθ le_rfl)
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    ((condDistrib V U P).measurable_coe (measurableSet_singleton v)) fun A hA _ => ?_
  have hL : ∫⁻ u in A, condDistrib V U P u {v} ∂(P.map U) = P (U ⁻¹' A ∩ V ⁻¹' {v}) := by
    rw [← Measure.compProd_apply_prod hA (measurableSet_singleton v),
      compProd_map_condDistrib hU.aemeasurable hV.aemeasurable,
      Measure.map_apply (hU.prodMk hV) (hA.prod (measurableSet_singleton v))]
    rfl
  rw [hL]
  refine (hPV v A hA).trans ?_
  have hF : Measurable fun p : ((Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ) × (Fin n → ℝ) =>
      A.indicator 1 p.1.1 * Φ p :=
    ((measurable_const.indicator hA).comp (measurable_fst.comp measurable_fst)).mul hΦ
  set f0 : (Fin (k + 1) → ℕ) → ℝ≥0∞ := fun u => A.indicator 1 u * Dn δ a M ℓ Δ Γ (u (Fin.last k)) v
  have hf0 : Measurable f0 := measurable_of_countable _
  calc ∫⁻ ω, A.indicator 1 (U ω) * ∏ j, ENNReal.ofReal (h (v j) (lpath n (X₀ ω) (R ω) j)) ∂P
      = ∫⁻ ω, (fun p => A.indicator 1 p.1.1 * Φ p) (W ω, R ω) ∂P := rfl
    _ = ∫⁻ w, ∫⁻ r, A.indicator 1 w.1 * Φ (w, r) ∂(condDistrib R W P w) ∂(P.map W) :=
        Novel.D14SupportRobustness.disint hW hR hF
    _ = ∫⁻ w, A.indicator 1 w.1 * ∫⁻ r, Φ (w, r) ∂(condDistrib R W P w) ∂(P.map W) :=
        lintegral_congr fun w => lintegral_const_mul _ (hΦ.comp measurable_prodMk_left)
    _ ≤ ∫⁻ w, f0 w.1 ∂(P.map W) := lintegral_mono_ae (by
        filter_upwards [hin] with w hw; exact mul_le_mul_right hw _)
    _ = ∫⁻ ω, f0 (U ω) ∂P := lintegral_map (hf0.comp measurable_fst) hW
    _ = ∫⁻ u, f0 u ∂(P.map U) := (lintegral_map hf0 hU).symm
    _ = ∫⁻ u in A, Dn δ a M ℓ Δ Γ (u (Fin.last k)) v ∂(P.map U) := by
        rw [← lintegral_indicator hA]
        refine lintegral_congr fun u => ?_
        by_cases hu : u ∈ A <;> simp [f0, hu]

end Dom

/-! ## The two modes -/

instance (a : ℝ) : IsFiniteMeasure (noiseLaw a) := by unfold noiseLaw; infer_instance

theorem support_holds : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k n : ℕ) (δ a : ℝ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (U : Ω → Fin (k + 1) → ℕ)
    (Θ : Ω → ℝ × ℝ) (X₀ Y₀ : Ω → ℝ) (R Y : Ω → Fin n → ℝ)
    (q : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ) (Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ),
    0 < δ → 0 ≤ a → (∀ j, 0 < Δ j) → Γ.Nonempty → (∀ θ ∈ Γ, 0 < θ.2) →
    Measurable U → Measurable Θ → Measurable X₀ → Measurable R → Measurable Y →
    (∀ u v, 0 ≤ q u v) → (∀ u, ∑' v, ENNReal.ofReal (q u v) = 1) →
    latent P δ a Δ Γ U Θ X₀ Y₀ R →
    (∀ᵐ ω ∂P, ∀ j, 0 ≤ Y ω j ∧ |Y ω j - lpath n (X₀ ω) (R ω) j| ≤ a) →
    conclusions P U (fun ω j => mlabel δ (Y ω j)) q Lv
      (fun ℓ u v => Dn δ a Msupp ℓ Δ Γ (u (Fin.last k)) v) := by
  intro Ω _ P _ k n δ a Δ Γ U Θ X₀ Y₀ R Y q Lv hδ ha hΔ hΓ hΓκ hU hΘ hX hR hY _ hq1 hlat hYb
  set V : Ω → Fin n → ℕ := fun ω j => mlabel δ (Y ω j)
  have hV : Measurable V :=
    measurable_pi_iff.2 fun j => (measurable_mlabel δ).comp ((measurable_pi_apply j).comp hY)
  set h : ℕ → ℝ → ℝ := fun z y => (ecell δ a z).indicator 1 y
  have hM : ∀ ℓ z d, d < 2 ^ ℓ → 0 < Msupp ℓ z d := fun _ _ _ _ => one_pos
  refine conclusions_of_dom hU hV hq1 (fun ℓ u v => Dn_bounds hδ ha hΔ hΓ hΓκ hM ℓ _ v) ?_
  refine dom_core (h := h) hδ ha hΔ hΓκ hU hΘ hX hR hV
    (fun z => measurable_one.indicator measurableSet_Ico)
    (fun z y => by by_cases hy : y ∈ ecell δ a z <;> simp [h, hy])
    (fun z y _ hy => indicator_of_notMem hy _) hM
    (fun ℓ z d _ y _ => by by_cases hy : y ∈ ecell δ a z <;> simp [h, Msupp, hy]) hlat
    fun v A hA => ?_
  have hS : MeasurableSet (U ⁻¹' A ∩ V ⁻¹' {v}) := hU hA |>.inter (hV (measurableSet_singleton v))
  rw [← lintegral_indicator_one hS]
  refine lintegral_mono_ae ?_
  filter_upwards [hYb, hlat.1] with ω hω hl
  by_cases hin : ω ∈ U ⁻¹' A ∩ V ⁻¹' {v}
  · rw [indicator_of_mem hin, indicator_of_mem (show U ω ∈ A from hin.1), Pi.one_apply, Pi.one_apply,
      one_mul]
    refine le_of_eq (Finset.prod_eq_one fun j _ => ?_).symm
    have hvj : mlabel δ (Y ω j) = v j := congrFun hin.2 j
    have hx : lpath n (X₀ ω) (R ω) j ∈ ecell δ a (v j) := by
      rw [← hvj]
      exact expanded_holds hδ (lpath_nonneg n _ hl.2.1 j) (hω j).1 (hω j).2
    simp [h, hx]
  · rw [indicator_of_notMem hin]; exact bot_le

theorem uniform_holds : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k n : ℕ) (δ a : ℝ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (U : Ω → Fin (k + 1) → ℕ)
    (Θ : Ω → ℝ × ℝ) (X₀ Y₀ : Ω → ℝ) (R ε : Ω → Fin n → ℝ)
    (q : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ) (Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ),
    0 < δ → 0 < a → (∀ j, 0 < Δ j) → Γ.Nonempty → (∀ θ ∈ Γ, 0 < θ.2) →
    Measurable U → Measurable Θ → Measurable X₀ → Measurable R → Measurable ε →
    (∀ u v, 0 ≤ q u v) → (∀ u, ∑' v, ENNReal.ofReal (q u v) = 1) →
    latent P δ a Δ Γ U Θ X₀ Y₀ R →
    (∀ᵐ w ∂(P.map fun ω => (U ω, Θ ω, X₀ ω, lpath n (X₀ ω) (R ω))),
      condDistrib ε (fun ω => (U ω, Θ ω, X₀ ω, lpath n (X₀ ω) (R ω))) P w =
        Measure.pi fun _ => noiseLaw a) →
    conclusions P U (fun ω j => mlabel δ (max 0 (lpath n (X₀ ω) (R ω) j + ε ω j))) q Lv
      (fun ℓ u v => Dn δ a (Mnoise δ a) ℓ Δ Γ (u (Fin.last k)) v) := by
  intro Ω _ P _ k n δ a Δ Γ U Θ X₀ Y₀ R ε q Lv hδ ha hΔ hΓ hΓκ hU hΘ hX hR hε _ hq1 hlat hnoise
  have hXf : Measurable fun ω => lpath n (X₀ ω) (R ω) := (measurable_lpath n).comp (hX.prodMk hR)
  set lab : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℕ :=
    fun p j => mlabel δ (max 0 (p.1 j + p.2 j)) with hlab
  have hlabm : Measurable lab := measurable_pi_iff.2 fun j => (measurable_mlabel δ).comp
    (measurable_const.max (((measurable_pi_apply j).comp measurable_fst).add
      ((measurable_pi_apply j).comp measurable_snd)))
  set V : Ω → Fin n → ℕ := fun ω j => mlabel δ (max 0 (lpath n (X₀ ω) (R ω) j + ε ω j))
  have hV : Measurable V := hlabm.comp (hXf.prodMk hε)
  have hM : ∀ ℓ z d, d < 2 ^ ℓ → 0 < Mnoise δ a ℓ z d := fun ℓ z d hd => Mnoise_pos hδ ha.le hd
  refine conclusions_of_dom hU hV hq1 (fun ℓ u v => Dn_bounds hδ ha.le hΔ hΓ hΓκ hM ℓ _ v) ?_
  refine dom_core (h := gnoise δ a) hδ ha.le hΔ hΓκ hU hΘ hX hR hV
    (fun z => (continuous_gnoise ha.ne' z).measurable) (fun z y => (gnoise_bounds ha.le z y).2)
    (fun z y hy hyo => gnoise_out hδ ha.le hy hyo) hM
    (fun ℓ z d _ y hy => g_le_Mnoise ha.le hy) hlat fun v A hA => le_of_eq ?_
  set W := fun ω => (U ω, Θ ω, X₀ ω, lpath n (X₀ ω) (R ω))
  have hW : Measurable W := hU.prodMk (hΘ.prodMk (hX.prodMk hXf))
  set T : Set (((Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ × (Fin n → ℝ)) × (Fin n → ℝ)) :=
    {p | lab (p.1.2.2.2, p.2) = v}
  have hT : MeasurableSet T :=
    measurableSet_eq_fun (hlabm.comp ((measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp measurable_fst))).prodMk measurable_snd)) measurable_const
  have hF : Measurable fun p : ((Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (A.indicator 1 p.1.1 * T.indicator 1 p : ℝ≥0∞) :=
    ((measurable_one.indicator hA).comp (measurable_fst.comp measurable_fst)).mul
      (measurable_one.indicator hT)
  have hS : MeasurableSet (U ⁻¹' A ∩ V ⁻¹' {v}) := hU hA |>.inter (hV (measurableSet_singleton v))
  have hpt : ∀ ω, ((U ⁻¹' A ∩ V ⁻¹' {v}).indicator 1 ω : ℝ≥0∞) =
      A.indicator 1 (W ω).1 * T.indicator 1 (W ω, ε ω) := fun ω => by
    by_cases h1 : U ω ∈ A <;> by_cases h2 : V ω = v <;>
      simp [T, W, V, hlab, h1, h2]
  have hgm : Measurable fun x : Fin n → ℝ => ∏ j, ENNReal.ofReal (gnoise δ a (v j) (x j)) :=
    Finset.measurable_prod _ fun j _ => ENNReal.measurable_ofReal.comp
      ((continuous_gnoise ha.ne' (v j)).measurable.comp (measurable_pi_apply j))
  have hin : ∀ᵐ w ∂(P.map W), ∫⁻ e, A.indicator 1 w.1 * T.indicator 1 (w, e)
      ∂(condDistrib ε W P w) = A.indicator 1 w.1 *
        ∏ j, ENNReal.ofReal (gnoise δ a (v j) (w.2.2.2 j)) := by
    filter_upwards [hnoise] with w hw
    have hTm : Measurable fun e : Fin n → ℝ => (T.indicator 1 (w, e) : ℝ≥0∞) :=
      (measurable_one.indicator hT).comp measurable_prodMk_left
    rw [lintegral_const_mul _ hTm, hw]
    congr 1
    have hset : Prod.mk w ⁻¹' T = Set.pi univ fun j => {t | mlabel δ (max 0 (w.2.2.2 j + t)) = v j} := by
      ext e; simp [T, hlab, funext_iff]
    rw [show (fun e => T.indicator 1 (w, e)) = (Prod.mk w ⁻¹' T).indicator 1 from rfl,
      lintegral_indicator_one (measurable_prodMk_left hT), hset, Measure.pi_pi]
    exact Finset.prod_congr rfl fun j _ => emission_holds hδ ha _ _
  rw [← lintegral_indicator_one hS]
  calc ∫⁻ ω, (U ⁻¹' A ∩ V ⁻¹' {v}).indicator 1 ω ∂P
      = ∫⁻ ω, (fun p => (A.indicator 1 p.1.1 * T.indicator 1 p : ℝ≥0∞)) (W ω, ε ω) ∂P :=
        lintegral_congr hpt
    _ = ∫⁻ w, ∫⁻ e, A.indicator 1 w.1 * T.indicator 1 (w, e) ∂(condDistrib ε W P w)
          ∂(P.map W) := Novel.D14SupportRobustness.disint hW hε hF
    _ = ∫⁻ w, A.indicator 1 w.1 * ∏ j, ENNReal.ofReal (gnoise δ a (v j) (w.2.2.2 j))
          ∂(P.map W) := lintegral_congr_ae hin
    _ = _ := lintegral_map (((measurable_one.indicator hA).comp measurable_fst).mul
          (hgm.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))) hW

end Novel.D18BoundedNoise
