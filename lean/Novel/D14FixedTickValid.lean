import Novel.D14FixedTickSub
import Novel.D14RoundedStartProof
import Novel.D14CellProof

/-!
# Claim 031: validity under the trapped Gaussian contract

* **The mixture** (`mix0`). This adapts claim 028's `mix` to the trapped zero state.
  - From a positive endpoint, the returns have the Gaussian law `L` given `(U, X)`.
  - From the endpoint `0`, the exact path is identically zero whatever the returns are, so the
    label law is the point mass at the zero path for every law of the returns.
  - Hence, given `U`, the labels are the mixture of the walk laws over the conditional law of `X`.
    Nothing is assumed about the returns at a zero endpoint.
* **Validity** (`validity_holds`).
  - The conditional law of `X` lives on the last training cell (`Measure.ae_ae_of_ae_compProd`).
  - So at every level, the label law is at most `B^(δ,ℓ)` (`walk_le_Bl`), which is at most `D^(δ,ℓ)`.
  - AX-58's pointwise step with counting measure, disintegration and Markov finish, as in claim 029.
    The level may depend on the data, since the domination holds at every level.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14FixedTick

open Standalone.D14FixedTick Standalone.D14Cell Novel.D14RoundedStart

section Mix

variable {Ω 𝒰 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰]

/-- The conditional label law given `U` is the walk-law mixture over the conditional law of the
exact endpoint, with the returns' law assumed only at positive endpoints. -/
theorem mix0 {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → 𝒰} {X : Ω → ℝ} {n : ℕ}
    {R : Ω → Fin n → ℝ} (δ : ℝ) (L : Measure (Fin n → ℝ)) [IsProbabilityMeasure L]
    (hU : Measurable U) (hX : Measurable X) (hR : Measurable R) (hX0 : ∀ᵐ ω ∂P, 0 ≤ X ω)
    (hRc : ∀ᵐ w ∂(P.map fun ω => (U ω, X ω)), 0 < w.2 →
      condDistrib R (fun ω => (U ω, X ω)) P w = L) :
    condDistrib (fun ω => mlabels δ n (X ω) (R ω)) U P =ᵐ[P.map U]
      Lk (measurable_mlabels δ n) L ∘ₖ condDistrib X U P := by
  have hF := measurable_mlabels δ n
  have hW : Measurable fun ω => (U ω, X ω) := hU.prodMk hX
  have hV : Measurable fun ω => mlabels δ n (X ω) (R ω) := hF.comp (hX.prodMk hR)
  refine condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hU hV ?_
  refine Measure.ext_prod fun {s t} hs ht => ?_
  have hjoint : P.map (fun ω => ((U ω, X ω), R ω)) =
      (P.map fun ω => (U ω, X ω)) ⊗ₘ condDistrib R (fun ω => (U ω, X ω)) P :=
    (compProd_map_condDistrib hW.aemeasurable hR.aemeasurable).symm
  have hWmap : P.map (fun ω => (U ω, X ω)) = P.map U ⊗ₘ condDistrib X U P :=
    (compProd_map_condDistrib hU.aemeasurable hX.aemeasurable).symm
  set S : Set ((𝒰 × ℝ) × (Fin n → ℝ)) := {p | p.1.1 ∈ s ∧ mlabels δ n p.1.2 p.2 ∈ t}
  have hS : MeasurableSet S :=
    (measurable_fst.comp measurable_fst hs).inter
      (hF.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd) ht)
  have hg : Measurable fun w : 𝒰 × ℝ => s.indicator (fun _ => (1 : ℝ≥0∞)) w.1 *
      Lk hF L w.2 t :=
    ((measurable_const.indicator hs).comp measurable_fst).mul
      ((Lk hF L).measurable_coe ht |>.comp measurable_snd)
  have hnn : ∀ᵐ w ∂(P.map fun ω => (U ω, X ω)), 0 ≤ w.2 :=
    (ae_map_iff hW.aemeasurable (measurableSet_le measurable_const measurable_snd)).2 hX0
  have hsec : ∀ᵐ w ∂(P.map fun ω => (U ω, X ω)),
      condDistrib R (fun ω => (U ω, X ω)) P w (Prod.mk w ⁻¹' S) =
        s.indicator (fun _ => (1 : ℝ≥0∞)) w.1 * Lk hF L w.2 t := by
    filter_upwards [hRc, hnn] with w hw hw0
    by_cases hws : w.1 ∈ s
    · rw [indicator_of_mem hws, one_mul, Lk_apply,
        Measure.map_apply (f := fun r => mlabels δ n w.2 r) (hF.comp measurable_prodMk_left) ht]
      have hset : Prod.mk w ⁻¹' S = (fun r => mlabels δ n w.2 r) ⁻¹' t := by
        ext r; simp [S, hws]
      rw [hset]
      rcases hw0.lt_or_eq with hpos | hzero
      · rw [hw hpos]
      · -- The trapped state: the label path is zero whatever the returns are.
        have hc : ∀ r, mlabels δ n w.2 r = fun _ => 0 := fun r => by rw [← hzero, mlabels_zero]
        by_cases h0 : (fun _ => 0 : Fin n → ℕ) ∈ t
        · have : (fun r => mlabels δ n w.2 r) ⁻¹' t = univ := by ext r; simp [hc r, h0]
          rw [this, measure_univ, measure_univ]
        · have : (fun r => mlabels δ n w.2 r) ⁻¹' t = ∅ := by ext r; simp [hc r, h0]
          rw [this, measure_empty, measure_empty]
    · rw [indicator_of_notMem hws, zero_mul]
      convert measure_empty (μ := condDistrib R (fun ω => (U ω, X ω)) P w)
      ext r
      simp [S, hws]
  calc P.map (fun ω => (U ω, mlabels δ n (X ω) (R ω))) (s ×ˢ t)
      = P.map (fun ω => ((U ω, X ω), R ω)) S := by
        rw [Measure.map_apply (hU.prodMk hV) (hs.prod ht),
          Measure.map_apply (hW.prodMk hR) hS]
        rfl
    _ = ∫⁻ w, condDistrib R (fun ω => (U ω, X ω)) P w (Prod.mk w ⁻¹' S)
          ∂(P.map fun ω => (U ω, X ω)) := by
        rw [hjoint, Measure.compProd_apply hS]
    _ = ∫⁻ w, s.indicator (fun _ => (1 : ℝ≥0∞)) w.1 * Lk hF L w.2 t
          ∂(P.map fun ω => (U ω, X ω)) := lintegral_congr_ae hsec
    _ = ∫⁻ u, ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) u * Lk hF L x t ∂(condDistrib X U P u)
          ∂(P.map U) := by
        rw [hWmap, Measure.lintegral_compProd hg]
    _ = ∫⁻ u in s, (Lk hF L ∘ₖ condDistrib X U P) u t ∂(P.map U) := by
        rw [← lintegral_indicator hs]
        refine lintegral_congr fun u => ?_
        rw [lintegral_const_mul _ ((Lk hF L).measurable_coe ht)]
        by_cases hu : u ∈ s
        · rw [indicator_of_mem hu, indicator_of_mem hu, one_mul, Kernel.comp_apply' _ _ _ ht]
        · rw [indicator_of_notMem hu, indicator_of_notMem hu, zero_mul]
    _ = (P.map U ⊗ₘ (Lk hF L ∘ₖ condDistrib X U P)) (s ×ˢ t) :=
        (Measure.compProd_apply_prod hs ht).symm

end Mix

theorem measurable_mlo (δ : ℝ) : Measurable (mlo δ) := measurable_of_countable _
theorem measurable_mhi (δ : ℝ) : Measurable (mhi δ) := measurable_of_countable _

theorem validity_holds : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k n : ℕ) (δ : ℝ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (U : Ω → Fin (k + 1) → ℕ) (X : Ω → ℝ)
    (R : Ω → Fin n → ℝ) (q : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ)
    (Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ) (θ : ℝ × ℝ),
    0 < δ → (∀ j, 0 < Δ j) → (∀ θ' ∈ Γ, 0 < θ'.2) → θ ∈ Γ →
    Measurable U → Measurable X → Measurable R →
    (∀ u v, 0 ≤ q u v) → (∀ u, ∑' v, ENNReal.ofReal (q u v) = 1) →
    (∀ᵐ ω ∂P, X ω ∈ mcell δ (U ω (Fin.last k))) →
    (∀ᵐ w ∂(P.map fun ω => (U ω, X ω)), 0 < w.2 →
      condDistrib R (fun ω => (U ω, X ω)) P w =
        Measure.pi fun j => gaussianReal (muθ Δ θ j) (sθ Δ θ j ^ 2).toNNReal) →
    let V := fun ω => mlabels δ n (X ω) (R ω)
    let E := fun u v => ENNReal.ofReal (q u v) / Dm δ (Lv u v) Δ Γ (u (Fin.last k)) v
    (∀ (ℓ : ℕ) (u : Fin (k + 1) → ℕ) (v : Fin n → ℕ),
      0 < Dm δ ℓ Δ Γ (u (Fin.last k)) v ∧ Dm δ ℓ Δ Γ (u (Fin.last k)) v ≤ 1) ∧
    (∀ u v, E u v < ⊤) ∧
    (∀ᵐ u ∂(P.map U), ∀ v ℓ, condDistrib V U P u {v} ≤
      ENNReal.ofReal (Bl δ ℓ (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v) ∧
      ENNReal.ofReal (Bl δ ℓ (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v) ≤
        Dm δ ℓ Δ Γ (u (Fin.last k)) v) ∧
    (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
    ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
    (∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
    ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1 := by
  intro Ω _ P _ k n δ Δ Γ U X R q Lv θ hδ hΔ hΓ hθ hU hX hR hq0 hq1 hXc hRc V E
  have hsθ : ∀ θ' ∈ Γ, ∀ j, 0 < sθ Δ θ' j := fun θ' h' j => Novel.D14Cell.sθ_pos hΔ (hΓ θ' h') j
  have hF := measurable_mlabels δ n
  have hV : Measurable V := hF.comp (hX.prodMk hR)
  have hX0 : ∀ᵐ ω ∂P, 0 ≤ X ω := by
    filter_upwards [hXc] with ω hω using (mlo_nonneg δ _).trans hω.1
  have hmix := mix0 δ _ hU hX hR hX0 hRc
  have hW : Measurable fun ω => (U ω, X ω) := hU.prodMk hX
  set C : Set ((Fin (k + 1) → ℕ) × ℝ) := {p | p.2 ∈ mcell δ (p.1 (Fin.last k))}
  have hz : Measurable fun p : (Fin (k + 1) → ℕ) × ℝ => p.1 (Fin.last k) :=
    (measurable_pi_apply _).comp measurable_fst
  have hC : MeasurableSet C :=
    (measurableSet_le ((measurable_mlo δ).comp hz) measurable_snd).inter
      (measurableSet_lt measurable_snd ((measurable_mhi δ).comp hz))
  have hcell : ∀ᵐ u ∂(P.map U), ∀ᵐ x ∂(condDistrib X U P u), x ∈ mcell δ (u (Fin.last k)) := by
    have h1 : ∀ᵐ w ∂(P.map fun ω => (U ω, X ω)), w ∈ C := (ae_map_iff hW.aemeasurable hC).2 hXc
    rw [← compProd_map_condDistrib hU.aemeasurable hX.aemeasurable] at h1
    exact Measure.ae_ae_of_ae_compProd h1
  have hDpos : ∀ ℓ (u : Fin (k + 1) → ℕ) v, 0 < Dm δ ℓ Δ Γ (u (Fin.last k)) v := fun ℓ u v =>
    (ENNReal.ofReal_pos.2 (Bl_pos hδ ℓ (hsθ θ hθ) _ v)).trans_le (le_iSup₂_of_le θ hθ le_rfl)
  have hDle : ∀ ℓ (u : Fin (k + 1) → ℕ) v, Dm δ ℓ Δ Γ (u (Fin.last k)) v ≤ 1 := fun ℓ u v =>
    iSup₂_le fun θ' h' => ENNReal.ofReal_le_one.2 (Bl_le_one hδ ℓ (hsθ θ' h') _ v)
  have hDtop : ∀ ℓ (u : Fin (k + 1) → ℕ) v, Dm δ ℓ Δ Γ (u (Fin.last k)) v ≠ ⊤ := fun ℓ u v =>
    ((hDle ℓ u v).trans_lt ENNReal.one_lt_top).ne
  have hfin : ∀ u v, E u v < ⊤ := fun u v =>
    ENNReal.div_lt_top ENNReal.ofReal_ne_top (hDpos _ u v).ne'
  have hbound : ∀ᵐ u ∂(P.map U), ∀ v ℓ, condDistrib V U P u {v} ≤
      ENNReal.ofReal (Bl δ ℓ (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v) ∧
      ENNReal.ofReal (Bl δ ℓ (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v) ≤
        Dm δ ℓ Δ Γ (u (Fin.last k)) v := by
    filter_upwards [hmix, hcell] with u hu hcu
    intro v ℓ
    refine ⟨?_, le_iSup₂_of_le θ hθ le_rfl⟩
    have hu' : condDistrib V U P u = _ := hu
    rw [hu', Kernel.comp_apply, Measure.bind_apply (measurableSet_singleton v)
      (Kernel.aemeasurable _)]
    change ∫⁻ x, walkM δ (muθ Δ θ) (sθ Δ θ) x {v} ∂(condDistrib X U P u) ≤ _
    calc ∫⁻ x, walkM δ (muθ Δ θ) (sθ Δ θ) x {v} ∂(condDistrib X U P u)
        ≤ ∫⁻ _, ENNReal.ofReal (Bl δ ℓ (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v)
            ∂(condDistrib X U P u) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hcu] with x hx
          exact walk_le_Bl hδ ℓ (hsθ θ hθ) v hx
      _ = ENNReal.ofReal (Bl δ ℓ (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v) := by
          rw [lintegral_const, measure_univ, mul_one]
  have hcond : ∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1 := by
    filter_upwards [hbound] with u hu
    rw [lintegral_countable']
    calc ∑' v, E u v * condDistrib V U P u {v} ≤ ∑' v, ENNReal.ofReal (q u v) :=
          ENNReal.tsum_le_tsum fun v => by
            calc E u v * condDistrib V U P u {v} ≤ E u v * Dm δ (Lv u v) Δ Γ (u (Fin.last k)) v :=
                  mul_le_mul_right ((hu v (Lv u v)).1.trans (hu v (Lv u v)).2) _
              _ = ENNReal.ofReal (q u v) :=
                  ENNReal.div_mul_cancel (hDpos _ u v).ne' (hDtop _ u v)
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
  refine ⟨fun ℓ u v => ⟨hDpos ℓ u v, hDle ℓ u v⟩, hfin, hbound, hcond, huncond,
    fun α hα hα1 => ?_, fun F _ hF => (lintegral_mono hF).trans huncond⟩
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

end Novel.D14FixedTick
