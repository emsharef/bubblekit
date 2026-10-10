import Standalone.D14RoundedStart
import Novel.D14RoundedStartCellsProof
import Novel.D14VolPathsAvgProof

/-!
# Claim 028 (D14): proof

Proves `Standalone.D14RoundedStart.statement` (`statement_holds`). The deterministic parts are
`Novel/D14RoundedStartCellsProof.lean`.
* **The mixture** (`mix`). Given `(U, X)` the returns have the fixed law `lawR`, so the joint law of
  `((U, X), R)` is a product (`compProd_map_condDistrib`, `compProd_const`). Integrating over the
  conditional law `ν(u, ·)` of `X` given `U`, the conditional law of `V = labF h X R` given `U` is
  the `ν(u, ·)` mixture of the restarted laws `gres x`. The identity is checked on rectangles
  (`Measure.ext_prod`) and identified by `condDistrib_ae_eq_of_measure_eq_compProd_of_measurable`.
* **The budget** (`budget_holds`). Almost surely, `ν(u, ·)` lives on the last training cell
  (`Measure.ae_ae_of_ae_compProd`), where `|log(x/x_h)| ≤ h/2`. Each restarted law `gres x` is
  within the `shift` bound of `gres x_h`, which is at most (2)'s bound there. Averaging over
  `ν(u, ·)` keeps the bound, whatever `ν` is.
* **Part 2** (`consequences_holds`). Claim 027's latent-mixture theorem with a one-point latent
  space: the actual conditional law, replaced by the reference on a null set of training values,
  is within the constant budget `ε^round` of the reference `gres x_h`, and the score has reference
  moment `≤ 1` (`cells`).
* **The panel** is claim 026's.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14RoundedStart

open Standalone.RoundedCells Standalone.D14Misspecification Standalone.D14RoundedStart
  Novel.D14RoundedStartCells

/-! ## The latent-endpoint mixture -/

section Mix

variable {Ω 𝒰 𝒳 𝓡 𝒱 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝓡] [MeasurableSpace 𝒱]

/-- The kernel `x ↦ L ∘ F(x, ·)⁻¹`. -/
noncomputable def Lk {F : 𝒳 × 𝓡 → 𝒱} (hF : Measurable F) (L : Measure 𝓡) [IsProbabilityMeasure L] :
    Kernel 𝒳 𝒱 where
  toFun x := L.map fun r => F (x, r)
  measurable' := Measure.measurable_of_measurable_coe _ fun A hA => by
    have : (fun x => (L.map fun r => F (x, r)) A) = fun x => L (Prod.mk x ⁻¹' (F ⁻¹' A)) := by
      funext x
      rw [Measure.map_apply (f := fun r => F (x, r)) (hF.comp measurable_prodMk_left) hA]
      rfl
    rw [this]
    exact measurable_measure_prodMk_left (hF hA)

theorem Lk_apply {F : 𝒳 × 𝓡 → 𝒱} (hF : Measurable F) (L : Measure 𝓡) [IsProbabilityMeasure L]
    (x : 𝒳) : Lk hF L x = L.map fun r => F (x, r) := rfl

instance {F : 𝒳 × 𝓡 → 𝒱} (hF : Measurable F) (L : Measure 𝓡) [IsProbabilityMeasure L] :
    IsMarkovKernel (Lk hF L) :=
  ⟨fun _ => (Measure.isProbabilityMeasure_map_iff
    (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable).2 inferInstance⟩

/-- The conditional law of `F(X, R)` given `U` is the mixture of `Lk` over the law of `X` given
`U`, when `R` has the fixed conditional law `L` given `(U, X)`. -/
theorem mix [StandardBorelSpace 𝒳] [Nonempty 𝒳] [StandardBorelSpace 𝓡] [Nonempty 𝓡]
    [StandardBorelSpace 𝒱] [Nonempty 𝒱] {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → 𝒰} {X : Ω → 𝒳} {R : Ω → 𝓡}
    {L : Measure 𝓡} [IsProbabilityMeasure L] {F : 𝒳 × 𝓡 → 𝒱} (hU : Measurable U)
    (hX : Measurable X) (hR : Measurable R) (hF : Measurable F)
    (hRc : ∀ᵐ w ∂(P.map fun ω => (U ω, X ω)), condDistrib R (fun ω => (U ω, X ω)) P w = L) :
    condDistrib (fun ω => F (X ω, R ω)) U P =ᵐ[P.map U] Lk hF L ∘ₖ condDistrib X U P := by
  have hW : Measurable fun ω => (U ω, X ω) := hU.prodMk hX
  have hV : Measurable fun ω => F (X ω, R ω) := hF.comp (hX.prodMk hR)
  refine condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hU hV ?_
  refine Measure.ext_prod fun {s t} hs ht => ?_
  -- The joint law of `((U, X), R)` is the product.
  have hjoint : P.map (fun ω => ((U ω, X ω), R ω)) = (P.map fun ω => (U ω, X ω)).prod L := by
    rw [← compProd_map_condDistrib hW.aemeasurable hR.aemeasurable,
      Measure.compProd_congr (κ := condDistrib R (fun ω => (U ω, X ω)) P) (η := Kernel.const _ L)
        (by filter_upwards [hRc] with w hw; rw [hw, Kernel.const_apply]),
      Measure.compProd_const]
  have hWmap : P.map (fun ω => (U ω, X ω)) = P.map U ⊗ₘ condDistrib X U P :=
    (compProd_map_condDistrib hU.aemeasurable hX.aemeasurable).symm
  set S : Set ((𝒰 × 𝒳) × 𝓡) := {p | p.1.1 ∈ s ∧ F (p.1.2, p.2) ∈ t}
  have hS : MeasurableSet S :=
    (measurable_fst.comp measurable_fst hs).inter
      (hF.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd) ht)
  have hg : Measurable fun w : 𝒰 × 𝒳 => s.indicator (fun _ => (1 : ℝ≥0∞)) w.1 * Lk hF L w.2 t :=
    ((measurable_const.indicator hs).comp measurable_fst).mul
      ((Lk hF L).measurable_coe ht |>.comp measurable_snd)
  have hsec : ∀ w : 𝒰 × 𝒳, L (Prod.mk w ⁻¹' S) =
      s.indicator (fun _ => (1 : ℝ≥0∞)) w.1 * Lk hF L w.2 t := by
    intro w
    rw [Lk_apply, Measure.map_apply (f := fun r => F (w.2, r)) (hF.comp measurable_prodMk_left) ht]
    by_cases hw : w.1 ∈ s
    · rw [indicator_of_mem hw, one_mul]
      congr 1
      ext r
      simp [S, hw]
    · rw [indicator_of_notMem hw, zero_mul]
      convert measure_empty (μ := L)
      ext r
      simp [S, hw]
  calc P.map (fun ω => (U ω, F (X ω, R ω))) (s ×ˢ t)
      = P.map (fun ω => ((U ω, X ω), R ω)) S := by
        rw [Measure.map_apply (hU.prodMk hV) (hs.prod ht),
          Measure.map_apply (hW.prodMk hR) hS]
        rfl
    _ = ∫⁻ w, L (Prod.mk w ⁻¹' S) ∂(P.map fun ω => (U ω, X ω)) := by
        rw [hjoint, Measure.prod_apply hS]
    _ = ∫⁻ u, ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) u * Lk hF L x t ∂(condDistrib X U P u)
          ∂(P.map U) := by
        simp_rw [hsec]
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


/-! ## (3) -/

theorem cell_log {h x : ℝ} (hh : 0 < h) (hx : 0 < x) {z : ℤ} (hq : Qh h x = rep h z) :
    |Real.log (x / rep h z)| ≤ h / 2 := by
  have hl : lab h x = z := by
    have h1 : h * (lab h x : ℝ) = h * z := Real.exp_injective hq
    exact_mod_cast mul_left_cancel₀ hh.ne' h1
  obtain ⟨h1, h2⟩ := Int.floor_eq_iff.1 hl
  rw [rep, Real.log_div hx.ne' (Real.exp_pos _).ne', Real.log_exp, abs_le]
  constructor
  · have h3 : (z : ℝ) - 1 / 2 ≤ Real.log x / h := by linarith
    rw [le_div_iff₀ hh] at h3
    linarith
  · have h3 : Real.log x / h < (z : ℝ) + 1 / 2 := by linarith
    rw [div_lt_iff₀ hh] at h3
    linarith

theorem shift_le {h Δ0 κ a : ℝ} (hΔ : 0 < Δ0) (hκ : 0 < κ) (ha : |a| ≤ h / 2) :
    Real.sqrt (1 - Real.exp (-(a ^ 2 / (4 * κ ^ 2 * Δ0)))) ≤ εb h Δ0 κ := by
  refine Real.sqrt_le_sqrt (sub_le_sub_left (Real.exp_le_exp.2 (neg_le_neg ?_)) 1)
  have ha2 : a ^ 2 ≤ (h / 2) ^ 2 := sq_le_sq' (abs_le.1 ha).1 (abs_le.1 ha).2
  have hd : 0 < 16 * κ ^ 2 * Δ0 := by positivity
  rw [div_le_div_iff₀ (by positivity) hd]
  have := mul_le_mul_of_nonneg_right ha2 hd.le
  nlinarith

theorem budget_holds : budget := by
  intro Ω 𝒰 _ _ P _ n Δ h b κ U X R z hΔ hκ hh hU hX hR hz hXc hRc
  have hF := labF_meas (n := n + 1) h
  have hmix := mix (F := fun p : ℝ × (Fin (n + 1) → ℝ) => labF h p.1 p.2) hU hX hR hF hRc
  have hW : Measurable fun ω => (U ω, X ω) := hU.prodMk hX
  set C : Set (𝒰 × ℝ) := {p | 0 < p.2 ∧ Qh h p.2 = rep h (z p.1)}
  have hC : MeasurableSet C := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_eq_fun ((Novel.RoundedCells.Qh_meas h).comp measurable_snd)
      ((measurable_from_top (f := rep h)).comp (hz.comp measurable_fst)))
  have hcell : ∀ᵐ u ∂(P.map U), ∀ᵐ x ∂(condDistrib X U P u), (u, x) ∈ C := by
    have h1 : ∀ᵐ w ∂(P.map fun ω => (U ω, X ω)), w ∈ C := (ae_map_iff hW.aemeasurable hC).2 hXc
    rw [← compProd_map_condDistrib hU.aemeasurable hX.aemeasurable] at h1
    exact Measure.ae_ae_of_ae_compProd h1
  filter_upwards [hmix, hcell] with u hu hcu A hA
  rw [hu]
  set ν := condDistrib X U P u
  set G := gres h Δ b κ (rep h (z u))
  have hm : Measurable fun x => (Lk hF (lawR Δ b κ)) x A := Kernel.measurable_coe _ hA
  have hreal : ((Lk hF (lawR Δ b κ) ∘ₖ condDistrib X U P) u).real A =
      ∫ x, (gres h Δ b κ x).real A ∂ν := by
    rw [measureReal_def, Kernel.comp_apply' _ _ _ hA,
      ← integral_toReal hm.aemeasurable (ae_of_all _ fun x => measure_lt_top _ _)]
    rfl
  have hint : Integrable (fun x => (gres h Δ b κ x).real A) ν :=
    Integrable.of_bound (C := 1) hm.ennreal_toReal.aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact Novel.RoundedCells.real_le_one _ _)
  have hsub : ∫ x, (gres h Δ b κ x).real A ∂ν - G.real A =
      ∫ x, ((gres h Δ b κ x).real A - G.real A) ∂ν := by
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [hreal, hsub]
  have hb := norm_integral_le_of_norm_le_const (μ := ν) (C := εb h (Δ 0) κ)
    (f := fun x => (gres h Δ b κ x).real A - G.real A) (by
      filter_upwards [hcu] with x hx
      obtain ⟨hx0, hq⟩ := hx
      rw [Real.norm_eq_abs]
      exact (shift_holds n Δ h b κ x (rep h (z u)) hΔ hκ hx0 (Real.exp_pos _) A hA).trans
        (shift_le (hΔ 0) hκ (cell_log hh hx0 hq)))
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at hb
  exact hb


/-! ## Part 2 -/

theorem Dres_meas (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty) (h : ℝ) {n : ℕ} (Δ : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℤ) : Measurable fun x => Dres Γ hΓ h Δ x v := by
  have := Finset.measurable_sup' hΓ (f := fun θ x => gR h Δ θ.1 θ.2 x v)
    fun θ _ => gR_meas h Δ θ.1 θ.2 v
  convert this using 1
  funext x
  simp [Dres, Finset.sup'_apply]

theorem cap_cond {E c e α : ℝ} (hc : 0 < c) (he : 0 ≤ e) (hα : 0 < α)
    (h : 1 / α < min E c / (1 + c * e)) : e < α ∧ 1 / (α - e) < c := by
  have hd : 0 < 1 + c * e := by positivity
  have h1 : 1 / α < c / (1 + c * e) := h.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) hd.le)
  rw [div_lt_div_iff₀ hα hd] at h1
  have h2 : 1 < c * (α - e) := by nlinarith
  have h3 : 0 < α - e := by
    by_contra h4; nlinarith [not_lt.1 h4]
  exact ⟨by linarith, by rw [div_lt_iff₀ h3]; linarith⟩

theorem consequences_holds : consequences := by
  intro Ω 𝒰 _ _ P _ n Δ h b κ U X R z Γ hΓ q hΔ hh hbκ hΓκ hU hX hR hz hq hq0 hq1 hXc hRc V E e
  have hκ : 0 < κ := hΓκ _ hbκ
  obtain ⟨hκm0, hκm⟩ := κmin_facts Γ hΓ hΓκ
  have he0 : 0 ≤ e := εb_nonneg _ _ _
  have he1 : e ≤ 1 := εb_le_one _ _ _
  have hbud := budget_holds P n Δ h b κ U X R z hΔ hκ hh hU hX hR hz hXc hRc
  have hle : εb h (Δ 0) κ ≤ e := εb_anti (hΔ 0) hκm0 (hκm _ hbκ)
  have hF := labF_meas (n := n + 1) h
  have hV : Measurable V := hF.comp (hX.prodMk hR)
  have hrep : Measurable fun u => rep h (z u) := (measurable_from_top (f := rep h)).comp hz
  -- The reference kernel `u ↦ g^restart(· | u)` at the true pair.
  let Gk : Kernel 𝒰 (Fin (n + 1) → ℤ) := (Lk hF (lawR Δ b κ)).comap (fun u => rep h (z u)) hrep
  have hGk : ∀ u, Gk u = gres h Δ b κ (rep h (z u)) := fun u => rfl
  -- The actual conditional law, replaced by the reference off a measurable full-measure set.
  obtain ⟨T, hTsub, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 hbud)
  classical
  let Hk : Kernel 𝒰 (Fin (n + 1) → ℤ) := Kernel.piecewise hTm.compl (condDistrib V U P) Gk
  have hgood : ∀ u A, MeasurableSet A → |(Hk u).real A - (Gk u).real A| ≤ e := by
    intro u A hA
    by_cases hu : u ∈ Tᶜ
    · have hp : ∀ A, MeasurableSet A → |(condDistrib V U P u).real A -
          (gres h Δ b κ (rep h (z u))).real A| ≤ εb h (Δ 0) κ := by
        by_contra hc
        exact hu (hTsub hc)
      rw [Kernel.piecewise_apply, ite_eq_left hu, hGk]
      exact (hp A hA).trans hle
    · rw [Kernel.piecewise_apply, ite_eq_right hu, sub_self, abs_zero]
      exact he0
  have hmixU : ∀ᵐ u ∂(P.map U), condDistrib V U P u = Hk u := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hT0] with u hu
    rw [Kernel.piecewise_apply, ite_eq_left (show u ∈ Tᶜ from hu)]
  have hEm : Measurable (Function.uncurry E) := by
    refine measurable_from_prod_countable_left fun v => ?_
    exact (hq v).div ((Dres_meas Γ hΓ h Δ v).comp hrep)
  have hE0 : ∀ u v, 0 ≤ E u v := fun u v =>
    div_nonneg (hq0 u v) (Dres_pos hΔ hh (Real.exp_pos _) hΓ hΓκ v).le
  have hmom : ∀ u, ∫⁻ v, ENNReal.ofReal (E u v) ∂(Gk u) ≤ 1 := fun u =>
    (cells_holds.2.2 n Δ h (rep h (z u)) Γ hΓ (q u) hΔ hh (Real.exp_pos _) hΓκ (hq0 u)
      (hq1 u)).2 (b, κ) hbκ
  have hA := Novel.D14VolPathsAvg.averaging_holds.1 P U V
    (Kernel.const 𝒰 (Measure.dirac ())) (Hk.comap Prod.fst measurable_fst)
    (Gk.comap Prod.fst measurable_fst) E (fun _ => e) hU hV hEm hE0 measurable_const
    (fun _ => ⟨he0, he1⟩) (fun u _ => hmom u) (fun u _ A hA => hgood u A hA) (by
      filter_upwards [hmixU] with u hu
      rw [Kernel.const_apply, Measure.dirac_bind (measurable_from_top) ()]
      exact hu)
  simp only [Kernel.const_apply, integral_const, probReal_univ, one_smul] at hA
  obtain ⟨h5c, h5u, hshift, h6, -⟩ := hA
  refine ⟨hEm, hE0, h5c, h5u, fun α hα => hshift α e he0 (fun _ => le_rfl) hα, fun c hc => ?_⟩
  obtain ⟨h6c, h6u⟩ := h6 c (fun _ => e) hc measurable_const fun _ => le_rfl
  refine ⟨h6c, h6u, fun F _ hF' => (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hF' ω).2).trans h6u,
    fun α hα u v hr => cap_cond hc he0 hα hr⟩

theorem statement_holds : Standalone.D14RoundedStart.statement :=
  ⟨cells_holds, shift_holds, budget_holds, consequences_holds, Novel.D14JumpRobustness.panel_holds,
    tolerance_holds⟩

end Novel.D14RoundedStart
