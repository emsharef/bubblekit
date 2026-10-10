import Standalone.D13Declaration
import Novel.D14JumpRobustnessProof
import Novel.D13DriftRectProof

/-!
# Claim 058: proof

Proves parts 1–2, (3) and the concrete score of `Standalone.D13Declaration.statement`; the
assembly `statement_holds` is `Novel/D13DeclarationProof.lean`.
* **`mechanism`.** On a covered record `x = (w, u)`, AX-58's pointwise bound `g · E ≤ Ĝ`
  (`mul_Edrift_le`) under the actual conditional law `g(u, ·) μ` gives a conditional mean `≤ 1`.
  Disintegration over `(W, U)` (claim 026's `disint`) turns bounds on conditional means into
  bounds on unconditional ones: `1` on covered records, and `1` or `c` on the rest (Markov for
  the size).
* **`condFDR`.** AX-53 applied to `P(· | W ∈ S)`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal

namespace Novel.D13Declaration

open Standalone.D13DriftNull Standalone.D13DriftRect Standalone.CEVSupport
  Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated Standalone.D3CatalogueCalibration
  Standalone.D12CatalogueFDR Standalone.D14JumpRobustness Standalone.D14Misspecification
  Standalone.D13Declaration

/-! ## Parts 1–2 for one name -/

section Mechanism

variable {Ω 𝒲 𝒰 𝒱 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒲] [MeasurableSpace 𝒰]
  [MeasurableSpace 𝒱]

/-- Integrating conditional bounds over the earlier record and training block. -/
theorem cond_bound [StandardBorelSpace 𝒱] [Nonempty 𝒱] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → 𝒲 × 𝒰} {V : Ω → 𝒱} (hX : Measurable X) (hV : Measurable V)
    {F : (𝒲 × 𝒰) × 𝒱 → ℝ≥0∞} (hF : Measurable F) {bd : 𝒲 × 𝒰 → ℝ≥0∞}
    (h : ∀ᵐ x ∂(P.map X), ∫⁻ v, F (x, v) ∂(condDistrib V X P x) ≤ bd x) :
    ∫⁻ ω, F (X ω, V ω) ∂P ≤ ∫⁻ x, bd x ∂(P.map X) :=
  (Novel.D14JumpRobustness.disint hX hV hF).trans_le (lintegral_mono_ae h)

open Classical in
/-- The bound `a₁` on covered records and `a₂` elsewhere. -/
theorem split_lint {P : Measure Ω} {W : Ω → 𝒲} {U : Ω → 𝒰} (hW : Measurable W) (hU : Measurable U)
    {A : Set 𝒲} (hA : MeasurableSet A) (a1 a2 : ℝ≥0∞) :
    ∫⁻ x, (if x.1 ∈ A then a1 else a2) ∂(P.map fun ω => (W ω, U ω)) =
      a1 * P (W ⁻¹' A) + a2 * P (W ⁻¹' Aᶜ) := by
  classical
  have hX : Measurable fun ω => (W ω, U ω) := hW.prodMk hU
  have hs : MeasurableSet (Prod.fst ⁻¹' A : Set (𝒲 × 𝒰)) := measurable_fst hA
  have : (fun x : 𝒲 × 𝒰 => if x.1 ∈ A then a1 else a2) =
      fun x => (Prod.fst ⁻¹' A).indicator (fun _ => a1) x +
        (Prod.fst ⁻¹' A)ᶜ.indicator (fun _ => a2) x := by
    funext x; by_cases h : x.1 ∈ A <;> simp [h, indicator]
  rw [this, lintegral_add_left ((measurable_const.indicator hs)),
    lintegral_indicator_const hs, lintegral_indicator_const hs.compl,
    Measure.map_apply hX hs, Measure.map_apply hX hs.compl]
  rfl


theorem ejump_ofReal (c δ : ℝ) (e : ℝ≥0∞) :
    ENNReal.ofReal (Ejump c δ e) =
      min e (ENNReal.ofReal c) * ENNReal.ofReal (1 / (1 + (c - 1) * δ)) := by
  rw [Ejump, div_eq_mul_one_div, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _))]

theorem mechanism_holds : mechanism := by
  classical
  intro Ω 𝒲 𝒰 𝒱 _ _ _ _ _ _ P _ W U V μ Gh g D A hW hU hV hμ hGh hGh0 hGhn hg hD hA hdom hCD E
  set X : Ω → 𝒲 × 𝒰 := fun ω => (W ω, U ω) with hXdef
  have hX : Measurable X := hW.prodMk hU
  set F : (𝒲 × 𝒰) × 𝒱 → ℝ≥0∞ := fun p => Edrift (Gh p.1.2 p.2) (D p.1.1 p.1.2 p.2) with hFdef
  have hF : Measurable F := Novel.SplitLikelihoodDominated.Edrift_meas.comp
    ((hGh.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).prodMk
      (hD.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
  have hFx : ∀ x, Measurable fun v => F (x, v) := fun x => hF.comp measurable_prodMk_left
  have hE : Measurable E := hF.comp (hX.prodMk hV)
  -- The conditional mean on a covered record.
  have hcm : ∀ᵐ x ∂(P.map X), x.1 ∈ A → ∫⁻ v, F (x, v) ∂(condDistrib V X P x) ≤ 1 := by
    filter_upwards [hCD] with x hx hxA
    rw [hx, lintegral_withDensity_eq_lintegral_mul _ (f := fun v => ENNReal.ofReal (g x.2 v))
      (ENNReal.measurable_ofReal.comp (hg.comp measurable_prodMk_left)) (g := fun v => F (x, v))
      (hFx x), ← hGhn x.2]
    exact lintegral_mono fun v => Novel.SplitLikelihoodDominated.mul_Edrift_le (hdom x.1 hxA x.2 v)
  have hAc : W ⁻¹' Aᶜ = (W ⁻¹' A)ᶜ := preimage_compl
  have hsum : P (W ⁻¹' A) + P (W ⁻¹' Aᶜ) = 1 := by
    rw [hAc, measure_add_measure_compl (hW hA), measure_univ]
  -- Tower property on covered records.
  have htower : ∀ S, MeasurableSet S → S ⊆ A → ∫⁻ ω in W ⁻¹' S, E ω ∂P ≤ P (W ⁻¹' S) := by
    intro S hS hSA
    have hs : MeasurableSet (Prod.fst ⁻¹' S : Set (𝒲 × 𝒰)) := measurable_fst hS
    set F' : (𝒲 × 𝒰) × 𝒱 → ℝ≥0∞ := fun p => (Prod.fst ⁻¹' S).indicator 1 p.1 * F p
    have hF' : Measurable F' := ((measurable_one.indicator hs).comp measurable_fst).mul hF
    have h1 : ∫⁻ ω in W ⁻¹' S, E ω ∂P = ∫⁻ ω, F' (X ω, V ω) ∂P := by
      rw [← lintegral_indicator (hW hS)]
      refine lintegral_congr fun ω => ?_
      by_cases h : W ω ∈ S <;> simp [F', h, indicator, E, F, X]
    rw [h1]
    refine (cond_bound hX hV hF' (bd := (Prod.fst ⁻¹' S).indicator 1) ?_).trans_eq ?_
    · filter_upwards [hcm] with x hx
      simp only [F']
      rw [lintegral_const_mul _ (hFx x)]
      by_cases h : x.1 ∈ S
      · simp only [indicator, mem_preimage, h, ↓reduceIte, Pi.one_apply, one_mul]
        exact hx (hSA h)
      · simp [indicator, h]
    · rw [lintegral_indicator_one hs, Measure.map_apply hX hs]; rfl
  -- Conditional size on covered records.
  have hsizeC : ∀ α : ℝ, 0 < α → α < 1 → ∀ᵐ x ∂(P.map X), x.1 ∈ A →
      condDistrib V X P x {v | ENNReal.ofReal (1 / α) < F (x, v)} ≤ ENNReal.ofReal α :=
    fun α hα _ => by
      filter_upwards [hcm] with x hx hxA
      exact Novel.D14JumpRobustness.ref_markov (hFx x) (hx hxA) hα
  -- Size under a split bound.
  have hsize : ∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) < E ω} ≤
      ENNReal.ofReal α * P (W ⁻¹' A) + 1 * P (W ⁻¹' Aᶜ) := fun α hα hα1 => by
    have hT : MeasurableSet {p : (𝒲 × 𝒰) × 𝒱 | ENNReal.ofReal (1 / α) < F p} :=
      measurableSet_lt measurable_const hF
    have h1 : P {ω | ENNReal.ofReal (1 / α) < E ω} =
        ∫⁻ ω, {p : (𝒲 × 𝒰) × 𝒱 | ENNReal.ofReal (1 / α) < F p}.indicator 1 (X ω, V ω) ∂P := by
      have : {ω | ENNReal.ofReal (1 / α) < E ω} = (fun ω => (X ω, V ω)) ⁻¹'
          {p : (𝒲 × 𝒰) × 𝒱 | ENNReal.ofReal (1 / α) < F p} := rfl
      rw [this, ← lintegral_indicator_one ((hX.prodMk hV) hT)]
      rfl
    rw [h1, ← split_lint hW hU hA]
    refine cond_bound hX hV (measurable_one.indicator hT) ?_
    filter_upwards [hsizeC α hα hα1] with x hx
    show ∫⁻ v, (Prod.mk x ⁻¹' {p : (𝒲 × 𝒰) × 𝒱 | ENNReal.ofReal (1 / α) < F p}).indicator 1 v
      ∂(condDistrib V X P x) ≤ _
    rw [lintegral_indicator_one (measurable_prodMk_left hT)]
    split_ifs with h
    · exact hx h
    · exact prob_le_one
  refine ⟨hcm, htower, fun α hα hα1 => hsizeC α hα hα1, fun h0 => ?_, ?_⟩
  · rw [← lintegral_add_compl _ (hW hA), ← hAc, setLIntegral_measure_zero _ _ h0, add_zero]
    exact (htower A hA subset_rfl).trans prob_le_one
  intro δ hδ0 hδ1 hP
  have hq0 : 0 ≤ (P (W ⁻¹' Aᶜ)).toReal := ENNReal.toReal_nonneg
  have hqδ : (P (W ⁻¹' Aᶜ)).toReal ≤ δ := ENNReal.toReal_le_of_le_ofReal hδ0 hP
  have hpa : P (W ⁻¹' A) = ENNReal.ofReal (1 - (P (W ⁻¹' Aᶜ)).toReal) := by
    rw [← ENNReal.toReal_one, ← hsum, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      add_sub_cancel_right, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  set q := (P (W ⁻¹' Aᶜ)).toReal with hq
  have hpc : P (W ⁻¹' Aᶜ) = ENNReal.ofReal q := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hsize' : ∀ α : ℝ, 0 < α → α < 1 →
      P {ω | ENNReal.ofReal (1 / α) < E ω} ≤ ENNReal.ofReal (α + (1 - α) * δ) := fun α hα hα1 => by
    refine (hsize α hα hα1).trans ?_
    rw [hpa, hpc, one_mul, ← ENNReal.ofReal_mul hα.le, ← ENNReal.ofReal_add
      (mul_nonneg hα.le (by linarith)) hq0]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  refine ⟨hsize', fun α hδα hα1 => ?_, fun c hc => ⟨?_, fun Fr hFr hFb => ?_⟩⟩
  · set β := (α - δ) / (1 - δ) with hβ
    have hβ0 : 0 < β := div_pos (by linarith) (by linarith)
    have hβ1 : β < 1 := (div_lt_one (by linarith)).2 (by linarith)
    have h1β : (1 - δ) / (α - δ) = 1 / β := by rw [hβ, one_div_div]
    rw [h1β]
    refine (hsize' β hβ0 hβ1).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    have hb : β * (1 - δ) = α - δ := div_mul_cancel₀ _ (by linarith)
    linear_combination hb
  · exact (ENNReal.measurable_toReal.comp (hE.min measurable_const)).div_const _
  · have hD1 : 1 ≤ 1 + (c - 1) * δ := by nlinarith
    set k := ENNReal.ofReal (1 / (1 + (c - 1) * δ))
    set Fs : (𝒲 × 𝒰) × 𝒱 → ℝ≥0∞ := fun p => min (F p) (ENNReal.ofReal c) * k
    have hFs : Measurable Fs := (hF.min measurable_const).mul_const _
    calc ∫⁻ ω, ENNReal.ofReal (Fr ω) ∂P
        ≤ ∫⁻ ω, Fs (X ω, V ω) ∂P := lintegral_mono fun ω => by
          rw [show Fs (X ω, V ω) = ENNReal.ofReal (Ejump c δ (E ω)) from (ejump_ofReal c δ _).symm]
          exact ENNReal.ofReal_le_ofReal (hFb ω).2
      _ ≤ ∫⁻ x, (if x.1 ∈ A then 1 * k else ENNReal.ofReal c * k) ∂(P.map X) := by
          refine cond_bound hX hV hFs ?_
          filter_upwards [hcm] with x hx
          simp only [Fs]
          rw [lintegral_mul_const _ ((hFx x).min measurable_const)]
          split_ifs with h
          · exact mul_le_mul_left ((lintegral_mono fun v => min_le_left _ _).trans (hx h)) _
          · refine mul_le_mul_left ((lintegral_mono fun v => min_le_right _ _).trans_eq ?_) _
            rw [lintegral_const, measure_univ, mul_one]
      _ = 1 * k * P (W ⁻¹' A) + ENNReal.ofReal c * k * P (W ⁻¹' Aᶜ) := split_lint hW hU hA _ _
      _ ≤ 1 := by
          have hk : 1 * k * ENNReal.ofReal (1 - q) + ENNReal.ofReal c * k * ENNReal.ofReal q =
              ENNReal.ofReal ((1 - q + c * q) * (1 / (1 + (c - 1) * δ))) := by
            have hD0 : 0 ≤ 1 / (1 + (c - 1) * δ) := by positivity
            have e1 : k * ENNReal.ofReal (1 - q) =
                ENNReal.ofReal (1 / (1 + (c - 1) * δ) * (1 - q)) :=
              (ENNReal.ofReal_mul hD0).symm
            have e2 : ENNReal.ofReal c * k * ENNReal.ofReal q =
                ENNReal.ofReal (c * (1 / (1 + (c - 1) * δ)) * q) := by
              rw [ENNReal.ofReal_mul (mul_nonneg (by linarith) hD0), ENNReal.ofReal_mul (by linarith)]
            rw [one_mul, e1, e2, ← ENNReal.ofReal_add (mul_nonneg hD0 (by linarith))
              (mul_nonneg (mul_nonneg (by linarith) hD0) hq0)]
            congr 1; ring
          rw [hpa, hpc, hk, ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← div_eq_mul_one_div, div_le_one (by linarith)]
          nlinarith

end Mechanism


/-! ## (3): conditional FDR given the earlier record -/

theorem condFDR_holds : condFDR := by
  classical
  intro h53 ι _ _ Ω 𝒲 _ _ P _ W Er N₀ q hq hq1 hW hEr hnn hmom S hS
  set T := W ⁻¹' S with hTdef
  have hT : MeasurableSet T := hW hS
  have key : ∀ E' : ι → Ω → ℝ, (∀ i, Measurable (E' i)) → (∀ i ω, 0 ≤ E' i ω) →
      (∀ i ω, E' i ω ≤ Er i ω) →
      (∫ ω in T, fdp q (fun i => E' i ω) N₀ ∂P) ≤ q * N₀.card / Fintype.card ι * P.real T := by
    intro E' hm hnn' hle
    by_cases h0 : P T = 0
    · rw [Measure.restrict_eq_zero.2 h0, integral_zero_measure, measureReal_def, h0,
        ENNReal.toReal_zero, mul_zero]
    set PS : Measure Ω := (P T)⁻¹ • P.restrict T
    have hPS : IsProbabilityMeasure PS := ⟨by
      rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
        ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)]⟩
    have hnull : ∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (E' i ω) ∂PS ≤ 1 := fun i hi => by
      rw [lintegral_smul_measure, smul_eq_mul]
      calc (P T)⁻¹ * ∫⁻ ω in T, ENNReal.ofReal (E' i ω) ∂P
          ≤ (P T)⁻¹ * P T := mul_le_mul_right ((lintegral_mono fun ω =>
            ENNReal.ofReal_le_ofReal (hle i ω)).trans (hmom i hi S hS)) _
        _ = 1 := ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)
    have := h53 PS E' N₀ q hq hq1 hm hnn' hnull
    rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul] at this
    have hpos : 0 < (P T).toReal := ENNReal.toReal_pos h0 (measure_ne_top _ _)
    rw [inv_mul_le_iff₀ hpos] at this
    rw [measureReal_def]
    linarith
  refine ⟨key Er hEr hnn fun _ _ => le_rfl, fun Scr hScr => key _
    (fun i => Measurable.ite (hScr i) (hEr i) measurable_const) (fun i ω => ?_) (fun i ω => ?_)⟩
  · split_ifs; exacts [hnn i ω, le_rfl]
  · split_ifs; exacts [le_rfl, hnn i ω]


/-! ## The concrete score -/

section Score

variable {α : Type*} [MeasurableSpace α] {n : ℕ} {Δ : Fin n → ℝ}

theorem meas_ret' {Y0 : α → ℝ} {Y : α → Fin n → ℝ} (h0 : Measurable Y0) (hY : Measurable Y)
    (j : Fin n) : Measurable fun x => ret (Y0 x) (Y x) j :=
  Measurable.comp (g := fun p : ℝ × (Fin n → ℝ) => ret p.1 p.2 j) (f := fun x => (Y0 x, Y x))
    (Novel.D13DriftNull.measurable_ret j) (h0.prodMk hY)

theorem meas_aG' {Y0 : α → ℝ} {Y : α → Fin n → ℝ} (h0 : Measurable Y0) (hY : Measurable Y) :
    Measurable fun x => aG Δ (Y0 x) (Y x) :=
  Measurable.comp (g := fun p : ℝ × (Fin n → ℝ) => aG Δ p.1 p.2) (f := fun x => (Y0 x, Y x))
    (Novel.D13DriftRect.measurable_aG (Δ := Δ)) (h0.prodMk hY)

theorem meas_QG' {Y0 : α → ℝ} {Y : α → Fin n → ℝ} (h0 : Measurable Y0) (hY : Measurable Y) :
    Measurable fun x => QG Δ (Y0 x) (Y x) :=
  Measurable.comp (g := fun p : ℝ × (Fin n → ℝ) => QG Δ p.1 p.2) (f := fun x => (Y0 x, Y x))
    (Novel.D13DriftNull.measurable_QG (Δ := Δ)) (h0.prodMk hY)

theorem meas_ellG' {Y0 : α → ℝ} {Y : α → Fin n → ℝ} (h0 : Measurable Y0) (hY : Measurable Y)
    {B Wv : α → ℝ} (hB : Measurable B) (hW : Measurable Wv) :
    Measurable fun x => ellG Δ (Y0 x) (Y x) (B x) (Wv x) := by
  unfold ellG
  refine ((measurable_const.mul (Real.measurable_log.comp (measurable_const.mul hW))).sub
    (measurable_const.add (Finset.measurable_sum _ fun j _ =>
      Real.measurable_log.comp ((measurable_pi_apply j).comp hY)))).sub
    ((Finset.measurable_sum _ fun j _ => ?_).div (measurable_const.mul hW))
  exact (((meas_ret' h0 hY j).sub ((hB.sub (hW.div_const 2)).mul_const _)).pow_const 2).div_const _

theorem meas_vEdge' {Y0 : α → ℝ} {Y : α → Fin n → ℝ} (h0 : Measurable Y0) (hY : Measurable Y)
    {C : α → ℝ} (hC : Measurable C) : Measurable fun x => vEdge Δ (Y0 x) (Y x) (C x) := by
  have hA : Measurable fun x => AGb Δ (Y0 x) (Y x) (C x) :=
    (meas_QG' h0 hY).add (measurable_const.mul ((hC.sub (meas_aG' h0 hY)).pow_const 2))
  unfold vEdge
  exact (measurable_const.mul hA).div
    (measurable_const.add (measurable_const.add (measurable_const.mul hA)).sqrt)

theorem meas_clip' {f l h : α → ℝ} (hf : Measurable f) (hl : Measurable l) (hh : Measurable h) :
    Measurable fun x => clip (l x) (h x) (f x) :=
  hh.min (hl.max hf)

/-- Claim 057's closed form is jointly measurable in the prices and the rectangle. -/
theorem meas_DGR' {Y0 : α → ℝ} {Y : α → Fin n → ℝ} (h0 : Measurable Y0) (hY : Measurable Y)
    {Bl Bh Sl Sh : α → ℝ} (hBl : Measurable Bl) (hBh : Measurable Bh) (hSl : Measurable Sl)
    (hSh : Measurable Sh) :
    Measurable fun x => DGR Δ (Bl x) (Bh x) (Sl x) (Sh x) (Y0 x) (Y x) := by
  classical
  have hQ := meas_QG' (Δ := Δ) h0 hY
  have ha := meas_aG' (Δ := Δ) h0 hY
  have hint : Measurable fun x => aG Δ (Y0 x) (Y x) + QG Δ (Y0 x) (Y x) / (2 * n) :=
    ha.add (hQ.div_const _)
  have hfeas : MeasurableSet {x | IntFeas Δ (Y0 x) (Y x) (Bl x) (Bh x) (Sl x) (Sh x)} :=
    ((measurableSet_le hBl hint).inter (measurableSet_le hint hBh)).inter
      ((measurableSet_le (hSl.pow_const 2) (hQ.div_const _)).inter
        (measurableSet_le (hQ.div_const _) (hSh.pow_const 2)))
  have hc : Measurable fun x => candMax Δ (Y0 x) (Y x) (Bl x) (Bh x) (Sl x) (Sh x) := by
    unfold candMax
    have e1 := meas_ellG' (Δ := Δ) h0 hY hBl
      (meas_clip' (meas_vEdge' (Δ := Δ) h0 hY hBl) (hSl.pow_const 2) (hSh.pow_const 2))
    have e2 := meas_ellG' (Δ := Δ) h0 hY hBh
      (meas_clip' (meas_vEdge' (Δ := Δ) h0 hY hBh) (hSl.pow_const 2) (hSh.pow_const 2))
    have e3 := meas_ellG' (Δ := Δ) h0 hY (meas_clip' (ha.add ((hSl.pow_const 2).div_const 2)) hBl hBh)
      (hSl.pow_const 2)
    have e4 := meas_ellG' (Δ := Δ) h0 hY (meas_clip' (ha.add ((hSh.pow_const 2).div_const 2)) hBl hBh)
      (hSh.pow_const 2)
    have e5 := meas_ellG' (Δ := Δ) h0 hY hint (hQ.div_const (n : ℝ))
    exact ((e1.max e2).max (e3.max e4)).max (Measurable.ite hfeas e5 e1)
  unfold DGR
  exact Measurable.ite (Novel.D13DriftNull.measurableSet_pos.preimage (h0.prodMk hY))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc))
    (Measurable.ite (Novel.D13DriftNull.measurableSet_trap.preimage (h0.prodMk hY))
      measurable_const measurable_const)

end Score


theorem score_holds : Standalone.D13Declaration.score := by
  classical
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN 𝒲 _ Fb blo bhi slo shi hFb hbl hbh
    hsl hsh hbd g sel Δe μ Dd cov
  have hC := Novel.D13CEVCatalogue.cited_of h55 h56 hW
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  have hm : 0 < m := hN.evals
  have hΔ : ∀ j, 0 < Δe j := fun j => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  -- Joint measurability of the denominator.
  have hY0 : Measurable fun x : 𝒲 × (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      ((x.2.1 (Fin.last k) : NNR) : ℝ) :=
    measurable_subtype_coe.comp ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd))
  have hY : Measurable fun x : 𝒲 × (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      fun l => ((x.2.2 l : NNR) : ℝ) :=
    measurable_pi_iff.2 fun l => measurable_subtype_coe.comp ((measurable_pi_apply l).comp
      (measurable_snd.comp measurable_snd))
  have hG0 : Measurable fun x : 𝒲 × (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      Gnull pw g x.2.1 x.2.2 :=
    (Measurable.iSup fun ϑ => Measurable.iSup fun _ =>
      ENNReal.measurable_ofReal.comp (hSM.measg ϑ)).comp measurable_snd
  have hDG : Measurable fun x : 𝒲 × (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      DG Δe ((x.2.1 (Fin.last k) : NNR) : ℝ) fun l => ((x.2.2 l : NNR) : ℝ) :=
    Measurable.comp (g := fun p : ℝ × (Fin m → ℝ) => DG Δe p.1 p.2)
      (f := fun x : 𝒲 × (Fin (k + 1) → NNR) × (Fin m → NNR) =>
        (((x.2.1 (Fin.last k) : NNR) : ℝ), fun l => ((x.2.2 l : NNR) : ℝ)))
      (Novel.D13DriftNull.measurable_DG (Δ := Δe)) (hY0.prodMk hY)
  have hDR : Measurable fun x : 𝒲 × (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      DGRN Δe (blo x.1) (bhi x.1) (slo x.1) (shi x.1) x.2.1 x.2.2 :=
    meas_DGR' hY0 hY (hbl.comp measurable_fst) (hbh.comp measurable_fst)
      (hsl.comp measurable_fst) (hsh.comp measurable_fst)
  have hDm : Measurable (fun x : 𝒲 × (Fin (k + 1) → NNR) × (Fin m → NNR) => Dd x.1 x.2.1 x.2.2) :=
    hG0.max (Measurable.ite (measurable_fst hFb) hDG hDR)
  -- Finiteness.
  have hfin : ∀ w u v, Edrift (g (sel u) u v) (Dd w u v) < ⊤ := fun w u v => by
    by_cases ha : g (sel u) u v = 0
    · rw [ha, Novel.D13DriftScore.Edrift_zero]; exact ENNReal.zero_lt_top
    have ha' : 0 < g (sel u) u v := lt_of_le_of_ne (hSM.nonneg _ _ _) (Ne.symm ha)
    have hD0 : Dd w u v ≠ 0 :=
      ((Novel.D13DriftRectScore.Gnull_pos hN hC u v ha').trans_le (le_max_left _ _)).ne'
    rw [Novel.D13DriftRectScore.Edrift_pos_eq ha hD0]
    exact ENNReal.div_lt_top ENNReal.ofReal_ne_top hD0
  refine ⟨hDm, hfin, Novel.SplitLikelihood.measurable_selected hSM.measg hSM.measSel,
    fun u v => hSM.nonneg _ _ _, fun u => hSM.norm _ u,
    fun ϑ hϑ w u v => le_max_of_le_left (le_iSup₂_of_le ϑ hϑ le_rfl), fun b κg hκg => ⟨?_, ?_,
      fun u => Novel.D13DriftScore.gGN_norm hΔ b hκg u⟩⟩
  · exact hFb.union (((measurableSet_le hbl measurable_const).inter
      (measurableSet_le measurable_const hbh)).inter ((measurableSet_le hsl measurable_const).inter
        (measurableSet_le measurable_const hsh)))
  · intro w hw u v
    refine le_max_of_le_right ?_
    by_cases hwF : w ∈ Fb
    · rw [ite_eq_left hwF, ← Novel.D13DriftNull.sup_eq hm hΔ]
      exact le_iSup_of_le b (le_iSup_of_le κg (le_iSup_of_le hκg le_rfl))
    · rw [ite_eq_right hwF]
      have hr : w ∈ {w | b ∈ Icc (blo w) (bhi w) ∧ κg ∈ Icc (slo w) (shi w)} :=
        hw.resolve_left hwF
      obtain ⟨hb1, hs1, hs2⟩ := hbd w
      show _ ≤ DGR Δe (blo w) (bhi w) (slo w) (shi w) _ _
      rw [← Novel.D13DriftRect.sup_eq hm hΔ hb1 hs1 hs2]
      exact le_iSup₂_of_le b hr.1 (le_iSup₂_of_le κg hr.2 le_rfl)

end Novel.D13Declaration
