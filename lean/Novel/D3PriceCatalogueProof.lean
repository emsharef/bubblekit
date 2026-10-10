import Standalone.D3PriceCatalogue
import Novel.PriceChainProof
import Novel.D3CatalogueCalibrationProof
import Novel.D3PowerTailProof
import Upstream.PriceKernels
import Novel.D30SmallScaleNorm

/-!
# Claim 052: proof

Proves `Standalone.D3PriceCatalogue.statement` (`proof`).
* **Kernels.** `ker` is `f1` or `f2`, which are positive and measurable (`Novel.PriceChain`). Their
  one-step normalization is AX-54/55's `norm`.
* **Part 1.**
  - `CatalogueModel`: the chain density (2) is positive, jointly measurable and normalized
    (`Novel.PriceChain.chain_norm`). The selector's fibres are Borel (`selector_fibre`), because
    the first maximizer is characterized by finitely many comparisons of measurable training
    likelihoods.
  - `IsCondDensity` is the true model's `SplitLaw`.
  - The coefficient `κx^pw` is in `C_pow(R)`. Its blocks are claim 013's `B1_eq` and `B2_eq` with
    `∫ x⁻¹ = log r` or `∫ x⁻³ = (1 − r⁻²)/(2R²)`.
* **Part 2.** It is claim 051's `core_holds` with these premises.
* **Part 3.** It is `Novel.PriceChain.chain_ac`, together with the true model's `GridLaw`.
* `ax55_of_upstream` and `ax54_of_upstream` derive the restated inputs from `Upstream.PriceKernels`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Novel.D3PriceCatalogue

open Standalone.PriceChain Standalone.D3CatalogueCalibration Standalone.D3PowerTail
  Standalone.D3VisitedRange Standalone.D1TwoEndpoint Standalone.D3PriceCatalogue

/-! ## Inputs from their Upstream structures -/

theorem ax55_of_upstream {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ} (h : Upstream.GBMKernel P 𝓕) :
    AX55 P 𝓕 W :=
  fun hW => ⟨fun S κ x hκ hx hS => h.law W S κ x hW hκ hx hS, h.norm W hW⟩

theorem ax54_of_upstream {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
    {X : Upstream.Diffusion.SDEPrimitives P 𝓕 W} (h : Upstream.BesselKernel X) :
    AX54 P 𝓕 W fun κ x S ζ =>
      X.Solves Upstream.PriceKernels.posInterval (fun _ => 0) (fun y => κ * y ^ 2) x S ζ :=
  fun hW S ζ κ x hκ hx hS => h.law S ζ κ x hW hκ hx hS

/-! ## Kernels, grids and the selector -/

theorem ker_meas (pw : ℕ) (κ Δ : ℝ) : Measurable (Function.uncurry (ker pw κ Δ)) := by
  unfold ker; split_ifs
  · exact Novel.PriceChain.f1_meas κ Δ
  · exact Novel.PriceChain.f2_meas κ Δ

theorem ker_pos {pw : ℕ} {κ Δ x y : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ)
    (hx : 0 < x) (hy : 0 < y) : 0 < ker pw κ Δ x y := by
  unfold ker; split_ifs
  · exact Novel.PriceChain.f1_pos hκ hΔ hy
  · exact Novel.PriceChain.f2_pos hκ hΔ hx hy

theorem incr_pos {n : ℕ} {t : Fin (n + 1) → ℝ≥0} (ht : StrictMono t) (j : Fin n) : 0 < incr t j := by
  have := ht j.castSucc_lt_succ
  unfold incr
  exact sub_pos.2 (by exact_mod_cast this)

theorem toPos_meas : Measurable toPos := by
  have : toPos = fun x => (⟨if 0 < x then x else 1, by split_ifs with h; exact h; exact one_pos⟩ :
      PosReal) := by
    funext x; unfold toPos; split_ifs <;> rfl
  rw [this]
  exact (Measurable.ite measurableSet_Ioi measurable_id measurable_const).subtype_mk

section Selector

variable {k m c : ℕ} {t : Fin (k + 1 + m + 1) → ℝ≥0} {s : ℝ} {pw : Fin c → ℕ} {κ : Fin c → ℝ}

theorem Ltrain_meas (ϑ : Fin c) : Measurable (Ltrain t s pw κ ϑ) :=
  (Novel.PriceChain.chain_meas fun _ => ker_meas _ _ _).comp (measurable_const.prodMk measurable_id)

theorem selector_eq_iff (hc : 0 < c) (u : Fin (k + 1) → PosReal) (j : Fin c) :
    selector hc t s pw κ u = j ↔ (∀ h, Ltrain t s pw κ h u ≤ Ltrain t s pw κ j u) ∧
      ∀ h, (∀ h', Ltrain t s pw κ h' u ≤ Ltrain t s pw κ h u) → j ≤ h := by
  classical
  set M := Finset.univ.filter fun j => ∀ h, Ltrain t s pw κ h u ≤ Ltrain t s pw κ j u
  have hne : M.Nonempty := by
    have : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j => Ltrain t s pw κ j u)
      Finset.univ_nonempty
    exact ⟨j₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun h => hj₀ h (Finset.mem_univ _)⟩⟩
  have hsel : selector hc t s pw κ u = M.min' hne := by
    unfold selector; exact dite_eq_left hne
  rw [hsel]
  constructor
  · rintro rfl
    exact ⟨(Finset.mem_filter.1 (M.min'_mem hne)).2,
      fun h hh => M.min'_le h (Finset.mem_filter.2 ⟨Finset.mem_univ _, hh⟩)⟩
  · rintro ⟨hj, hmin⟩
    exact le_antisymm (M.min'_le j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩))
      (M.le_min' hne j fun h hh => hmin h (Finset.mem_filter.1 hh).2)

theorem selector_fibre (hc : 0 < c) (j : Fin c) :
    MeasurableSet (selector hc t s pw κ ⁻¹' {j}) := by
  have hset : selector hc t s pw κ ⁻¹' {j} =
      (⋂ h, {u | Ltrain t s pw κ h u ≤ Ltrain t s pw κ j u}) ∩
        ⋂ h, ({u | ∀ h', Ltrain t s pw κ h' u ≤ Ltrain t s pw κ h u}ᶜ ∪ {_u | j ≤ h}) := by
    ext u
    simp only [mem_preimage, mem_singleton_iff, selector_eq_iff, mem_inter_iff, mem_iInter,
      mem_ofPred_eq, mem_union, mem_compl_iff]
    refine and_congr_right fun _ => forall_congr' fun h => ?_
    tauto
  rw [hset]
  refine (MeasurableSet.iInter fun h => measurableSet_le (Ltrain_meas h) (Ltrain_meas j)).inter
    (MeasurableSet.iInter fun h => (MeasurableSet.compl ?_).union (MeasurableSet.const _))
  have : {u | ∀ h', Ltrain t s pw κ h' u ≤ Ltrain t s pw κ h u} =
      ⋂ h', {u | Ltrain t s pw κ h' u ≤ Ltrain t s pw κ h u} := by ext; simp
  rw [this]
  exact MeasurableSet.iInter fun h' => measurableSet_le (Ltrain_meas h') (Ltrain_meas h)

end Selector

/-! ## Coefficients and blocks -/

theorem cpow_sigma {pw : ℕ} {κ R : ℝ} (hκ : 0 < κ) :
    CPow R (sigmaCat pw κ) ∧ ∃ κ' : ℝ, 0 < κ' ∧ ∀ x, R ≤ x → sigmaCat pw κ x = κ' * x ^ (pw : ℝ) := by
  have hcont : ContinuousOn (sigmaCat pw κ) (Ioi 0) :=
    continuousOn_const.mul (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx))
  have hposf : ∀ x, 0 < x → 0 < sigmaCat pw κ x := fun x hx =>
    mul_pos hκ (Real.rpow_pos_of_pos hx _)
  refine ⟨⟨⟨?_, fun x hx => (hposf x hx).ne', fun a b ha hb => ?_⟩, hposf, hcont,
    κ, pw, hκ, fun _ _ => rfl⟩, κ, hκ, fun _ _ => rfl⟩
  · exact measurable_const.mul (measurable_id.pow_const _)
  · refine ContinuousOn.integrableOn_Icc ?_
    refine continuousOn_const.div ((hcont.mono fun x hx => ha.trans_le hx.1).pow 2) fun x hx => ?_
    exact pow_ne_zero 2 (hposf x (ha.trans_le hx.1)).ne'

theorem blocks_one {κ R r : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hr : 1 < r) :
    B1 R r (sigmaCat 1 κ) = Real.log r / κ ^ 2 ∧ B2 R r (sigmaCat 1 κ) = Real.log r / κ ^ 2 := by
  have hσ : ∀ x, R ≤ x → sigmaCat 1 κ x = κ * x ^ ((1 : ℕ) : ℝ) := fun _ _ => rfl
  have h1 := Novel.D3PowerTail.B1_eq hκ hσ hR hr
  have h2 := Novel.D3PowerTail.B2_eq hκ hσ hR hr
  have hRr : 0 < R * r := mul_pos hR (zero_lt_one.trans hr)
  have hint : ∫ x in R..R * r, x ^ (1 - 2 * ((1 : ℕ) : ℝ)) = Real.log r := by
    have : ∀ x : ℝ, x ^ (1 - 2 * ((1 : ℕ) : ℝ)) = x⁻¹ := fun x => by
      norm_num [Real.rpow_neg_one]
    simp_rw [this]
    rw [integral_inv_of_pos hR hRr, mul_div_cancel_left₀ _ hR.ne']
  have hB1 : B1 R r (sigmaCat 1 κ) = Real.log r / κ ^ 2 := by
    rw [h1, hint]; ring
  refine ⟨hB1, ?_⟩
  rw [h2, hB1]; norm_num

theorem blocks_two {κ R r : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hr : 1 < r) :
    B1 R r (sigmaCat 2 κ) = (1 - r ^ (-2 : ℤ)) / (2 * κ ^ 2 * R ^ 2) ∧
      B2 R r (sigmaCat 2 κ) = r ^ (-2 : ℤ) * B1 R r (sigmaCat 2 κ) := by
  have hσ : ∀ x, R ≤ x → sigmaCat 2 κ x = κ * x ^ ((2 : ℕ) : ℝ) := fun _ _ => rfl
  have h1 := Novel.D3PowerTail.B1_eq hκ hσ hR hr
  have h2 := Novel.D3PowerTail.B2_eq hκ hσ hR hr
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hRr : 0 < R * r := mul_pos hR hr0
  have hint : ∫ x in R..R * r, x ^ (1 - 2 * ((2 : ℕ) : ℝ)) = (1 - r ^ (-2 : ℤ)) / (2 * R ^ 2) := by
    have h0 : (0 : ℝ) ∉ Set.uIcc R (R * r) := by
      rw [uIcc_of_le (by nlinarith)]; exact fun h => absurd h.1 (not_le.2 hR)
    rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
    have e : (1 - 2 * ((2 : ℕ) : ℝ) + 1) = -2 := by norm_num
    rw [e, Real.mul_rpow hR.le hr0.le]
    have hR2 : R ^ (-2 : ℝ) = (R ^ 2)⁻¹ := by
      rw [Real.rpow_neg hR.le]; norm_cast
    have hr2 : r ^ (-2 : ℝ) = r ^ (-2 : ℤ) := by
      rw [Real.rpow_neg hr0.le, zpow_neg]; norm_cast
    rw [hR2, hr2]
    field_simp
    ring
  have hB1 : B1 R r (sigmaCat 2 κ) = (1 - r ^ (-2 : ℤ)) / (2 * κ ^ 2 * R ^ 2) := by
    rw [h1, hint]; field_simp
  refine ⟨hB1, ?_⟩
  rw [h2]
  congr 1
  rw [show (2 - 2 * ((2 : ℕ) : ℝ)) = -2 by norm_num, Real.rpow_neg (zero_lt_one.trans hr).le,
    zpow_neg]
  norm_cast


/-! ## The statement -/

/-- Claim 052. -/
theorem proof : Standalone.D3PriceCatalogue.statement := by
  intro ι _ Ω _ P _ 𝓕 W S ζ Solves s R r k m c t pw κ θs α αt hc hName hr h55 h54 hW hSm hS1 hS2
    hα hαt U V μ g sel σ p
  have hκ : ∀ i ϑ, 0 < κ i ϑ := fun i => (hName i).scales
  have hpw : ∀ i ϑ, pw i ϑ = 1 ∨ pw i ϑ = 2 := fun i => (hName i).powers
  have hkerpos : ∀ i (ϑ : Fin (c i)) {n : ℕ} (tt : Fin (n + 1) → ℝ≥0), StrictMono tt →
      ∀ j x y, 0 < x → 0 < y → 0 < ker (pw i ϑ) (κ i ϑ) (incr tt j) x y :=
    fun i ϑ n tt htt j x y hx hy => ker_pos (hκ i ϑ) (incr_pos htt j) hx hy
  have hkernorm : ∀ i (ϑ : Fin (c i)) Δ x, 0 < Δ → 0 < x →
      ∫⁻ y, ENNReal.ofReal (ker (pw i ϑ) (κ i ϑ) Δ x y) ∂posVol = 1 := fun i ϑ Δ x hΔ hx => by
    unfold ker; split_ifs
    · exact (h55 i (hW i)).2 _ _ _ (hκ i ϑ) hΔ hx
    · exact Novel.D30SmallScale.kernelNorm2_holds _ _ _ (hκ i ϑ) hΔ hx
  -- The true model's laws, martingale property and strictness.
  have htrue : ∀ i, (pw i (θs i) = 1 → Martingale (S i) (𝓕 i) P) ∧
      (pw i (θs i) = 2 → ∀ T : ℝ≥0, 0 < T → ¬ Martingale (fun t' => S i (min t' T)) (𝓕 i) P) ∧
      GridLaw P (S i) (ker (pw i (θs i)) (κ i (θs i))) (t i) (s i) ∧
      SplitLaw P (S i) (ker (pw i (θs i)) (κ i (θs i))) (t i) := fun i => by
    rcases hpw i (θs i) with h | h
    · have hk : ker (pw i (θs i)) (κ i (θs i)) = f1 (κ i (θs i)) := by simp [ker, h]
      obtain ⟨hm, hg, hs⟩ := (h55 i (hW i)).1 (S i) _ (s i) (hκ i _) (hName i).start (hS1 i h)
      rw [hk]
      exact ⟨fun _ => hm, fun h2 => absurd (h.symm.trans h2) (by norm_num),
        hg _ (t i) (hName i).grid0 (hName i).gridMono, hs _ _ (t i) (hName i).grid0
          (hName i).gridMono⟩
    · have hk : ker (pw i (θs i)) (κ i (θs i)) = f2 (κ i (θs i)) := by simp [ker, h]
      obtain ⟨-, -, hstr, hg, hs⟩ :=
        h54 i (hW i) (S i) (ζ i) _ (s i) (hκ i _) (hName i).start (hS2 i h)
      rw [hk]
      exact ⟨fun h1 => absurd (h.symm.trans h1) (by norm_num), fun _ => hstr,
        hg _ (t i) (hName i).grid0 (hName i).gridMono, hs _ _ (t i) (hName i).grid0
          (hName i).gridMono⟩
  -- Claim 051's statistical premises.
  have hCM : ∀ i, CatalogueModel (U i) (V i) (μ i) (g i) (sel i) := fun i =>
    { measU := measurable_pi_iff.2 fun j => toPos_meas.comp (hSm i _)
      measV := measurable_pi_iff.2 fun l => toPos_meas.comp (hSm i _)
      sfinite := inferInstance
      measg := fun ϑ => (Novel.PriceChain.chain_meas fun l => ker_meas _ _ _).comp
        ((measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_fst)).prodMk
          measurable_snd)
      pos := fun ϑ u v => Novel.PriceChain.chain_pos
        (fun l x y hx hy => hkerpos i ϑ (t i) (hName i).gridMono _ x y hx hy) (u (Fin.last _)).2 v
      norm := fun ϑ u => Novel.PriceChain.chain_norm _ _ (fun l => ker_meas _ _ _)
        (fun l x y hx hy => hkerpos i ϑ (t i) (hName i).gridMono _ x y hx hy)
        (fun l x hx => hkernorm i ϑ _ x (incr_pos (hName i).gridMono _) hx) _ (u (Fin.last _)).2
      measSel := fun ϑ => selector_fibre (hc i) ϑ }
  have hCD : ∀ i, IsCondDensity P (U i) (V i) (μ i) (g i (θs i)) := fun i => (htrue i).2.2.2
  have hcp : ∀ i ϑ, CPow (R i) (σ i ϑ) ∧ ∃ κ' : ℝ, 0 < κ' ∧ ∀ x, R i ≤ x → σ i ϑ x = κ' * x ^ p i ϑ :=
    fun i ϑ => cpow_sigma (hκ i ϑ)
  have : ∀ i, Nonempty (Fin (c i)) := fun i => ⟨⟨0, hc i⟩⟩
  refine ⟨⟨fun i => ⟨hCM i, hCD i, hcp i⟩, fun i ϑ h => ?_, fun i ϑ h => ?_,
    fun i => (htrue i).1, fun i => (htrue i).2.1⟩,
    Novel.D3CatalogueCalibration.core_holds R r (fun i => Fin (c i)) σ p
      (fun i => Fin (k i + 1) → PosReal) (fun i => Fin (m i) → PosReal) P U V μ g sel θs α αt
      (fun i => (hName i).onset) hr hcp hCM hCD hα hαt,
    fun i _ ϑ' => Novel.PriceChain.chain_ac (fun j => ker_meas _ _ _)
      (fun j x y hx hy => hkerpos i ϑ' (t i) (hName i).gridMono j x y hx hy) (hName i).start,
    fun i => (htrue i).2.2.1⟩
  · show B1 (R i) r (sigmaCat (pw i ϑ) (κ i ϑ)) = _ ∧ B2 (R i) r (sigmaCat (pw i ϑ) (κ i ϑ)) = _
    rw [h]; exact blocks_one (hκ i ϑ) (hName i).onset hr
  · show B1 (R i) r (sigmaCat (pw i ϑ) (κ i ϑ)) = _ ∧
      B2 (R i) r (sigmaCat (pw i ϑ) (κ i ϑ)) = r ^ (-2 : ℤ) * B1 (R i) r (sigmaCat (pw i ϑ) (κ i ϑ))
    rw [h]; exact blocks_two (hκ i ϑ) (hName i).onset hr

end Novel.D3PriceCatalogue
