import Novel.D19CondSensitivityRatio
import Novel.D19FilteredLikelihoodProof
import Novel.D20ClockConfidenceModel

/-!
# Claim 037, (6): the direct conditional bound

* **Densities.** A label string's mass is the integral, over the returns with those labels, of the
  product of the Gaussian step densities (`walk_eq_int`, through `pi_gauss_eq`). The product is
  `exp` of the log density `ll` (claim 036's `pdf_eq_exp`).
* **Latent paths.** The returns `ξ` define the log-price path `cpath`, whose increments are `ξ`. On
  returns with the observed labels, the training path lies in the training cells (from `log s`) and
  the evaluation path in the evaluation cells (from the last training cell).
* **(10).** The full log ratio is the training ratio plus the evaluation ratio. Let `m_T` be the
  infimum of the training ratio over compatible paths. Then the training ratio lies in
  `[m_T, m_T + c₁Ω_(B,T) + c₂Ω_(C,T)]` and the evaluation ratio is at most
  `T_E + c₁d_(B,E) + c₂d_(C,E)`. So the joint mass grows by at most `exp(m_T + osc + η_E)`, the
  training mass by at least `exp(m_T)`, and the constant `m_T` cancels. Nothing about the filtered
  posterior is assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal

namespace Novel.D19CondSensitivity

open Standalone.D19CondSensitivity Standalone.D19FilteredLikelihood Standalone.D14FixedTick
  Standalone.D17ClockCells Novel.D19FilteredLikelihood

/-! ## Densities -/

theorem pi_gauss_eq {m : ℕ} (μ σ : Fin m → ℝ) (hσ : ∀ j, (σ j ^ 2).toNNReal ≠ 0) :
    gpm μ σ = (Measure.pi fun _ : Fin m => (volume : Measure ℝ)).withDensity
      fun ξ => ∏ j, gaussianPDF (μ j) (σ j ^ 2).toNNReal (ξ j) := by
  unfold gpm
  refine Measure.pi_eq fun S hS => ?_
  have hpi : MeasurableSet (Set.pi univ S) := MeasurableSet.univ_pi hS
  rw [withDensity_apply _ hpi, ← lintegral_indicator hpi]
  have hind : (Set.pi univ S).indicator (fun ξ => ∏ j, gaussianPDF (μ j) (σ j ^ 2).toNNReal (ξ j)) =
      fun ξ => ∏ j, (S j).indicator (gaussianPDF (μ j) (σ j ^ 2).toNNReal) (ξ j) := by
    funext ξ
    by_cases h : ξ ∈ Set.pi univ S
    · rw [indicator_of_mem h]
      exact Finset.prod_congr rfl fun j _ => (indicator_of_mem (h j (mem_univ j)) _).symm
    · rw [indicator_of_notMem h]
      obtain ⟨j, -, hj⟩ : ∃ j ∈ univ, ξ j ∉ S j := by
        by_contra hc; push Not at hc; exact h hc
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (indicator_of_notMem hj _)).symm
  rw [hind, Novel.D20ClockConfidence.lintegral_pi_prod volume m _ fun j =>
    (measurable_gaussianPDF _ _).indicator (hS j)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [gaussianReal_of_var_ne_zero _ (hσ j), withDensity_apply _ (hS j), lintegral_indicator (hS j)]

/-- A label string's mass as an integral of the product density. -/
theorem walk_eq_int (δ : ℝ) {m : ℕ} (μ σ : Fin m → ℝ) (hσ : ∀ j, (σ j ^ 2).toNNReal ≠ 0) (x : ℝ)
    (z : Fin m → ℕ) :
    walkM δ μ σ x {z} = ∫⁻ ξ in {ξ : Fin m → ℝ | mlabels δ m x ξ = z},
      ∏ j, ENNReal.ofReal (gaussianPDFReal (μ j) (σ j ^ 2).toNNReal (ξ j))
        ∂(Measure.pi fun _ : Fin m => (volume : Measure ℝ)) := by
  unfold walkM
  rw [Measure.map_apply (measurable_mlabels'' δ m x) (measurableSet_singleton z)]
  change gpm μ σ _ = _
  rw [pi_gauss_eq μ σ hσ, withDensity_apply _ (measurable_mlabels'' δ m x (measurableSet_singleton z))]
  rfl

theorem lpdf_eq_lphi {Δ v b w R : ℝ} (hv : 0 < v) (hw : 0 < w) :
    lpdf Δ v b w R = lphi R (b * Δ - w * v / 2) (w * v) := by
  unfold lpdf lphi
  have : 0 < w * v := mul_pos hw hv
  field_simp
  ring

/-- The product of the step densities is `exp` of the log density. -/
theorem dens_eq {m : ℕ} {Δ v : Fin m → ℝ} (hv : ∀ j, 0 < v j) {b w : ℝ} (hw : 0 < w)
    (ξ : Fin m → ℝ) :
    ∏ j, ENNReal.ofReal (gaussianPDFReal (muF Δ v b w j) (sdF v w j ^ 2).toNNReal (ξ j)) =
      ENNReal.ofReal (Real.exp (ll Δ v ξ b w)) := by
  rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => gaussianPDFReal_nonneg _ _ _]
  congr 1
  unfold ll
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [sdF_sq hv hw, show muF Δ v b w j = b * Δ j - w * v j / 2 from rfl, pdf_eq_exp (hv j) hw,
    lpdf_eq_lphi (hv j) hw]

theorem var_ne_zero {m : ℕ} {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) {w : ℝ} (hw : 0 < w) (j : Fin m) :
    (sdF v w j ^ 2).toNNReal ≠ 0 := by
  rw [sdF_sq hv hw]
  exact (Real.toNNReal_pos.2 (mul_pos hw (hv j))).ne'

/-! ## Latent paths -/

variable {m : ℕ}

/-- The log-price path from `c` with returns `ξ`. -/
noncomputable def cpath (c : ℝ) (ξ : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  fun i => c + ∑ l : Fin m, if (l : ℕ) < (i : ℕ) then ξ l else 0

theorem cpath_zero (c : ℝ) (ξ : Fin m → ℝ) : cpath c ξ 0 = c := by simp [cpath]

theorem cpath_succ (c : ℝ) (ξ : Fin m → ℝ) (j : Fin m) : cpath c ξ j.succ = c + psum ξ j := by
  unfold cpath psum
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  have : (l : ℕ) < (j.succ : ℕ) ↔ l ≤ j := by rw [Fin.le_def, Fin.val_succ]; omega
  exact if_congr this rfl rfl

theorem cpath_last (c : ℝ) (ξ : Fin m → ℝ) : cpath c ξ (Fin.last m) = c + ∑ l, ξ l := by
  unfold cpath
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [l.isLt]

theorem inc_cpath (c : ℝ) (ξ : Fin m → ℝ) : inc (cpath c ξ) = ξ := by
  funext j
  unfold inc cpath
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    have : (l : ℕ) ≠ j := fun h => hl (Fin.ext h)
    simp only [Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> first | (exfalso; omega) | ring
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The full log ratio splits into the training and evaluation ratios. -/
theorem ll_split {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box) (b w : ℝ) (ξ : Fin (K + n) → ℝ)
    (c c' : ℝ) :
    ll Δ v ξ b w - ll Δ v ξ (bg B) (wg B) =
      LR (trn Δ) (trn v) B b w (cpath c (trn ξ)) + LR (evl Δ) (evl v) B b w (cpath c' (evl ξ)) := by
  unfold LR
  rw [inc_cpath, inc_cpath]
  unfold ll
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [trn, evl]
  ring

theorem lA_le_lD {δ : ℝ} (hδ : 0 < δ) {z : ℕ} (hz : 1 ≤ z) : lA δ z ≤ lD δ z := by
  have : (1 : ℝ) ≤ z := by exact_mod_cast hz
  unfold lA lD
  exact Real.log_le_log (by nlinarith) (by nlinarith)

theorem aP_le_dP {δ s : ℝ} (hδ : 0 < δ) {K : ℕ} {u : Fin K → ℕ} (hu : ∀ j, 1 ≤ u j)
    (i : Fin (K + 1)) : aP δ s u i ≤ dP δ s u i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [aP, dP]
  · simp only [aP, dP, Fin.cons_succ]; exact lA_le_lD hδ (hu j)

theorem mid_in {lo hi : Fin (m + 1) → ℝ} (h : ∀ i, lo i ≤ hi i) : InCells lo hi (mid lo hi) :=
  fun i => by unfold mid; constructor <;> linarith [h i]

/-- A label from a positive price `x e^p` puts `log x + p` in its log cell. -/
theorem log_in_cell {δ : ℝ} (hδ : 0 < δ) {x p : ℝ} (hx : 0 < x) {z : ℕ} (hz : 1 ≤ z)
    (h : mlabel δ (x * Real.exp p) = z) : lA δ z ≤ Real.log x + p ∧ Real.log x + p ≤ lD δ z := by
  have hpos : 0 < x * Real.exp p := mul_pos hx (Real.exp_pos p)
  have hc := (Novel.D14FixedTick.mlabel_eq_iff hδ hpos.le z).1 h
  have h2 := (mem_mcell_iff hδ hz hpos).1 hc
  rw [Real.log_mul hx.ne' (Real.exp_pos p).ne', Real.log_exp] at h2
  exact ⟨h2.1, h2.2.le⟩

/-- On returns with the training labels, the training path lies in the training cells. -/
theorem train_in {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) {K : ℕ} {u : Fin K → ℕ} (hu : ∀ j, 1 ≤ u j)
    {ξ : Fin K → ℝ} (hl : mlabels δ K s ξ = u) :
    InCells (aP δ s u) (dP δ s u) (cpath (Real.log s) ξ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [aP, dP, cpath_zero]
  · simp only [aP, dP, Fin.cons_succ, cpath_succ]
    have h := congrFun hl j
    rw [mlabels_eq] at h
    exact log_in_cell hδ hs (hu j) h

/-- On returns with the evaluation labels, the evaluation path lies in the evaluation cells. -/
theorem eval_in {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) {K n : ℕ} {u : Fin K → ℕ} {y : Fin n → ℕ}
    (hu : ∀ j, 1 ≤ u j) (hy : ∀ j, 1 ≤ y j) {ξ : Fin (K + n) → ℝ}
    (hl : mlabels δ (K + n) s ξ = Fin.append u y) :
    InCells (aP δ s u) (dP δ s u) (cpath (Real.log s) (trn ξ)) ∧
      InCells (loE δ s u y) (hiE δ s u y)
        (cpath (cpath (Real.log s) (trn ξ) (Fin.last K)) (evl ξ)) := by
  rw [mlabels_append, append_eq_iff] at hl
  have hT := train_in hδ hs hu hl.1
  refine ⟨hT, fun i => ?_⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [loE, hiE, Fin.cons_zero, cpath_zero]
    exact hT (Fin.last K)
  · simp only [loE, hiE, Fin.cons_succ, cpath_succ]
    have h := congrFun hl.2 j
    rw [mlabels_eq] at h
    have hx : 0 < xEnd s (trn ξ) := xEnd_pos hs _
    have := log_in_cell hδ hx (hy j) h
    rw [cpath_last]
    unfold xEnd at this
    rw [Real.log_mul hs.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    exact this

theorem cond_holds : Standalone.D19CondSensitivity.cond := by
  intro δ s K n Δ v B u y b w hδ hs hΔ hv hB hm hz
  have hu : ∀ j, 1 ≤ u j := all_pos_left hz
  have hy : ∀ j, 1 ≤ y j := fun j => by have := hz (Fin.natAdd K j); rwa [Fin.append_right] at this
  have hw : 0 < w := hB.2.1.trans_le hm.2.1
  have hwg : 0 < wg B := by unfold wg; linarith [hB.2.1, hB.2.2]
  have hvT : ∀ j, 0 < trn v j := fun j => hv _
  have hvE : ∀ j, 0 < evl v j := fun j => hv _
  have hT := pathRatio_holds K (trn Δ) (trn v) (aP δ s u) (dP δ s u) B hvT hB b w hm
  have hE := pathRatio_holds n (evl Δ) (evl v) (loE δ s u y) (hiE δ s u y) B hvE hB b w hm
  set osc := c1 B * (2 * wB (trn Δ) (trn v) (aP δ s u) (dP δ s u)) +
    c2 B * OmC (trn v) (aP δ s u) (dP δ s u) with hosc
  set ηE := TE (evl Δ) (evl v) (Rst (loE δ s u y) (hiE δ s u y)) B +
    c1 B * wB (evl Δ) (evl v) (loE δ s u y) (hiE δ s u y) +
    c2 B * dC (evl v) (loE δ s u y) (hiE δ s u y) with hηE
  -- The infimum of the training ratio over compatible paths.
  set TS := (fun Y => LR (trn Δ) (trn v) B b w Y) '' {Y | InCells (aP δ s u) (dP δ s u) Y}
  have hmid := mid_in (aP_le_dP (s := s) hδ hu)
  have hne : TS.Nonempty := ⟨_, mem_image_of_mem _ hmid⟩
  have hbdd : BddBelow TS := by
    refine ⟨LR (trn Δ) (trn v) B b w (mid (aP δ s u) (dP δ s u)) - osc, ?_⟩
    rintro _ ⟨Y, hY, rfl⟩
    linarith [hT.2.1 _ Y hmid hY]
  set mT := sInf TS
  have hlo : ∀ Y, InCells (aP δ s u) (dP δ s u) Y → mT ≤ LR (trn Δ) (trn v) B b w Y :=
    fun Y hY => csInf_le hbdd (mem_image_of_mem _ hY)
  have hhi : ∀ Y, InCells (aP δ s u) (dP δ s u) Y → LR (trn Δ) (trn v) B b w Y ≤ mT + osc :=
    fun Y hY => by
      have : LR (trn Δ) (trn v) B b w Y - osc ≤ mT := by
        refine le_csInf hne ?_
        rintro _ ⟨Y', hY', rfl⟩
        linarith [hT.2.1 Y Y' hY hY']
      linarith
  -- The joint mass grows by at most `exp(m_T + osc + η_E)`.
  have hN : walkM δ (muF Δ v b w) (sdF v w) s {Fin.append u y} ≤
      ENNReal.ofReal (Real.exp (mT + osc + ηE)) *
        walkM δ (muF Δ v (bg B) (wg B)) (sdF v (wg B)) s {Fin.append u y} := by
    rw [walk_eq_int δ _ _ (var_ne_zero hv hw), walk_eq_int δ _ _ (var_ne_zero hv hwg),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' (measurableSet_lab δ s _) fun ξ hξ => ?_
    rw [dens_eq hv hw, dens_eq hv hwg, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    obtain ⟨hTin, hEin⟩ := eval_in hδ hs hu hy hξ
    have hsplit := ll_split Δ v B b w ξ (Real.log s) (cpath (Real.log s) (trn ξ) (Fin.last K))
    have h1 := hhi _ hTin
    have h2 := hE.2.2 _ hEin
    linarith
  -- The training mass grows by at least `exp(m_T)`.
  have hK : ENNReal.ofReal (Real.exp mT) *
        walkM δ (muF (trn Δ) (trn v) (bg B) (wg B)) (sdF (trn v) (wg B)) s {u} ≤
      walkM δ (muF (trn Δ) (trn v) b w) (sdF (trn v) w) s {u} := by
    rw [walk_eq_int δ _ _ (var_ne_zero hvT hw), walk_eq_int δ _ _ (var_ne_zero hvT hwg),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' (measurableSet_lab δ s _) fun ξ hξ => ?_
    rw [dens_eq hvT hw, dens_eq hvT hwg, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have hin := train_in hδ hs hu hξ
    have h1 := hlo _ hin
    unfold LR at h1
    rw [inc_cpath] at h1
    linarith
  -- Back to the real masses.
  have hLkc : 0 < Lz δ s (muF (trn Δ) (trn v) (bg B) (wg B)) (sdF (trn v) (wg B)) u :=
    Lz_pos hδ hs _ _ (fun j => sdF_pos hvT hwg j) u
  have hLkθ : 0 < Lz δ s (muF (trn Δ) (trn v) b w) (sdF (trn v) w) u :=
    Lz_pos hδ hs _ _ (fun j => sdF_pos hvT hw j) u
  have hNr : Lz δ s (muF Δ v b w) (sdF v w) (Fin.append u y) ≤
      Real.exp (mT + osc + ηE) * Lz δ s (muF Δ v (bg B) (wg B)) (sdF v (wg B)) (Fin.append u y) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (walk_ne_top _ _ s _)) hN
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  have hKr : Real.exp mT * Lz δ s (muF (trn Δ) (trn v) (bg B) (wg B)) (sdF (trn v) (wg B)) u ≤
      Lz δ s (muF (trn Δ) (trn v) b w) (sdF (trn v) w) u := by
    have := ENNReal.toReal_mono (walk_ne_top _ _ s _) hK
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  have heta : etaC δ s Δ v B u y = osc + ηE := by unfold etaC; ring
  show Lz δ s (muF Δ v b w) (sdF v w) (Fin.append u y) /
      Lz δ s (muF (trn Δ) (trn v) b w) (sdF (trn v) w) u ≤
    Real.exp (etaC δ s Δ v B u y) * (Lz δ s (muF Δ v (bg B) (wg B)) (sdF v (wg B)) (Fin.append u y) /
      Lz δ s (muF (trn Δ) (trn v) (bg B) (wg B)) (sdF (trn v) (wg B)) u)
  rw [heta, div_le_iff₀ hLkθ]
  set LNc := Lz δ s (muF Δ v (bg B) (wg B)) (sdF v (wg B)) (Fin.append u y)
  set Lkc := Lz δ s (muF (trn Δ) (trn v) (bg B) (wg B)) (sdF (trn v) (wg B)) u
  have hLNc : 0 ≤ LNc := ENNReal.toReal_nonneg
  calc Lz δ s (muF Δ v b w) (sdF v w) (Fin.append u y) ≤ Real.exp (mT + osc + ηE) * LNc := hNr
    _ = Real.exp (osc + ηE) * (LNc / Lkc) * (Real.exp mT * Lkc) := by
        rw [show mT + osc + ηE = mT + (osc + ηE) by ring, Real.exp_add]
        field_simp
    _ ≤ Real.exp (osc + ηE) * (LNc / Lkc) * Lz δ s (muF (trn Δ) (trn v) b w) (sdF (trn v) w) u :=
        mul_le_mul_of_nonneg_left hKr (mul_nonneg (Real.exp_pos _).le (div_nonneg hLNc hLkc.le))

end Novel.D19CondSensitivity
