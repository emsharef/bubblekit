import Standalone.D13DriftNull
import Novel.D13DriftProfileProof
import Novel.SplitLikelihoodDominatedProof
import Novel.D14SupportRobustnessProof

/-!
# Claim 055 (D13): proof of the score and parts 1–4 on claim 054's design

Proves `Standalone.D13DriftNull.drift` (`drift_holds`). `Novel/D13DriftNullProof.lean` combines it
with `profile_holds` (`Novel/D13DriftProfileProof.lean`).

* **(1) is normalized against `μ_CEV^m`.** On nonnegative arrays, (1) is the chain of the one-step
  kernel `KG` (`gG_chain`): trapped at a zero state, zero at a zero target from a positive state,
  and `φ(log(y/x))/y` otherwise. Each step integrates to one (`KG_norm`): the atom contributes the
  trapped mass, and on `(0, ∞)` the substitution `y = x eʳ`
  (`lintegral_image_eq_lintegral_abs_deriv_mul`) gives Mathlib's Gaussian integral. Claim 054's
  `chainN_norm` then integrates the chain.
* **AX-58.** The null family is the catalogue nulls together with every `(b, κ > 0)`, and
  `D = max(G₀, D_G)` dominates all of them: `D_G` is the supremum (`sup_eq`). `D` is measurable
  from `D_G`'s closed form (`measurable_DG`). So `ax58_holds` gives the conditional bound, the
  moment and the test. The p-value is claim 054's `zval_valid`.
* **Finiteness.** `Ĝ > 0` forces a positive null density (claim 054's `support`), so `D > 0`.
* **Part 4.**
  - `D ≥ G₀` gives `E^drift ≤ E`.
  - Training absorption makes every density one.
  - Evaluation absorption from a positive endpoint gives `D_G = 0`, so `E^drift = E ≤ 1`
    (`Ecomp_absorbed`).
  - Zero residual gives `D_G = ∞`.
* **One increment.** Every array falls into one of these cases.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal NNReal

namespace Novel.D13DriftScore

open Standalone.D13DriftNull Standalone.CEVSupport Standalone.D13CEVCatalogue
  Standalone.SplitLikelihoodDominated Standalone.D3CatalogueCalibration

/-! ## One step of (1) -/

/-- One step of (1) from `x` to `y`, with the trapped extension. -/
noncomputable def KG (b κ Δ x y : ℝ) : ℝ :=
  open Classical in
  if x = 0 then (if y = 0 then 1 else 0) else if y = 0 then 0 else
    gaussianPDFReal ((b - κ ^ 2 / 2) * Δ) (κ ^ 2 * Δ).toNNReal (Real.log (y / x)) / y

theorem KG_meas (b κ Δ : ℝ) : Measurable (Function.uncurry (KG b κ Δ)) := by
  classical
  show Measurable fun p : ℝ × ℝ => KG b κ Δ p.1 p.2
  unfold KG
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
      measurable_const)
    (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const ?_)
  exact ((measurable_gaussianPDFReal _ _).comp
    (Real.measurable_log.comp (measurable_snd.div measurable_fst))).div measurable_snd

theorem KG_nonneg (b κ Δ : ℝ) {x y : ℝ} (hy : 0 ≤ y) : 0 ≤ KG b κ Δ x y := by
  unfold KG
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact le_rfl
  · exact div_nonneg (gaussianPDFReal_nonneg _ _ _) hy

/-- The log-normal step integrates to one over `(0, ∞)`. -/
theorem lint_lognormal {x : ℝ} (hx : 0 < x) (μ0 : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (gaussianPDFReal μ0 v (Real.log (y / x)) / y) = 1 := by
  have himg : (fun r => x * Real.exp r) '' univ = Ioi 0 := by
    ext y
    simp only [image_univ, mem_range, mem_Ioi]
    constructor
    · rintro ⟨r, rfl⟩; positivity
    · intro hy
      exact ⟨Real.log (y / x), by rw [Real.exp_log (div_pos hy hx)]; field_simp⟩
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (f := fun r => x * Real.exp r) (f' := fun r => x * Real.exp r)
    (fun r _ => ((Real.hasDerivAt_exp r).const_mul x).hasDerivWithinAt)
    (fun r1 _ r2 _ h => Real.exp_injective (mul_left_cancel₀ hx.ne' h)),
    Measure.restrict_univ, ← lintegral_gaussianPDFReal_eq_one μ0 hv]
  refine lintegral_congr fun r => ?_
  rw [abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show x * Real.exp r / x = Real.exp r by field_simp, Real.log_exp]
  field_simp

theorem coe_zero : ((zero : NNR) : ℝ) = 0 := rfl

/-- One-step normalization against `μ_CEV` from every `x ≥ 0`. -/
theorem KG_norm (b : ℝ) {κ Δ x : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ) (hx : 0 ≤ x) :
    ∫⁻ y, ENNReal.ofReal (KG b κ Δ x (y : ℝ)) ∂muCEV = 1 := by
  have hv : (κ ^ 2 * Δ).toNNReal ≠ 0 := by
    intro h
    have : (0 : ℝ) < ((κ ^ 2 * Δ).toNNReal : ℝ) := by
      rw [Real.coe_toNNReal _ (by positivity)]; positivity
    rw [h, NNReal.coe_zero] at this
    exact lt_irrefl _ this
  rw [muCEV, lintegral_add_measure, lintegral_dirac, coe_zero,
    Novel.D13CEVCatalogue.lebNN_lintegral fun y => ENNReal.ofReal (KG b κ Δ x y)]
  rcases hx.lt_or_eq with hx | hx
  · have h0 : KG b κ Δ x 0 = 0 := by unfold KG; simp [hx.ne']
    rw [h0, ENNReal.ofReal_zero, add_zero, ← lint_lognormal hx ((b - κ ^ 2 / 2) * Δ) hv]
    refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    unfold KG
    simp [hx.ne', (mem_Ioi.1 hy).ne']
  · subst hx
    have h0 : KG b κ Δ 0 0 = 1 := by unfold KG; simp
    rw [h0, ENNReal.ofReal_one]
    have : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (KG b κ Δ 0 y) = 0 := by
      rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ≥0∞))
        fun y hy => by unfold KG; simp [(mem_Ioi.1 hy).ne'], lintegral_zero]
    rw [this, zero_add]

/-! ## (1) as a chain -/

section Chain

variable {n : ℕ}

theorem prev_eq (y0 : ℝ) (v : Fin n → NNR) (j : Fin n) :
    prev y0 (fun l => (v l : ℝ)) j = prevN y0 v j := by
  unfold prev prevN
  split_ifs with h
  · have : j.castSucc = (0 : Fin (n + 1)) := Fin.ext (by simp [h])
    rw [this, Fin.cons_zero]
  · have : j.castSucc = (⟨j - 1, by omega⟩ : Fin n).succ := Fin.ext (by simp; omega)
    rw [this, Fin.cons_succ]

theorem chain_zero_start {f : ℝ → ℝ → ℝ → ℝ} (hf0 : ∀ Δ, f Δ 0 0 = 1)
    (hf1 : ∀ Δ y, y ≠ 0 → f Δ 0 y = 0) (Δ : Fin n → ℝ) (v : Fin n → NNR) :
    chainN f Δ 0 v = if ∀ l, (v l : ℝ) = 0 then 1 else 0 := by
  classical
  split_ifs with hz
  · refine Finset.prod_eq_one fun j _ => ?_
    have hp : prevN 0 v j = 0 := by
      unfold prevN; split_ifs
      · rfl
      · exact hz _
    rw [hp, hz j]; exact hf0 _
  · push Not at hz
    have hex : ∃ n', ∃ h : n' < n, (v ⟨n', h⟩ : ℝ) ≠ 0 := by
      obtain ⟨l, hl⟩ := hz; exact ⟨l, l.2, hl⟩
    set n' := Nat.find hex
    obtain ⟨hn, hvn⟩ := Nat.find_spec hex
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨n', hn⟩) ?_
    have hprev : prevN 0 v ⟨n', hn⟩ = 0 := by
      rcases Nat.eq_zero_or_pos n' with h0 | h0
      · exact Novel.CEVSupport.prevN_zero 0 v ⟨n', hn⟩ h0
      · rw [Novel.CEVSupport.prevN_succ 0 v ⟨n', hn⟩ h0.ne']
        by_contra h
        exact Nat.find_min hex (show n' - 1 < n' by omega) ⟨by omega, h⟩
    show f (Δ ⟨n', hn⟩) (prevN 0 v ⟨n', hn⟩) (v ⟨n', hn⟩) = 0
    rw [hprev]; exact hf1 _ _ hvn

theorem chain_first_zero {f : ℝ → ℝ → ℝ → ℝ} (hf : ∀ Δ x, x ≠ 0 → f Δ x 0 = 0) {x0 : ℝ}
    (hx0 : x0 ≠ 0) (Δ : Fin n → ℝ) {v : Fin n → NNR} (hz : ∃ l, (v l : ℝ) = 0) :
    chainN f Δ x0 v = 0 := by
  classical
  have hex : ∃ n', ∃ h : n' < n, (v ⟨n', h⟩ : ℝ) = 0 := by
    obtain ⟨l, hl⟩ := hz; exact ⟨l, l.2, hl⟩
  set n' := Nat.find hex
  obtain ⟨hn, hvn⟩ := Nat.find_spec hex
  refine Finset.prod_eq_zero (Finset.mem_univ ⟨n', hn⟩) ?_
  have hprev : prevN x0 v ⟨n', hn⟩ ≠ 0 := by
    rcases Nat.eq_zero_or_pos n' with h0 | h0
    · rw [Novel.CEVSupport.prevN_zero x0 v ⟨n', hn⟩ h0]; exact hx0
    · rw [Novel.CEVSupport.prevN_succ x0 v ⟨n', hn⟩ h0.ne']
      intro h
      exact Nat.find_min hex (show n' - 1 < n' by omega) ⟨by omega, h⟩
  show f (Δ ⟨n', hn⟩) (prevN x0 v ⟨n', hn⟩) (v ⟨n', hn⟩) = 0
  rw [hvn]; exact hf _ _ hprev

/-- (1) on nonnegative arrays is the chain of `KG`. -/
theorem gG_chain {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (b κ : ℝ) {y0 : ℝ} (hy0 : 0 ≤ y0)
    (v : Fin n → NNR) :
    gG Δ b κ y0 (fun l => (v l : ℝ)) = chainN (fun Δj => KG b κ Δj) Δ y0 v := by
  classical
  by_cases hp : PosPath y0 (fun l => (v l : ℝ))
  · unfold gG chainN
    simp only [hp, ↓reduceIte]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hprev : 0 < prevN y0 v j := by
      rw [← prev_eq]; unfold prev
      by_cases h : (j : ℕ) = 0
      · have : j.castSucc = (0 : Fin (n + 1)) := Fin.ext (by simp [h])
        rw [this, Fin.cons_zero]; exact hp.1
      · have : j.castSucc = (⟨j - 1, by omega⟩ : Fin n).succ := Fin.ext (by simp; omega)
        rw [this, Fin.cons_succ]; exact hp.2 _
    have hy : 0 < (v j : ℝ) := hp.2 j
    unfold KG ret
    simp only [hprev.ne', hy.ne', ↓reduceIte, prev_eq]
    have hκΔ : 0 ≤ κ ^ 2 * Δ j := mul_nonneg (sq_nonneg κ) (hΔ j).le
    rw [gaussianPDFReal, Real.coe_toNNReal _ hκΔ,
      show 2 * π * (κ ^ 2 * Δ j) = 2 * π * κ ^ 2 * Δ j by ring,
      show 2 * (κ ^ 2 * Δ j) = 2 * κ ^ 2 * Δ j by ring]
    field_simp
  · have hgz : gG Δ b κ y0 (fun l => (v l : ℝ)) =
        if y0 = 0 ∧ ∀ j, (v j : ℝ) = 0 then 1 else 0 := by
      unfold gG; simp only [hp, ↓reduceIte]
    rw [hgz]
    rcases hy0.lt_or_eq with hpos | hzero
    · have hz : ∃ l, (v l : ℝ) = 0 := by
        by_contra hz
        push Not at hz
        exact hp ⟨hpos, fun l => lt_of_le_of_ne (v l).2 (Ne.symm (hz l))⟩
      simp only [hpos.ne', false_and, ↓reduceIte]
      exact (chain_first_zero (fun Δ x hx => by unfold KG; simp [hx]) hpos.ne' Δ hz).symm
    · subst hzero
      rw [chain_zero_start (fun Δ => by unfold KG; simp) (fun Δ y hy => by unfold KG; simp [hy])]
      simp

end Chain

/-! ## The score -/

/-- (1) is normalized against `μ_CEV^m` at every training value. -/
theorem gGN_norm {k m : ℕ} {Δe : Fin m → ℝ} (hΔ : ∀ j, 0 < Δe j) (b : ℝ) {κg : ℝ} (hκ : 0 < κg)
    (u : Fin (k + 1) → NNR) :
    ∫⁻ v, ENNReal.ofReal (gGN Δe b κg u v) ∂(Measure.pi fun _ : Fin m => muCEV) = 1 := by
  have h := Novel.D13CEVCatalogue.chainN_norm (f := KG b κg) m Δe
    (fun j => KG_meas b κg (Δe j)) (fun j x y _ hy => KG_nonneg _ _ _ hy)
    (fun j x hx => KG_norm b hκ (hΔ j) hx) _ (u (Fin.last k)).2
  rw [← h]
  refine lintegral_congr fun v => ?_
  unfold gGN
  rw [gG_chain hΔ b κg (u (Fin.last k)).2 v]


theorem Edrift_zero (d : ℝ≥0∞) : Edrift 0 d = 0 := by unfold Edrift; simp

theorem Edrift_top (a : ℝ) : Edrift a ⊤ = 0 := by unfold Edrift; simp

theorem Edrift_eq {a : ℝ} {d : ℝ≥0∞} (ha : a ≠ 0) (hd0 : d ≠ 0) (hdt : d ≠ ⊤) :
    Edrift a d = ENNReal.ofReal a / d := by
  unfold Edrift; simp [ha, hd0, hdt]

theorem drift_holds : Standalone.D13DriftNull.drift := by
  refine ⟨?_, Novel.D14SupportRobustness.general_holds.2⟩
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN g sel Δe E
  have hC := Novel.D13CEVCatalogue.cited_of h55 h56 hW
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  have hm : 0 < m := hN.evals
  have hΔ : ∀ j, 0 < Δe j := fun j => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  -- (1) is normalized.
  have hnorm : ∀ (b κg : ℝ) (u : Fin (k + 1) → NNR), 0 < κg →
      ∫⁻ v, ENNReal.ofReal (gGN Δe b κg u v) ∂(Measure.pi fun _ : Fin m => muCEV) = 1 :=
    fun b κg u hκ => gGN_norm hΔ b hκ u
  -- Domination.
  have hdomC : ∀ u v ϑ, pw ϑ ≤ 1 → ENNReal.ofReal (g ϑ u v) ≤ Dmax Δe pw g u v :=
    fun u v ϑ hϑ => le_max_of_le_left (le_iSup₂_of_le ϑ hϑ le_rfl)
  have hdomG : ∀ (b κg : ℝ) u v, 0 < κg → ENNReal.ofReal (gGN Δe b κg u v) ≤ Dmax Δe pw g u v :=
    fun b κg u v hκ => le_max_of_le_right (by
      rw [← Novel.D13DriftNull.sup_eq hm hΔ]
      exact le_iSup_of_le b (le_iSup_of_le κg (le_iSup_of_le hκ le_rfl)))
  -- Measurability.
  have hu_meas : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      ((p.1 (Fin.last k) : NNR) : ℝ) :=
    measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_fst)
  have hv_meas : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      fun l => ((p.2 l : NNR) : ℝ) :=
    measurable_pi_iff.2 fun l => measurable_subtype_coe.comp ((measurable_pi_apply l).comp
      measurable_snd)
  have hDm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => Dmax Δe pw g p.1 p.2 := by
    unfold Dmax
    exact (Measurable.iSup fun ϑ => Measurable.iSup fun _ =>
      ENNReal.measurable_ofReal.comp (hSM.measg ϑ)).max
      ((Novel.D13DriftNull.measurable_DG (Δ := Δe)).comp (hu_meas.prodMk hv_meas))
  have hGm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => g (sel p.1) p.1 p.2 :=
    Novel.SplitLikelihood.measurable_selected hSM.measg hSM.measSel
  have hEm : Measurable (Function.uncurry E) :=
    Novel.SplitLikelihoodDominated.Edrift_meas.comp (hGm.prodMk hDm)
  -- Finiteness.
  have hDpos : ∀ u v, 0 < g (sel u) u v → 0 < Dmax Δe pw g u v := fun u v h => by
    obtain ⟨ϑ, hϑ, hpos⟩ := Novel.D13CEVCatalogue.support hN hC u v h
    exact (ENNReal.ofReal_pos.2 hpos).trans_le (hdomC u v ϑ hϑ)
  have hfin : ∀ u v, E u v < ⊤ := fun u v => by
    show Edrift _ _ < ⊤
    unfold Edrift
    split_ifs with h1 h2
    · exact ENNReal.zero_lt_top
    · exfalso
      push Not at h1
      exact (hDpos u v (lt_of_le_of_ne (hSM.nonneg _ _ _) (Ne.symm h1.1))).ne' h2
    · push Not at h1
      exact ENNReal.div_lt_top ENNReal.ofReal_ne_top h2
  -- Part 2, by AX-58.
  have hpart2 : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      ((∃ ϑ, pw ϑ ≤ 1 ∧ IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (g ϑ)) ∨
        ∃ b κg : ℝ, 0 < κg ∧
          IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (gGN Δe b κg)) →
      (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a := by
    intro Ω _ P _ U V hU hV hnull
    let gl : ({ϑ : Fin c // pw ϑ ≤ 1} ⊕ (ℝ × {κg : ℝ // 0 < κg})) →
        (Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ :=
      Sum.elim (fun ϑ => g ϑ.1) (fun p => gGN Δe p.1 p.2.1)
    have hDM : DomModel U V (Measure.pi fun _ : Fin m => muCEV) (fun u v => g (sel u) u v) gl
        (Dmax Δe pw g) :=
by
      refine ⟨hU, hV, hSM.sfinite, hGm, fun u v => hSM.nonneg _ _ _, fun u => hSM.norm _ u,
        ?_, ?_, ?_, hDm, ?_⟩
      · rintro (ϑ | p)
        · exact hSM.measg ϑ.1
        · exact (Novel.D13DriftNull.measurable_gG (Δ := Δe) p.1 p.2.1).comp
            (hu_meas.prodMk hv_meas)
      · rintro (ϑ | p) u v
        · exact hSM.nonneg _ _ _
        · exact Novel.D13DriftNull.gG_nonneg _ _ _ _
      · rintro (ϑ | p) u
        · exact hSM.norm _ u
        · exact hnorm p.1 p.2.1 u p.2.2
      · rintro (ϑ | p) u v
        · exact hdomC u v ϑ.1 ϑ.2
        · exact hdomG p.1 p.2.1 u v p.2.2
    have hl : ∃ l, IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (gl l) := by
      rcases hnull with ⟨ϑ, hϑ, h⟩ | ⟨b, κg, hκ, h⟩
      · exact ⟨Sum.inl ⟨ϑ, hϑ⟩, h⟩
      · exact ⟨Sum.inr (b, ⟨κg, hκ⟩), h⟩
    obtain ⟨l, hlc⟩ := hl
    obtain ⟨h1, h2, h3⟩ := Novel.SplitLikelihoodDominated.ax58_holds P U V _ _ gl _ l hDM hlc
    exact ⟨h1, h2, h3, fun a ha0 ha1 => Novel.D13CEVCatalogue.zval_valid
      (hEm.comp (hU.prodMk hV)) (fun ω => hfin _ _) h2 a ha0 ha1⟩
  -- Part 4.
  have hdom : ∀ u v, E u v ≤ Ecomp pw (fun ϑ => g ϑ u v) (sel u) := fun u v => by
    have hsc := Novel.CEVSupport.score pw (fun ϑ => g ϑ u v) (sel u)
      (fun ϑ => hSM.nonneg _ _ _) hN.hasNull (Novel.D13CEVCatalogue.support hN hC u v)
    show Edrift _ _ ≤ _
    rcases (hSM.nonneg (sel u) u v).lt_or_eq with ha | ha
    · obtain ⟨G0, hG0, -, ⟨ϑs, hϑs, hGs⟩, hE⟩ := hsc.2.2.1 ha
      rw [hE]
      have hD : ENNReal.ofReal G0 ≤ Dmax Δe pw g u v := hGs ▸ hdomC u v ϑs hϑs
      unfold Edrift
      split_ifs with h1 h2
      · exact bot_le
      · exact absurd h2 (hDpos u v ha).ne'
      · rw [ENNReal.ofReal_div_of_pos hG0]; exact ENNReal.div_le_div_left hD _
    · have ha' : g (sel u) u v = 0 := ha.symm
      rw [ha', Edrift_zero]; exact bot_le
  have htrain : ∀ u v, (u (Fin.last k) : ℝ) = 0 → (∀ l, (v l : ℝ) = 0) → E u v = 1 :=
    fun u v hu0 hv0 => by
      have hvz : v = fun _ => zero := funext fun l => Subtype.ext (hv0 l)
      have hg1 : ∀ ϑ, g ϑ u v = 1 := fun ϑ => by
        show chainN _ _ (u (Fin.last k) : ℝ) v = 1
        rw [hu0, hvz]; exact Novel.CEVSupport.chain_absorbed _ _ _
      have hDG : DG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) = 1 := by
        unfold DG PosPath; simp [hu0, hv0]
      have hsup : (⨆ ϑ ∈ {ϑ | pw ϑ ≤ 1}, ENNReal.ofReal (g ϑ u v)) = 1 := by
        simp only [hg1, ENNReal.ofReal_one]
        obtain ⟨ϑ0, h0⟩ := hN.hasNull
        exact le_antisymm (iSup₂_le fun _ _ => le_rfl) (le_iSup₂_of_le ϑ0 h0 le_rfl)
      show Edrift (g (sel u) u v) (Dmax Δe pw g u v) = 1
      unfold Dmax
      rw [hsup, hDG, max_self, hg1, Edrift_eq one_ne_zero one_ne_zero ENNReal.one_ne_top,
        ENNReal.ofReal_one, ENNReal.div_self one_ne_zero ENNReal.one_ne_top]
  have hfirst : ∀ u v, 0 < (u (Fin.last k) : ℝ) → (∃ l, (v l : ℝ) = 0) →
      E u v = Ecomp pw (fun ϑ => g ϑ u v) (sel u) ∧ E u v ≤ 1 := fun u v hpos hz => by
    have hsc := Novel.CEVSupport.score pw (fun ϑ => g ϑ u v) (sel u)
      (fun ϑ => hSM.nonneg _ _ _) hN.hasNull (Novel.D13CEVCatalogue.support hN hC u v)
    have hDG0 : DG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) = 0 := by
      have hnp : ¬ PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) := fun h => by
        obtain ⟨l, hl⟩ := hz; exact (h.2 l).ne' hl
      unfold DG; simp only [hnp, ↓reduceIte, hpos.ne', false_and]
    have hD : Dmax Δe pw g u v = ⨆ ϑ ∈ {ϑ | pw ϑ ≤ 1}, ENNReal.ofReal (g ϑ u v) := by
      unfold Dmax; rw [hDG0]; exact max_eq_left bot_le
    have hE1 : E u v = Ecomp pw (fun ϑ => g ϑ u v) (sel u) := by
      show Edrift _ _ = _
      rcases (hSM.nonneg (sel u) u v).lt_or_eq with ha | ha
      · obtain ⟨G0, hG0, hle, ⟨ϑs, hϑs, hGs⟩, hE⟩ := hsc.2.2.1 ha
        have hS : (⨆ ϑ ∈ {ϑ | pw ϑ ≤ 1}, ENNReal.ofReal (g ϑ u v)) = ENNReal.ofReal G0 :=
          le_antisymm (iSup₂_le fun ϑ hϑ => ENNReal.ofReal_le_ofReal (hle ϑ hϑ))
            (le_iSup₂_of_le ϑs hϑs (by rw [hGs]))
        rw [hD, hS, hE, Edrift_eq ha.ne' (ENNReal.ofReal_pos.2 hG0).ne' ENNReal.ofReal_ne_top,
          ENNReal.ofReal_div_of_pos hG0]
      · have ha' : g (sel u) u v = 0 := ha.symm
        rw [hsc.2.1 ha', ha', Edrift_zero]
    exact ⟨hE1, hE1 ▸ Novel.D14SupportRobustness.Ecomp_absorbed hN hC u v (Or.inr hz)⟩
  have hzero : ∀ u v, PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) →
      QG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) = 0 → E u v = 0 := fun u v hp hQ => by
    have hDG : DG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) = ⊤ := by
      unfold DG; simp only [hp, ↓reduceIte, hQ, lt_irrefl]
    show Edrift _ _ = 0
    have : Dmax Δe pw g u v = ⊤ := by unfold Dmax; rw [hDG]; exact max_eq_right le_top
    rw [this, Edrift_top]
  refine ⟨hnorm, hdomC, hdomG, hDm, hEm, hfin, hDpos, hpart2, hdom, htrain, hfirst, hzero, ?_⟩
  intro hm1 u v
  by_cases hx : (u (Fin.last k) : ℝ) = 0
  · by_cases hv0 : ∀ l, (v l : ℝ) = 0
    · exact (htrain u v hx hv0).le
    · have h0 : g (sel u) u v = 0 := by
        show chainN _ _ (u (Fin.last k) : ℝ) v = 0
        rw [hx, Novel.D14SupportRobustness.chain_from_zero]
        simp only [hv0, ↓reduceIte]
      show Edrift _ _ ≤ 1
      rw [h0, Edrift_zero]; exact zero_le_one
  · have hpos := lt_of_le_of_ne (u (Fin.last k)).2 (Ne.symm hx)
    by_cases hz : ∃ l, (v l : ℝ) = 0
    · exact (hfirst u v hpos hz).2
    · push Not at hz
      have hp : PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) :=
        ⟨hpos, fun l => lt_of_le_of_ne (v l).2 (Ne.symm (hz l))⟩
      have hQ : QG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) = 0 := by
        subst hm1
        unfold QG aG
        simp only [Fin.sum_univ_one]
        rw [div_mul_cancel₀ _ (hΔ 0).ne', sub_self]
        simp
      rw [hzero u v hp hQ]; exact zero_le_one

end Novel.D13DriftScore
