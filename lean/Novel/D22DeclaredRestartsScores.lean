import Standalone.D22DeclaredRestarts
import Novel.D22FilteredSequentialNull

/-!
# Claim 040, part 1: the restart scores and (4)

* The prefix masses decrease along the record (claim 039's prefix consistency), so from its anchor
  on each ratio `G_(θ,t)/G_(θ,o_r)` lies in `(0, 1]`, and it is continuous in `(b, w)`; claim 039's
  compactness argument (`exists_greatest`) gives an attained maximum `D^restart` in `(0, 1]`, equal to
  one at the anchor.
* The anchor scores are adapted (the forecasts are predictable and the masses depend on the observed
  prefix only), and so is the weighted scan; (4) is the finite-maximum inequality.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D22DeclaredRestarts

open Standalone.D22DeclaredRestarts Standalone.D22FilteredSequential Standalone.D19FilteredLikelihood
  Standalone.D17ClockCells Novel.D22FilteredSequential

variable {k n J : ℕ}

section Mass

variable {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ : Fin (k + n) → ℝ) {𝒱 : Finset (Fin (k + n) → ℝ)}
  (hv : ∀ v ∈ 𝒱, ∀ j, 0 < v j) {ℬ : Box} (hℬ : ℬ.Valid)
include hδ hs hv hℬ

/-- The prefix masses decrease along the record. -/
theorem Gs_anti {θ} (hθ : θ ∈ Θset 𝒱 ℬ) (u : Fin k → ℕ) (y : Fin n → ℕ) {t t' : Fin (n + 1)}
    (h : t ≤ t') : Gs δ s Δ θ t' u y ≤ Gs δ s Δ θ t u y := by
  obtain ⟨m, hm⟩ : ∃ m, (t' : ℕ) = t + m := ⟨t' - t, by have := Fin.le_def.1 h; omega⟩
  induction m generalizing t' with
  | zero => have : t' = t := Fin.ext (by simpa using hm); rw [this]
  | succ m ih =>
    have hlt : (t : ℕ) + m < n := by have := t'.isLt; omega
    set i : Fin n := ⟨t + m, hlt⟩
    have hsucc : t' = i.succ := Fin.ext (by simp [i]; omega)
    have hcs : i.castSucc ≥ t := Fin.le_def.2 (by simp [i])
    have hstep : Gs δ s Δ θ i.succ u y ≤ Gs δ s Δ θ i.castSucc u y := by
      have hs' := Gs_hasSum hδ hs Δ θ (hv _ hθ.1) (Θ_w_pos hℬ hθ) i u y
      have := le_hasSum hs' (y i) fun z _ => (Gs_pos' hδ hs Δ hv hℬ hθ _ u _).le
      rwa [Function.update_eq_self] at this
    rw [hsucc]
    exact hstep.trans (ih hcs (by simp [i]))

/-- The ratio of a later to an earlier prefix mass lies in `(0, 1]`. -/
theorem ratio_mem {θ} (hθ : θ ∈ Θset 𝒱 ℬ) (o : Fin n) {t : Fin (n + 1)} (h : (o : ℕ) ≤ t)
    (u : Fin k → ℕ) (y : Fin n → ℕ) :
    0 < Gs δ s Δ θ t u y / Gs δ s Δ θ o.castSucc u y ∧
      Gs δ s Δ θ t u y / Gs δ s Δ θ o.castSucc u y ≤ 1 := by
  have h1 := Gs_pos' hδ hs Δ hv hℬ hθ t u y
  have h2 := Gs_pos' hδ hs Δ hv hℬ hθ o.castSucc u y
  exact ⟨div_pos h1 h2, (div_le_one h2).2 (Gs_anti hδ hs Δ hv hℬ hθ u y (Fin.le_def.2 (by simpa using h)))⟩

/-- `D^restart` is an attained maximum. -/
theorem Drs_greatest (h𝒱 : 𝒱.Nonempty) (o : Fin n) (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    ∃ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y / Gs δ s Δ θ o.castSucc u y = Drs δ s Δ 𝒱 ℬ o t u y ∧
      ∀ θ' ∈ Θset 𝒱 ℬ, Gs δ s Δ θ' t u y / Gs δ s Δ θ' o.castSucc u y ≤
        Gs δ s Δ θ t u y / Gs δ s Δ θ o.castSucc u y := by
  obtain ⟨θ, hθ, hG⟩ := exists_greatest h𝒱 hℬ
    (fun θ => Gs δ s Δ θ t u y / Gs δ s Δ θ o.castSucc u y) fun v hvv =>
      (Gs_contOn hδ hs Δ hv t u y v hvv).div (Gs_contOn hδ hs Δ hv o.castSucc u y v hvv)
        fun bw hbw => (Gs_pos hδ hs Δ (v, bw) (hv v hvv) hbw _ u y).ne'
  exact ⟨θ, hθ, hG.csSup_eq.symm, fun θ' hθ' => hG.2 ⟨θ', hθ', rfl⟩⟩

theorem Drs_props (h𝒱 : 𝒱.Nonempty) (o : Fin n) {t : Fin (n + 1)} (h : (o : ℕ) ≤ t) (u : Fin k → ℕ)
    (y : Fin n → ℕ) :
    0 < Drs δ s Δ 𝒱 ℬ o t u y ∧ Drs δ s Δ 𝒱 ℬ o t u y ≤ 1 ∧
      (∃ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y / Gs δ s Δ θ o.castSucc u y = Drs δ s Δ 𝒱 ℬ o t u y) ∧
      ∀ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y / Gs δ s Δ θ o.castSucc u y ≤ Drs δ s Δ 𝒱 ℬ o t u y := by
  obtain ⟨θ, hθ, he, hmax⟩ := Drs_greatest hδ hs Δ hv hℬ h𝒱 o t u y
  have hr := ratio_mem hδ hs Δ hv hℬ hθ o h u y
  exact ⟨he ▸ hr.1, he ▸ hr.2, ⟨θ, hθ, he⟩, fun θ' hθ' => he ▸ hmax θ' hθ'⟩

theorem Drs_anchor (h𝒱 : 𝒱.Nonempty) (o : Fin n) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    Drs δ s Δ 𝒱 ℬ o o.castSucc u y = 1 := by
  obtain ⟨θ, hθ, he, -⟩ := Drs_greatest hδ hs Δ hv hℬ h𝒱 o o.castSucc u y
  rw [← he, div_self (Gs_pos' hδ hs Δ hv hℬ hθ _ u y).ne']

end Mass

theorem Qr_nonneg {q : Fc k n} (hq : Forecast q) (o : Fin n) (t : Fin (n + 1)) (u : Fin k → ℕ)
    (y : Fin n → ℕ) : 0 ≤ Qr q o t u y :=
  Finset.prod_nonneg fun i _ => by split_ifs; exacts [hq.2.1 _ _ _ _, zero_le_one]

theorem Qr_agree {q : Fc k n} (hq : Forecast q) (o : Fin n) (t : Fin (n + 1)) (u : Fin k → ℕ)
    {y y' : Fin n → ℕ} (h : Agree (t : ℕ) y y') : Qr q o t u y = Qr q o t u y' := by
  unfold Qr
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [hq.1 i u y y' fun j hj => h j (hj.trans hi.2), h i hi.2]
  · rfl

theorem Drs_agree (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box) (o : Fin n)
    {t : Fin (n + 1)} (h : (o : ℕ) ≤ t) (u : Fin k → ℕ) {y y' : Fin n → ℕ} (hy : Agree (t : ℕ) y y') :
    Drs δ s Δ 𝒱 ℬ o t u y = Drs δ s Δ 𝒱 ℬ o t u y' := by
  unfold Drs
  congr 1
  refine Set.image_congr fun θ _ => ?_
  rw [Gs_agree δ s Δ θ t u hy, Gs_agree δ s Δ θ o.castSucc u (agree_mono (by simpa using h) hy)]

theorem Er_adapted (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    {q : Fc k n} (hq : Forecast q) (o : Fin n) : Adapted (Er δ s Δ 𝒱 ℬ q o) := fun t u y y' h => by
  unfold Er
  split_ifs with ho
  · rw [Qr_agree hq o t u h, Drs_agree δ s Δ 𝒱 ℬ o ho u h]
  · rfl

theorem Er_nonneg {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) {Δ : Fin (k + n) → ℝ}
    {𝒱 : Finset (Fin (k + n) → ℝ)} (hv : ∀ v ∈ 𝒱, ∀ j, 0 < v j) {ℬ : Box} (hℬ : ℬ.Valid)
    (h𝒱 : 𝒱.Nonempty) {q : Fc k n} (hq : Forecast q) (o : Fin n) (t : Fin (n + 1)) (u : Fin k → ℕ)
    (y : Fin n → ℕ) : 0 ≤ Er δ s Δ 𝒱 ℬ q o t u y := by
  unfold Er
  split_ifs with ho
  · exact div_nonneg (Qr_nonneg hq o t u y) (Drs_props hδ hs Δ hv hℬ h𝒱 o ho u y).1.le
  · exact zero_le_one

theorem le_scan (lam : Fin J → ℝ) (E : Fin J → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ)
    (r : Fin J) (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    lam r * E r t u y ≤ scan lam E t u y :=
  le_ciSup (f := fun r => lam r * E r t u y) (Set.finite_range _).bddAbove r

theorem scan_adapted (lam : Fin J → ℝ) {E : Fin J → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ}
    (hE : ∀ r, Adapted (E r)) : Adapted (scan lam E) := fun t u y y' h => by
  unfold scan
  exact iSup_congr fun r => by rw [hE r t u y y' h]

theorem scan_nonneg (hJ : 0 < J) {lam : Fin J → ℝ} (hlam : ∀ r, 0 < lam r)
    {E : Fin J → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ} (hE : ∀ r t u y, 0 ≤ E r t u y)
    (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) : 0 ≤ scan lam E t u y :=
  (mul_nonneg (hlam ⟨0, hJ⟩).le (hE _ t u y)).trans (le_scan lam E ⟨0, hJ⟩ t u y)

theorem scores_holds : Standalone.D22DeclaredRestarts.scores := by
  intro δ s k n J Δ 𝒱 ℬ o lam q hδ hs hΔ h𝒱 hv hℬ hD hq E
  obtain ⟨hJ, -, -, hlam, -⟩ := hD
  have hEr := fun r => Er_nonneg (Δ := Δ) hδ hs hv hℬ h𝒱 (hq r) (o r)
  refine ⟨fun r t u y ho => Drs_props hδ hs Δ hv hℬ h𝒱 (o r) ho u y,
    fun r u y => Drs_anchor hδ hs Δ hv hℬ h𝒱 (o r) u y,
    scan_nonneg hJ hlam hEr, scan_adapted lam fun r => Er_adapted δ s Δ 𝒱 ℬ (hq r) (o r),
    fun r => Er_adapted δ s Δ 𝒱 ℬ (hq r) (o r),
    fun r t u y => le_scan lam (fun r => Er δ s Δ 𝒱 ℬ (q r) (o r)) r t u y,
    fun r t u y hpos => ?_, fun r hr => ?_⟩
  · have hle := le_scan lam (fun r => Er δ s Δ 𝒱 ℬ (q r) (o r)) r t u y
    have hlp := mul_pos (hlam r) hpos
    have := Real.log_le_log hlp hle
    rw [Real.log_mul (hlam r).ne' hpos.ne'] at this
    show Real.log _ - Real.log (scan lam _ t u y) ≤ _
    linarith
  · rw [hr, one_div, Real.log_inv, neg_neg]

end Novel.D22DeclaredRestarts
