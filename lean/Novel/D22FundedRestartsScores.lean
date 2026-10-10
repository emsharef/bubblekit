import Standalone.D22FundedRestarts
import Novel.D22DeclaredRestartsProof

/-!
# Claim 041: the slot scores, the total evidence and part 2

* From a launch `σ` on, `G_(θ,t)/G_(θ,σ) ∈ (0, 1]` (claim 040's `Gs_anti`), and the maximum over the
  compact family is attained, so `D^fund ∈ (0, 1]`, equal to one at launch.
* Once launched, a slot's date and allocation are fixed by the labels before it, so the total
  evidence is adapted. Its unused capital lies in `[0, 1]` by (1).
* Part 2 is bookkeeping: each launched term is one nonnegative summand of `C_t`, and extending
  unlaunched scores as one replaces their unspent allocations exactly.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Novel.D22FundedRestarts

open Standalone.D22FundedRestarts Standalone.D22DeclaredRestarts Standalone.D22FilteredSequential
  Standalone.D19FilteredLikelihood Standalone.D17ClockCells Novel.D22FilteredSequential
  Novel.D22DeclaredRestarts

variable {k n J : ℕ}

section Mass

variable {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ : Fin (k + n) → ℝ) {𝒱 : Finset (Fin (k + n) → ℝ)}
  (hv : ∀ v ∈ 𝒱, ∀ j, 0 < v j) {ℬ : Box} (hℬ : ℬ.Valid)
include hδ hs hv hℬ

theorem Df_greatest (h𝒱 : 𝒱.Nonempty) (σ t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    ∃ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y / Gs δ s Δ θ σ u y = Df δ s Δ 𝒱 ℬ σ t u y ∧
      ∀ θ' ∈ Θset 𝒱 ℬ, Gs δ s Δ θ' t u y / Gs δ s Δ θ' σ u y ≤
        Gs δ s Δ θ t u y / Gs δ s Δ θ σ u y := by
  obtain ⟨θ, hθ, hG⟩ := exists_greatest h𝒱 hℬ
    (fun θ => Gs δ s Δ θ t u y / Gs δ s Δ θ σ u y) fun v hvv =>
      (Gs_contOn hδ hs Δ hv t u y v hvv).div (Gs_contOn hδ hs Δ hv σ u y v hvv)
        fun bw hbw => (Gs_pos hδ hs Δ (v, bw) (hv v hvv) hbw _ u y).ne'
  exact ⟨θ, hθ, hG.csSup_eq.symm, fun θ' hθ' => hG.2 ⟨θ', hθ', rfl⟩⟩

theorem Df_props (h𝒱 : 𝒱.Nonempty) {σ t : Fin (n + 1)} (h : σ ≤ t) (u : Fin k → ℕ)
    (y : Fin n → ℕ) :
    0 < Df δ s Δ 𝒱 ℬ σ t u y ∧ Df δ s Δ 𝒱 ℬ σ t u y ≤ 1 ∧
      (∃ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y / Gs δ s Δ θ σ u y = Df δ s Δ 𝒱 ℬ σ t u y) ∧
      ∀ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y / Gs δ s Δ θ σ u y ≤ Df δ s Δ 𝒱 ℬ σ t u y := by
  obtain ⟨θ, hθ, he, hmax⟩ := Df_greatest hδ hs Δ hv hℬ h𝒱 σ t u y
  have h1 := Gs_pos' hδ hs Δ hv hℬ hθ t u y
  have h2 := Gs_pos' hδ hs Δ hv hℬ hθ σ u y
  refine ⟨he ▸ div_pos h1 h2, he ▸ (div_le_one h2).2 (Gs_anti hδ hs Δ hv hℬ hθ u y h),
    ⟨θ, hθ, he⟩, fun θ' hθ' => he ▸ hmax θ' hθ'⟩

theorem Df_self (h𝒱 : 𝒱.Nonempty) (σ : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    Df δ s Δ 𝒱 ℬ σ σ u y = 1 := by
  obtain ⟨θ, hθ, he, -⟩ := Df_greatest hδ hs Δ hv hℬ h𝒱 σ σ u y
  rw [← he, div_self (Gs_pos' hδ hs Δ hv hℬ hθ _ u y).ne']

end Mass

theorem Qf_self (q : Fc k n) (σ : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    Qf q σ σ u y = 1 :=
  Finset.prod_eq_one fun i _ => by rw [if_neg (by omega)]

theorem Qf_nonneg {q : Fc k n} (hq : Forecast q) (σ t : Fin (n + 1)) (u : Fin k → ℕ)
    (y : Fin n → ℕ) : 0 ≤ Qf q σ t u y :=
  Finset.prod_nonneg fun i _ => by split_ifs; exacts [hq.2.1 _ _ _ _, zero_le_one]

theorem Qf_agree {q : Fc k n} (hq : Forecast q) (σ t : Fin (n + 1)) (u : Fin k → ℕ)
    {y y' : Fin n → ℕ} (h : Agree (t : ℕ) y y') : Qf q σ t u y = Qf q σ t u y' := by
  unfold Qf
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [hq.1 i u y y' fun j hj => h j (hj.trans hi.2), h i hi.2]
  · rfl

theorem Df_agree (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    {σ t : Fin (n + 1)} (h : σ ≤ t) (u : Fin k → ℕ) {y y' : Fin n → ℕ} (hy : Agree (t : ℕ) y y') :
    Df δ s Δ 𝒱 ℬ σ t u y = Df δ s Δ 𝒱 ℬ σ t u y' := by
  unfold Df
  congr 1
  refine Set.image_congr fun θ _ => ?_
  rw [Gs_agree δ s Δ θ t u hy, Gs_agree δ s Δ θ σ u (agree_mono (Fin.le_def.1 h) hy)]

/-! ### Launch bookkeeping -/

section Policy

variable {σ : Launch J k n} {lam : Alloc J k n} (hP : Policy σ lam)
include hP

/-- A slot launched by `t` has the same date and allocation on records agreeing before `t`. -/
theorem launched_agree (r : Fin J) {t : Fin (n + 1)} {u : Fin k → ℕ} {y y' : Fin n → ℕ}
    (h : Agree (t : ℕ) y y') (hl : σ r u y ≤ t) : σ r u y' = σ r u y ∧ lam r u y' = lam r u y := by
  have ha : Agree (σ r u y : ℕ) y y' := agree_mono (Fin.le_def.1 hl) h
  exact ⟨hP.1 r u y y' ha, (hP.2.1 r u y y' ha).symm⟩

theorem launched_iff (r : Fin J) {t : Fin (n + 1)} {u : Fin k → ℕ} {y y' : Fin n → ℕ}
    (h : Agree (t : ℕ) y y') : σ r u y ≤ t ↔ σ r u y' ≤ t :=
  ⟨fun hl => (launched_agree hP r h hl).1 ▸ hl,
    fun hl => (launched_agree hP r (agree_symm h) hl).1 ▸ hl⟩

theorem Rfund_bounds (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    0 ≤ Rfund σ lam t u y ∧ Rfund σ lam t u y ≤ 1 := by
  have h0 : ∀ r, 0 ≤ (if σ r u y ≤ t then lam r u y else 0) := fun r => by
    split_ifs; exacts [hP.2.2.1 r u y, le_rfl]
  have hle : ∑ r, (if σ r u y ≤ t then lam r u y else 0) ≤ ∑ r, lam r u y :=
    Finset.sum_le_sum fun r _ => by split_ifs; exacts [le_rfl, hP.2.2.1 r u y]
  unfold Rfund
  exact ⟨by linarith [hP.2.2.2 u y], by linarith [Finset.sum_nonneg fun r (_ : r ∈ Finset.univ) => h0 r]⟩

theorem Rfund_agree {t : Fin (n + 1)} (u : Fin k → ℕ) {y y' : Fin n → ℕ} (h : Agree (t : ℕ) y y') :
    Rfund σ lam t u y = Rfund σ lam t u y' := by
  unfold Rfund
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hl : σ r u y ≤ t
  · rw [if_pos hl, if_pos ((launched_iff hP r h).1 hl), (launched_agree hP r h hl).2]
  · rw [if_neg hl, if_neg fun h' => hl ((launched_iff hP r h).2 h')]

/-- The total evidence is adapted when every slot score is, from its launch on. -/
theorem Ctot_adapted {E : Fin J → Fin (n + 1) → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ}
    (hE : ∀ r (σ₀ t : Fin (n + 1)) u y y', σ₀ ≤ t → Agree (t : ℕ) y y' →
      E r σ₀ t u y = E r σ₀ t u y') : Adapted (Ctot σ lam E) := fun t u y y' h => by
  unfold Ctot
  rw [Rfund_agree hP u h]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hl : σ r u y ≤ t
  · obtain ⟨h1, h2⟩ := launched_agree hP r h hl
    rw [if_pos hl, if_pos ((launched_iff hP r h).1 hl), h1, h2, hE r _ t u y y' hl h]
  · rw [if_neg hl, if_neg fun h' => hl ((launched_iff hP r h).2 h')]

theorem Ctot_nonneg {E : Fin J → Fin (n + 1) → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ}
    (hE : ∀ r (σ₀ t : Fin (n + 1)) u y, σ₀ ≤ t → 0 ≤ E r σ₀ t u y) (t : Fin (n + 1))
    (u : Fin k → ℕ) (y : Fin n → ℕ) : 0 ≤ Ctot σ lam E t u y :=
  add_nonneg (Rfund_bounds hP t u y).1 (Finset.sum_nonneg fun r _ => by
    split_ifs with hl
    · exact mul_nonneg (hP.2.2.1 r u y) (hE r _ t u y hl)
    · exact le_rfl)

theorem le_Ctot {E : Fin J → Fin (n + 1) → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ}
    (hE : ∀ r (σ₀ t : Fin (n + 1)) u y, σ₀ ≤ t → 0 ≤ E r σ₀ t u y) (r : Fin J) (t : Fin (n + 1))
    (u : Fin k → ℕ) (y : Fin n → ℕ) (hl : σ r u y ≤ t) :
    lam r u y * E r (σ r u y) t u y ≤ Ctot σ lam E t u y := by
  have hsum := Finset.single_le_sum (f := fun r => if σ r u y ≤ t then lam r u y * E r (σ r u y) t u y
    else 0) (fun r _ => by
      split_ifs with hl'
      · exact mul_nonneg (hP.2.2.1 r u y) (hE r _ t u y hl')
      · exact le_rfl) (Finset.mem_univ r)
  simp only [if_pos hl] at hsum
  unfold Ctot
  linarith [(Rfund_bounds hP t u y).1]

/-- (5)'s identity: unlaunched scores extended as one replace their unspent allocations. -/
theorem Ctot_eq (E : Fin J → Fin (n + 1) → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ)
    (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    Ctot σ lam E t u y = 1 - ∑ r, lam r u y + ∑ r, lam r u y *
      (if σ r u y ≤ t then E r (σ r u y) t u y else 1) := by
  unfold Ctot Rfund
  have h : ∀ r, lam r u y * (if σ r u y ≤ t then E r (σ r u y) t u y else 1) =
      (if σ r u y ≤ t then lam r u y * E r (σ r u y) t u y else 0) +
        (lam r u y - if σ r u y ≤ t then lam r u y else 0) := fun r => by
    split_ifs <;> ring
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem Ctot_zero {E : Fin J → Fin (n + 1) → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ}
    (hE : ∀ r (σ₀ : Fin (n + 1)) u y, E r σ₀ σ₀ u y = 1) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    Ctot σ lam E 0 u y = 1 := by
  rw [Ctot_eq hP]
  have h : ∀ r, lam r u y * (if σ r u y ≤ 0 then E r (σ r u y) 0 u y else 1) = lam r u y :=
    fun r => by
      split_ifs with hl
      · have : σ r u y = 0 := le_antisymm hl (Fin.zero_le _)
        rw [this, hE, mul_one]
      · rw [mul_one]
  simp_rw [h]
  ring

end Policy

theorem scores_holds : Standalone.D22FundedRestarts.scores := by
  intro δ s k n J Δ 𝒱 ℬ q σ lam hM hP hq C
  obtain ⟨hδ, hs, _, h𝒱, hv, hℬ⟩ := hM
  have hEnn : ∀ r (σ₀ t : Fin (n + 1)) u y, σ₀ ≤ t → 0 ≤ Ef δ s Δ 𝒱 ℬ (q r) σ₀ t u y :=
    fun r σ₀ t u y h => div_nonneg (Qf_nonneg (hq r) σ₀ t u y)
      (Df_props hδ hs Δ hv hℬ h𝒱 h u y).1.le
  have hEself : ∀ r (σ₀ : Fin (n + 1)) u y, Ef δ s Δ 𝒱 ℬ (q r) σ₀ σ₀ u y = 1 := fun r σ₀ u y => by
    unfold Ef; rw [Qf_self, Df_self hδ hs Δ hv hℬ h𝒱, div_one]
  have hC0 : ∀ t u y, 0 ≤ C t u y := Ctot_nonneg hP hEnn
  refine ⟨fun σ₀ t u y h => Df_props hδ hs Δ hv hℬ h𝒱 h u y, hEself, hEnn,
    Rfund_bounds hP, hC0,
    Ctot_adapted hP fun r σ₀ t u y y' h hy => by
      unfold Ef; rw [Qf_agree (hq r) σ₀ t u hy, Df_agree δ s Δ 𝒱 ℬ h u hy],
    Ctot_zero hP hEself, fun r t u y hl => le_Ctot hP hEnn r t u y hl,
    fun r t u y hl hlam hE => ?_, fun r t u y α hl hlam hα hE => ?_, Ctot_eq hP _,
    fun o lam₀ hσ hlam t u y => ?_⟩
  · -- The log form.
    rw [← Real.log_mul hE.ne' hlam.ne', mul_comm]
    exact Real.log_le_log (mul_pos hlam hE) (le_Ctot hP hEnn r t u y hl)
  · -- The threshold `1/(αλ_r)`.
    refine le_trans ?_ (le_Ctot hP hEnn r t u y hl)
    calc 1 / α = lam r u y * (1 / (α * lam r u y)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hE hlam.le
  · -- (5) against claim 040.
    have hEr : ∀ r, (if σ r u y ≤ t then Ef δ s Δ 𝒱 ℬ (q r) (σ r u y) t u y else 1) =
        Er δ s Δ 𝒱 ℬ (q r) (o r) t u y := fun r => by
      rw [hσ r u y]
      unfold Er Ef
      simp only [Fin.le_def, Fin.val_castSucc]
      rfl
    have hid : C t u y = 1 - ∑ r, lam₀ r + ∑ r, lam₀ r * Er δ s Δ 𝒱 ℬ (q r) (o r) t u y := by
      rw [show C t u y = _ from Ctot_eq hP _ t u y]
      simp_rw [hlam, hEr]
    refine ⟨hid, Real.iSup_le (fun r => ?_) (hC0 t u y)⟩
    have hsum : ∑ r, lam r u y ≤ 1 := hP.2.2.2 u y
    simp_rw [hlam] at hsum
    have hnn : ∀ r', 0 ≤ lam₀ r' * Er δ s Δ 𝒱 ℬ (q r') (o r') t u y := fun r' =>
      mul_nonneg (hlam r' u y ▸ hP.2.2.1 r' u y) (Er_nonneg hδ hs hv hℬ h𝒱 (hq r') (o r') t u y)
    have := Finset.single_le_sum (fun r' (_ : r' ∈ Finset.univ) => hnn r') (Finset.mem_univ r)
    rw [hid]
    linarith

end Novel.D22FundedRestarts
