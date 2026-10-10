import Novel.D23JointSwitchesValid

/-!
# Claim 070, (9), (10) and the common shape multiplier

* A path with no pair change is constant, and claim 068's flattening makes its density claim 033's
  full-record density at that pair, so `P_joint(0) = P_common`.
* Larger budgets enlarge the family; every scale change is a pair change, so `P_joint ≤ P_sw`;
  every path has a free pair per day, so `P_sw ≤ P_day` (claim 068's joint supremum), with equality
  for `P_joint` at the full budget `D − 1`.
* A common multiplier `c` maps the family onto itself by `w ↦ w/c` (claim 033's `gV_scale`).
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23JointSwitches

open Standalone.D23JointSwitches Standalone.D23DailyProfile Standalone.D17ClockDrift
  Standalone.D13DriftNull Standalone.CEVSupport Novel.D17ClockDrift Novel.D23DailyProfile

variable {D : ℕ} {n : Fin D → ℕ} {Δ u : Fam n}

/-- A path with no pair change is constant. -/
theorem const_of_count_zero (hD : 0 < D) {b w : Fin D → ℝ} (h0 : countPair b w = 0) (d : Fin D) :
    b d = b ⟨0, hD⟩ ∧ w d = w ⟨0, hD⟩ := by
  rw [countPair_eq, Finset.card_eq_zero, chg, Finset.filter_eq_empty_iff] at h0
  rcases d with ⟨d, hd⟩
  induction d with
  | zero => exact ⟨rfl, rfl⟩
  | succ d ih =>
    have := h0 (Finset.mem_univ ⟨d + 1, hd⟩)
    push Not at this
    have hp := this (Nat.succ_pos d)
    simp only [Prod.mk.injEq] at hp
    obtain ⟨h1, h2⟩ := ih (by omega)
    exact ⟨hp.1.trans h1, hp.2.trans h2⟩

theorem countPair_le (b w : Fin D → ℝ) (hD : 0 < D) : countPair b w ≤ D - 1 := by
  rw [countPair_eq]
  calc (chg b w).card ≤ (Finset.univ.erase (⟨0, hD⟩ : Fin D)).card :=
        Finset.card_le_card fun d hd => Finset.mem_erase.2 ⟨fun h => by
          obtain ⟨h0, -⟩ := (Finset.mem_filter.1 hd).2; rw [h] at h0; exact lt_irrefl 0 h0,
          Finset.mem_univ _⟩
    _ = D - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

theorem countSw_le_countPair (b w : Fin D → ℝ) : countSw w ≤ countPair b w := by
  classical
  unfold countSw countPair
  refine Finset.card_le_card fun d hd => ?_
  obtain ⟨h0, hne⟩ := (Finset.mem_filter.1 hd).2
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h0, fun h => hne (congrArg Prod.snd h)⟩

section Nest

variable (hD : 0 < D) (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) (hu : ∀ d j, 0 < u d j)
  {s : ℝ} {y : Arr n} (hy : AllPos s y)
include hD hn hΔ hu hy

theorem Pcommon_eq : Pcommon Δ u s y = Pjoint Δ u 0 s y := by
  have hflat : ∀ b0 w0 : ℝ, G Δ u (fun _ => b0) (fun _ => w0) s y =
      ENNReal.ofReal (gV (flatR Δ) (flatR u) b0 w0 s (flatR (toR y))) := fun b0 w0 => by
    rw [gV_flat Δ (flatR u) b0 w0 hy hn, ENNReal.ofReal_prod_of_nonneg fun d _ => gV_nonneg _ _ _ _]
    unfold G
    simp only [restr_flatR]
  unfold Pcommon
  rw [← sup_eq (N_pos hD hn) (flatR_pos hΔ) (flatR_pos hu)]
  refine le_antisymm (iSup_le fun b0 => iSup_le fun w0 => iSup_le fun hw0 => ?_)
    (iSup_le fun b => iSup_le fun w => iSup_le fun hbw => ?_)
  · rw [← hflat]
    exact le_iSup₂_of_le (fun _ => b0) (fun _ => w0)
      (le_iSup_of_le ⟨fun _ => hw0, (countPair_const b0 w0).le⟩ le_rfl)
  · have hc := const_of_count_zero hD (Nat.le_zero.1 hbw.2)
    have hbw' : b = (fun _ => b ⟨0, hD⟩) ∧ w = (fun _ => w ⟨0, hD⟩) :=
      ⟨funext fun d => (hc d).1, funext fun d => (hc d).2⟩
    rw [hbw'.1, hbw'.2, hflat]
    exact le_iSup₂_of_le (b ⟨0, hD⟩) (w ⟨0, hD⟩) (le_iSup_of_le (hbw.1 _) le_rfl)

omit hD hn hΔ hu hy in
theorem Pjoint_mono {K K' : ℕ} (hK : K ≤ K') (s : ℝ) (y : Arr n) :
    Pjoint Δ u K s y ≤ Pjoint Δ u K' s y :=
  iSup₂_mono fun _ _ => iSup_le fun hbw => le_iSup_of_le ⟨hbw.1, hbw.2.trans hK⟩ le_rfl

omit hD hn hΔ hu hy in
theorem Pjoint_le_Psw (K : ℕ) (s : ℝ) (y : Arr n) : Pjoint Δ u K s y ≤ Psw Δ u K s y :=
  iSup₂_mono fun b w => iSup_le fun hbw =>
    le_iSup_of_le ⟨hbw.1, (countSw_le_countPair b w).trans hbw.2⟩ le_rfl

omit hD hy in
theorem Psw_le_Pday (K : ℕ) (s : ℝ) (y : Arr n) : Psw Δ u K s y ≤ Pday (fun d => {u d}) Δ s y :=
  iSup₂_le fun b w => iSup_le fun hbw =>
    jointG_le hn hΔ (fun d v hv => by rw [Finset.mem_singleton.1 hv]; exact hu d)
      (fun d => (u d, b d, w d)) fun d => ⟨Finset.mem_singleton_self _, hbw.1 d⟩

theorem Pjoint_full : Pjoint Δ u (D - 1) s y = Pday (fun d => {u d}) Δ s y := by
  refine le_antisymm ((Pjoint_le_Psw _ s y).trans (Psw_le_Pday hn hΔ hu _ s y)) ?_
  rw [← jointSup_eq hn hΔ (fun d => Finset.singleton_nonempty _)
    (fun d v hv => by rw [Finset.mem_singleton.1 hv]; exact hu d) hy]
  refine iSup₂_le fun ch hch => ?_
  have hu' : ∀ d, (ch d).1 = u d := fun d => Finset.mem_singleton.1 (hch d).1
  have : jointG Δ ch s y = G Δ u (fun d => (ch d).2.1) (fun d => (ch d).2.2) s y := by
    unfold jointG G; simp only [hu']
  rw [this]
  exact le_iSup₂_of_le _ _ (le_iSup_of_le ⟨fun d => (hch d).2, countPair_le _ _ hD⟩ le_rfl)

end Nest

theorem countPair_div {c : ℝ} (hc : 0 < c) (b w : Fin D → ℝ) :
    countPair b (fun d => w d / c) = countPair b w := by
  classical
  unfold countPair
  congr 1
  refine Finset.filter_congr fun d _ => ?_
  refine exists_congr fun _ => ?_
  simp only [ne_eq, Prod.mk.injEq, div_left_inj' hc.ne']

theorem G_scale {c : ℝ} (hc : 0 < c) (b w : Fin D → ℝ) (s : ℝ) (y : Arr n) :
    G Δ (fun d => c • u d) b (fun d => w d / c) s y = G Δ u b w s y := by
  unfold G
  exact Finset.prod_congr rfl fun d _ => by rw [gV_scale hc]

theorem Pjoint_scale {c : ℝ} (hc : 0 < c) (K : ℕ) (s : ℝ) (y : Arr n) :
    Pjoint Δ (fun d => c • u d) K s y = Pjoint Δ u K s y := by
  refine le_antisymm (iSup_le fun b => iSup_le fun w => iSup_le fun hbw => ?_)
    (iSup_le fun b => iSup_le fun w => iSup_le fun hbw => ?_)
  · have hG := G_scale (Δ := Δ) (u := u) hc b (fun d => c * w d) s y
    simp only [mul_div_cancel_left₀ _ hc.ne'] at hG
    rw [hG]
    refine le_iSup₂_of_le b (fun d => c * w d) (le_iSup_of_le ⟨fun d => mul_pos hc (hbw.1 d), ?_⟩ le_rfl)
    have := countPair_div hc b (fun d => c * w d)
    simp only [mul_div_cancel_left₀ _ hc.ne'] at this
    rw [← this]; exact hbw.2
  · rw [← G_scale hc b w s y]
    exact le_iSup₂_of_le b (fun d => w d / c) (le_iSup_of_le ⟨fun d => div_pos (hbw.1 d) hc,
      (countPair_div hc b w).symm ▸ hbw.2⟩ le_rfl)

theorem Escore_anti {P P' : ℝ≥0∞} (h : P ≤ P') (s q : ℝ) (y : Arr n) :
    Escore P' s q y ≤ Escore P s q y := by
  unfold Escore
  split_ifs
  · exact ENNReal.div_le_div_left h _
  · exact le_rfl

theorem nesting_holds : Standalone.D23JointSwitches.nesting := by
  intro D n Δ u hD hn hΔ hu s y hy
  have hc := Pcommon_eq hD hn hΔ hu hy
  have hmono := fun K K' (h : K ≤ K') => Pjoint_mono (Δ := Δ) (u := u) h s y
  refine ⟨hc, fun K K' h => hmono K K' h, fun K => Pjoint_le_Psw K s y,
    fun K => Psw_le_Pday hn hΔ hu K s y, Pjoint_full hD hn hΔ hu hy,
    fun K K' q hK => ⟨Escore_anti (hmono K K' hK) s q y, Escore_anti (Pjoint_le_Psw K s y) s q y,
      Escore_anti (hc ▸ hmono 0 K (Nat.zero_le K)) s q y⟩, fun K q hfin => ?_,
    fun c K hc' => Pjoint_scale hc' K s y⟩
  -- (10).
  have hle : Pcommon Δ u s y ≤ Pjoint Δ u K s y := hc ▸ hmono 0 K (Nat.zero_le K)
  have hcpos : 0 < Pcommon Δ u s y := by
    rw [hc]; exact ((budget_holds D n Δ u hD hn hΔ hu 0).2 s y hy).1
  have hcfin : Pcommon Δ u s y < ⊤ := lt_of_le_of_lt hle hfin
  set a := (Pjoint Δ u K s y).toReal
  set c := (Pcommon Δ u s y).toReal
  have ha : 0 < a := ENNReal.toReal_pos (hcpos.trans_le hle).ne' hfin.ne
  have hc0 : 0 < c := ENNReal.toReal_pos hcpos.ne' hcfin.ne
  have hca : c ≤ a := ENNReal.toReal_mono hfin.ne hle
  have hPa : Pjoint Δ u K s y = ENNReal.ofReal a := (ENNReal.ofReal_toReal hfin.ne).symm
  have hPc : Pcommon Δ u s y = ENNReal.ofReal c := (ENNReal.ofReal_toReal hcfin.ne).symm
  refine ⟨?_, sub_nonneg.2 (Real.log_le_log hc0 hca)⟩
  unfold Escore
  simp only [hy, ↓reduceIte]
  rw [neg_sub, Real.exp_sub, Real.exp_log hc0, Real.exp_log ha, hPa, hPc,
    ← ENNReal.ofReal_div_of_pos ha, ← ENNReal.ofReal_div_of_pos hc0,
    ← ENNReal.ofReal_mul' (div_nonneg hc0.le ha.le)]
  congr 1
  field_simp

end Novel.D23JointSwitches
