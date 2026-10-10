import Novel.D23ScaleSwitchesValid

/-!
# Claim 069, (7), the common shape multiplier and the catalogue comparison

* `P_common = P_joint(0) ≤ P_sw(0)` (claim 070: a constant pair path has no scale change); larger
  budgets enlarge the family; every path has a free pair per day, so `P_sw ≤ P_day`, with equality at
  `D − 1` because claim 070's `P_joint(D − 1) = P_day` and `P_joint ≤ P_sw`.
* A common multiplier `c` maps the family onto itself by `w ↦ w/c`, which preserves each equality
  `w_d = w_(d−1)` (claim 033's `gV_scale`).
* For a catalogue, the largest budget gives `max_u Π_d P_(d,u)`, at most `Π_d max_u P_(d,u)`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23ScaleSwitches

open Standalone.D23ScaleSwitches Standalone.D23JointSwitches Standalone.D23DailyProfile
  Standalone.D17ClockDrift Standalone.D13DriftNull Standalone.CEVSupport Novel.D17ClockDrift
  Novel.D23DailyProfile Novel.D23JointSwitches

variable {D : ℕ} {n : Fin D → ℕ} {Δ u : Fam n}

theorem Psw_mono {K K' : ℕ} (hK : K ≤ K') (s : ℝ) (y : Arr n) :
    Psw Δ u K s y ≤ Psw Δ u K' s y :=
  iSup₂_mono fun _ _ => iSup_le fun hbw => le_iSup_of_le ⟨hbw.1, hbw.2.trans hK⟩ le_rfl

theorem countSw_div {c : ℝ} (hc : 0 < c) (w : Fin D → ℝ) :
    countSw (fun d => w d / c) = countSw w := by
  classical
  unfold countSw
  congr 1
  refine Finset.filter_congr fun d _ => exists_congr fun _ => ?_
  simp only [ne_eq, div_left_inj' hc.ne']

theorem Psw_scale {c : ℝ} (hc : 0 < c) (K : ℕ) (s : ℝ) (y : Arr n) :
    Psw Δ (fun d => c • u d) K s y = Psw Δ u K s y := by
  refine le_antisymm (iSup_le fun b => iSup_le fun w => iSup_le fun hbw => ?_)
    (iSup_le fun b => iSup_le fun w => iSup_le fun hbw => ?_)
  · have hG := G_scale (Δ := Δ) (u := u) hc b (fun d => c * w d) s y
    simp only [mul_div_cancel_left₀ _ hc.ne'] at hG
    rw [hG]
    refine le_iSup₂_of_le b (fun d => c * w d) (le_iSup_of_le ⟨fun d => mul_pos hc (hbw.1 d), ?_⟩ le_rfl)
    have := countSw_div hc (fun d => c * w d)
    simp only [mul_div_cancel_left₀ _ hc.ne'] at this
    rw [← this]; exact hbw.2
  · rw [← G_scale hc b w s y]
    exact le_iSup₂_of_le b (fun d => w d / c) (le_iSup_of_le ⟨fun d => div_pos (hbw.1 d) hc,
      (countSw_div hc w).symm ▸ hbw.2⟩ le_rfl)

section Nest

variable (hD : 0 < D) (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) (hu : ∀ d j, 0 < u d j)
  {s : ℝ} {y : Arr n} (hy : AllPos s y)
include hD hn hΔ hu hy

theorem Pcommon_le_Psw : Pcommon Δ u s y ≤ Psw Δ u 0 s y := by
  rw [Pcommon_eq hD hn hΔ hu hy]; exact Pjoint_le_Psw 0 s y

theorem Psw_full : Psw Δ u (D - 1) s y = Pday (fun d => {u d}) Δ s y :=
  le_antisymm (Psw_le_Pday hn hΔ hu _ s y)
    ((Pjoint_full hD hn hΔ hu hy).symm ▸ Pjoint_le_Psw (D - 1) s y)

end Nest

theorem nesting_holds : Standalone.D23ScaleSwitches.nesting := by
  intro D n Δ u hD hn hΔ hu s y hy
  have hc := Pcommon_le_Psw hD hn hΔ hu hy
  have hday := fun K => Psw_le_Pday (Δ := Δ) (u := u) hn hΔ hu K s y
  refine ⟨hc, fun K K' h => Psw_mono h s y, hday, Psw_full hD hn hΔ hu hy,
    fun K K' q hK => ⟨Escore_anti (Psw_mono hK s y) s q y,
      Escore_anti (hc.trans (Psw_mono (Nat.zero_le K) s y)) s q y, Escore_anti (hday K) s q y⟩,
    fun c K hc' => Psw_scale hc' K s y⟩

theorem catalogue_holds : Standalone.D23ScaleSwitches.catalogue := by
  intro D n Δ 𝒰 hD hn hΔ hu s y hy
  refine ⟨fun K K' hK => Finset.sup_mono_fun fun u _ => Psw_mono hK s y,
    Finset.sup_congr rfl fun u hu𝒰 => ?_, Finset.sup_le fun u hu𝒰 => ?_⟩
  · rw [Psw_full hD hn hΔ (hu u hu𝒰) hy]
    unfold Pday Pd
    simp only [Finset.sup_singleton]
  · unfold Pday Pd
    exact Finset.prod_le_prod fun d _ =>
      Finset.le_sup (f := fun v => Dv (Δ d) v (start s y d) (toR y d))
        (Finset.mem_image_of_mem (fun u : Fam n => u d) hu𝒰)

end Novel.D23ScaleSwitches
