import Novel.D23DailyProfileFlat

/-!
# Claim 068, part 1: the separable daily profile

Each block's profile is claim 033's closed form at the block's start. Block parameters are free, so
the joint supremum of the product is the product of the block maxima: off the singular set every
block maximum is attained (claim 033's unique optimizer) and so is the product; a singular block's
supremum is infinite, and with admissible positive densities fixed in the other blocks the product is
unbounded (`jointSup_eq`).
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23DailyProfile

open Standalone.D23DailyProfile Standalone.D17ClockDrift Standalone.D13DriftNull Standalone.CEVSupport
  Novel.D17ClockDrift

variable {D : ℕ} {n : Fin D → ℕ} {Δ : (d : Fin D) → Fin (n d) → ℝ}
  {𝒰 : (d : Fin D) → Finset (Fin (n d) → ℝ)}

section Block

variable {m : ℕ} {Δ₁ v : Fin m → ℝ}

theorem gV_pos (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin m → ℝ} (hp : PosPath y0 y) (b : ℝ) {w : ℝ}
    (hw : 0 < w) : 0 < gV Δ₁ v b w y0 y := by
  rw [gV_eq hv hp b hw]; exact Real.exp_pos _

theorem Dv_pos (hm : 0 < m) (hΔ : ∀ j, 0 < Δ₁ j) (hv : ∀ j, 0 < v j) {y0 : ℝ} {y : Fin m → ℝ}
    (hp : PosPath y0 y) : 0 < Dv Δ₁ v y0 y := by
  rw [← sup_eq hm hΔ hv y0 y]
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (gV_pos (Δ₁ := Δ₁) hv hp 0 one_pos))
    (le_iSup₂_of_le (0 : ℝ) (1 : ℝ) (le_iSup_of_le one_pos le_rfl))

theorem gV_le_Dv (hm : 0 < m) (hΔ : ∀ j, 0 < Δ₁ j) (hv : ∀ j, 0 < v j) (b : ℝ) {w : ℝ} (hw : 0 < w)
    (y0 : ℝ) (y : Fin m → ℝ) : ENNReal.ofReal (gV Δ₁ v b w y0 y) ≤ Dv Δ₁ v y0 y := by
  rw [← sup_eq hm hΔ hv y0 y]
  exact le_iSup₂_of_le b w (le_iSup_of_le hw le_rfl)

theorem Dv_fin {y0 : ℝ} {y : Fin m → ℝ}
    (hp : PosPath y0 y) (hQ : 0 < Qv Δ₁ v y0 y) :
    Dv Δ₁ v y0 y = ENNReal.ofReal (Real.exp (logDv Δ₁ v y0 y)) := by
  unfold Dv; simp only [hp, hQ, ↓reduceIte]

theorem Dv_top {y0 : ℝ} {y : Fin m → ℝ}
    (hp : PosPath y0 y) (hQ : Qv Δ₁ v y0 y = 0) : Dv Δ₁ v y0 y = ⊤ := by
  unfold Dv; simp only [hp, hQ, lt_irrefl, ↓reduceIte]

end Block

variable (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) (h𝒰 : ∀ d, (𝒰 d).Nonempty)
  (hu : ∀ d, ∀ u ∈ 𝒰 d, ∀ j, 0 < u j)
include hn hΔ hu

theorem Qd_pos_iff (s : ℝ) (y : Arr n) (d : Fin D) {u : Fin (n d) → ℝ}
    (hud : u ∈ 𝒰 d) : 0 < Qv (Δ d) u (start s y d) (toR y d) ↔ ¬ Sing Δ s y d := by
  have hiff := Qv_zero_iff (hn d) (hΔ d) (hu d u hud) (start s y d) (toR y d)
  have h0 := Qv_nonneg (hn d) (hΔ d) (hu d u hud) (start s y d) (toR y d)
  unfold Sing
  rw [← hiff]
  constructor
  · intro h h'; rw [h'] at h; exact lt_irrefl _ h
  · intro h; exact lt_of_le_of_ne h0 (Ne.symm h)

include h𝒰 in
theorem Pd_pos {s : ℝ} {y : Arr n} (hy : AllPos s y) (d : Fin D) : 0 < Pd 𝒰 Δ s y d := by
  obtain ⟨u, hud⟩ := h𝒰 d
  exact lt_of_lt_of_le (Dv_pos (hn d) (hΔ d) (hu d u hud) (posPath_block hy hn d))
    (Finset.le_sup (f := fun u => Dv (Δ d) u (start s y d) (toR y d)) hud)

include h𝒰 in
theorem Pday_pos {s : ℝ} {y : Arr n} (hy : AllPos s y) : 0 < Pday 𝒰 Δ s y := by
  unfold Pday
  exact pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun d _ => (Pd_pos hn hΔ h𝒰 hu hy d).ne')

theorem jointG_le {s : ℝ} {y : Arr n} (ch : (d : Fin D) → (Fin (n d) → ℝ) × ℝ × ℝ)
    (hch : ∀ d, (ch d).1 ∈ 𝒰 d ∧ 0 < (ch d).2.2) : jointG Δ ch s y ≤ Pday 𝒰 Δ s y :=
  Finset.prod_le_prod fun d _ =>
    (gV_le_Dv (hn d) (hΔ d) (hu d _ (hch d).1) _ (hch d).2 _ _).trans
      (Finset.le_sup (f := fun u => Dv (Δ d) u (start s y d) (toR y d)) (hch d).1)

include h𝒰 in
/-- Off the singular set every block maximum is attained, and so is the product. -/
theorem attained {s : ℝ} {y : Arr n} (hy : AllPos s y) (hns : ∀ d, ¬ Sing Δ s y d) :
    ∃ ch : (d : Fin D) → (Fin (n d) → ℝ) × ℝ × ℝ, (∀ d, (ch d).1 ∈ 𝒰 d ∧ 0 < (ch d).2.2) ∧
      jointG Δ ch s y = Pday 𝒰 Δ s y := by
  have hmax : ∀ d, ∃ u ∈ 𝒰 d, Pd 𝒰 Δ s y d = Dv (Δ d) u (start s y d) (toR y d) := fun d =>
    Finset.exists_mem_eq_sup _ (h𝒰 d) _
  choose U hU hUe using hmax
  have hp := posPath_block hy hn
  have hQ : ∀ d, 0 < Qv (Δ d) (U d) (start s y d) (toR y d) := fun d =>
    (Qd_pos_iff hn hΔ hu s y d (hU d)).2 (hns d)
  refine ⟨fun d => (U d, bstar (Δ d) (U d) (start s y d) (toR y d),
    wstar (Δ d) (U d) (start s y d) (toR y d)), fun d => ⟨hU d, wstar_pos (hn d) (hQ d)⟩, ?_⟩
  unfold jointG Pday
  refine Finset.prod_congr rfl fun d _ => ?_
  rw [hUe d, Dv_fin (hp d) (hQ d),
    gV_attain (hn d) (hΔ d) (hu d _ (hU d)) (hp d) (hQ d)]

include h𝒰 in
/-- A singular block makes every profile of the block and `P_day` infinite. -/
theorem singular_top {s : ℝ} {y : Arr n} (hy : AllPos s y) {d₀ : Fin D} (hd : Sing Δ s y d₀) :
    (∀ u ∈ 𝒰 d₀, Dv (Δ d₀) u (start s y d₀) (toR y d₀) = ⊤) ∧ Pday 𝒰 Δ s y = ⊤ := by
  have hp := posPath_block hy hn
  have htop : ∀ u ∈ 𝒰 d₀, Dv (Δ d₀) u (start s y d₀) (toR y d₀) = ⊤ := fun u hud => by
    have h := (Qd_pos_iff hn hΔ hu s y d₀ hud).not.2 (not_not.2 hd)
    exact Dv_top (hp d₀)
      (le_antisymm (not_lt.1 h) (Qv_nonneg (hn d₀) (hΔ d₀) (hu d₀ u hud) _ _))
  refine ⟨htop, ?_⟩
  obtain ⟨u, hud⟩ := h𝒰 d₀
  have hP0 : Pd 𝒰 Δ s y d₀ = ⊤ :=
    top_unique ((htop u hud).symm.le.trans
      (Finset.le_sup (f := fun u => Dv (Δ d₀) u (start s y d₀) (toR y d₀)) hud))
  unfold Pday
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ d₀), hP0, ENNReal.top_mul]
  exact Finset.prod_ne_zero_iff.2 fun d _ => (Pd_pos hn hΔ h𝒰 hu hy d).ne'

include h𝒰 in
/-- The joint supremum over independent daily choices is `P_day`. -/
theorem jointSup_eq {s : ℝ} {y : Arr n} (hy : AllPos s y) :
    (⨆ (ch : (d : Fin D) → (Fin (n d) → ℝ) × ℝ × ℝ) (_ : ∀ d, (ch d).1 ∈ 𝒰 d ∧ 0 < (ch d).2.2),
      jointG Δ ch s y) = Pday 𝒰 Δ s y := by
  refine le_antisymm (iSup₂_le fun ch hch => jointG_le hn hΔ hu ch hch) ?_
  by_cases hns : ∀ d, ¬ Sing Δ s y d
  · obtain ⟨ch, hch, he⟩ := attained hn hΔ h𝒰 hu hy hns
    exact he.symm.le.trans (le_iSup₂_of_le ch hch le_rfl)
  · push Not at hns
    obtain ⟨d₀, hd₀⟩ := hns
    rw [(singular_top hn hΔ h𝒰 hu hy hd₀).2]
    have hp := posPath_block hy hn
    choose U hU using h𝒰
    -- Fixed admissible parameters in every block.
    set ch₀ : (d : Fin D) → (Fin (n d) → ℝ) × ℝ × ℝ := fun d => (U d, 0, 1)
    set c := ∏ d ∈ Finset.univ.erase d₀, ENNReal.ofReal (gV (Δ d) (U d) 0 1 (start s y d) (toR y d))
    have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun d _ =>
      (ENNReal.ofReal_pos.2 (gV_pos (Δ₁ := Δ d) (hu d _ (hU d)) (hp d) 0 one_pos)).ne'
    have hct : c ≠ ⊤ := ENNReal.prod_ne_top fun d _ => ENNReal.ofReal_ne_top
    have hsup : Dv (Δ d₀) (U d₀) (start s y d₀) (toR y d₀) = ⊤ :=
      (singular_top hn hΔ (fun d => ⟨U d, hU d⟩) hu hy hd₀).1 _ (hU d₀)
    rw [← sup_eq (hn d₀) (hΔ d₀) (hu d₀ _ (hU d₀))] at hsup
    refine (ENNReal.eq_top_of_forall_nnreal_le fun r => ?_).ge
    -- A singular-block parameter with density above `r/c`.
    have hlt : (r : ℝ≥0∞) / c < ⊤ := ENNReal.div_lt_top ENNReal.coe_ne_top hc0
    rw [← hsup] at hlt
    obtain ⟨b, hb⟩ := lt_iSup_iff.1 hlt
    obtain ⟨w, hw⟩ := lt_iSup_iff.1 hb
    obtain ⟨hw0, hgw⟩ := lt_iSup_iff.1 hw
    set ch := Function.update ch₀ d₀ (U d₀, b, w)
    have hch : ∀ d, (ch d).1 ∈ 𝒰 d ∧ 0 < (ch d).2.2 := fun d => by
      by_cases h : d = d₀
      · subst h; simp [ch, hU, hw0]
      · simp [ch, ch₀, Function.update_of_ne h, hU]
    refine le_trans ?_ (le_iSup₂_of_le ch hch le_rfl)
    unfold jointG
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ d₀)]
    have hrest : ∏ d ∈ Finset.univ.erase d₀,
        ENNReal.ofReal (gV (Δ d) (ch d).1 (ch d).2.1 (ch d).2.2 (start s y d) (toR y d)) = c :=
      Finset.prod_congr rfl fun d hd => by
        simp [ch, ch₀, Function.update_of_ne (Finset.ne_of_mem_erase hd)]
    rw [hrest]
    simp only [ch, Function.update_self]
    calc (r : ℝ≥0∞) = r / c * c := (ENNReal.div_mul_cancel hc0 hct).symm
      _ ≤ _ := mul_le_mul_left hgw.le _

end Novel.D23DailyProfile
