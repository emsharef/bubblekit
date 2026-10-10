import Standalone.D13BoundedDrift
import Novel.D13DriftRectProfileProof

/-!
# Claim 056 (D13): proof of part 1's exact drift-interval profile

Proves `Standalone.D13BoundedDrift.profile` (`profile_holds`), reusing claim 057's analysis
(`Novel.D13DriftRect`).
* **Covering** (`le_candB`). For fixed `w`, clip `b` to the ridge `a_G + w/2` (`ellG_concave`,
  `sq_clip_le`).
  - If the clip lands on a drift endpoint `c`, the unconstrained edge maximum bounds it
    (`edge_le` on an interval containing `w` and `w_c`). This needs `A_G(c) > 0`, which holds
    outside the exceptional case.
  - Otherwise `w` is ridge-feasible, `2(b_lo − a_G) ≤ w ≤ 2(b_hi − a_G)`. The ridge is unimodal
    with peak `Q_G/n` (`ridge_le`), so it is bounded by the interior candidate, or by the ridge at
    a feasible end, which lies on a drift endpoint.
* **Attainment.** Every candidate is feasible, with `κ = √w`.
* **Exceptional case.** At `b = a_G` and `Q_G = 0`, `ℓ = C − (n/2) log w − τw/8` is unbounded as
  `w ↓ 0`.
* **One increment.** `Q_G = 0` (claim 055), so the closed form is infinite iff `a_G ∈ B`.
* **Measurability.** A finite maximum of measurable expressions on Borel strata.
-/

open MeasureTheory Real Set Filter
open scoped ENNReal

namespace Novel.D13BoundedDrift

open Standalone.D13DriftNull Standalone.D13DriftRect Standalone.D13BoundedDrift Novel.D13DriftRect

section Profile

variable {n : ℕ} {Δ : Fin n → ℝ} {y0 : ℝ} {y : Fin n → ℝ} {blo bhi : ℝ}

theorem tau_pos (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) : 0 < ∑ j, Δ j :=
  Finset.sum_pos (fun j _ => hΔ j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem AGb_pos (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hexc : ¬ Exc Δ y0 y blo bhi) {c : ℝ}
    (hc : c ∈ Icc blo bhi) : 0 < AGb Δ y0 y c := by
  have hQ := Novel.D13DriftNull.QG_nonneg (y0 := y0) (y := y) hΔ
  have hτ := tau_pos hn hΔ
  rcases (AGb_nonneg (y0 := y0) (y := y) hΔ c).lt_or_eq with h | h
  · exact h
  exfalso
  have h2 : (∑ j, Δ j) * (c - aG Δ y0 y) ^ 2 = 0 := by
    unfold AGb at h; nlinarith [mul_nonneg hτ.le (sq_nonneg (c - aG Δ y0 y))]
  have hQ0 : QG Δ y0 y = 0 := by unfold AGb at h; linarith
  have hca : c = aG Δ y0 y := by
    have := (mul_eq_zero.1 h2).resolve_left hτ.ne'
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  exact hexc ⟨hQ0, hca ▸ hc⟩

theorem vEdge_pos (hn : 0 < n) {c : ℝ} (hA : 0 < AGb Δ y0 y c) : 0 < vEdge Δ y0 y c := by
  unfold vEdge
  have : (0 : ℝ) < n := Nat.cast_pos.2 hn
  positivity

/-- The unconstrained maximum on a drift edge. -/
theorem edge_le' (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) {c : ℝ} (hA : 0 < AGb Δ y0 y c) {w : ℝ}
    (hw : 0 < w) : ellG Δ y0 y c w ≤ ellG Δ y0 y c (vEdge Δ y0 y c) := by
  have hv := vEdge_pos (Δ := Δ) (y0 := y0) (y := y) hn hA
  have := Novel.D13DriftRect.edge_le (y0 := y0) (y := y) hn hΔ c (l := min w (vEdge Δ y0 y c))
    (h := max w (vEdge Δ y0 y c)) (lt_min hw hv) (min_le_max) ⟨min_le_left _ _, le_max_left _ _⟩
  rwa [clip_of_mem ⟨min_le_right _ _, le_max_right _ _⟩] at this

theorem le_candB (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hb : blo ≤ bhi)
    (hexc : ¬ Exc Δ y0 y blo bhi) {b w : ℝ} (hbB : b ∈ Icc blo bhi) (hw : 0 < w) :
    ellG Δ y0 y b w ≤ candB Δ y0 y blo bhi := by
  classical
  set a := aG Δ y0 y
  set Q := QG Δ y0 y
  set e1 := ellG Δ y0 y blo (vEdge Δ y0 y blo)
  set e2 := ellG Δ y0 y bhi (vEdge Δ y0 y bhi)
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hQ0 : 0 ≤ Q := Novel.D13DriftNull.QG_nonneg hΔ
  have he1 : e1 ≤ candB Δ y0 y blo bhi := le_max_of_le_left (le_max_left _ _)
  have he2 : e2 ≤ candB Δ y0 y blo bhi := le_max_of_le_left (le_max_right _ _)
  have he5 : IntB Δ y0 y blo bhi → ellG Δ y0 y (a + Q / (2 * n)) (Q / n) ≤ candB Δ y0 y blo bhi :=
    fun h => by
      refine le_trans ?_ (le_max_right _ _)
      show _ ≤ (if IntB Δ y0 y blo bhi then _ else _)
      rw [if_pos h]
  have hA1 := AGb_pos hn hΔ hexc ⟨le_rfl, hb⟩
  have hA2 := AGb_pos hn hΔ hexc ⟨hb, le_rfl⟩
  have hlo : ∀ w', 0 < w' → ellG Δ y0 y blo w' ≤ candB Δ y0 y blo bhi := fun w' hw' =>
    (edge_le' hn hΔ hA1 hw').trans he1
  have hhi : ∀ w', 0 < w' → ellG Δ y0 y bhi w' ≤ candB Δ y0 y blo bhi := fun w' hw' =>
    (edge_le' hn hΔ hA2 hw').trans he2
  -- Clip the drift to the ridge.
  set r := a + w / 2
  set β := clip blo bhi r
  have hstep : ellG Δ y0 y b w ≤ ellG Δ y0 y β w := by
    rw [ellG_concave hn hΔ b hw, ellG_concave hn hΔ β hw]
    have := sq_clip_le (x := r) hbB
    have hτ := tau_pos hn hΔ
    have : (∑ j, Δ j) * (β - r) ^ 2 / (2 * w) ≤ (∑ j, Δ j) * (b - r) ^ 2 / (2 * w) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this hτ.le) (by positivity)
    linarith
  refine hstep.trans ?_
  by_cases hrlo : r < blo
  · have : β = blo := by
      show min bhi (max blo r) = blo; rw [max_eq_left hrlo.le, min_eq_right hb]
    rw [this]; exact hlo w hw
  by_cases hrhi : bhi < r
  · have : β = bhi := by
      show min bhi (max blo r) = bhi; rw [max_eq_right (not_lt.1 hrlo), min_eq_left hrhi.le]
    rw [this]; exact hhi w hw
  -- The ridge-feasible case.
  have hrB : r ∈ Icc blo bhi := ⟨not_lt.1 hrlo, not_lt.1 hrhi⟩
  have hβ : β = r := clip_of_mem hrB
  rw [hβ]
  set wl := 2 * (blo - a)
  set wh := 2 * (bhi - a)
  have hwl : wl ≤ w := by have := hrB.1; simp only [r] at this; linarith
  have hwh : w ≤ wh := by have := hrB.2; simp only [r] at this; linarith
  set p := Q / n
  have hp0 : 0 ≤ p := div_nonneg hQ0 hnr.le
  have hQz : p = 0 → Q = 0 := fun h => by
    have := (div_eq_zero_iff.1 h).resolve_right hnr.ne'; exact this
  rcases le_or_gt wh p with hp | hp
  · -- The peak is right of the feasible interval.
    have hwh0 : 0 < wh := hw.trans_le hwh
    have := ridge_le (y0 := y0) (y := y) hn hΔ hw hwh ⟨le_rfl, hwh⟩
    rw [show clip w wh (QG Δ y0 y / n) = wh by
      show min wh (max w p) = wh; rw [max_eq_right (hwh.trans hp), min_eq_left hp]] at this
    refine this.trans ?_
    rw [show a + wh / 2 = bhi by simp only [wh]; ring]
    exact hhi wh hwh0
  rcases le_or_gt p wl with hp' | hp'
  · -- The peak is left of the feasible interval.
    have hwl0 : 0 < wl := by
      rcases (hp0.trans hp').lt_or_eq with h | h
      · exact h
      · exfalso
        have hp00 : p = 0 := le_antisymm (h ▸ hp') hp0
        have hab : a = blo := by simp only [wl] at h; linarith
        exact hexc ⟨hQz hp00, ⟨hab.ge, by rw [show aG Δ y0 y = a from rfl, hab]; exact hb⟩⟩
    have := ridge_le (y0 := y0) (y := y) hn hΔ hwl0 hwl ⟨hwl, le_rfl⟩
    rw [show clip wl w (QG Δ y0 y / n) = wl by
      show min w (max wl p) = wl; rw [max_eq_left hp', min_eq_right hwl]] at this
    refine this.trans ?_
    rw [show a + wl / 2 = blo by simp only [wl]; ring]
    exact hlo wl hwl0
  · -- The peak is feasible: the interior candidate.
    have hpos : 0 < p := by
      rcases hp0.lt_or_eq with h | h
      · exact h
      · exfalso
        have h1 : blo < a := by have := hp'; rw [← h] at this; simp only [wl] at this; linarith
        have h2 : a < bhi := by have := hp; rw [← h] at this; simp only [wh] at this; linarith
        exact hexc ⟨hQz h.symm, ⟨h1.le, h2.le⟩⟩
    have hint : IntB Δ y0 y blo bhi := by
      refine ⟨by
        have : 0 < Q / n := hpos
        exact (div_pos_iff_of_pos_right hnr).1 this, ?_, ?_⟩
      · have : wl ≤ p := hp'.le; simp only [wl, p] at this ⊢
        have : Q / (2 * n) = Q / n / 2 := by ring
        rw [this]; linarith
      · have : p ≤ wh := hp.le; simp only [wh, p] at this ⊢
        have : Q / (2 * n) = Q / n / 2 := by ring
        rw [this]; linarith
    have := ridge_le (y0 := y0) (y := y) hn hΔ (lt_min hw hpos) min_le_max
      ⟨min_le_left _ _, le_max_left _ _⟩
    rw [clip_of_mem ⟨min_le_right _ _, le_max_right _ _⟩] at this
    refine this.trans ?_
    rw [show a + Q / n / 2 = a + Q / (2 * n) by ring]
    exact he5 hint


theorem candB_mem (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hb : blo ≤ bhi)
    (hexc : ¬ Exc Δ y0 y blo bhi) :
    ∃ b ∈ Icc blo bhi, ∃ w, 0 < w ∧ candB Δ y0 y blo bhi = ellG Δ y0 y b w := by
  classical
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hmax : ∀ x y' : ℝ, (∃ b ∈ Icc blo bhi, ∃ w, 0 < w ∧ x = ellG Δ y0 y b w) →
      (∃ b ∈ Icc blo bhi, ∃ w, 0 < w ∧ y' = ellG Δ y0 y b w) →
      ∃ b ∈ Icc blo bhi, ∃ w, 0 < w ∧ max x y' = ellG Δ y0 y b w := fun x y' hx hy => by
    rcases le_total x y' with h | h
    · rw [max_eq_right h]; exact hy
    · rw [max_eq_left h]; exact hx
  have c1 : ∃ b ∈ Icc blo bhi, ∃ w, 0 < w ∧
      ellG Δ y0 y blo (vEdge Δ y0 y blo) = ellG Δ y0 y b w :=
    ⟨blo, ⟨le_rfl, hb⟩, _, vEdge_pos hn (AGb_pos hn hΔ hexc ⟨le_rfl, hb⟩), rfl⟩
  have c2 : ∃ b ∈ Icc blo bhi, ∃ w, 0 < w ∧
      ellG Δ y0 y bhi (vEdge Δ y0 y bhi) = ellG Δ y0 y b w :=
    ⟨bhi, ⟨hb, le_rfl⟩, _, vEdge_pos hn (AGb_pos hn hΔ hexc ⟨hb, le_rfl⟩), rfl⟩
  have c5 : ∃ b ∈ Icc blo bhi, ∃ w, 0 < w ∧ (if IntB Δ y0 y blo bhi then
      ellG Δ y0 y (aG Δ y0 y + QG Δ y0 y / (2 * n)) (QG Δ y0 y / n)
      else ellG Δ y0 y blo (vEdge Δ y0 y blo)) = ellG Δ y0 y b w := by
    split_ifs with hf
    · exact ⟨_, hf.2, _, div_pos hf.1 hnr, rfl⟩
    · exact c1
  exact hmax _ _ (hmax _ _ c1 c2) c5

theorem sup_eq_B (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hb : blo ≤ bhi) (y0 : ℝ) (y : Fin n → ℝ) :
    (⨆ b ∈ Icc blo bhi, ⨆ κ ∈ Ioi (0 : ℝ), ENNReal.ofReal (gG Δ b κ y0 y)) =
      DGBc Δ blo bhi y0 y := by
  classical
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  by_cases hp : PosPath y0 y
  · unfold DGBc
    simp only [hp, ↓reduceIte]
    by_cases hexc : Exc Δ y0 y blo bhi
    · -- Zero residual with `a_G ∈ B`: the supremum is infinite.
      simp only [hexc, ↓reduceIte]
      refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
      set τ := ∑ j, Δ j
      set T := max 0 ((Real.log ((r : ℝ) + 1) - Kc Δ y + τ / 8) * 2 / n)
      set w := Real.exp (-T)
      have hw0 : 0 < w := Real.exp_pos _
      have hw1 : w ≤ 1 := Real.exp_le_one_iff.2 (by simp only [neg_nonpos]; exact le_max_left _ _)
      have hτ := tau_pos hn hΔ
      have hell : Real.log ((r : ℝ) + 1) ≤ ellG Δ y0 y (aG Δ y0 y) w := by
        rw [ellG_eq hn hΔ _ hw0, hexc.1, Real.log_exp]
        have hT : (Real.log ((r : ℝ) + 1) - Kc Δ y + τ / 8) * 2 / n ≤ T := le_max_right _ _
        rw [div_le_iff₀ hnr] at hT
        have h1 : (∑ j, Δ j) * (aG Δ y0 y - w / 2 - aG Δ y0 y) ^ 2 / (2 * w) = τ * w / 8 := by
          field_simp; ring
        rw [zero_add, h1]
        nlinarith [mul_le_mul_of_nonneg_left hw1 hτ.le]
      refine le_iSup₂_of_le (aG Δ y0 y) hexc.2 (le_iSup₂_of_le (Real.sqrt w)
        (show Real.sqrt w ∈ Ioi 0 from Real.sqrt_pos.2 hw0) ?_)
      rw [gG_ellG hp hΔ _ (Real.sqrt_pos.2 hw0), Real.sq_sqrt hw0.le, ← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal ?_
      have := Real.exp_le_exp.2 hell
      rw [Real.exp_log (by positivity)] at this
      linarith
    · simp only [hexc, ↓reduceIte]
      apply le_antisymm
      · refine iSup₂_le fun b hb' => iSup₂_le fun κ hκ => ?_
        have hκ0 : 0 < κ := hκ
        rw [gG_ellG hp hΔ b hκ0]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_candB hn hΔ hb hexc hb'
          (by positivity)))
      · obtain ⟨b, hb', w, hw0, he⟩ := candB_mem (Δ := Δ) (y0 := y0) (y := y) hn hΔ hb hexc
        refine le_iSup₂_of_le b hb' (le_iSup₂_of_le (Real.sqrt w)
          (show Real.sqrt w ∈ Ioi 0 from Real.sqrt_pos.2 hw0) ?_)
        rw [gG_ellG hp hΔ b (Real.sqrt_pos.2 hw0), Real.sq_sqrt hw0.le, he]
  · have hg : ∀ b κ, gG Δ b κ y0 y = if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0 := fun b κ => by
      unfold gG; simp only [hp, ↓reduceIte]
    simp only [hg]
    unfold DGBc
    simp only [hp, ↓reduceIte]
    apply le_antisymm
    · exact iSup₂_le fun _ _ => iSup₂_le fun _ _ => by split_ifs <;> simp
    · exact le_iSup₂_of_le blo ⟨le_rfl, hb⟩ (le_iSup₂_of_le 1
        (show (1 : ℝ) ∈ Ioi 0 from mem_Ioi.2 one_pos) (by split_ifs <;> simp))

theorem measurable_DGBc (blo bhi : ℝ) :
    Measurable fun x : ℝ × (Fin n → ℝ) => DGBc Δ blo bhi x.1 x.2 := by
  classical
  have hQ := Novel.D13DriftNull.measurable_QG (Δ := Δ)
  have hexcS : MeasurableSet {x : ℝ × (Fin n → ℝ) | Exc Δ x.1 x.2 blo bhi} :=
    (hQ (measurableSet_singleton 0)).inter ((measurable_aG (Δ := Δ)) measurableSet_Icc)
  have hintS : MeasurableSet {x : ℝ × (Fin n → ℝ) | IntB Δ x.1 x.2 blo bhi} :=
    (hQ measurableSet_Ioi).inter
      (((measurable_aG (Δ := Δ)).add (hQ.div_const (2 * (n : ℝ)))) measurableSet_Icc)
  have hc : Measurable fun x : ℝ × (Fin n → ℝ) => candB Δ x.1 x.2 blo bhi := by
    unfold candB
    have e1 := measurable_ellG (Δ := Δ) (measurable_const (a := blo))
      (measurable_vEdge (Δ := Δ) blo)
    have e2 := measurable_ellG (Δ := Δ) (measurable_const (a := bhi))
      (measurable_vEdge (Δ := Δ) bhi)
    have e5 := measurable_ellG (Δ := Δ) ((measurable_aG (Δ := Δ)).add (hQ.div_const (2 * (n : ℝ))))
      (hQ.div_const (n : ℝ))
    exact (e1.max e2).max (Measurable.ite hintS e5 e1)
  unfold DGBc
  exact Measurable.ite Novel.D13DriftNull.measurableSet_pos
    (Measurable.ite hexcS measurable_const
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc)))
    (Measurable.ite Novel.D13DriftNull.measurableSet_trap measurable_const measurable_const)

end Profile

theorem profile_holds : Standalone.D13BoundedDrift.profile := by
  classical
  intro n Δ blo bhi hn hΔ hb
  refine ⟨fun y0 y => sup_eq_B hn hΔ hb y0 y, fun y0 y hp b κ hκ => gG_ellG hp hΔ b hκ,
    fun y0 y _ hexc => ⟨vEdge_pos hn (AGb_pos hn hΔ hexc ⟨le_rfl, hb⟩),
      vEdge_pos hn (AGb_pos hn hΔ hexc ⟨hb, le_rfl⟩)⟩, fun h1 y0 y hp => ?_,
    measurable_DGBc blo bhi⟩
  have hQ : QG Δ y0 y = 0 :=
    (Novel.D13DriftNull.profile_holds n Δ hn hΔ).2.2.2.2.2.2.1 h1 y0 y hp
  unfold DGBc
  simp only [hp, ↓reduceIte, Exc, hQ, true_and]
  split_ifs with h
  · simp [h]
  · simp [h]

end Novel.D13BoundedDrift
