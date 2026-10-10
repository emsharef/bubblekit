import Standalone.D13DriftRect
import Novel.D13DriftProfileProof

/-!
# Claim 057 (D13): proof of part 1's exact rectangle profile

Proves `Standalone.D13DriftRect.profile` (`profile_holds`). The score and parts 2–4 are
`Novel/D13DriftRectScoreProof.lean`; `Novel/D13DriftRectProof.lean` assembles `statement_holds`.

* **The log density** (`ellG_eq`). With `C = −(n/2) log 2π − c₀`,
  `ℓ(b, w) = C − (n/2) log w − (Q_G + τ (b − w/2 − a_G)²)/(2w)` (claim 055's `Sa_eq`). So:
  - at fixed `w`, it is a concave quadratic in `b` with peak `a_G + w/2`, and the best feasible
    drift is the clip;
  - on a drift edge `b = c`, it is `C + τ(c − a_G)/2 + φ(w)` with
    `φ(w) = −(n/2) log w − A_G(c)/(2w) − τ w/8`;
  - on the ridge `b = a_G + w/2`, it is `C − (n/2) log w − Q_G/(2w)`.
* **Unimodality** (`unimodal`). A function whose derivative is `≥ 0` up to `p` and `≤ 0` after
  attains its maximum over `[l, h]` at `clip_[l,h](p)` (`monotoneOn_of_hasDerivWithinAt_nonneg`).
  For the drift edge the peak is (3): with `s = √(n² + τA)`, `τ v² + 4 n v = 4A`. For the ridge it
  is `Q_G/n`.
* **Covering** (`le_candMax`). Clip `b` to the ridge. If the clip lands on a drift edge, the drift
  edge bounds it. Otherwise maximize along the ridge over the sub-interval where its drift is
  feasible. The clipped ridge peak is the interior candidate, a variance-edge candidate, or a point
  on a drift edge.
* **Exactness.** Every candidate is feasible, so the supremum is the largest candidate value.
* **Measurability.** The closed form is a finite maximum of measurable expressions, with an
  indicator for the interior candidate, on Borel strata.
-/

open MeasureTheory Real Set Filter
open scoped ENNReal

namespace Novel.D13DriftRect

open Standalone.D13DriftNull Standalone.D13DriftRect

/-! ## Clipping -/

theorem clip_mem {l h : ℝ} (hlh : l ≤ h) (x : ℝ) : clip l h x ∈ Icc l h :=
  ⟨le_min hlh (le_max_left _ _), min_le_left _ _⟩

theorem clip_of_mem {l h x : ℝ} (hx : x ∈ Icc l h) : clip l h x = x := by
  unfold clip; rw [max_eq_right hx.1, min_eq_right hx.2]

theorem clip_le_max (l h x : ℝ) : clip l h x ≤ max l x := min_le_right _ _

theorem min_le_clip (l h x : ℝ) : min h x ≤ clip l h x :=
  min_le_min le_rfl (le_max_right _ _)

/-- The clip is the nearest point of `[l, h]`. -/
theorem sq_clip_le {l h x b : ℝ} (hb : b ∈ Icc l h) : (clip l h x - x) ^ 2 ≤ (b - x) ^ 2 := by
  unfold clip
  rcases le_total x l with hxl | hxl
  · rw [max_eq_left hxl, min_eq_right (hb.1.trans hb.2)]
    nlinarith [hb.1]
  · rw [max_eq_right hxl]
    rcases le_total x h with hxh | hxh
    · rw [min_eq_right hxh]; simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]; positivity
    · rw [min_eq_left hxh]; nlinarith [hb.2]

/-! ## Unimodality -/

/-- If `φ' ≥ 0` on `(0, p]` and `φ' ≤ 0` on `[p, ∞)`, the maximum over `[l, h] ⊆ (0, ∞)` is at
`clip_[l,h](p)`. -/
theorem unimodal {φ φ' : ℝ → ℝ} {p : ℝ} (hd : ∀ w, 0 < w → HasDerivAt φ (φ' w) w)
    (hup : ∀ w, 0 < w → w ≤ p → 0 ≤ φ' w) (hdown : ∀ w, 0 < w → p ≤ w → φ' w ≤ 0)
    {l h : ℝ} (hl : 0 < l) (hlh : l ≤ h) {w : ℝ} (hw : w ∈ Icc l h) :
    φ w ≤ φ (clip l h p) := by
  set c := clip l h p
  have hc := clip_mem hlh p
  have hcont : ∀ a b, l ≤ a → ContinuousOn φ (Icc a b) := fun a b ha =>
    fun x hx => (hd x (by linarith [hx.1])).continuousAt.continuousWithinAt
  rcases le_total w c with hwc | hcw
  · have hmono : MonotoneOn φ (Icc w c) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc w c) (hcont w c hw.1)
        (fun x hx => by
          rw [interior_Icc] at hx
          exact (hd x (by linarith [hw.1, hx.1])).hasDerivWithinAt)
        (fun x hx => by
          rw [interior_Icc] at hx
          refine hup x (by linarith [hw.1, hx.1]) ?_
          by_contra hxp
          push Not at hxp
          have := clip_le_max l h p
          rcases le_max_iff.1 (hx.2.le.trans this) with h1 | h1 <;> linarith [hx.1, hw.1])
    exact hmono ⟨le_rfl, hwc⟩ ⟨hwc, le_rfl⟩ hwc
  · have hanti : AntitoneOn φ (Icc c w) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc c w) (hcont c w hc.1)
        (fun x hx => by
          rw [interior_Icc] at hx
          exact (hd x (by linarith [hc.1, hx.1])).hasDerivWithinAt)
        (fun x hx => by
          rw [interior_Icc] at hx
          refine hdown x (by linarith [hc.1, hx.1]) ?_
          by_contra hxp
          push Not at hxp
          have := min_le_clip l h p
          rcases min_le_iff.1 (le_trans (min_le_min le_rfl le_rfl) this) with h1 | h1
          · have : min h p ≤ c := this
            rcases min_le_iff.1 this with h2 | h2 <;> linarith [hx.1, hx.2, hw.2, hc.2]
          · linarith [hx.1])
    exact hanti ⟨le_rfl, hcw⟩ ⟨hcw, le_rfl⟩ hcw

/-- `φ(w) = −(n/2) log w − A/(2w) − β w` and its derivative. -/
theorem hasDeriv_fam (n A β : ℝ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun w => -(n / 2) * Real.log w - A / (2 * w) - β * w)
      ((A - n * w - 2 * β * w ^ 2) / (2 * w ^ 2)) w := by
  have h1 := ((Real.hasDerivAt_log hw.ne').const_mul (-(n / 2)))
  have h2 := ((hasDerivAt_id w).const_mul 2).inv (by positivity : (2 * w) ≠ 0) |>.const_mul A
  have h3 := (hasDerivAt_id w).const_mul β
  have := (h1.sub h2).sub h3
  convert this using 1
  · ext x; simp [div_eq_mul_inv]
  · simp only [id]; field_simp; ring

/-- The family is unimodal with peak `2A/(n + √(n² + 8βA))`. -/
theorem fam_max {n A β : ℝ} (hn : 0 < n) (hA : 0 ≤ A) (hβ : 0 ≤ β) {l h : ℝ} (hl : 0 < l)
    (hlh : l ≤ h) {w : ℝ} (hw : w ∈ Icc l h) :
    -(n / 2) * Real.log w - A / (2 * w) - β * w ≤
      -(n / 2) * Real.log (clip l h (2 * A / (n + Real.sqrt (n ^ 2 + 8 * β * A)))) -
        A / (2 * clip l h (2 * A / (n + Real.sqrt (n ^ 2 + 8 * β * A)))) -
        β * clip l h (2 * A / (n + Real.sqrt (n ^ 2 + 8 * β * A))) := by
  set s := Real.sqrt (n ^ 2 + 8 * β * A)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = n ^ 2 + 8 * β * A := Real.sq_sqrt (by positivity)
  set p := 2 * A / (n + s)
  have hp0 : 0 ≤ p := by positivity
  have hroot : n * p + 2 * β * p ^ 2 = A := by
    simp only [p]
    field_simp
    nlinarith [hs2]
  refine unimodal (φ' := fun w => (A - n * w - 2 * β * w ^ 2) / (2 * w ^ 2))
    (fun w hw => hasDeriv_fam n A β hw) (fun w hw hwp => ?_) (fun w hw hwp => ?_) hl hlh hw
  · apply div_nonneg _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hwp hβ, mul_le_mul hwp hwp hw.le hp0]
  · apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hwp hβ, mul_le_mul hwp hwp hp0 hw.le]

/-! ## The log density -/

section Profile

variable {n : ℕ} {Δ : Fin n → ℝ} {y0 : ℝ} {y : Fin n → ℝ}

/-- The constant `−(n/2) log 2π − c₀`. -/
noncomputable def Kc (Δ : Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log (2 * π) - ((1 / 2) * ∑ j, Real.log (Δ j) + ∑ j, Real.log (y j))

theorem ellG_eq (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (b : ℝ) {w : ℝ} (hw : 0 < w) :
    ellG Δ y0 y b w = Kc Δ y - ((n : ℝ) / 2) * Real.log w -
      (QG Δ y0 y + (∑ j, Δ j) * (b - w / 2 - aG Δ y0 y) ^ 2) / (2 * w) := by
  have hS := Novel.D13DriftNull.Sa_eq (y0 := y0) (y := y) hn hΔ (b - w / 2)
  unfold Novel.D13DriftNull.Sa at hS
  unfold ellG Kc
  rw [hS, Real.log_mul (by positivity) hw.ne']
  ring

theorem ellG_edge (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (c : ℝ) {w : ℝ} (hw : 0 < w) :
    ellG Δ y0 y c w = Kc Δ y + (∑ j, Δ j) * (c - aG Δ y0 y) / 2 +
      (-((n : ℝ) / 2) * Real.log w - AGb Δ y0 y c / (2 * w) - ((∑ j, Δ j) / 8) * w) := by
  rw [ellG_eq hn hΔ c hw]
  unfold AGb
  field_simp
  ring

theorem ellG_ridge (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) {w : ℝ} (hw : 0 < w) :
    ellG Δ y0 y (aG Δ y0 y + w / 2) w = Kc Δ y +
      (-((n : ℝ) / 2) * Real.log w - QG Δ y0 y / (2 * w) - 0 * w) := by
  rw [ellG_eq hn hΔ _ hw]
  ring

theorem ellG_concave (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (b : ℝ) {w : ℝ} (hw : 0 < w) :
    ellG Δ y0 y b w = ellG Δ y0 y (aG Δ y0 y + w / 2) w -
      (∑ j, Δ j) * (b - (aG Δ y0 y + w / 2)) ^ 2 / (2 * w) := by
  rw [ellG_eq hn hΔ _ hw, ellG_eq hn hΔ _ hw]
  field_simp
  ring

theorem AGb_nonneg (hΔ : ∀ j, 0 < Δ j) (c : ℝ) : 0 ≤ AGb Δ y0 y c :=
  add_nonneg (Novel.D13DriftNull.QG_nonneg hΔ)
    (mul_nonneg (Finset.sum_nonneg fun j _ => (hΔ j).le) (sq_nonneg _))

/-- The maximum along a drift edge is at the clipped root (3). -/
theorem edge_le (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (c : ℝ) {l h w : ℝ} (hl : 0 < l) (hlh : l ≤ h)
    (hw : w ∈ Icc l h) : ellG Δ y0 y c w ≤ ellG Δ y0 y c (clip l h (vEdge Δ y0 y c)) := by
  have hc := clip_mem hlh (vEdge Δ y0 y c)
  rw [ellG_edge hn hΔ c (hl.trans_le hw.1), ellG_edge hn hΔ c (hl.trans_le hc.1)]
  have hpeak : vEdge Δ y0 y c = 2 * AGb Δ y0 y c /
      (n + Real.sqrt ((n : ℝ) ^ 2 + 8 * ((∑ j, Δ j) / 8) * AGb Δ y0 y c)) := by
    unfold vEdge; congr 3; ring
  rw [hpeak]
  have hβ : 0 ≤ (∑ j, Δ j) / 8 := div_nonneg (Finset.sum_nonneg fun j _ => (hΔ j).le) (by norm_num)
  have := fam_max (β := (∑ j, Δ j) / 8) (Nat.cast_pos.2 hn) (AGb_nonneg (y0 := y0) (y := y) hΔ c) hβ
    hl hlh hw
  linarith

/-- The maximum along the ridge is at the clipped `Q_G/n`. -/
theorem ridge_le (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) {l h w : ℝ} (hl : 0 < l) (hlh : l ≤ h)
    (hw : w ∈ Icc l h) :
    ellG Δ y0 y (aG Δ y0 y + w / 2) w ≤
      ellG Δ y0 y (aG Δ y0 y + clip l h (QG Δ y0 y / n) / 2) (clip l h (QG Δ y0 y / n)) := by
  have hc := clip_mem hlh (QG Δ y0 y / n)
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [ellG_ridge hn hΔ (hl.trans_le hw.1), ellG_ridge hn hΔ (hl.trans_le hc.1)]
  have hpeak : QG Δ y0 y / n = 2 * QG Δ y0 y / (n + Real.sqrt ((n : ℝ) ^ 2 + 8 * 0 * QG Δ y0 y)) := by
    rw [show (n : ℝ) ^ 2 + 8 * 0 * QG Δ y0 y = (n : ℝ) ^ 2 by ring, Real.sqrt_sq hnr.le]
    field_simp; ring
  rw [hpeak]
  have := fam_max (β := 0) hnr (Novel.D13DriftNull.QG_nonneg (y0 := y0) (y := y) hΔ) le_rfl hl hlh hw
  linarith

/-! ## Covering -/

theorem le_candMax (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) {blo bhi slo shi : ℝ} (hb : blo ≤ bhi)
    (hs : 0 < slo) (hss : slo ≤ shi) {b w : ℝ} (hbB : b ∈ Icc blo bhi)
    (hwW : w ∈ Icc (slo ^ 2) (shi ^ 2)) : ellG Δ y0 y b w ≤ candMax Δ y0 y blo bhi slo shi := by
  classical
  have hwlo : 0 < slo ^ 2 := by positivity
  have hW : slo ^ 2 ≤ shi ^ 2 := pow_le_pow_left₀ hs.le hss 2
  have hw0 : 0 < w := hwlo.trans_le hwW.1
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hτ : 0 ≤ ∑ j, Δ j := Finset.sum_nonneg fun j _ => (hΔ j).le
  have he1 : ellG Δ y0 y blo (clip (slo ^ 2) (shi ^ 2) (vEdge Δ y0 y blo)) ≤
      candMax Δ y0 y blo bhi slo shi := by
    unfold candMax; simp only [le_max_iff, le_refl, true_or]
  have he2 : ellG Δ y0 y bhi (clip (slo ^ 2) (shi ^ 2) (vEdge Δ y0 y bhi)) ≤
      candMax Δ y0 y blo bhi slo shi := by
    unfold candMax; simp only [le_max_iff, le_refl, true_or, or_true]
  have he3 : ellG Δ y0 y (clip blo bhi (aG Δ y0 y + slo ^ 2 / 2)) (slo ^ 2) ≤
      candMax Δ y0 y blo bhi slo shi := by
    unfold candMax; simp only [le_max_iff, le_refl, true_or, or_true]
  have he4 : ellG Δ y0 y (clip blo bhi (aG Δ y0 y + shi ^ 2 / 2)) (shi ^ 2) ≤
      candMax Δ y0 y blo bhi slo shi := by
    unfold candMax; simp only [le_max_iff, le_refl, true_or, or_true]
  have he5 : IntFeas Δ y0 y blo bhi slo shi →
      ellG Δ y0 y (aG Δ y0 y + QG Δ y0 y / (2 * n)) (QG Δ y0 y / n) ≤
      candMax Δ y0 y blo bhi slo shi := fun hf => by
    unfold candMax; simp only [hf, ↓reduceIte, le_max_iff, le_refl, or_true]
  -- Step 1: clip the drift to the ridge.
  set p := aG Δ y0 y + w / 2 with hp
  have h1 : ellG Δ y0 y b w ≤ ellG Δ y0 y (clip blo bhi p) w := by
    rw [ellG_concave hn hΔ b hw0, ellG_concave hn hΔ (clip blo bhi p) hw0]
    have := sq_clip_le (x := p) hbB
    have h2w : 0 < 2 * w := by positivity
    have := mul_le_mul_of_nonneg_left this hτ
    have := div_le_div_of_nonneg_right this h2w.le
    linarith
  refine h1.trans ?_
  rcases le_total p blo with hpl | hpl
  · have : clip blo bhi p = blo := by unfold clip; rw [max_eq_left hpl, min_eq_right hb]
    rw [this]; exact (edge_le hn hΔ blo hwlo hW hwW).trans he1
  rcases le_total bhi p with hph | hph
  · have : clip blo bhi p = bhi := by unfold clip; rw [max_eq_right hpl, min_eq_left hph]
    rw [this]; exact (edge_le hn hΔ bhi hwlo hW hwW).trans he2
  -- Step 2: along the ridge, where its drift is feasible.
  rw [clip_of_mem ⟨hpl, hph⟩]
  set L := max (slo ^ 2) (2 * (blo - aG Δ y0 y)) with hLdef
  set H := min (shi ^ 2) (2 * (bhi - aG Δ y0 y)) with hHdef
  have hL1 : slo ^ 2 ≤ L := le_max_left _ _
  have hL2 : 2 * (blo - aG Δ y0 y) ≤ L := le_max_right _ _
  have hH1 : H ≤ shi ^ 2 := min_le_left _ _
  have hH2 : H ≤ 2 * (bhi - aG Δ y0 y) := min_le_right _ _
  have hL0 : 0 < L := hwlo.trans_le hL1
  have hwLH : w ∈ Icc L H := ⟨max_le hwW.1 (by linarith), le_min hwW.2 (by linarith)⟩
  have hLH : L ≤ H := hwLH.1.trans hwLH.2
  have h2 := ridge_le (y0 := y0) (y := y) hn hΔ hL0 hLH hwLH
  refine h2.trans ?_
  set c := clip L H (QG Δ y0 y / n) with hcdef
  have hc := clip_mem hLH (QG Δ y0 y / n)
  have hcW : c ∈ Icc (slo ^ 2) (shi ^ 2) := ⟨hL1.trans hc.1, hc.2.trans hH1⟩
  rcases lt_or_ge (QG Δ y0 y / n) L with hqL | hqL
  · have hcL : c = L := by rw [hcdef]; unfold clip; rw [max_eq_left hqL.le, min_eq_right hLH]
    rcases max_choice (slo ^ 2) (2 * (blo - aG Δ y0 y)) with hm | hm
    · have hLs : L = slo ^ 2 := hm
      have hfeas : aG Δ y0 y + slo ^ 2 / 2 ∈ Icc blo bhi :=
        ⟨by linarith, by linarith [hc.2]⟩
      have e : aG Δ y0 y + c / 2 = clip blo bhi (aG Δ y0 y + slo ^ 2 / 2) := by
        rw [clip_of_mem hfeas, hcL, hLs]
      have e' : c = slo ^ 2 := hcL.trans hLs
      rw [e, e']; exact he3
    · have hLb : L = 2 * (blo - aG Δ y0 y) := hm
      have e : aG Δ y0 y + c / 2 = blo := by rw [hcL, hLb]; ring
      rw [e]; exact (edge_le hn hΔ blo hwlo hW hcW).trans he1
  rcases lt_or_ge H (QG Δ y0 y / n) with hqH | hqH
  · have hcH : c = H := by
      rw [hcdef]; unfold clip; rw [max_eq_right (hLH.trans hqH.le), min_eq_left hqH.le]
    rcases min_choice (shi ^ 2) (2 * (bhi - aG Δ y0 y)) with hm | hm
    · have hHs : H = shi ^ 2 := hm
      have hfeas : aG Δ y0 y + shi ^ 2 / 2 ∈ Icc blo bhi :=
        ⟨by linarith [hc.1], by linarith⟩
      have e : aG Δ y0 y + c / 2 = clip blo bhi (aG Δ y0 y + shi ^ 2 / 2) := by
        rw [clip_of_mem hfeas, hcH, hHs]
      have e' : c = shi ^ 2 := hcH.trans hHs
      rw [e, e']; exact he4
    · have hHb : H = 2 * (bhi - aG Δ y0 y) := hm
      have e : aG Δ y0 y + c / 2 = bhi := by rw [hcH, hHb]; ring
      rw [e]; exact (edge_le hn hΔ bhi hwlo hW hcW).trans he2
  · have hcq : c = QG Δ y0 y / n := clip_of_mem ⟨hqL, hqH⟩
    have e : aG Δ y0 y + c / 2 = aG Δ y0 y + QG Δ y0 y / (2 * n) := by rw [hcq]; field_simp
    have hfeas : IntFeas Δ y0 y blo bhi slo shi := by
      refine ⟨?_, hcq ▸ hcW⟩
      rw [← e]
      exact ⟨by linarith [hc.1], by linarith [hc.2]⟩
    rw [e, hcq]
    exact he5 hfeas

/-! ## Exactness -/

theorem gG_ellG (hp : PosPath y0 y) (hΔ : ∀ j, 0 < Δ j) (b : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    gG Δ b κ y0 y = Real.exp (ellG Δ y0 y b (κ ^ 2)) := by
  rw [Novel.D13DriftNull.gG_pos hp hΔ hκ]
  rfl

/-- The largest candidate value is attained at a feasible point. -/
theorem candMax_mem {blo bhi slo shi : ℝ} (hb : blo ≤ bhi) (hss : slo ≤ shi) (hs : 0 < slo) :
    ∃ b ∈ Icc blo bhi, ∃ w ∈ Icc (slo ^ 2) (shi ^ 2),
      candMax Δ y0 y blo bhi slo shi = ellG Δ y0 y b w := by
  classical
  have hW : slo ^ 2 ≤ shi ^ 2 := pow_le_pow_left₀ hs.le hss 2
  have hmax : ∀ x z : ℝ, (∃ b ∈ Icc blo bhi, ∃ w ∈ Icc (slo ^ 2) (shi ^ 2), x = ellG Δ y0 y b w) →
      (∃ b ∈ Icc blo bhi, ∃ w ∈ Icc (slo ^ 2) (shi ^ 2), z = ellG Δ y0 y b w) →
      ∃ b ∈ Icc blo bhi, ∃ w ∈ Icc (slo ^ 2) (shi ^ 2), max x z = ellG Δ y0 y b w :=
    fun x z hx hz => by rcases max_choice x z with h | h <;> rw [h] <;> assumption
  have c1 : ∃ b ∈ Icc blo bhi, ∃ w ∈ Icc (slo ^ 2) (shi ^ 2),
      ellG Δ y0 y blo (clip (slo ^ 2) (shi ^ 2) (vEdge Δ y0 y blo)) = ellG Δ y0 y b w :=
    ⟨blo, ⟨le_rfl, hb⟩, _, clip_mem hW _, rfl⟩
  have c2 : ∃ b ∈ Icc blo bhi, ∃ w ∈ Icc (slo ^ 2) (shi ^ 2),
      ellG Δ y0 y bhi (clip (slo ^ 2) (shi ^ 2) (vEdge Δ y0 y bhi)) = ellG Δ y0 y b w :=
    ⟨bhi, ⟨hb, le_rfl⟩, _, clip_mem hW _, rfl⟩
  have c3 : ∃ b ∈ Icc blo bhi, ∃ w ∈ Icc (slo ^ 2) (shi ^ 2),
      ellG Δ y0 y (clip blo bhi (aG Δ y0 y + slo ^ 2 / 2)) (slo ^ 2) = ellG Δ y0 y b w :=
    ⟨_, clip_mem hb _, _, ⟨le_rfl, hW⟩, rfl⟩
  have c4 : ∃ b ∈ Icc blo bhi, ∃ w ∈ Icc (slo ^ 2) (shi ^ 2),
      ellG Δ y0 y (clip blo bhi (aG Δ y0 y + shi ^ 2 / 2)) (shi ^ 2) = ellG Δ y0 y b w :=
    ⟨_, clip_mem hb _, _, ⟨hW, le_rfl⟩, rfl⟩
  have c5 : ∃ b ∈ Icc blo bhi, ∃ w ∈ Icc (slo ^ 2) (shi ^ 2),
      (if IntFeas Δ y0 y blo bhi slo shi then
        ellG Δ y0 y (aG Δ y0 y + QG Δ y0 y / (2 * n)) (QG Δ y0 y / n)
      else ellG Δ y0 y blo (clip (slo ^ 2) (shi ^ 2) (vEdge Δ y0 y blo))) = ellG Δ y0 y b w := by
    split_ifs with hf
    · exact ⟨_, hf.1, _, hf.2, rfl⟩
    · exact c1
  exact hmax _ _ (hmax _ _ (hmax _ _ c1 c2) (hmax _ _ c3 c4)) c5

theorem sup_eq (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) {blo bhi slo shi : ℝ} (hb : blo ≤ bhi)
    (hs : 0 < slo) (hss : slo ≤ shi) (y0 : ℝ) (y : Fin n → ℝ) :
    (⨆ b ∈ Icc blo bhi, ⨆ κ ∈ Icc slo shi, ENNReal.ofReal (gG Δ b κ y0 y)) =
      DGR Δ blo bhi slo shi y0 y := by
  classical
  by_cases hp : PosPath y0 y
  · unfold DGR
    simp only [hp, ↓reduceIte]
    apply le_antisymm
    · refine iSup₂_le fun b hb' => iSup₂_le fun κ hκ => ?_
      have hκ0 : 0 < κ := hs.trans_le hκ.1
      rw [gG_ellG hp hΔ b hκ0]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_candMax hn hΔ hb hs hss hb'
        ⟨pow_le_pow_left₀ hs.le hκ.1 2, pow_le_pow_left₀ hκ0.le hκ.2 2⟩))
    · obtain ⟨b, hb', w, hw, he⟩ := candMax_mem (Δ := Δ) (y0 := y0) (y := y) hb hss hs
      have hw0 : 0 < w := (by positivity : (0 : ℝ) < slo ^ 2).trans_le hw.1
      have hκ : Real.sqrt w ∈ Icc slo shi :=
        ⟨by rw [← Real.sqrt_sq hs.le]; exact Real.sqrt_le_sqrt hw.1,
          by rw [← Real.sqrt_sq (hs.le.trans hss)]; exact Real.sqrt_le_sqrt hw.2⟩
      refine le_iSup₂_of_le b hb' (le_iSup₂_of_le (Real.sqrt w) hκ ?_)
      rw [gG_ellG hp hΔ b (Real.sqrt_pos.2 hw0), Real.sq_sqrt hw0.le, he]
  · have hg : ∀ b κ, gG Δ b κ y0 y = if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0 := fun b κ => by
      unfold gG; simp only [hp, ↓reduceIte]
    simp only [hg]
    unfold DGR
    simp only [hp, ↓reduceIte]
    apply le_antisymm
    · exact iSup₂_le fun _ _ => iSup₂_le fun _ _ => by split_ifs <;> simp
    · exact le_iSup₂_of_le blo ⟨le_rfl, hb⟩ (le_iSup₂_of_le slo ⟨le_rfl, hss⟩
        (by split_ifs <;> simp))

/-! ## Measurability -/

theorem measurable_aG : Measurable fun x : ℝ × (Fin n → ℝ) => aG Δ x.1 x.2 :=
  (Finset.measurable_sum _ fun j _ => Novel.D13DriftNull.measurable_ret j).div_const _

theorem measurable_ellG {B W : ℝ × (Fin n → ℝ) → ℝ} (hB : Measurable B) (hW : Measurable W) :
    Measurable fun x => ellG Δ x.1 x.2 (B x) (W x) := by
  unfold ellG
  refine ((measurable_const.mul (Real.measurable_log.comp (measurable_const.mul hW))).sub
    (measurable_const.add (Finset.measurable_sum _ fun j _ =>
      Real.measurable_log.comp ((measurable_pi_apply j).comp measurable_snd)))).sub
    ((Finset.measurable_sum _ fun j _ => ?_).div (measurable_const.mul hW))
  exact (((Novel.D13DriftNull.measurable_ret j).sub
    ((hB.sub (hW.div_const 2)).mul_const _)).pow_const 2).div_const _

theorem measurable_vEdge (c : ℝ) : Measurable fun x : ℝ × (Fin n → ℝ) => vEdge Δ x.1 x.2 c := by
  have hA : Measurable fun x : ℝ × (Fin n → ℝ) => AGb Δ x.1 x.2 c :=
    Novel.D13DriftNull.measurable_QG.add
      (measurable_const.mul ((measurable_const.sub measurable_aG).pow_const 2))
  unfold vEdge
  exact (measurable_const.mul hA).div
    (measurable_const.add (measurable_const.add (measurable_const.mul hA)).sqrt)

theorem measurable_clip {f : ℝ × (Fin n → ℝ) → ℝ} (hf : Measurable f) (l h : ℝ) :
    Measurable fun x => clip l h (f x) :=
  measurable_const.min (measurable_const.max hf)

theorem measurable_DGR (blo bhi slo shi : ℝ) :
    Measurable fun x : ℝ × (Fin n → ℝ) => DGR Δ blo bhi slo shi x.1 x.2 := by
  classical
  have hQ := Novel.D13DriftNull.measurable_QG (Δ := Δ)
  have hfeas : MeasurableSet {x : ℝ × (Fin n → ℝ) | IntFeas Δ x.1 x.2 blo bhi slo shi} :=
    (((measurable_aG (Δ := Δ)).add (hQ.div_const (2 * (n : ℝ)))) measurableSet_Icc).inter
      ((hQ.div_const (n : ℝ)) measurableSet_Icc)
  have hc : Measurable fun x : ℝ × (Fin n → ℝ) => candMax Δ x.1 x.2 blo bhi slo shi := by
    unfold candMax
    have e1 := measurable_ellG (Δ := Δ) (measurable_const (a := blo))
      (measurable_clip (measurable_vEdge (Δ := Δ) blo) (slo ^ 2) (shi ^ 2))
    have e2 := measurable_ellG (Δ := Δ) (measurable_const (a := bhi))
      (measurable_clip (measurable_vEdge (Δ := Δ) bhi) (slo ^ 2) (shi ^ 2))
    have e3 := measurable_ellG (Δ := Δ)
      (measurable_clip ((measurable_aG (Δ := Δ)).add_const (slo ^ 2 / 2)) blo bhi)
      (measurable_const (a := slo ^ 2))
    have e4 := measurable_ellG (Δ := Δ)
      (measurable_clip ((measurable_aG (Δ := Δ)).add_const (shi ^ 2 / 2)) blo bhi)
      (measurable_const (a := shi ^ 2))
    have e5 := measurable_ellG (Δ := Δ) ((measurable_aG (Δ := Δ)).add (hQ.div_const (2 * (n : ℝ))))
      (hQ.div_const (n : ℝ))
    exact ((e1.max e2).max (e3.max e4)).max (Measurable.ite hfeas e5 e1)
  unfold DGR
  exact Measurable.ite Novel.D13DriftNull.measurableSet_pos
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc))
    (Measurable.ite Novel.D13DriftNull.measurableSet_trap measurable_const measurable_const)

end Profile

theorem profile_holds : Standalone.D13DriftRect.profile := by
  intro n Δ blo bhi slo shi hn hΔ hb hs hss
  have hW : slo ^ 2 ≤ shi ^ 2 := pow_le_pow_left₀ hs.le hss 2
  refine ⟨fun y0 y => sup_eq hn hΔ hb hs hss y0 y,
    fun y0 y hp => ⟨clip_mem hW _, clip_mem hW _, clip_mem hb _, clip_mem hb _,
      fun b κ hκ => gG_ellG hp hΔ b hκ⟩, fun y0 y => ?_, fun y0 y hp => ?_, measurable_DGR _ _ _ _⟩
  · unfold DGR; split_ifs
    · exact ENNReal.ofReal_lt_top
    · exact ENNReal.one_lt_top
    · exact ENNReal.zero_lt_top
  · unfold DGR; simp only [hp, ↓reduceIte]
    exact ENNReal.ofReal_pos.2 (Real.exp_pos _)

end Novel.D13DriftRect
