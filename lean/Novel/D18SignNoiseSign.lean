import Standalone.D18SignNoise
import Novel.D18BoundedNoiseProof

/-!
# Claim 065: the sign law, its bound (3) and the sign intervals (2), deterministically

* `lg` is strictly between zero and one and monotone, with `lg 0 = 1/2`.
* `L_between`: `L₋ ≤ L(x, y) ≤ L₊` on `[a, b) × [c, d)`. On positive pairs, `log(y/x)` lies between
  `r₋` and `r₊`; the logistic is monotone (order reversed for `β < 0`), and its limits at infinite
  arguments bound everything. A pair with a zero coordinate forces `a = 0` or `c = 0`, where the
  enlarged interval contains `1/2`.
* So `0 < A ≤ Ā ≤ 1`, every `Ā` is positive, the rows of `A` sum to one and those of `Ā` to at least
  one.
* (2): a label from sign `t` places the latent price in `I_(z,t)`, which lies in claim 064's
  expanded interval; the negative sign is always feasible. Feasible intervals are partitioned into
  `2^ℓ` nested subcells.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18SignNoise

open Standalone.D18SignNoise Standalone.D18BoundedNoise Standalone.D14FixedTick Novel.D14FixedTick

/-! ## The logistic and the sign law -/

theorem lg_pos (v : ℝ) : 0 < lg v := by unfold lg; positivity

theorem lg_lt_one (v : ℝ) : lg v < 1 := by
  unfold lg
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos (-v)]

theorem lg_zero : lg 0 = 1 / 2 := by unfold lg; norm_num

theorem lg_mono {v w : ℝ} (h : v ≤ w) : lg v ≤ lg w := by
  unfold lg
  exact one_div_le_one_div_of_le (by positivity) (by linarith [Real.exp_le_exp.2 (neg_le_neg h)])

theorem lgMinus_mem (β b c : ℝ) : 0 ≤ lgMinus β b c ∧ lgMinus β b c ≤ 1 := by
  unfold lgMinus
  split_ifs
  · exact ⟨(lg_pos _).le, (lg_lt_one _).le⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩

theorem lgPlus_mem (β a d : ℝ) : 0 ≤ lgPlus β a d ∧ lgPlus β a d ≤ 1 := by
  unfold lgPlus
  split_ifs
  · exact ⟨(lg_pos _).le, (lg_lt_one _).le⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨le_rfl, zero_le_one⟩

theorem Lminus_le_Lplus (β a b c d : ℝ) : Lminus β a b c d ≤ Lplus β a b c d := by
  unfold Lminus Lplus
  split_ifs
  · exact le_rfl
  · exact (min_le_right _ _).trans (le_max_right _ _)
  · exact (min_le_left _ _).trans (le_max_left _ _)

theorem Lplus_mem (β a b c d : ℝ) : 0 ≤ Lplus β a b c d ∧ Lplus β a b c d ≤ 1 := by
  have h1 := lgMinus_mem β b c; have h2 := lgPlus_mem β a d
  unfold Lplus
  split_ifs
  · norm_num
  · exact ⟨(lgMinus_mem β b c).1.trans ((le_max_left _ _).trans (le_max_left _ _)),
      max_le (max_le h1.2 h2.2) (by norm_num)⟩
  · exact ⟨h1.1.trans (le_max_left _ _), max_le h1.2 h2.2⟩

theorem Lminus_mem (β a b c d : ℝ) : 0 ≤ Lminus β a b c d ∧ Lminus β a b c d ≤ 1 := by
  have h1 := lgMinus_mem β b c; have h2 := lgPlus_mem β a d
  unfold Lminus
  split_ifs
  · norm_num
  · exact ⟨le_min (le_min h1.1 h2.1) (by norm_num), (min_le_right _ _).trans (by norm_num)⟩
  · exact ⟨le_min h1.1 h2.1, (min_le_left _ _).trans h1.2⟩

/-- `L₊ > 0` on nonnegative endpoints. -/
theorem Lplus_pos {β a b c d : ℝ} (hc : 0 ≤ c) : 0 < Lplus β a b c d := by
  unfold Lplus
  split_ifs with hβ h0
  · norm_num
  · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  · push Not at h0
    have : lgMinus β b c = lg (β * Real.log (c / b)) := by
      unfold lgMinus; simp only [lt_of_le_of_ne hc (Ne.symm h0.2), ↓reduceIte]
    rw [this]
    exact (lg_pos _).trans_le (le_max_left _ _)

/-- `L₋ < 1` on nonnegative endpoints. -/
theorem Lminus_lt_one {β a b c d : ℝ} (ha : 0 ≤ a) : Lminus β a b c d < 1 := by
  unfold Lminus
  split_ifs with hβ h0
  · norm_num
  · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  · push Not at h0
    have : lgPlus β a d = lg (β * Real.log (d / a)) := by
      unfold lgPlus; simp only [lt_of_le_of_ne ha (Ne.symm h0.1), ↓reduceIte]
    rw [this]
    exact (min_le_right _ _).trans_lt (lg_lt_one _)

/-- The logistic of `β r` lies between its values (or limits) at the ends of `r`'s range. -/
theorem lg_between {β b c a d r : ℝ} (hβ : β ≠ 0) (hlo : 0 < c → Real.log (c / b) ≤ r)
    (hhi : 0 < a → r ≤ Real.log (d / a)) :
    min (lgMinus β b c) (lgPlus β a d) ≤ lg (β * r) ∧
      lg (β * r) ≤ max (lgMinus β b c) (lgPlus β a d) := by
  have hl0 := lg_pos (β * r); have hl1 := lg_lt_one (β * r)
  rcases lt_or_gt_of_ne hβ with hneg | hpos
  · -- `β < 0`: `lgPlus ≤ lg (β r) ≤ lgMinus`.
    have h1 : lgPlus β a d ≤ lg (β * r) := by
      unfold lgPlus
      split_ifs with ha' hb'
      · exact lg_mono (by nlinarith [hhi ha'])
      · exact absurd hb' (not_lt.2 hneg.le)
      · exact hl0.le
    have h2 : lg (β * r) ≤ lgMinus β b c := by
      unfold lgMinus
      split_ifs with hc' hb'
      · exact lg_mono (by nlinarith [hlo hc'])
      · exact absurd hb' (not_lt.2 hneg.le)
      · exact hl1.le
    exact ⟨(min_le_right _ _).trans h1, h2.trans (le_max_left _ _)⟩
  · have h1 : lgMinus β b c ≤ lg (β * r) := by
      unfold lgMinus
      split_ifs with hc'
      · exact lg_mono (by nlinarith [hlo hc'])
      · exact hl0.le
    have h2 : lg (β * r) ≤ lgPlus β a d := by
      unfold lgPlus
      split_ifs with ha'
      · exact lg_mono (by nlinarith [hhi ha'])
      · exact hl1.le
    exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_right _ _)⟩

/-- (3): `L₋ ≤ L(x, y) ≤ L₊` on `[a, b) × [c, d)`. -/
theorem L_between {β a b c d x y : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hx : x ∈ Ico a b)
    (hy : y ∈ Ico c d) : Lminus β a b c d ≤ Lsig β x y ∧ Lsig β x y ≤ Lplus β a b c d := by
  unfold Lminus Lplus
  by_cases hβ : β = 0
  · simp only [hβ, ↓reduceIte, Lsig, zero_mul, lg_zero, ite_self, le_refl, and_self]
  simp only [hβ, ↓reduceIte]
  by_cases hxy : 0 < x ∧ 0 < y
  · have hL : Lsig β x y = lg (β * Real.log (y / x)) := by unfold Lsig; simp only [hxy, and_self, ↓reduceIte]
    rw [hL]
    have hb := lg_between (b := b) (c := c) (a := a) (d := d) (r := Real.log (y / x)) hβ
      (fun hc' => Real.log_le_log (div_pos hc' (hxy.1.trans hx.2))
        (div_le_div₀ hxy.2.le hy.1 hxy.1 hx.2.le))
      (fun ha' => Real.log_le_log (div_pos hxy.2 hxy.1) (div_le_div₀ (hc.trans hy.1 |>.trans
        hy.2.le) hy.2.le ha' hx.1))
    split_ifs
    · exact ⟨(min_le_left _ _).trans hb.1, hb.2.trans (le_max_left _ _)⟩
    · exact hb
  · have hL : Lsig β x y = 1 / 2 := by unfold Lsig; simp only [hxy, ↓reduceIte]
    have h0 : a = 0 ∨ c = 0 := by
      rw [not_and_or, not_lt, not_lt] at hxy
      rcases hxy with h | h
      · exact Or.inl (le_antisymm (hx.1.trans h) ha)
      · exact Or.inr (le_antisymm (hy.1.trans h) hc)
    rw [hL]; simp only [h0, ↓reduceIte]
    exact ⟨min_le_right _ _, le_max_right _ _⟩

theorem Lsig_mem (β x y : ℝ) : 0 < Lsig β x y ∧ Lsig β x y < 1 := by
  unfold Lsig
  split_ifs
  · exact ⟨lg_pos _, lg_lt_one _⟩
  · norm_num

theorem ind_mem (h : Bool) : (0 : ℝ) ≤ (if h then 1 else 0) ∧ (if h then (1 : ℝ) else 0) ≤ 1 := by
  cases h <;> simp

variable {ρ β : ℝ}

theorem Asig_pos (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (h t : Bool) (x y : ℝ) : 0 < Asig ρ β h t x y := by
  have hL := Lsig_mem β x y
  unfold Asig
  cases h <;> cases t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith

theorem Asig_sum (h : Bool) (x y : ℝ) : Asig ρ β h true x y + Asig ρ β h false x y = 1 := by
  unfold Asig; simp

/-- (3): `0 < A ≤ Ā ≤ 1` on `[a, b) × [c, d)`. -/
theorem Asig_le_Abar (hρ1 : ρ < 1) (h t : Bool) {a b c d x y : ℝ} (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hx : x ∈ Ico a b) (hy : y ∈ Ico c d) :
    Asig ρ β h t x y ≤ Abar ρ β h t a b c d := by
  have hL := L_between (β := β) ha hc hx hy
  unfold Asig Abar
  cases t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith [ind_mem h]

theorem Abar_le_one (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (h t : Bool) (a b c d : ℝ) :
    Abar ρ β h t a b c d ≤ 1 := by
  have h1 := Lplus_mem β a b c d; have h2 := Lminus_mem β a b c d
  unfold Abar
  cases h <;> cases t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith

theorem Abar_pos (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (h t : Bool) {a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    0 < Abar ρ β h t a b c d := by
  have h1 := Lplus_pos (β := β) (a := a) (b := b) (d := d) hc
  have h2 := Lminus_lt_one (β := β) (b := b) (c := c) (d := d) ha
  have h3 := Lminus_mem β a b c d
  unfold Abar
  cases h <;> cases t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith

theorem Abar_sum (hρ1 : ρ < 1) (h : Bool) (a b c d : ℝ) :
    1 ≤ Abar ρ β h true a b c d + Abar ρ β h false a b c d := by
  have := Lminus_le_Lplus β a b c d
  unfold Abar
  simp only [↓reduceIte, Bool.false_eq_true]
  nlinarith

/-- `β = 0`: the sign stays with probability `(1 + ρ)/2`. -/
theorem Asig_beta0 (ρ : ℝ) (h t : Bool) (x y : ℝ) :
    Asig ρ 0 h t x y = if t = h then (1 + ρ) / 2 else (1 - ρ) / 2 := by
  have hL : Lsig 0 x y = 1 / 2 := by unfold Lsig; split_ifs <;> simp [lg_zero]
  unfold Asig
  rw [hL]
  cases h <;> cases t <;> simp <;> ring

/-- `β = 0`: the bound (3) is the constant sign transition. -/
theorem Abar_beta0 (ρ : ℝ) (h t : Bool) (a b c d : ℝ) :
    Abar ρ 0 h t a b c d = if t = h then (1 + ρ) / 2 else (1 - ρ) / 2 := by
  unfold Abar Lplus Lminus
  cases h <;> cases t <;> simp <;> ring

/-! ## The sign intervals (2) -/

variable {δ a : ℝ}

theorem sg_abs (t : Bool) : |sg t| = 1 := by cases t <;> simp [sg]

theorem ilo_nonneg (z : ℕ) (t : Bool) : 0 ≤ ilo δ a z t := by
  unfold ilo; split_ifs
  · exact le_rfl
  · exact le_max_left _ _

/-- The negative sign is always feasible. -/
theorem feas_false (hδ : 0 < δ) (ha : 0 ≤ a) (z : ℕ) : Feas δ a z false := by
  unfold Feas ilo ihi sg
  simp only [Bool.false_eq_true, ↓reduceIte]
  have := mlo_lt_mhi hδ z
  split_ifs with hz
  · subst hz; unfold mhi; push_cast; nlinarith
  · rw [max_lt_iff]; exact ⟨by linarith [mlo_nonneg δ z], by linarith⟩

theorem false_mem_feasT (hδ : 0 < δ) (ha : 0 ≤ a) (z : ℕ) : false ∈ feasT δ a z := by
  classical
  unfold feasT; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact feas_false hδ ha z

theorem mem_feasT {z : ℕ} {t : Bool} : t ∈ feasT δ a z ↔ Feas δ a z t := by
  classical
  unfold feasT; simp

/-- (2): a label from the sign `t` places the latent price in `I_(z,t)`. -/
theorem obs_mem (hδ : 0 < δ) {x : ℝ} (hx : 0 ≤ x) (t : Bool) :
    x ∈ Ico (ilo δ a (obs δ a x t) t) (ihi δ a (obs δ a x t) t) := by
  set z := obs δ a x t
  have hc := (mlabel_eq_iff hδ (le_max_left 0 (x + sg t * a)) z).1 rfl
  obtain ⟨h1, h2⟩ := hc
  have hmax := le_max_right 0 (x + sg t * a)
  refine ⟨?_, ?_⟩
  · unfold ilo
    split_ifs with hz
    · exact hx
    · have hpos : 0 < mlo δ z := Novel.D18BoundedNoise.mlo_pos hδ hz
      have : max 0 (x + sg t * a) = x + sg t * a := max_eq_right (by
        by_contra hneg; push Not at hneg
        rw [max_eq_left hneg.le] at h1; linarith)
      rw [this] at h1
      exact max_le hx (by linarith)
  · unfold ihi; linarith

/-- `I_(z,t)` lies in claim 064's expanded interval. -/
theorem icell_sub_ecell (hδ : 0 < δ) (ha : 0 ≤ a) (z : ℕ) (t : Bool) :
    Ico (ilo δ a z t) (ihi δ a z t) ⊆ ecell δ a z := by
  intro x hx
  have hs := sg_abs t
  have hsa : |sg t * a| ≤ a := by rw [abs_mul, hs, one_mul, abs_of_nonneg ha]
  rw [abs_le] at hsa
  refine ⟨?_, ?_⟩
  · unfold elo
    refine max_le ((ilo_nonneg z t).trans hx.1) ?_
    refine le_trans ?_ hx.1
    unfold ilo
    split_ifs with hz
    · subst hz; rw [mlo_zero hδ]; linarith
    · exact le_max_of_le_right (by linarith)
  · unfold ehi; have := hx.2; unfold ihi at this; linarith

/-! ## Subcells of a feasible interval -/

theorem islo_lt (hf : Feas δ a z t) (ℓ : ℕ) {d d' : ℕ} (h : d < d') :
    islo δ a ℓ z t d < islo δ a ℓ z t d' := by
  unfold islo
  have hw : 0 < ihi δ a z t - ilo δ a z t := sub_pos.2 hf
  have : (d : ℝ) < d' := Nat.cast_lt.2 h
  have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
  rw [add_lt_add_iff_left, div_lt_div_iff_of_pos_right h2]
  nlinarith

theorem islo_mono (hf : Feas δ a z t) (ℓ : ℕ) {d d' : ℕ} (h : d ≤ d') :
    islo δ a ℓ z t d ≤ islo δ a ℓ z t d' := by
  rcases h.lt_or_eq with h | h
  · exact (islo_lt hf ℓ h).le
  · rw [h]

theorem islo_nonneg (hf : Feas δ a z t) (ℓ d : ℕ) : 0 ≤ islo δ a ℓ z t d := by
  unfold islo
  have := (sub_pos.2 hf).le
  have := ilo_nonneg (δ := δ) (a := a) z t
  positivity

theorem islo_zero (ℓ z : ℕ) (t : Bool) : islo δ a ℓ z t 0 = ilo δ a z t := by simp [islo]

theorem islo_top (ℓ z : ℕ) (t : Bool) : islo δ a ℓ z t (2 ^ ℓ) = ihi δ a z t := by
  unfold islo
  rw [Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel_left₀ _ (by positivity)]
  ring

theorem isub_nonneg (hf : Feas δ a z t) {ℓ d : ℕ} {x : ℝ} (hx : x ∈ isub δ a ℓ z t d) : 0 ≤ x :=
  (islo_nonneg hf ℓ d).trans hx.1

theorem isub_cover (hf : Feas δ a z t) (ℓ : ℕ) :
    Ico (ilo δ a z t) (ihi δ a z t) ⊆ ⋃ d ∈ Finset.range (2 ^ ℓ), isub δ a ℓ z t d := by
  intro y hy
  set w := ihi δ a z t - ilo δ a z t
  have hw : 0 < w := sub_pos.2 hf
  have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
  set r := (y - ilo δ a z t) * 2 ^ ℓ / w
  have hr0 : 0 ≤ r := div_nonneg (mul_nonneg (by linarith [hy.1]) h2.le) hw.le
  have hrl : r < 2 ^ ℓ := by
    rw [div_lt_iff₀ hw]
    have : y - ilo δ a z t < w := by simp only [w]; linarith [hy.2]
    nlinarith
  refine mem_iUnion₂.2 ⟨⌊r⌋₊, Finset.mem_range.2 ?_, ?_⟩
  · exact Nat.floor_lt hr0 |>.2 (by exact_mod_cast hrl : r < ((2 ^ ℓ : ℕ) : ℝ))
  · have hf1 := Nat.floor_le hr0
    have hf2 := Nat.lt_floor_add_one r
    have key : ∀ k : ℝ, ilo δ a z t + k * w / 2 ^ ℓ ≤ y ↔ k ≤ r := fun k => by
      rw [← le_sub_iff_add_le', div_le_iff₀ h2, le_div_iff₀ hw]
    have key' : ∀ k : ℝ, y < ilo δ a z t + k * w / 2 ^ ℓ ↔ r < k := fun k => by
      rw [← sub_lt_iff_lt_add', lt_div_iff₀ h2, div_lt_iff₀ hw]
    refine ⟨(key _).2 hf1, ?_⟩
    have := (key' _).2 hf2
    unfold islo
    push_cast
    exact this

theorem isub_nest (hf : Feas δ a z t) (ℓ d : ℕ) :
    isub δ a (ℓ + 1) z t d ⊆ isub δ a ℓ z t (d / 2) := by
  intro x hx
  have hw : ∀ k : ℕ, islo δ a (ℓ + 1) z t (2 * k) = islo δ a ℓ z t k := fun k => by
    unfold islo; push_cast; rw [pow_succ]; field_simp
  have hd := Nat.div_add_mod d 2
  have hm := Nat.mod_lt d two_pos
  constructor
  · rw [← hw]; exact (islo_mono hf _ (by omega)).trans hx.1
  · rw [← hw]; exact hx.2.trans_le (islo_mono hf _ (by omega))

theorem isub_sub (hf : Feas δ a z t) {ℓ d : ℕ} (hd : d < 2 ^ ℓ) :
    isub δ a ℓ z t d ⊆ Ico (ilo δ a z t) (ihi δ a z t) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [← islo_zero (δ := δ) (a := a) ℓ z t]
    exact (islo_mono hf ℓ (Nat.zero_le d)).trans hx.1
  · rw [← islo_top (δ := δ) (a := a) ℓ z t]
    exact hx.2.trans_le (islo_mono hf ℓ hd)

/-- At zero radius, every sign interval is claim 031's cell and its subcells are claim 031's. -/
theorem islo_zero_radius (hδ : 0 < δ) (ℓ z : ℕ) (t : Bool) (d : ℕ) :
    islo δ 0 ℓ z t d = slo δ ℓ z d := by
  have h1 : ilo δ 0 z t = mlo δ z := by
    unfold ilo; split_ifs with hz
    · subst hz; exact (mlo_zero hδ).symm
    · simp only [mul_zero, sub_zero]; exact max_eq_right (mlo_nonneg δ z)
  have h2 : ihi δ 0 z t = mhi δ z := by unfold ihi; simp
  unfold islo slo; rw [h1, h2]

theorem feas_zero_radius (hδ : 0 < δ) (z : ℕ) (t : Bool) : Feas δ 0 z t := by
  have := islo_zero_radius hδ 0 z t 0
  have h1 := islo_zero_radius hδ 0 z t 1
  rw [islo_zero, slo_zero] at this
  unfold Feas
  rw [this, ← islo_top (δ := δ) (a := 0) 0 z t, pow_zero, h1, slo_one]
  exact mlo_lt_mhi hδ z

end Novel.D18SignNoise
