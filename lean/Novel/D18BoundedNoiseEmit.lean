import Novel.D18BoundedNoiseSub

/-!
# Claim 064: the uniform emissions (3) and their suprema (4)

* `emission_holds`: (3) is the exact probability that `max(0, x + ε)` has label `z` under the uniform
  error. For `z = 0` the event is `x + ε < δ/2`; for `z > 0` the clamp is irrelevant and the event is
  `l_z ≤ x + ε < r_z`. The uniform probability of an interval is its overlap with `[−a, a]` over `2a`.
* `sup_holds`: (4). The zero-label emission decreases in `x`. The positive-label emission is the
  overlap length `min(a, r − x) + min(a, x − l)`, which increases up to the midpoint and decreases
  after it, so the supremum over `[c, d)` sits at the midpoint clipped to `[c, d]`. When that point
  is the excluded end `d`, continuity gives points of `[c, d)` approaching it.
* `Mnoise` is positive on every subcell of an expanded interval and at most one, and bounds the
  emission there.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Novel.D18BoundedNoise

open Standalone.D18BoundedNoise Standalone.D14FixedTick Novel.D14FixedTick

variable {δ a : ℝ}

theorem mlo_pos (hδ : 0 < δ) {z : ℕ} (hz : z ≠ 0) : 0 < mlo δ z := by
  have : (1 : ℝ) ≤ z := Nat.one_le_cast.2 (Nat.pos_of_ne_zero hz)
  unfold mlo; exact lt_max_of_lt_right (by nlinarith)

theorem mhi_zero : mhi δ 0 = δ / 2 := by unfold mhi; push_cast; ring

theorem gnoise_pos_a {z : ℕ} {x : ℝ} (ha : a ≠ 0) : gnoise δ a z x =
    if z = 0 then min 1 (max 0 ((δ / 2 - x + a) / (2 * a)))
    else max 0 (min a (mhi δ z - x) - max (-a) (mlo δ z - x)) / (2 * a) := by
  unfold gnoise; rw [ite_eq_right ha]

theorem gnoise_bounds (ha : 0 ≤ a) (z : ℕ) (x : ℝ) : 0 ≤ gnoise δ a z x ∧ gnoise δ a z x ≤ 1 := by
  rcases ha.lt_or_eq with ha | ha
  · rw [gnoise_pos_a ha.ne']
    split_ifs
    · exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
    · refine ⟨div_nonneg (le_max_left _ _) (by positivity), (div_le_one (by positivity)).2 ?_⟩
      have h1 := min_le_left a (mhi δ z - x)
      have h2 := le_max_left (-a) (mlo δ z - x)
      exact max_le (by positivity) (by linarith)
  · rw [← ha]
    unfold gnoise
    rw [ite_eq_left rfl]
    by_cases h : x ∈ mcell δ z <;> simp [h]

/-- The emission vanishes outside the expanded interval. -/
theorem gnoise_out (hδ : 0 < δ) (ha : 0 ≤ a) {z : ℕ} {x : ℝ} (hx : 0 ≤ x) (hxo : x ∉ ecell δ a z) :
    gnoise δ a z x = 0 := by
  rcases ha.lt_or_eq with ha | ha
  · rw [gnoise_pos_a ha.ne']
    unfold ecell elo ehi at hxo
    rw [mem_Ico, not_and_or, not_le, not_lt] at hxo
    split_ifs with hz
    · subst hz
      rcases hxo with h | h
      · rw [show max 0 (mlo δ 0 - a) = 0 from elo_zero_label ha.le hδ] at h; linarith
      · rw [mhi_zero] at h
        rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)),
          min_eq_right zero_le_one]
    · rw [div_eq_zero_iff]; left
      refine max_eq_left ?_
      rcases hxo with h | h
      · have h' : x < mlo δ z - a := by
          rcases lt_max_iff.1 h with h | h
          · exact absurd h (not_lt.2 hx)
          · exact h
        have := le_max_right (-a) (mlo δ z - x)
        have := min_le_left a (mhi δ z - x)
        linarith
      · have := min_le_right a (mhi δ z - x)
        have := le_max_left (-a) (mlo δ z - x)
        linarith
  · subst ha
    unfold gnoise
    have : x ∉ mcell δ z := by
      unfold ecell at hxo; rwa [show elo δ 0 z = mlo δ z from elo_zero z, ehi, add_zero] at hxo
    simp [this]

/-! ## (3) -/

theorem vol_overlap (a l r : ℝ) :
    volume {e : ℝ | -a ≤ e ∧ e ≤ a ∧ l ≤ e ∧ e < r} = ENNReal.ofReal (min a r - max (-a) l) := by
  refine le_antisymm ?_ ?_
  · calc volume {e : ℝ | -a ≤ e ∧ e ≤ a ∧ l ≤ e ∧ e < r}
        ≤ volume (Icc (max (-a) l) (min a r)) := measure_mono fun e he =>
          ⟨max_le he.1 he.2.2.1, le_min he.2.1 he.2.2.2.le⟩
      _ = _ := Real.volume_Icc
  · calc ENNReal.ofReal (min a r - max (-a) l) = volume (Ico (max (-a) l) (min a r)) :=
          Real.volume_Ico.symm
      _ ≤ _ := measure_mono fun e (he : e ∈ Ico _ _) =>
          (⟨(le_max_left _ _).trans he.1, (lt_min_iff.1 he.2).1.le, (le_max_right _ _).trans he.1,
            (lt_min_iff.1 he.2).2⟩ : -a ≤ e ∧ e ≤ a ∧ l ≤ e ∧ e < r)

theorem noise_apply (ha : 0 < a) {S : Set ℝ} {l r : ℝ}
    (hS : ∀ e, -a ≤ e → e ≤ a → (e ∈ S ↔ l ≤ e ∧ e < r)) :
    noiseLaw a S = ENNReal.ofReal ((min a r - max (-a) l) / (2 * a)) := by
  unfold noiseLaw
  rw [cond_apply measurableSet_Icc, Real.volume_Icc]
  have hset : Icc (-a) a ∩ S = {e : ℝ | -a ≤ e ∧ e ≤ a ∧ l ≤ e ∧ e < r} := by
    ext e
    simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, (hS e h1 h2).1 h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, (hS e h1 h2).2 h3⟩
  rw [hset, vol_overlap, sub_neg_eq_add, ← two_mul, ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.div_eq_inv_mul]

theorem ofReal_clip (y : ℝ) : ENNReal.ofReal (min 1 y) = ENNReal.ofReal (min 1 (max 0 y)) := by
  rcases le_total 0 y with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, min_eq_right (h.trans zero_le_one), min_eq_right zero_le_one,
      ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]

/-- (3) is the exact emission probability. -/
theorem emission_holds (hδ : 0 < δ) (ha : 0 < a) (x : ℝ) (z : ℕ) :
    noiseLaw a {e | mlabel δ (max 0 (x + e)) = z} = ENNReal.ofReal (gnoise δ a z x) := by
  rw [gnoise_pos_a ha.ne']
  split_ifs with hz
  · subst hz
    rw [noise_apply ha (l := -a) (r := δ / 2 - x) fun e h1 _ => by
      rw [mem_ofPred_eq, mlabel_eq_iff hδ (le_max_left _ _), mcell, mem_Ico, mlo_zero hδ, mhi_zero,
        max_lt_iff]
      constructor
      · rintro ⟨-, -, h⟩; exact ⟨h1, by linarith⟩
      · rintro ⟨-, h⟩; exact ⟨le_max_left _ _, by linarith, by linarith⟩]
    rw [max_self, sub_neg_eq_add, ← min_add_add_right,
      ← min_div_div_right (by positivity : (0 : ℝ) ≤ 2 * a),
      show (a + a) / (2 * a) = 1 by field_simp; ring, ofReal_clip]
  · have hl := mlo_pos hδ hz
    rw [noise_apply ha (l := mlo δ z - x) (r := mhi δ z - x) fun e _ _ => by
      rw [mem_ofPred_eq, mlabel_eq_iff hδ (le_max_left _ _), mcell, mem_Ico, le_max_iff, max_lt_iff]
      constructor
      · rintro ⟨h | h, -, h2⟩
        · exact absurd h (not_le.2 hl)
        · exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨Or.inr (by linarith), by linarith [mlo_lt_mhi hδ z], by linarith⟩]
    set w := min a (mhi δ z - x) - max (-a) (mlo δ z - x)
    rcases le_total 0 w with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, zero_div, ENNReal.ofReal_zero,
        ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg h (by positivity))]

/-! ## (4) -/

/-- The overlap length, before clamping. -/
theorem ov_eq (a l r x : ℝ) :
    min a (r - x) - max (-a) (l - x) = min a (r - x) + min a (x - l) := by
  rw [show l - x = -(x - l) by ring, max_neg_neg]; ring

theorem ov_left {a l r x y : ℝ} (hxy : x ≤ y) (hy : y ≤ (l + r) / 2) :
    min a (r - x) + min a (x - l) ≤ min a (r - y) + min a (y - l) := by
  rcases le_total a (r - y) with h | h
  · rw [min_eq_left (show a ≤ r - x by linarith), min_eq_left h]
    have := min_le_min (le_refl a) (show x - l ≤ y - l by linarith)
    linarith
  · rw [min_eq_right h, min_eq_right (show y - l ≤ a by linarith)]
    linarith [min_le_right a (r - x), min_le_right a (x - l)]

theorem ov_right {a l r x y : ℝ} (hxy : y ≤ x) (hy : (l + r) / 2 ≤ y) :
    min a (r - x) + min a (x - l) ≤ min a (r - y) + min a (y - l) := by
  rcases le_total a (y - l) with h | h
  · rw [min_eq_left (show a ≤ x - l by linarith), min_eq_left h]
    have := min_le_min (le_refl a) (show r - x ≤ r - y by linarith)
    linarith
  · rw [min_eq_right h, min_eq_right (show r - y ≤ a by linarith)]
    linarith [min_le_right a (r - x), min_le_right a (x - l)]

theorem continuous_gnoise (ha : a ≠ 0) (z : ℕ) : Continuous (gnoise δ a z) := by
  have e : gnoise δ a z = fun x => gnoise δ a z x := rfl
  rw [e]
  simp_rw [gnoise_pos_a ha]
  split_ifs
  · exact continuous_const.min (continuous_const.max
      (((continuous_const.sub continuous_id).add continuous_const).div_const _))
  · exact (continuous_const.max ((continuous_const.min (continuous_const.sub continuous_id)).sub
      (continuous_const.max (continuous_const.sub continuous_id)))).div_const _

theorem xstar_mem {z : ℕ} {c d : ℝ} (hcd : c < d) : xstar δ z c d ∈ Icc c d := by
  unfold xstar
  split_ifs
  · exact ⟨le_rfl, hcd.le⟩
  · exact ⟨le_max_left _ _, max_le hcd.le (min_le_left _ _)⟩

theorem sup_le (ha : 0 < a) {c d : ℝ} (z : ℕ) {x : ℝ} (hx : x ∈ Ico c d) :
    gnoise δ a z x ≤ gnoise δ a z (xstar δ z c d) := by
  rw [gnoise_pos_a ha.ne', gnoise_pos_a ha.ne']
  unfold xstar
  split_ifs with hz
  · refine min_le_min le_rfl (max_le_max le_rfl ?_)
    exact div_le_div_of_nonneg_right (by linarith [hx.1]) (by positivity)
  · refine div_le_div_of_nonneg_right (max_le_max le_rfl ?_) (by positivity)
    rw [ov_eq, ov_eq]
    set m := (mlo δ z + mhi δ z) / 2
    rcases le_total m c with h1 | h1
    · rw [min_eq_right (h1.trans (hx.1.trans hx.2.le)), max_eq_left h1]
      exact ov_right hx.1 h1
    · rcases le_total d m with h2 | h2
      · rw [min_eq_left h2, max_eq_right (hx.1.trans hx.2.le)]
        exact ov_left hx.2.le h2
      · rw [min_eq_right h2, max_eq_right h1]
        rcases le_total x m with h3 | h3
        · exact ov_left h3 le_rfl
        · exact ov_right h3 le_rfl

theorem sup_approach (ha : 0 < a) {c d : ℝ} (hcd : c < d) (z : ℕ) {y : ℝ}
    (hy : y < gnoise δ a z (xstar δ z c d)) : ∃ x ∈ Ico c d, y < gnoise δ a z x := by
  have hcl : xstar δ z c d ∈ closure (Ico c d) := by
    rw [closure_Ico hcd.ne]; exact xstar_mem hcd
  have : (𝓝[Ico c d] xstar δ z c d).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hev := ((continuous_gnoise (δ := δ) ha.ne' z).continuousWithinAt
    (s := Ico c d) (x := xstar δ z c d)).eventually (lt_mem_nhds hy)
  obtain ⟨x, hyx, hx⟩ := (hev.and self_mem_nhdsWithin).exists
  exact ⟨x, hx, hyx⟩

/-! ## The emission suprema on the expanded subcells -/

theorem Mnoise_le_one (ha : 0 ≤ a) (ℓ z d : ℕ) : Mnoise δ a ℓ z d ≤ 1 := by
  unfold Mnoise; split_ifs
  · exact le_rfl
  · exact (gnoise_bounds ha _ _).2

theorem g_le_Mnoise (ha : 0 ≤ a) {ℓ z d : ℕ} {y : ℝ} (hy : y ∈ esub δ a ℓ z d) :
    gnoise δ a z y ≤ Mnoise δ a ℓ z d := by
  unfold Mnoise; split_ifs with h0
  · exact (gnoise_bounds ha _ _).2
  · exact sup_le (lt_of_le_of_ne ha (Ne.symm h0)) z hy

theorem Mnoise_pos (hδ : 0 < δ) (ha : 0 ≤ a) {ℓ z d : ℕ} (hd : d < 2 ^ ℓ) : 0 < Mnoise δ a ℓ z d := by
  unfold Mnoise
  split_ifs with h0
  · exact one_pos
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
  set c := eslo δ a ℓ z d
  set d' := eslo δ a ℓ z (d + 1)
  have hcd : c < d' := eslo_lt hδ ha ℓ z (Nat.lt_succ_self d)
  have hd' : d' ≤ ehi δ a z := by
    rw [← eslo_top (δ := δ) (a := a) ℓ z]
    rcases (Nat.succ_le_of_lt hd).lt_or_eq with h | h
    · exact (eslo_lt hδ ha ℓ z h).le
    · exact (congrArg (eslo δ a ℓ z) h).le
  have hc0 : elo δ a z ≤ c := by
    rw [← eslo_zero (δ := δ) (a := a) ℓ z]
    rcases (Nat.zero_le d).lt_or_eq with h | h
    · exact (eslo_lt hδ ha ℓ z h).le
    · exact (congrArg (eslo δ a ℓ z) h).le
  rw [gnoise_pos_a h0]
  unfold xstar ehi at *
  split_ifs with hz
  · subst hz
    rw [mhi_zero] at hd'
    refine lt_min one_pos (lt_max_of_lt_right (div_pos (by linarith) (by positivity)))
  · refine div_pos (lt_max_of_lt_right (sub_pos.2 ?_)) (by positivity)
    have hlr := mlo_lt_mhi hδ z
    set m := (mlo δ z + mhi δ z) / 2
    have hlow : mlo δ z - a < max c (min d' m) := by
      refine lt_max_of_lt_right (lt_min ?_ (by simp only [m]; linarith))
      linarith [le_max_right 0 (mlo δ z - a), show elo δ a z = max 0 (mlo δ z - a) from rfl]
    have hhigh : max c (min d' m) < mhi δ z + a :=
      max_lt (by linarith) ((min_le_right _ _).trans_lt (by simp only [m]; linarith))
    exact max_lt_iff.2 ⟨lt_min_iff.2 ⟨by linarith, by linarith⟩, lt_min_iff.2 ⟨by linarith,
      by linarith⟩⟩

theorem gnoise_zero_zero (hδ : 0 < δ) (ha : 0 ≤ a) :
    gnoise δ a 0 0 = if a = 0 then 1 else min 1 (1 / 2 + δ / (4 * a)) := by
  split_ifs with h0
  · subst h0
    unfold gnoise
    have : (0 : ℝ) ∈ mcell δ 0 := by
      unfold mcell; rw [mlo_zero hδ, mhi_zero]; exact ⟨le_rfl, by linarith⟩
    simp [this]
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    rw [gnoise_pos_a h0, ite_eq_left rfl, max_eq_right (div_nonneg (by linarith) (by linarith))]
    congr 1; field_simp; ring

theorem Mnoise_first (hδ : 0 < δ) (ha : 0 ≤ a) (ℓ : ℕ) : Mnoise δ a ℓ 0 0 = gnoise δ a 0 0 := by
  unfold Mnoise
  split_ifs with h0
  · rw [gnoise_zero_zero hδ ha, ite_eq_left h0]
  · unfold xstar; rw [ite_eq_left rfl, eslo_zero, elo_zero_label ha hδ]

end Novel.D18BoundedNoise
