import Novel.D14FixedTickWalk

/-!
# Claim 031, part 2: claim 030's backward recursion on monetary subcells

* The `2^ℓ` subcells of `C_z^δ` are nonempty, in increasing order, and cover the cell. Each one lies
  in its parent at level `ℓ − 1`. Subcell `0` of `C_0^δ` starts at the trapped state `0`.
* `bounds_aux`: every `U` lies in `(0, 1]` and bounds the remaining-path probability from every
  exact state of its subcell. The proof is by induction on the path length and then the level,
  using `walk_le_sum` with the subcells of the next observed cell, the parent bound and `1`.
* `Ub_level0`: level zero is part 1's direct envelope. With the parent bound this gives the
  ordering (3).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14FixedTick

open Standalone.D14FixedTick Novel.GaussianCell Novel.D14CellEnvelope

variable {δ : ℝ}

theorem width_pos (hδ : 0 < δ) (z : ℕ) : 0 < mhi δ z - mlo δ z := sub_pos.2 (mlo_lt_mhi hδ z)

theorem slo_lt (hδ : 0 < δ) (ℓ z : ℕ) {a a' : ℕ} (h : a < a') : slo δ ℓ z a < slo δ ℓ z a' := by
  unfold slo
  have hw := width_pos hδ z
  have : (a : ℝ) < a' := Nat.cast_lt.2 h
  have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
  rw [add_lt_add_iff_left, div_lt_div_iff_of_pos_right h2]
  nlinarith

theorem slo_nonneg (hδ : 0 < δ) (ℓ z a : ℕ) : 0 ≤ slo δ ℓ z a := by
  unfold slo
  have := (width_pos hδ z).le
  have := mlo_nonneg δ z
  positivity

theorem slo_zero (ℓ z : ℕ) : slo δ ℓ z 0 = mlo δ z := by simp [slo]

theorem slo_top (ℓ z : ℕ) : slo δ ℓ z (2 ^ ℓ) = mhi δ z := by
  unfold slo
  rw [Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel_left₀ _ (by positivity)]
  ring

theorem sub_nonneg' (hδ : 0 < δ) {ℓ z a : ℕ} {x : ℝ} (hx : x ∈ sub δ ℓ z a) : 0 ≤ x :=
  (slo_nonneg hδ ℓ z a).trans hx.1

theorem sub_cover (hδ : 0 < δ) (ℓ z : ℕ) :
    mcell δ z ⊆ ⋃ d ∈ Finset.range (2 ^ ℓ), sub δ ℓ z d := by
  intro y hy
  set w := mhi δ z - mlo δ z
  have hw := width_pos hδ z
  have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
  set t := (y - mlo δ z) * 2 ^ ℓ / w
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg (by linarith [hy.1]) h2.le) hw.le
  have htl : t < 2 ^ ℓ := by
    rw [div_lt_iff₀ hw]
    have : y - mlo δ z < w := by simp only [w]; linarith [hy.2]
    nlinarith
  refine mem_iUnion₂.2 ⟨⌊t⌋₊, Finset.mem_range.2 ?_, ?_⟩
  · have := Nat.floor_lt ht0 |>.2 (by exact_mod_cast htl : t < ((2 ^ ℓ : ℕ) : ℝ))
    exact this
  · have hf1 := Nat.floor_le ht0
    have hf2 := Nat.lt_floor_add_one t
    have key : ∀ k : ℝ, slo δ ℓ z 0 + k * w / 2 ^ ℓ ≤ y ↔ k ≤ t := fun k => by
      rw [slo_zero, ← le_sub_iff_add_le', div_le_iff₀ h2, le_div_iff₀ hw]
    have key' : ∀ k : ℝ, y < slo δ ℓ z 0 + k * w / 2 ^ ℓ ↔ t < k := fun k => by
      rw [slo_zero, ← sub_lt_iff_lt_add', lt_div_iff₀ h2, div_lt_iff₀ hw]
    constructor
    · have := (key _).2 hf1
      rwa [slo_zero] at this
    · have := (key' _).2 hf2
      rw [slo_zero] at this
      unfold slo
      push_cast
      exact this

theorem sub_nest (hδ : 0 < δ) (ℓ z a : ℕ) : sub δ (ℓ + 1) z a ⊆ sub δ ℓ z (a / 2) := by
  intro x hx
  have hw : ∀ k : ℕ, slo δ (ℓ + 1) z (2 * k) = slo δ ℓ z k := fun k => by
    unfold slo; push_cast; rw [pow_succ]; field_simp
  have hmono : Monotone fun k : ℕ => slo δ (ℓ + 1) z k := fun k k' hk => by
    rcases hk.lt_or_eq with hk | hk
    · exact (slo_lt hδ _ _ hk).le
    · rw [hk]
  have hd := Nat.div_add_mod a 2
  have hm := Nat.mod_lt a two_pos
  constructor
  · rw [← hw]; exact (hmono (by omega)).trans hx.1
  · rw [← hw]; exact hx.2.trans_le (hmono (by omega))

theorem Wsub_bounds (hδ : 0 < δ) {μ s : ℝ} (hs : 0 < s) (ℓ z a z' d : ℕ) :
    0 < Wsub δ μ s ℓ z a z' d ∧ Wsub δ μ s ℓ z a z' d ≤ 1 :=
  let h := interval_holds (μ := μ) (slo_nonneg hδ ℓ z a) (slo_lt hδ ℓ z (Nat.lt_succ_self a))
    (slo_nonneg hδ ℓ z' d) (slo_lt hδ ℓ z' (Nat.lt_succ_self d)) hs
  ⟨h.2.2.1, h.2.2.2⟩

theorem step_le_Wsub (hδ : 0 < δ) {μ s : ℝ} (hs : 0 < s) {ℓ z a : ℕ} (z' d : ℕ) {x : ℝ}
    (hx : x ∈ sub δ ℓ z a) :
    stepP μ s x (sub δ ℓ z' d) ≤ ENNReal.ofReal (Wsub δ μ s ℓ z a z' d) :=
  (interval_holds (μ := μ) (slo_nonneg hδ ℓ z a) (slo_lt hδ ℓ z (Nat.lt_succ_self a))
    (slo_nonneg hδ ℓ z' d) (slo_lt hδ ℓ z' (Nat.lt_succ_self d)) hs).1 x hx

theorem Ub_nil (ℓ : ℕ) (μ s : Fin 0 → ℝ) (z : ℕ) (v : Fin 0 → ℕ) (a : ℕ) :
    Ub δ ℓ 0 μ s z v a = 1 := by
  cases ℓ <;> simp [Ub]

theorem Ub_zero_succ {n : ℕ} (μ s : Fin (n + 1) → ℝ) (z : ℕ) (v : Fin (n + 1) → ℕ) (a : ℕ) :
    Ub δ 0 (n + 1) μ s z v a = min 1 (∑ d ∈ Finset.range (2 ^ 0), Wsub δ (μ 0) (s 0) 0 z a (v 0) d *
      Ub δ 0 n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d) := by
  rw [Ub]

theorem Ub_succ_succ (ℓ : ℕ) {n : ℕ} (μ s : Fin (n + 1) → ℝ) (z : ℕ) (v : Fin (n + 1) → ℕ)
    (a : ℕ) : Ub δ (ℓ + 1) (n + 1) μ s z v a =
      min (min 1 (∑ d ∈ Finset.range (2 ^ (ℓ + 1)), Wsub δ (μ 0) (s 0) (ℓ + 1) z a (v 0) d *
        Ub δ (ℓ + 1) n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d))
        (Ub δ ℓ (n + 1) μ s z v (a / 2)) := by
  rw [Ub]

theorem le_ofReal_min {w : ℝ≥0∞} {a b : ℝ} (ha : w ≤ ENNReal.ofReal a)
    (hb : w ≤ ENNReal.ofReal b) : w ≤ ENNReal.ofReal (min a b) := by
  rcases le_total a b with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

/-- The `T` step of (3): from subcell `a`, the path has probability at most `T`. -/
theorem walk_le_T (hδ : 0 < δ) {n : ℕ} (μ s : Fin (n + 1) → ℝ) (hs : ∀ j, 0 < s j) (ℓ z : ℕ)
    (v : Fin (n + 1) → ℕ) (a : ℕ) (Un : ℕ → ℝ) (hUn : ∀ d < 2 ^ ℓ, 0 ≤ Un d)
    (hnext : ∀ d < 2 ^ ℓ, ∀ y ∈ sub δ ℓ (v 0) d,
      walkM δ (Fin.tail μ) (Fin.tail s) y {Fin.tail v} ≤ ENNReal.ofReal (Un d))
    {x : ℝ} (hx : x ∈ sub δ ℓ z a) :
    walkM δ μ s x {v} ≤ ENNReal.ofReal (∑ d ∈ Finset.range (2 ^ ℓ),
      Wsub δ (μ 0) (s 0) ℓ z a (v 0) d * Un d) := by
  refine (walk_le_sum hδ μ s (sub_nonneg' hδ hx) v (Finset.range (2 ^ ℓ)) (sub δ ℓ (v 0))
    (fun d => ENNReal.ofReal (Un d)) (fun _ => measurableSet_Ico) (sub_cover hδ ℓ (v 0))
    (fun d hd y hy _ => hnext d (Finset.mem_range.1 hd) y hy)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun d _ =>
    mul_nonneg (Wsub_bounds hδ (hs 0) _ _ _ _ _).1.le (hUn d (Finset.mem_range.1 ‹_›))]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [ENNReal.ofReal_mul (Wsub_bounds hδ (hs 0) _ _ _ _ _).1.le]
  gcongr
  exact step_le_Wsub hδ (hs 0) _ _ hx

/-- Part 2's subcell assertion. -/
theorem bounds_aux (hδ : 0 < δ) : ∀ (n ℓ : ℕ) (μ s : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (a : ℕ),
    (∀ j, 0 < s j) → a < 2 ^ ℓ →
    0 < Ub δ ℓ n μ s z v a ∧ Ub δ ℓ n μ s z v a ≤ 1 ∧
    ∀ x ∈ sub δ ℓ z a, walkM δ μ s x {v} ≤ ENNReal.ofReal (Ub δ ℓ n μ s z v a)
  | 0, ℓ, μ, s, z, v, a, _, _ => by
    rw [Ub_nil]
    exact ⟨one_pos, le_rfl, fun x _ => by rw [ENNReal.ofReal_one]; exact prob_le_one⟩
  | n + 1, ℓ, μ, s, z, v, a, hs, ha => by
    have IH := bounds_aux hδ n
    have hT : ∀ ℓ' a', 0 < ∑ d ∈ Finset.range (2 ^ ℓ'), Wsub δ (μ 0) (s 0) ℓ' z a' (v 0) d *
        Ub δ ℓ' n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d := fun ℓ' a' => by
      refine Finset.sum_pos' (fun d hd => mul_nonneg (Wsub_bounds hδ (hs 0) _ _ _ _ _).1.le
        (IH ℓ' _ _ _ _ d (fun j => hs _) (Finset.mem_range.1 hd)).1.le)
        ⟨0, Finset.mem_range.2 (pow_pos two_pos _), mul_pos (Wsub_bounds hδ (hs 0) _ _ _ _ _).1
          (IH ℓ' _ _ _ _ 0 (fun j => hs _) (pow_pos two_pos _)).1⟩
    have hTwalk : ∀ ℓ' a', ∀ x ∈ sub δ ℓ' z a', walkM δ μ s x {v} ≤ ENNReal.ofReal
        (∑ d ∈ Finset.range (2 ^ ℓ'), Wsub δ (μ 0) (s 0) ℓ' z a' (v 0) d *
          Ub δ ℓ' n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d) := fun ℓ' a' x hx =>
      walk_le_T hδ μ s hs ℓ' z v a' _
        (fun d hd => (IH ℓ' _ _ _ _ d (fun j => hs _) hd).1.le)
        (fun d hd y hy => (IH ℓ' _ _ _ _ d (fun j => hs _) hd).2.2 y hy) hx
    have h1 : ∀ x, walkM δ μ s x {v} ≤ ENNReal.ofReal 1 := fun x => by
      rw [ENNReal.ofReal_one]; exact prob_le_one
    induction ℓ generalizing a with
    | zero =>
      rw [Ub_zero_succ]
      exact ⟨lt_min one_pos (hT 0 a), min_le_left _ _,
        fun x hx => le_ofReal_min (h1 x) (hTwalk 0 a x hx)⟩
    | succ ℓ ih =>
      have ha2 : a / 2 < 2 ^ ℓ := by rw [pow_succ] at ha; omega
      obtain ⟨hp0, hp1, hpw⟩ := ih (a / 2) ha2
      rw [Ub_succ_succ]
      refine ⟨lt_min (lt_min one_pos (hT _ a)) hp0, (min_le_left _ _).trans (min_le_left _ _),
        fun x hx => le_ofReal_min (le_ofReal_min (h1 x) (hTwalk _ a x hx))
          (hpw x (sub_nest hδ ℓ z a hx))⟩

/-! ## The ordering (3) -/

theorem slo_one (z : ℕ) : slo δ 0 z 1 = mhi δ z := by
  have := slo_top (δ := δ) 0 z
  simpa using this

theorem Ub_level0 (hδ : 0 < δ) : ∀ (n : ℕ) (μ s : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ),
    (∀ j, 0 < s j) → Ub δ 0 n μ s z v 0 = Bm δ μ s z v
  | 0, μ, s, z, v, _ => by rw [Ub_nil]; simp [Bm]
  | n + 1, μ, s, z, v, hs => by
    rw [Ub_zero_succ, pow_zero, Finset.sum_range_one,
      Ub_level0 hδ n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) (fun j => hs _), Bm_succ]
    have hW : Wsub δ (μ 0) (s 0) 0 z 0 (v 0) 0 =
        Wm (mlo δ z) (mhi δ z) (mlo δ (v 0)) (mhi δ (v 0)) (μ 0) (s 0) := by
      unfold Wsub; rw [slo_zero, slo_zero, zero_add, slo_one, slo_one]
    rw [hW, min_eq_right]
    calc _ ≤ 1 * Bm δ (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) :=
          mul_le_mul_of_nonneg_right (Wm_cell hδ _ _ (hs 0)).2 (Bm_pos hδ (fun j => hs _) _ _).le
      _ ≤ 1 := by rw [one_mul]; exact Bm_le_one hδ (fun j => hs _) _ _

theorem Ub_parent (ℓ : ℕ) {n : ℕ} (μ s : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (a : ℕ) :
    Ub δ (ℓ + 1) n μ s z v a ≤ Ub δ ℓ n μ s z v (a / 2) := by
  cases n with
  | zero => rw [Ub_nil, Ub_nil]
  | succ n => rw [Ub_succ_succ]; exact min_le_right _ _

theorem mem_range_pow (ℓ : ℕ) : 0 ∈ Finset.range (2 ^ ℓ) := Finset.mem_range.2 (pow_pos two_pos ℓ)

theorem Bl_succ_le (ℓ : ℕ) {n : ℕ} (μ s : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ) :
    Bl δ (ℓ + 1) μ s z₀ v ≤ Bl δ ℓ μ s z₀ v := by
  unfold Bl
  refine Finset.sup'_le _ _ fun a ha => (Ub_parent ℓ μ s z₀ v a).trans ?_
  refine Finset.le_sup' (Ub δ ℓ n μ s z₀ v) (Finset.mem_range.2 ?_)
  have := Finset.mem_range.1 ha
  rw [pow_succ] at this; omega

theorem Bl_le_Bm (hδ : 0 < δ) {n : ℕ} {μ s : Fin n → ℝ} (hs : ∀ j, 0 < s j) (z₀ : ℕ)
    (v : Fin n → ℕ) : ∀ ℓ, Bl δ ℓ μ s z₀ v ≤ Bm δ μ s z₀ v
  | 0 => by
    unfold Bl
    refine Finset.sup'_le _ _ fun a ha => ?_
    rw [pow_zero, Finset.mem_range, Nat.lt_one_iff] at ha
    rw [ha, Ub_level0 hδ n μ s z₀ v hs]
  | ℓ + 1 => (Bl_succ_le ℓ μ s z₀ v).trans (Bl_le_Bm hδ hs z₀ v ℓ)

theorem Bl_pos (hδ : 0 < δ) (ℓ : ℕ) {n : ℕ} {μ s : Fin n → ℝ} (hs : ∀ j, 0 < s j) (z₀ : ℕ)
    (v : Fin n → ℕ) : 0 < Bl δ ℓ μ s z₀ v :=
  (bounds_aux hδ n ℓ μ s z₀ v 0 hs (pow_pos two_pos ℓ)).1.trans_le
    (Finset.le_sup' (Ub δ ℓ n μ s z₀ v) (mem_range_pow ℓ))

theorem Bl_le_one (hδ : 0 < δ) (ℓ : ℕ) {n : ℕ} {μ s : Fin n → ℝ} (hs : ∀ j, 0 < s j) (z₀ : ℕ)
    (v : Fin n → ℕ) : Bl δ ℓ μ s z₀ v ≤ 1 :=
  Finset.sup'_le _ _ fun a ha =>
    (bounds_aux hδ n ℓ μ s z₀ v a hs (Finset.mem_range.1 ha)).2.1

/-- (3) from every exact start in the last training cell, at every level. -/
theorem walk_le_Bl (hδ : 0 < δ) (ℓ : ℕ) {n : ℕ} {μ s : Fin n → ℝ} (hs : ∀ j, 0 < s j) {z₀ : ℕ}
    (v : Fin n → ℕ) {x : ℝ} (hx : x ∈ mcell δ z₀) :
    walkM δ μ s x {v} ≤ ENNReal.ofReal (Bl δ ℓ μ s z₀ v) := by
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (sub_cover hδ ℓ z₀ hx)
  exact ((bounds_aux hδ n ℓ μ s z₀ v a hs (Finset.mem_range.1 ha)).2.2 x hxa).trans
    (ENNReal.ofReal_le_ofReal (Finset.le_sup' (Ub δ ℓ n μ s z₀ v) ha))

/-! ## The all-zero path from a zero quote -/

theorem mlo_zero (hδ : 0 < δ) : mlo δ 0 = 0 := by
  unfold mlo; push_cast; exact max_eq_left (by nlinarith)

theorem Ub_allzero (hδ : 0 < δ) : ∀ (n ℓ : ℕ) (μ s : Fin n → ℝ), (∀ j, 0 < s j) →
    Ub δ ℓ n μ s 0 (fun _ => 0) 0 = 1
  | 0, ℓ, μ, s, _ => Ub_nil ℓ μ s 0 _ 0
  | n + 1, ℓ, μ, s, hs => by
    have hW : ∀ ℓ', Wsub δ (μ 0) (s 0) ℓ' 0 0 0 0 = 1 := fun ℓ' => by
      unfold Wsub; rw [slo_zero, mlo_zero hδ, Wm_c0_a0]
    have hT : ∀ ℓ', 1 ≤ ∑ d ∈ Finset.range (2 ^ ℓ'), Wsub δ (μ 0) (s 0) ℓ' 0 0 0 d *
        Ub δ ℓ' n (Fin.tail μ) (Fin.tail s) 0 (fun _ => 0) d := fun ℓ' => by
      have h0 : Wsub δ (μ 0) (s 0) ℓ' 0 0 0 0 *
          Ub δ ℓ' n (Fin.tail μ) (Fin.tail s) 0 (fun _ => 0) 0 = 1 := by
        rw [hW, one_mul]
        exact Ub_allzero hδ n ℓ' (Fin.tail μ) (Fin.tail s) (fun j => hs _)
      rw [← h0]
      refine Finset.single_le_sum (f := fun d => Wsub δ (μ 0) (s 0) ℓ' 0 0 0 d *
        Ub δ ℓ' n (Fin.tail μ) (Fin.tail s) 0 (fun _ => 0) d) (fun d hd => ?_) (mem_range_pow ℓ')
      exact mul_nonneg (Wsub_bounds hδ (hs 0) _ _ _ _ _).1.le
        (bounds_aux hδ n ℓ' _ _ _ _ d (fun j => hs _) (Finset.mem_range.1 hd)).1.le
    induction ℓ with
    | zero =>
      rw [Ub_zero_succ]
      exact min_eq_left (hT 0)
    | succ ℓ ih =>
      rw [Ub_succ_succ, Nat.zero_div, ih]
      exact (congrArg (min · 1) (min_eq_left (hT (ℓ + 1)))).trans (min_self 1)

theorem mlabels_zero (δ : ℝ) : ∀ (n : ℕ) (ξ : Fin n → ℝ), mlabels δ n 0 ξ = fun _ => 0
  | 0, _ => funext fun j => j.elim0
  | n + 1, ξ => by
    have h0 : mlabel δ 0 = 0 := by norm_num [mlabel]
    rw [show mlabels δ (n + 1) 0 ξ = Fin.cons (mlabel δ (0 * Real.exp (ξ 0)))
      (mlabels δ n (0 * Real.exp (ξ 0)) (Fin.tail ξ)) from rfl, zero_mul, h0, mlabels_zero δ n]
    funext j
    refine Fin.cases rfl (fun i => rfl) j

theorem allzero_holds (hδ : 0 < δ) (ℓ n : ℕ) (μ s : Fin n → ℝ) (hs : ∀ j, 0 < s j) :
    Bm δ μ s 0 (fun _ => 0) = 1 ∧ Bl δ ℓ μ s 0 (fun _ => 0) = 1 ∧
      walkM δ μ s 0 {fun _ => 0} = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Ub_level0 hδ n μ s 0 _ hs, Ub_allzero hδ n 0 μ s hs]
  · refine le_antisymm (Bl_le_one hδ ℓ hs _ _) ?_
    rw [← Ub_allzero hδ n ℓ μ s hs]
    exact Finset.le_sup' (Ub δ ℓ n μ s 0 (fun _ => 0)) (mem_range_pow ℓ)
  · rw [walkM, Measure.map_apply (measurable_mlabels' δ n 0) (measurableSet_singleton _)]
    have : mlabels δ n 0 ⁻¹' {fun _ => 0} = univ := by
      ext ξ; simp [mlabels_zero]
    rw [this, measure_univ]

end Novel.D14FixedTick
