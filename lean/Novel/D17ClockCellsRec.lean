import Novel.D17ClockCellsTrans

/-!
# Claim 034, part 2: the recursion (4) for one box and clock

* `Wcs_mono`: a valid child box gives a smaller transition bound. On a positive source, the child's
  bound is attained inside the child's mean/scale rectangle, which lies in the parent's. From the
  trapped source the zero target gives one for both, and a positive target is attained at the
  child's clipped mean, which lies below the parent's highest mean.
* `Uc_bounds`, `Uc_mono`: every `U` is in `(0, 1]`, and decreases with the box (double induction,
  as in claim 030).
* `walk_le_Uc` (claims 030–031's finite-partition argument): from every state of a subcell, for every
  parameter in the box, the label probability is at most `U`. Claim 031's first-step decomposition
  `walk_le_sum` is used with the transition bound of part 1.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D17ClockCells

open Standalone.D17ClockCells Standalone.D14FixedTick Novel.D14FixedTick Novel.GaussianCell

/-- Step means under the parameters `p = (b, w)` and the clock `vc`. -/
noncomputable def muC {n : ℕ} (Δ vc : Fin n → ℝ) (p : ℝ × ℝ) : Fin n → ℝ :=
  fun j => p.1 * Δ j - p.2 * vc j / 2

/-- Step standard deviations. -/
noncomputable def sdC {n : ℕ} (vc : Fin n → ℝ) (p : ℝ × ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (p.2 * vc j)

section

variable {δ : ℝ} {B : Box}

theorem Wcs_bounds (hδ : 0 < δ) (hB : B.Valid) {Δ v : ℝ} (hΔ : 0 < Δ) (hv : 0 < v) (ℓ z a z' d : ℕ) :
    0 < Wcs δ B Δ v ℓ z a z' d ∧ Wcs δ B Δ v ℓ z a z' d ≤ 1 :=
  let h := transition_holds B _ _ _ _ Δ v hB (slo_nonneg hδ ℓ z a) (slo_lt hδ ℓ z (Nat.lt_succ_self a))
    (slo_nonneg hδ ℓ z' d) (slo_lt hδ ℓ z' (Nat.lt_succ_self d)) hΔ hv
  ⟨h.1, h.2.1⟩

theorem step_le_Wcs (hδ : 0 < δ) (hB : B.Valid) {Δ v : ℝ} (hΔ : 0 < Δ) (hv : 0 < v) {ℓ z a : ℕ}
    (z' d : ℕ) {x : ℝ} (hx : x ∈ sub δ ℓ z a) {p : ℝ × ℝ} (hp : B.Mem p) :
    stepP (p.1 * Δ - p.2 * v / 2) (Real.sqrt (p.2 * v)) x (sub δ ℓ z' d) ≤
      ENNReal.ofReal (Wcs δ B Δ v ℓ z a z' d) :=
  (transition_holds B _ _ _ _ Δ v hB (slo_nonneg hδ ℓ z a) (slo_lt hδ ℓ z (Nat.lt_succ_self a))
    (slo_nonneg hδ ℓ z' d) (slo_lt hδ ℓ z' (Nat.lt_succ_self d)) hΔ hv).2.2.1 x hx p hp

end

/-! ## Monotonicity of the transition bound in the box -/

section Mono

variable {B B' : Box} {a dS c dT Δ v : ℝ}

theorem meanLo_mono (hsub : B'.Sub B) (hΔ : 0 < Δ) (hv : 0 < v) :
    meanLo B a Δ v ≤ meanLo B' a Δ v := by
  unfold meanLo
  nlinarith [mul_le_mul_of_nonneg_right hsub.1 hΔ.le, mul_le_mul_of_nonneg_right hsub.2.2.2 hv.le]

theorem meanHi_mono (hsub : B'.Sub B) (hΔ : 0 < Δ) (hv : 0 < v) :
    meanHi B' dS Δ v ≤ meanHi B dS Δ v := by
  unfold meanHi
  nlinarith [mul_le_mul_of_nonneg_right hsub.2.1 hΔ.le, mul_le_mul_of_nonneg_right hsub.2.2.1 hv.le]

theorem sd_sub (hsub : B'.Sub B) (hv : 0 < v) {s : ℝ} (hs : s ∈ Icc (sdLo B' v) (sdHi B' v)) :
    s ∈ Icc (sdLo B v) (sdHi B v) :=
  ⟨(Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hsub.2.2.1 hv.le)).trans hs.1,
   hs.2.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hsub.2.2.2 hv.le))⟩

theorem Wclock_mono (hB : B.Valid) (hB' : B'.Valid) (hsub : B'.Sub B) (ha : 0 ≤ a) (hadS : a < dS)
    (hc : 0 ≤ c) (hcd : c < dT) (hΔ : 0 < Δ) (hv : 0 < v) :
    Wclock B' a dS c dT Δ v ≤ Wclock B a dS c dT Δ v := by
  have hT := transition_holds B a dS c dT Δ v hB ha hadS hc hcd hΔ hv
  have hT' := transition_holds B' a dS c dT Δ v hB' ha hadS hc hcd hΔ hv
  rcases ha.lt_or_eq with ha0 | ha0
  · obtain ⟨m, hm, s, hs, he⟩ := (hT'.2.2.2.1 ha0).2
    rw [← he]
    exact (hT.2.2.2.1 ha0).1 m ⟨(meanLo_mono hsub hΔ hv).trans hm.1,
      hm.2.trans (meanHi_mono hsub hΔ hv)⟩ s (sd_sub hsub hv hs)
  · subst ha0
    rcases hc.lt_or_eq with hc0 | hc0
    · have hs := sstar_mem (c := c) (dT := dT) hB' hv (mstarC B' 0 dS c dT Δ v)
      have hW' : Wclock B' 0 dS c dT Δ v = cellP (sstarC B' c dT v (mstarC B' 0 dS c dT Δ v))
          (Real.log c) (Real.log dT) (mstarC B' 0 dS c dT Δ v) := by
        unfold Wclock; dsimp only; rw [ite_eq_right hc0.ne', gmass_pos_eq hc0.ne']
      rw [hW']
      refine rect_le hB hv hc0 hcd (fun h => absurd rfl h) ?_ (sd_sub hsub hv hs)
      unfold mstarC; dsimp only; rw [ite_eq_left rfl]
      exact (min_le_left _ _).trans (meanHi_mono hsub hΔ hv)
    · subst hc0
      unfold Wclock; simp

end Mono

theorem Wcs_mono {δ : ℝ} (hδ : 0 < δ) {B B' : Box} (hB : B.Valid) (hB' : B'.Valid)
    (hsub : B'.Sub B) {Δ v : ℝ} (hΔ : 0 < Δ) (hv : 0 < v) (ℓ z a z' d : ℕ) :
    Wcs δ B' Δ v ℓ z a z' d ≤ Wcs δ B Δ v ℓ z a z' d :=
  Wclock_mono hB hB' hsub (slo_nonneg hδ ℓ z a) (slo_lt hδ ℓ z (Nat.lt_succ_self a))
    (slo_nonneg hδ ℓ z' d) (slo_lt hδ ℓ z' (Nat.lt_succ_self d)) hΔ hv

/-! ## The recursion -/

section Rec

variable {δ : ℝ} {B : Box}

theorem Uc_nil (ℓ : ℕ) (Δ vc : Fin 0 → ℝ) (z : ℕ) (v : Fin 0 → ℕ) (a : ℕ) :
    Uc δ B ℓ 0 Δ vc z v a = 1 := by
  cases ℓ <;> simp [Uc]

theorem Uc_zero_succ {n : ℕ} (Δ vc : Fin (n + 1) → ℝ) (z : ℕ) (v : Fin (n + 1) → ℕ) (a : ℕ) :
    Uc δ B 0 (n + 1) Δ vc z v a = min 1 (∑ d ∈ Finset.range (2 ^ 0),
      Wcs δ B (Δ 0) (vc 0) 0 z a (v 0) d *
        Uc δ B 0 n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d) := by
  rw [Uc]

theorem Uc_succ_succ (ℓ : ℕ) {n : ℕ} (Δ vc : Fin (n + 1) → ℝ) (z : ℕ) (v : Fin (n + 1) → ℕ)
    (a : ℕ) : Uc δ B (ℓ + 1) (n + 1) Δ vc z v a =
      min (min 1 (∑ d ∈ Finset.range (2 ^ (ℓ + 1)), Wcs δ B (Δ 0) (vc 0) (ℓ + 1) z a (v 0) d *
        Uc δ B (ℓ + 1) n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d))
        (Uc δ B ℓ (n + 1) Δ vc z v (a / 2)) := by
  rw [Uc]

theorem Uc_parent (ℓ : ℕ) {n : ℕ} (Δ vc : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (a : ℕ) :
    Uc δ B (ℓ + 1) n Δ vc z v a ≤ Uc δ B ℓ n Δ vc z v (a / 2) := by
  cases n with
  | zero => rw [Uc_nil, Uc_nil]
  | succ n => rw [Uc_succ_succ]; exact min_le_right _ _

theorem Uc_bounds (hδ : 0 < δ) (hB : B.Valid) :
    ∀ (n ℓ : ℕ) (Δ vc : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (a : ℕ), (∀ j, 0 < Δ j) →
      (∀ j, 0 < vc j) → 0 < Uc δ B ℓ n Δ vc z v a ∧ Uc δ B ℓ n Δ vc z v a ≤ 1
  | 0, ℓ, Δ, vc, z, v, a, _, _ => by rw [Uc_nil]; exact ⟨one_pos, le_rfl⟩
  | n + 1, ℓ, Δ, vc, z, v, a, hΔ, hv => by
    have IH := Uc_bounds hδ hB n
    have hT : ∀ ℓ' a', 0 < ∑ d ∈ Finset.range (2 ^ ℓ'), Wcs δ B (Δ 0) (vc 0) ℓ' z a' (v 0) d *
        Uc δ B ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d := fun ℓ' a' =>
      Finset.sum_pos (fun d _ => mul_pos (Wcs_bounds hδ hB (hΔ 0) (hv 0) _ _ _ _ _).1
        (IH ℓ' _ _ _ _ d (fun j => hΔ _) (fun j => hv _)).1)
        ⟨0, Finset.mem_range.2 (pow_pos two_pos _)⟩
    induction ℓ generalizing a with
    | zero => rw [Uc_zero_succ]; exact ⟨lt_min one_pos (hT 0 a), min_le_left _ _⟩
    | succ ℓ ih =>
      rw [Uc_succ_succ]
      exact ⟨lt_min (lt_min one_pos (hT _ a)) (ih (a / 2)).1, (min_le_left _ _).trans (min_le_left _ _)⟩

theorem Uc_mono (hδ : 0 < δ) (hB : B.Valid) {B' : Box} (hB' : B'.Valid) (hsub : B'.Sub B) :
    ∀ (n ℓ : ℕ) (Δ vc : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (a : ℕ), (∀ j, 0 < Δ j) →
      (∀ j, 0 < vc j) → Uc δ B' ℓ n Δ vc z v a ≤ Uc δ B ℓ n Δ vc z v a
  | 0, ℓ, Δ, vc, z, v, a, _, _ => by rw [Uc_nil, Uc_nil]
  | n + 1, ℓ, Δ, vc, z, v, a, hΔ, hv => by
    have IH := Uc_mono hδ hB hB' hsub n
    have hT : ∀ ℓ' a', ∑ d ∈ Finset.range (2 ^ ℓ'), Wcs δ B' (Δ 0) (vc 0) ℓ' z a' (v 0) d *
          Uc δ B' ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d ≤
        ∑ d ∈ Finset.range (2 ^ ℓ'), Wcs δ B (Δ 0) (vc 0) ℓ' z a' (v 0) d *
          Uc δ B ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d := fun ℓ' a' =>
      Finset.sum_le_sum fun d _ => mul_le_mul (Wcs_mono hδ hB hB' hsub (hΔ 0) (hv 0) _ _ _ _ _)
        (IH ℓ' _ _ _ _ d (fun j => hΔ _) (fun j => hv _))
        (Uc_bounds hδ hB' n ℓ' _ _ _ _ d (fun j => hΔ _) (fun j => hv _)).1.le
        (Wcs_bounds hδ hB (hΔ 0) (hv 0) _ _ _ _ _).1.le
    induction ℓ generalizing a with
    | zero => rw [Uc_zero_succ, Uc_zero_succ]; exact min_le_min le_rfl (hT 0 a)
    | succ ℓ ih =>
      rw [Uc_succ_succ, Uc_succ_succ]
      exact min_le_min (min_le_min le_rfl (hT _ a)) (ih (a / 2))

/-- From every state of the subcell and every parameter in the box, the label probability is at
most `U`. -/
theorem walk_le_Uc (hδ : 0 < δ) (hB : B.Valid) :
    ∀ (n ℓ : ℕ) (Δ vc : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (a : ℕ), (∀ j, 0 < Δ j) →
      (∀ j, 0 < vc j) → a < 2 ^ ℓ → ∀ p, B.Mem p → ∀ x ∈ sub δ ℓ z a,
        walkM δ (muC Δ vc p) (sdC vc p) x {v} ≤ ENNReal.ofReal (Uc δ B ℓ n Δ vc z v a)
  | 0, ℓ, Δ, vc, z, v, a, _, _, _, p, _, x, _ => by
    rw [Uc_nil, ENNReal.ofReal_one]; exact prob_le_one
  | n + 1, ℓ, Δ, vc, z, v, a, hΔ, hv, ha, p, hp, x, hx => by
    have IH := walk_le_Uc hδ hB n
    have hTw : ∀ ℓ' a', ∀ x ∈ sub δ ℓ' z a', walkM δ (muC Δ vc p) (sdC vc p) x {v} ≤
        ENNReal.ofReal (∑ d ∈ Finset.range (2 ^ ℓ'), Wcs δ B (Δ 0) (vc 0) ℓ' z a' (v 0) d *
          Uc δ B ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d) := fun ℓ' a' x hx => by
      refine (walk_le_sum hδ (muC Δ vc p) (sdC vc p) (sub_nonneg' hδ hx) v (Finset.range (2 ^ ℓ'))
        (sub δ ℓ' (v 0)) (fun d => ENNReal.ofReal
          (Uc δ B ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d))
        (fun _ => measurableSet_Ico) (sub_cover hδ ℓ' (v 0))
        (fun d hd y hy _ => IH ℓ' _ _ _ _ d (fun j => hΔ _) (fun j => hv _)
          (Finset.mem_range.1 hd) p hp y hy)).trans ?_
      have hnn : ∀ d ∈ Finset.range (2 ^ ℓ'), 0 ≤ Wcs δ B (Δ 0) (vc 0) ℓ' z a' (v 0) d *
          Uc δ B ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d := fun d _ =>
        mul_nonneg (Wcs_bounds hδ hB (hΔ 0) (hv 0) _ _ _ _ _).1.le
          (Uc_bounds hδ hB n ℓ' _ _ _ _ d (fun j => hΔ _) (fun j => hv _)).1.le
      rw [ENNReal.ofReal_sum_of_nonneg hnn]
      refine Finset.sum_le_sum fun d _ => ?_
      rw [ENNReal.ofReal_mul (Wcs_bounds hδ hB (hΔ 0) (hv 0) _ _ _ _ _).1.le]
      gcongr
      exact step_le_Wcs hδ hB (hΔ 0) (hv 0) _ _ hx hp
    have h1 : ∀ x, walkM δ (muC Δ vc p) (sdC vc p) x {v} ≤ ENNReal.ofReal 1 := fun x => by
      rw [ENNReal.ofReal_one]; exact prob_le_one
    induction ℓ generalizing a x with
    | zero =>
      rw [Uc_zero_succ]
      exact le_ofReal_min (h1 x) (hTw 0 a x hx)
    | succ ℓ ih =>
      have ha2 : a / 2 < 2 ^ ℓ := by rw [pow_succ] at ha; omega
      rw [Uc_succ_succ]
      exact le_ofReal_min (le_ofReal_min (h1 x) (hTw _ a x hx))
        (ih (a / 2) ha2 x (sub_nest hδ ℓ z a hx))

end Rec

/-! ## The initial-subcell maximum -/

section Bc

variable {δ : ℝ} {B : Box}

theorem Bc_bounds (hδ : 0 < δ) (hB : B.Valid) (ℓ : ℕ) {n : ℕ} {Δ vc : Fin n → ℝ}
    (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < vc j) (z₀ : ℕ) (v : Fin n → ℕ) :
    0 < Bc δ B ℓ Δ vc z₀ v ∧ Bc δ B ℓ Δ vc z₀ v ≤ 1 :=
  ⟨(Uc_bounds hδ hB n ℓ Δ vc z₀ v 0 hΔ hv).1.trans_le (Finset.le_sup' _ (mem_range_pow ℓ)),
   Finset.sup'_le _ _ fun a _ => (Uc_bounds hδ hB n ℓ Δ vc z₀ v a hΔ hv).2⟩

theorem Bc_succ_le (ℓ : ℕ) {n : ℕ} (Δ vc : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ) :
    Bc δ B (ℓ + 1) Δ vc z₀ v ≤ Bc δ B ℓ Δ vc z₀ v := by
  unfold Bc
  refine Finset.sup'_le _ _ fun a ha => (Uc_parent ℓ Δ vc z₀ v a).trans ?_
  refine Finset.le_sup' (Uc δ B ℓ n Δ vc z₀ v) (Finset.mem_range.2 ?_)
  have := Finset.mem_range.1 ha
  rw [pow_succ] at this; omega

theorem Bc_mono (hδ : 0 < δ) (hB : B.Valid) {B' : Box} (hB' : B'.Valid) (hsub : B'.Sub B)
    (ℓ : ℕ) {n : ℕ} {Δ vc : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < vc j) (z₀ : ℕ)
    (v : Fin n → ℕ) : Bc δ B' ℓ Δ vc z₀ v ≤ Bc δ B ℓ Δ vc z₀ v :=
  Finset.sup'_le _ _ fun a ha => (Uc_mono hδ hB hB' hsub n ℓ Δ vc z₀ v a hΔ hv).trans
    (Finset.le_sup' (Uc δ B ℓ n Δ vc z₀ v) ha)

theorem walk_le_Bc (hδ : 0 < δ) (hB : B.Valid) (ℓ : ℕ) {n : ℕ} {Δ vc : Fin n → ℝ}
    (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < vc j) {z₀ : ℕ} (v : Fin n → ℕ) {p : ℝ × ℝ} (hp : B.Mem p)
    {x : ℝ} (hx : x ∈ mcell δ z₀) :
    walkM δ (muC Δ vc p) (sdC vc p) x {v} ≤ ENNReal.ofReal (Bc δ B ℓ Δ vc z₀ v) := by
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (sub_cover hδ ℓ z₀ hx)
  exact (walk_le_Uc hδ hB n ℓ Δ vc z₀ v a hΔ hv (Finset.mem_range.1 ha) p hp x hxa).trans
    (ENNReal.ofReal_le_ofReal (Finset.le_sup' (Uc δ B ℓ n Δ vc z₀ v) ha))

end Bc

end Novel.D17ClockCells
