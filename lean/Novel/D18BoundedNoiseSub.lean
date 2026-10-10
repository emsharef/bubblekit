import Standalone.D18BoundedNoise
import Novel.D14FixedTickProof

/-!
# Claim 064: expanded subcells and the recursion (5), deterministically

* The `2^ℓ` subcells of the expanded interval `I_z^a` are nonempty, in increasing order, cover it,
  and each lies in its parent at level `ℓ − 1` (as for claim 031's ordinary cells).
* `Ue_bounds`: with positive emission factors, every `U` lies in `(0, 1]`.
* `Ue_mono`: `U` is monotone in the emission factor, so uniform mode is below support mode.
* `Ue_zero_noise`: at `a = 0` with unit emissions, (5) is claim 031's recursion.
* `Ue_level0`: support mode at level zero is the product of the interval maxima.
* `Bn_allzero`: on the all-zero path from a zero quote, `B = m^n` when the emission factor of the
  first subcell of `I_0^a` is `m` at every level.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18BoundedNoise

open Standalone.D18BoundedNoise Standalone.D14FixedTick Novel.D14FixedTick

variable {δ a : ℝ}

theorem elo_nonneg (z : ℕ) : 0 ≤ elo δ a z := le_max_left _ _

theorem elo_le_mlo (ha : 0 ≤ a) (z : ℕ) : elo δ a z ≤ mlo δ z :=
  max_le (mlo_nonneg δ z) (by linarith)

theorem mhi_le_ehi (ha : 0 ≤ a) (z : ℕ) : mhi δ z ≤ ehi δ a z := by unfold ehi; linarith

theorem ewidth_pos (hδ : 0 < δ) (ha : 0 ≤ a) (z : ℕ) : 0 < ehi δ a z - elo δ a z := by
  have := mlo_lt_mhi hδ z; have := elo_le_mlo (δ := δ) ha z; have := mhi_le_ehi (δ := δ) ha z
  linarith

theorem eslo_lt (hδ : 0 < δ) (ha : 0 ≤ a) (ℓ z : ℕ) {c c' : ℕ} (h : c < c') :
    eslo δ a ℓ z c < eslo δ a ℓ z c' := by
  unfold eslo
  have hw := ewidth_pos hδ ha z
  have : (c : ℝ) < c' := Nat.cast_lt.2 h
  have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
  rw [add_lt_add_iff_left, div_lt_div_iff_of_pos_right h2]
  nlinarith

theorem eslo_nonneg (hδ : 0 < δ) (ha : 0 ≤ a) (ℓ z c : ℕ) : 0 ≤ eslo δ a ℓ z c := by
  unfold eslo
  have := (ewidth_pos hδ ha z).le
  have := elo_nonneg (δ := δ) (a := a) z
  positivity

theorem eslo_zero (ℓ z : ℕ) : eslo δ a ℓ z 0 = elo δ a z := by simp [eslo]

theorem eslo_top (ℓ z : ℕ) : eslo δ a ℓ z (2 ^ ℓ) = ehi δ a z := by
  unfold eslo
  rw [Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel_left₀ _ (by positivity)]
  ring

theorem eslo_one (z : ℕ) : eslo δ a 0 z 1 = ehi δ a z := by
  have := eslo_top (δ := δ) (a := a) 0 z
  simpa using this

theorem esub_nonneg (hδ : 0 < δ) (ha : 0 ≤ a) {ℓ z c : ℕ} {x : ℝ} (hx : x ∈ esub δ a ℓ z c) :
    0 ≤ x :=
  (eslo_nonneg hδ ha ℓ z c).trans hx.1

theorem esub_cover (hδ : 0 < δ) (ha : 0 ≤ a) (ℓ z : ℕ) :
    ecell δ a z ⊆ ⋃ d ∈ Finset.range (2 ^ ℓ), esub δ a ℓ z d := by
  intro y hy
  set w := ehi δ a z - elo δ a z
  have hw := ewidth_pos hδ ha z
  have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
  set t := (y - elo δ a z) * 2 ^ ℓ / w
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg (by linarith [hy.1]) h2.le) hw.le
  have htl : t < 2 ^ ℓ := by
    rw [div_lt_iff₀ hw]
    have : y - elo δ a z < w := by simp only [w]; linarith [hy.2]
    nlinarith
  refine mem_iUnion₂.2 ⟨⌊t⌋₊, Finset.mem_range.2 ?_, ?_⟩
  · exact Nat.floor_lt ht0 |>.2 (by exact_mod_cast htl : t < ((2 ^ ℓ : ℕ) : ℝ))
  · have hf1 := Nat.floor_le ht0
    have hf2 := Nat.lt_floor_add_one t
    have key : ∀ k : ℝ, eslo δ a ℓ z 0 + k * w / 2 ^ ℓ ≤ y ↔ k ≤ t := fun k => by
      rw [eslo_zero, ← le_sub_iff_add_le', div_le_iff₀ h2, le_div_iff₀ hw]
    have key' : ∀ k : ℝ, y < eslo δ a ℓ z 0 + k * w / 2 ^ ℓ ↔ t < k := fun k => by
      rw [eslo_zero, ← sub_lt_iff_lt_add', lt_div_iff₀ h2, div_lt_iff₀ hw]
    constructor
    · have := (key _).2 hf1
      rwa [eslo_zero] at this
    · have := (key' _).2 hf2
      rw [eslo_zero] at this
      unfold eslo
      push_cast
      exact this

theorem esub_nest (hδ : 0 < δ) (ha : 0 ≤ a) (ℓ z c : ℕ) :
    esub δ a (ℓ + 1) z c ⊆ esub δ a ℓ z (c / 2) := by
  intro x hx
  have hw : ∀ k : ℕ, eslo δ a (ℓ + 1) z (2 * k) = eslo δ a ℓ z k := fun k => by
    unfold eslo; push_cast; rw [pow_succ]; field_simp
  have hmono : Monotone fun k : ℕ => eslo δ a (ℓ + 1) z k := fun k k' hk => by
    rcases hk.lt_or_eq with hk | hk
    · exact (eslo_lt hδ ha _ _ hk).le
    · rw [hk]
  have hd := Nat.div_add_mod c 2
  have hm := Nat.mod_lt c two_pos
  constructor
  · rw [← hw]; exact (hmono (by omega)).trans hx.1
  · rw [← hw]; exact hx.2.trans_le (hmono (by omega))

theorem esub_sub_ecell (hδ : 0 < δ) (ha : 0 ≤ a) {ℓ z d : ℕ} (hd : d < 2 ^ ℓ) :
    esub δ a ℓ z d ⊆ ecell δ a z := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [← eslo_zero (δ := δ) (a := a) ℓ z]
    rcases (Nat.zero_le d).lt_or_eq with h | h
    · exact (eslo_lt hδ ha ℓ z h).le.trans hx.1
    · rw [h]; exact hx.1
  · rw [← eslo_top (δ := δ) (a := a) ℓ z]
    refine hx.2.trans_le ?_
    rcases (Nat.succ_le_of_lt hd).lt_or_eq with h | h
    · exact (eslo_lt hδ ha ℓ z h).le
    · rw [show d + 1 = 2 ^ ℓ from h]

theorem Wesub_bounds (hδ : 0 < δ) (ha : 0 ≤ a) {μ s : ℝ} (hs : 0 < s) (ℓ z c z' d : ℕ) :
    0 < Wesub δ a μ s ℓ z c z' d ∧ Wesub δ a μ s ℓ z c z' d ≤ 1 :=
  let h := interval_holds (μ := μ) (eslo_nonneg hδ ha ℓ z c) (eslo_lt hδ ha ℓ z (Nat.lt_succ_self c))
    (eslo_nonneg hδ ha ℓ z' d) (eslo_lt hδ ha ℓ z' (Nat.lt_succ_self d)) hs
  ⟨h.2.2.1, h.2.2.2⟩

theorem step_le_Wesub (hδ : 0 < δ) (ha : 0 ≤ a) {μ s : ℝ} (hs : 0 < s) {ℓ z c : ℕ} (z' d : ℕ)
    {x : ℝ} (hx : x ∈ esub δ a ℓ z c) :
    stepP μ s x (esub δ a ℓ z' d) ≤ ENNReal.ofReal (Wesub δ a μ s ℓ z c z' d) :=
  (interval_holds (μ := μ) (eslo_nonneg hδ ha ℓ z c) (eslo_lt hδ ha ℓ z (Nat.lt_succ_self c))
    (eslo_nonneg hδ ha ℓ z' d) (eslo_lt hδ ha ℓ z' (Nat.lt_succ_self d)) hs).1 x hx

/-! ## Unfolding the recursion -/

variable {M : ℕ → ℕ → ℕ → ℝ}

theorem Ue_nil (ℓ : ℕ) (μ s : Fin 0 → ℝ) (z : ℕ) (v : Fin 0 → ℕ) (c : ℕ) :
    Ue δ a M ℓ 0 μ s z v c = 1 := by
  cases ℓ <;> simp [Ue]

theorem Ue_zero_succ {n : ℕ} (μ s : Fin (n + 1) → ℝ) (z : ℕ) (v : Fin (n + 1) → ℕ) (c : ℕ) :
    Ue δ a M 0 (n + 1) μ s z v c = min 1 (∑ d ∈ Finset.range (2 ^ 0),
      Wesub δ a (μ 0) (s 0) 0 z c (v 0) d * M 0 (v 0) d *
        Ue δ a M 0 n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d) := by
  rw [Ue]

theorem Ue_succ_succ (ℓ : ℕ) {n : ℕ} (μ s : Fin (n + 1) → ℝ) (z : ℕ) (v : Fin (n + 1) → ℕ)
    (c : ℕ) : Ue δ a M (ℓ + 1) (n + 1) μ s z v c =
      min (min 1 (∑ d ∈ Finset.range (2 ^ (ℓ + 1)),
        Wesub δ a (μ 0) (s 0) (ℓ + 1) z c (v 0) d * M (ℓ + 1) (v 0) d *
          Ue δ a M (ℓ + 1) n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d))
        (Ue δ a M ℓ (n + 1) μ s z v (c / 2)) := by
  rw [Ue]

theorem Ue_parent (ℓ : ℕ) {n : ℕ} (μ s : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (c : ℕ) :
    Ue δ a M (ℓ + 1) n μ s z v c ≤ Ue δ a M ℓ n μ s z v (c / 2) := by
  cases n with
  | zero => rw [Ue_nil, Ue_nil]
  | succ n => rw [Ue_succ_succ]; exact min_le_right _ _

/-- Every `U` lies in `(0, 1]` when the emission factors on the subcells are positive. -/
theorem Ue_bounds (hδ : 0 < δ) (ha : 0 ≤ a) (hM : ∀ ℓ z d, d < 2 ^ ℓ → 0 < M ℓ z d) :
    ∀ (n ℓ : ℕ) (μ s : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (c : ℕ), (∀ j, 0 < s j) →
      c < 2 ^ ℓ → 0 < Ue δ a M ℓ n μ s z v c ∧ Ue δ a M ℓ n μ s z v c ≤ 1
  | 0, ℓ, μ, s, z, v, c, _, _ => by rw [Ue_nil]; exact ⟨one_pos, le_rfl⟩
  | n + 1, ℓ, μ, s, z, v, c, hs, hc => by
    have IH := Ue_bounds hδ ha hM n
    have hT : ∀ ℓ' c', 0 < ∑ d ∈ Finset.range (2 ^ ℓ'),
        Wesub δ a (μ 0) (s 0) ℓ' z c' (v 0) d * M ℓ' (v 0) d *
          Ue δ a M ℓ' n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d := fun ℓ' c' => by
      refine Finset.sum_pos' (fun d hd => mul_nonneg (mul_nonneg
        (Wesub_bounds hδ ha (hs 0) _ _ _ _ _).1.le (hM _ _ _ (Finset.mem_range.1 hd)).le)
        (IH ℓ' _ _ _ _ d (fun j => hs _) (Finset.mem_range.1 hd)).1.le)
        ⟨0, Finset.mem_range.2 (pow_pos two_pos _), mul_pos (mul_pos
          (Wesub_bounds hδ ha (hs 0) _ _ _ _ _).1 (hM _ _ _ (pow_pos two_pos _)))
          (IH ℓ' _ _ _ _ 0 (fun j => hs _) (pow_pos two_pos _)).1⟩
    induction ℓ generalizing c with
    | zero =>
      rw [Ue_zero_succ]
      exact ⟨lt_min one_pos (hT 0 c), min_le_left _ _⟩
    | succ ℓ ih =>
      have hc2 : c / 2 < 2 ^ ℓ := by rw [pow_succ] at hc; omega
      obtain ⟨hp0, -⟩ := ih (c / 2) hc2
      rw [Ue_succ_succ]
      exact ⟨lt_min (lt_min one_pos (hT _ c)) hp0, (min_le_left _ _).trans (min_le_left _ _)⟩

/-- `U` is monotone in the emission factor. -/
theorem Ue_mono (hδ : 0 < δ) (ha : 0 ≤ a) {M' : ℕ → ℕ → ℕ → ℝ}
    (hM : ∀ ℓ z d, d < 2 ^ ℓ → 0 < M ℓ z d) (hMM : ∀ ℓ z d, d < 2 ^ ℓ → M ℓ z d ≤ M' ℓ z d) :
    ∀ (n ℓ : ℕ) (μ s : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (c : ℕ), (∀ j, 0 < s j) →
      c < 2 ^ ℓ → Ue δ a M ℓ n μ s z v c ≤ Ue δ a M' ℓ n μ s z v c
  | 0, ℓ, μ, s, z, v, c, _, _ => by rw [Ue_nil, Ue_nil]
  | n + 1, ℓ, μ, s, z, v, c, hs, hc => by
    have IH := Ue_mono hδ ha hM hMM n
    have hM' : ∀ ℓ z d, d < 2 ^ ℓ → 0 < M' ℓ z d := fun ℓ z d hd =>
      (hM ℓ z d hd).trans_le (hMM ℓ z d hd)
    have hT : ∀ ℓ' c', ∑ d ∈ Finset.range (2 ^ ℓ'),
        Wesub δ a (μ 0) (s 0) ℓ' z c' (v 0) d * M ℓ' (v 0) d *
          Ue δ a M ℓ' n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d ≤
        ∑ d ∈ Finset.range (2 ^ ℓ'), Wesub δ a (μ 0) (s 0) ℓ' z c' (v 0) d * M' ℓ' (v 0) d *
          Ue δ a M' ℓ' n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d := fun ℓ' c' =>
      Finset.sum_le_sum fun d hd => by
        have hd' := Finset.mem_range.1 hd
        have hW := (Wesub_bounds hδ ha (μ := μ 0) (hs 0) ℓ' z c' (v 0) d).1.le
        have hU := (Ue_bounds hδ ha hM n ℓ' (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d
          (fun j => hs _) hd').1.le
        have hU' := IH ℓ' (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d (fun j => hs _) hd'
        have h1 := hMM ℓ' (v 0) d hd'
        have h2 := (hM' ℓ' (v 0) d hd').le
        calc _ ≤ Wesub δ a (μ 0) (s 0) ℓ' z c' (v 0) d * M' ℓ' (v 0) d *
              Ue δ a M ℓ' n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d := by gcongr
          _ ≤ _ := by gcongr
    induction ℓ generalizing c with
    | zero =>
      rw [Ue_zero_succ, Ue_zero_succ]
      exact min_le_min le_rfl (hT 0 c)
    | succ ℓ ih =>
      have hc2 : c / 2 < 2 ^ ℓ := by rw [pow_succ] at hc; omega
      rw [Ue_succ_succ, Ue_succ_succ]
      exact min_le_min (min_le_min le_rfl (hT _ c)) (ih (c / 2) hc2)

/-! ## Zero error: claim 031's recursion -/

theorem elo_zero (z : ℕ) : elo δ 0 z = mlo δ z := by
  unfold elo; rw [sub_zero]; exact max_eq_right (mlo_nonneg δ z)

theorem eslo_zero_noise : eslo δ 0 = slo δ := by
  funext ℓ z c
  unfold eslo slo ehi
  rw [elo_zero, add_zero]

theorem Ue_zero_noise (hM : ∀ ℓ z d, M ℓ z d = 1) :
    ∀ (n ℓ : ℕ) (μ s : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (c : ℕ),
      Ue δ 0 M ℓ n μ s z v c = Ub δ ℓ n μ s z v c
  | 0, ℓ, μ, s, z, v, c => by rw [Ue_nil, Ub_nil]
  | n + 1, ℓ, μ, s, z, v, c => by
    have hW : ∀ ℓ' c' d, Wesub δ 0 (μ 0) (s 0) ℓ' z c' (v 0) d = Wsub δ (μ 0) (s 0) ℓ' z c' (v 0) d :=
      fun ℓ' c' d => by unfold Wesub Wsub; rw [eslo_zero_noise]
    induction ℓ generalizing c with
    | zero =>
      rw [Ue_zero_succ, Ub_zero_succ]
      simp only [hW, hM, mul_one, Ue_zero_noise hM n]
    | succ ℓ ih =>
      rw [Ue_succ_succ, Ub_succ_succ, ih]
      simp only [hW, hM, mul_one, Ue_zero_noise hM n]

/-! ## Level zero and the all-zero path -/

theorem Bn_succ_le (ℓ : ℕ) {n : ℕ} (μ s : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ) :
    Bn δ a M (ℓ + 1) μ s z₀ v ≤ Bn δ a M ℓ μ s z₀ v := by
  unfold Bn
  refine Finset.sup'_le _ _ fun c hc => (Ue_parent ℓ μ s z₀ v c).trans ?_
  refine Finset.le_sup' (Ue δ a M ℓ n μ s z₀ v) (Finset.mem_range.2 ?_)
  have := Finset.mem_range.1 hc
  rw [pow_succ] at this; omega

theorem Bn_bounds (hδ : 0 < δ) (ha : 0 ≤ a) (hM : ∀ ℓ z d, d < 2 ^ ℓ → 0 < M ℓ z d) (ℓ : ℕ)
    {n : ℕ} {μ s : Fin n → ℝ} (hs : ∀ j, 0 < s j) (z₀ : ℕ) (v : Fin n → ℕ) :
    0 < Bn δ a M ℓ μ s z₀ v ∧ Bn δ a M ℓ μ s z₀ v ≤ 1 :=
  ⟨(Ue_bounds hδ ha hM n ℓ μ s z₀ v 0 hs (pow_pos two_pos ℓ)).1.trans_le
    (Finset.le_sup' (Ue δ a M ℓ n μ s z₀ v) (mem_range_pow ℓ)),
   Finset.sup'_le _ _ fun c hc => (Ue_bounds hδ ha hM n ℓ μ s z₀ v c hs (Finset.mem_range.1 hc)).2⟩

theorem Bn_mono (hδ : 0 < δ) (ha : 0 ≤ a) {M' : ℕ → ℕ → ℕ → ℝ}
    (hM : ∀ ℓ z d, d < 2 ^ ℓ → 0 < M ℓ z d) (hMM : ∀ ℓ z d, d < 2 ^ ℓ → M ℓ z d ≤ M' ℓ z d)
    (ℓ : ℕ) {n : ℕ} {μ s : Fin n → ℝ} (hs : ∀ j, 0 < s j) (z₀ : ℕ) (v : Fin n → ℕ) :
    Bn δ a M ℓ μ s z₀ v ≤ Bn δ a M' ℓ μ s z₀ v :=
  Finset.sup'_le _ _ fun c hc => (Ue_mono hδ ha hM hMM n ℓ μ s z₀ v c hs
    (Finset.mem_range.1 hc)).trans (Finset.le_sup' (Ue δ a M' ℓ n μ s z₀ v) hc)

/-- The product of the expanded-interval maxima. -/
noncomputable def Pe (δ a : ℝ) {n : ℕ} (μ s : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ) : ℝ :=
  ∏ j, let zp := (Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc
    Wm (elo δ a zp) (ehi δ a zp) (elo δ a (v j)) (ehi δ a (v j)) (μ j) (s j)

theorem Wm_ecell (hδ : 0 < δ) (ha : 0 ≤ a) (zp z : ℕ) {μ s : ℝ} (hs : 0 < s) :
    0 < Wm (elo δ a zp) (ehi δ a zp) (elo δ a z) (ehi δ a z) μ s ∧
      Wm (elo δ a zp) (ehi δ a zp) (elo δ a z) (ehi δ a z) μ s ≤ 1 :=
  let h := interval_holds (μ := μ) (elo_nonneg zp) (by linarith [ewidth_pos hδ ha zp])
    (elo_nonneg z) (by linarith [ewidth_pos hδ ha z]) hs
  ⟨h.2.2.1, h.2.2.2⟩

theorem Pe_succ {n : ℕ} (μ s : Fin (n + 1) → ℝ) (z₀ : ℕ) (v : Fin (n + 1) → ℕ) :
    Pe δ a μ s z₀ v = Wm (elo δ a z₀) (ehi δ a z₀) (elo δ a (v 0)) (ehi δ a (v 0)) (μ 0) (s 0) *
      Pe δ a (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) := by
  unfold Pe
  rw [Fin.prod_univ_succ]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have e1 : (Fin.cons z₀ v : Fin (n + 2) → ℕ) j.succ.castSucc = v j.castSucc := by
    rw [← Fin.succ_castSucc, Fin.cons_succ]
  have e2 : (Fin.cons (v 0) (Fin.tail v) : Fin (n + 1) → ℕ) j.castSucc = v j.castSucc := by
    rw [Fin.cons_self_tail]
  simp only [e1, e2]
  rfl

theorem Pe_bounds (hδ : 0 < δ) (ha : 0 ≤ a) {n : ℕ} {μ s : Fin n → ℝ} (hs : ∀ j, 0 < s j)
    (z₀ : ℕ) (v : Fin n → ℕ) : 0 < Pe δ a μ s z₀ v ∧ Pe δ a μ s z₀ v ≤ 1 :=
  ⟨Finset.prod_pos fun j _ => (Wm_ecell hδ ha _ _ (hs j)).1,
   Finset.prod_le_one₀ (fun j _ => (Wm_ecell hδ ha _ _ (hs j)).1.le)
    (fun j _ => (Wm_ecell hδ ha _ _ (hs j)).2)⟩

theorem Ue_level0 (hδ : 0 < δ) (ha : 0 ≤ a) : ∀ (n : ℕ) (μ s : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ),
    (∀ j, 0 < s j) → Ue δ a Msupp 0 n μ s z v 0 = Pe δ a μ s z v
  | 0, μ, s, z, v, _ => by rw [Ue_nil]; simp [Pe]
  | n + 1, μ, s, z, v, hs => by
    rw [Ue_zero_succ, pow_zero, Finset.sum_range_one,
      Ue_level0 hδ ha n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) (fun j => hs _), Pe_succ]
    have hW : Wesub δ a (μ 0) (s 0) 0 z 0 (v 0) 0 =
        Wm (elo δ a z) (ehi δ a z) (elo δ a (v 0)) (ehi δ a (v 0)) (μ 0) (s 0) := by
      unfold Wesub; rw [eslo_zero, eslo_zero, zero_add, eslo_one, eslo_one]
    rw [hW, show Msupp 0 (v 0) 0 = 1 from rfl, mul_one, min_eq_right]
    calc _ ≤ 1 * Pe δ a (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) :=
          mul_le_mul_of_nonneg_right (Wm_ecell hδ ha _ _ (hs 0)).2
            (Pe_bounds hδ ha (fun j => hs _) _ _).1.le
      _ ≤ 1 := by rw [one_mul]; exact (Pe_bounds hδ ha (fun j => hs _) _ _).2

theorem Bn_level0 (hδ : 0 < δ) (ha : 0 ≤ a) {n : ℕ} {μ s : Fin n → ℝ} (hs : ∀ j, 0 < s j)
    (z₀ : ℕ) (v : Fin n → ℕ) : Bn δ a Msupp 0 μ s z₀ v = Pe δ a μ s z₀ v := by
  unfold Bn
  rw [← Ue_level0 hδ ha n μ s z₀ v hs]
  refine le_antisymm (Finset.sup'_le _ _ fun c hc => ?_) (Finset.le_sup' _ (mem_range_pow 0))
  rw [pow_zero, Finset.mem_range, Nat.lt_one_iff] at hc
  rw [hc]

theorem elo_zero_label (ha : 0 ≤ a) (hδ : 0 < δ) : elo δ a 0 = 0 := by
  unfold elo; rw [mlo_zero hδ]; exact max_eq_left (by linarith)

/-- The all-zero path from a zero quote, from the first subcell of `I_0^a`. -/
theorem Ue_allzero (hδ : 0 < δ) (ha : 0 ≤ a) (hM : ∀ ℓ z d, d < 2 ^ ℓ → 0 < M ℓ z d) {m : ℝ}
    (hm : ∀ ℓ, M ℓ 0 0 = m) (hm1 : m ≤ 1) : ∀ (n ℓ : ℕ) (μ s : Fin n → ℝ), (∀ j, 0 < s j) →
      m ^ n ≤ Ue δ a M ℓ n μ s 0 (fun _ => 0) 0 ∧ Ue δ a M 0 n μ s 0 (fun _ => 0) 0 = m ^ n
  | 0, ℓ, μ, s, _ => by rw [Ue_nil, Ue_nil, pow_zero]; exact ⟨le_rfl, rfl⟩
  | n + 1, ℓ, μ, s, hs => by
    have hm0 : 0 < m := hm 0 ▸ hM 0 0 0 (pow_pos two_pos 0)
    have IH := Ue_allzero hδ ha hM hm hm1 n
    have hW : ∀ ℓ', Wesub δ a (μ 0) (s 0) ℓ' 0 0 0 0 = 1 := fun ℓ' => by
      unfold Wesub; rw [eslo_zero, elo_zero_label ha hδ, Wm_c0_a0]
    have hpow : m ^ (n + 1) ≤ 1 := pow_le_one₀ hm0.le hm1
    have hT : ∀ ℓ', m ^ (n + 1) ≤ ∑ d ∈ Finset.range (2 ^ ℓ'),
        Wesub δ a (μ 0) (s 0) ℓ' 0 0 0 d * M ℓ' 0 d *
          Ue δ a M ℓ' n (Fin.tail μ) (Fin.tail s) 0 (fun _ => 0) d := fun ℓ' => by
      have h0 : m ^ (n + 1) ≤ Wesub δ a (μ 0) (s 0) ℓ' 0 0 0 0 * M ℓ' 0 0 *
          Ue δ a M ℓ' n (Fin.tail μ) (Fin.tail s) 0 (fun _ => 0) 0 := by
        rw [hW, one_mul, hm, pow_succ, mul_comm]
        exact mul_le_mul_of_nonneg_left (IH ℓ' _ _ (fun j => hs _)).1 hm0.le
      refine h0.trans (Finset.single_le_sum (f := fun d => Wesub δ a (μ 0) (s 0) ℓ' 0 0 0 d *
        M ℓ' 0 d * Ue δ a M ℓ' n (Fin.tail μ) (Fin.tail s) 0 (fun _ => 0) d)
        (fun d hd => ?_) (mem_range_pow ℓ'))
      exact mul_nonneg (mul_nonneg (Wesub_bounds hδ ha (hs 0) _ _ _ _ _).1.le
        (hM _ _ _ (Finset.mem_range.1 hd)).le)
        (Ue_bounds hδ ha hM n ℓ' _ _ _ _ d (fun j => hs _) (Finset.mem_range.1 hd)).1.le
    have h0eq : Ue δ a M 0 (n + 1) μ s 0 (fun _ => 0) 0 = m ^ (n + 1) := by
      rw [Ue_zero_succ, pow_zero, Finset.sum_range_one, hW, one_mul, hm,
        show (Fin.tail fun _ => 0 : Fin n → ℕ) = fun _ => 0 from rfl,
        (IH 0 (Fin.tail μ) (Fin.tail s) (fun j => hs _)).2]
      show min 1 (m * m ^ n) = _
      rw [← pow_succ', min_eq_right hpow]
    refine ⟨?_, h0eq⟩
    induction ℓ with
    | zero => rw [h0eq]
    | succ ℓ ih =>
      rw [Ue_succ_succ, Nat.zero_div]
      exact le_min (le_min hpow (hT _)) ih

theorem Bn_allzero (hδ : 0 < δ) (ha : 0 ≤ a) (hM : ∀ ℓ z d, d < 2 ^ ℓ → 0 < M ℓ z d) {m : ℝ}
    (hm : ∀ ℓ, M ℓ 0 0 = m) (hm1 : m ≤ 1) (ℓ : ℕ) {n : ℕ} {μ s : Fin n → ℝ}
    (hs : ∀ j, 0 < s j) : Bn δ a M ℓ μ s 0 (fun _ => 0) = m ^ n := by
  refine le_antisymm ?_ ((Ue_allzero hδ ha hM hm hm1 n ℓ μ s hs).1.trans
    (Finset.le_sup' (Ue δ a M ℓ n μ s 0 (fun _ => 0)) (mem_range_pow ℓ)))
  have h0 : Bn δ a M 0 μ s 0 (fun _ => 0) = m ^ n := by
    unfold Bn
    refine le_antisymm (Finset.sup'_le _ _ fun c hc => ?_) ?_
    · rw [pow_zero, Finset.mem_range, Nat.lt_one_iff] at hc
      rw [hc, (Ue_allzero hδ ha hM hm hm1 n 0 μ s hs).2]
    · rw [← (Ue_allzero hδ ha hM hm hm1 n 0 μ s hs).2]
      exact Finset.le_sup' _ (mem_range_pow 0)
  induction ℓ with
  | zero => exact h0.le
  | succ ℓ ih => exact (Bn_succ_le ℓ μ s 0 _).trans ih

end Novel.D18BoundedNoise
