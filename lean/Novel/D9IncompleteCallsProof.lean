import Standalone.D9IncompleteCalls
import Novel.OuterSetLevProof
import Novel.D9HoldingPeriodProof

/-!
# Claim 021 (D9): proof

Proves `Standalone.D9IncompleteCalls.statement` (`statement_holds`).

**Finite inequalities.**
* `feas_comb`: the constraints (2) are linear, so convex combinations of feasible vectors are
  feasible; the slopes are linear in `c`.
* `bcall_compact`: the feasible set, restricted to the coordinates `0..r` (`emb`), is closed and
  lies in a box, so it is compact. Its image `B_call` is a compact convex subset of `ℝ`, hence empty or
  `Icc (sInf) (sSup)` (Mathlib's `eq_Icc_of_connected_compact`).
* `closed_form`: with exact calls, `m` enters only through `s₁ = (c₁ − m)/K₁`.
* OTM: replacing `m` by `1` keeps every constraint when `K₁ ≥ 1`.
* The joint set uses claim 018's elimination (`Novel.OuterSetLev.proof`).

**Terminal laws.**
* `icall_sub`: the call function `K ↦ E(x − K)⁺` has pointwise secant slopes in `[−1, 0]` that
  increase, and these integrate.
* `no_flat_law`: the flat-call gap. A nonnegative payoff difference with zero integral vanishes
  almost everywhere.
* `lift`: the mixture (4) with the law of `max(x, K₁)`.
* `icall_convex`: mixtures of two laws.
* The fixture law is `¾δ₀ + ¼δ₂`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace Novel.D9IncompleteCalls

open Standalone.D9IncompleteCalls
open Standalone.OuterSetLev (Blev lo up lower)

/-! ## Finite inequalities -/

section Finite

variable {K lo hi : ℕ → ℝ} {r : ℕ}

theorem K1_pos (hS : Strikes K r) : 0 < K 1 := by
  have := hS.2.2 0 (by have := hS.1; omega); rw [hS.2.1] at this; exact this

theorem slope_one (hS : Strikes K r) (c : ℕ → ℝ) : cslope K c 1 = (c 1 - c 0) / K 1 := by
  simp [cslope, hS.2.1]

theorem slope_congr {c c' : ℕ → ℝ} {i : ℕ} (h1 : c i = c' i) (h2 : c (i - 1) = c' (i - 1)) :
    cslope K c i = cslope K c' i := by simp only [cslope, h1, h2]

theorem comb_ge {a x y t : ℝ} (hx : a ≤ x) (hy : a ≤ y) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    a ≤ (1 - t) * x + t * y := by nlinarith

theorem comb_le {a x y t : ℝ} (hx : x ≤ a) (hy : y ≤ a) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (1 - t) * x + t * y ≤ a := by nlinarith

theorem slope_comb (c₁ c₂ : ℕ → ℝ) (t : ℝ) (i : ℕ) :
    cslope K (fun j => (1 - t) * c₁ j + t * c₂ j) i = (1 - t) * cslope K c₁ i + t * cslope K c₂ i := by
  unfold cslope; ring

theorem feas_comb {c₁ c₂ : ℕ → ℝ} (h1 : Feas K lo hi r c₁) (h2 : Feas K lo hi r c₂) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Feas K lo hi r (fun j => (1 - t) * c₁ j + t * c₂ j) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h1
  obtain ⟨b0, b1, b2, b3, b4⟩ := h2
  refine ⟨comb_ge a0 b0 ht0 ht1, comb_le a1 b1 ht0 ht1, fun i hi1 hi2 => ?_, fun i hi1 hi2 => ?_,
    fun i hi1 hi2 => ?_⟩
  · obtain ⟨x1, x2, x3⟩ := a2 i hi1 hi2
    obtain ⟨y1, y2, y3⟩ := b2 i hi1 hi2
    exact ⟨comb_ge x1 y1 ht0 ht1, comb_le x2 y2 ht0 ht1, comb_ge x3 y3 ht0 ht1⟩
  · rw [slope_comb]
    obtain ⟨x1, x2⟩ := a3 i hi1 hi2
    obtain ⟨y1, y2⟩ := b3 i hi1 hi2
    exact ⟨comb_ge x1 y1 ht0 ht1, comb_le x2 y2 ht0 ht1⟩
  · rw [slope_comb, slope_comb]
    have := a4 i hi1 hi2
    have := b4 i hi1 hi2
    nlinarith

theorem bcall_convex : Convex ℝ (Bcall K lo hi r) := by
  rintro _ ⟨c₁, h1, rfl⟩ _ ⟨c₂, h2, rfl⟩ a b ha hb hab
  refine ⟨_, feas_comb h1 h2 hb (by linarith), ?_⟩
  simp only [smul_eq_mul]
  have : a = 1 - b := by linarith
  subst this; ring

theorem bcall_sub : Bcall K lo hi r ⊆ Icc 0 1 := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨by linarith [hc.2.1], by linarith [hc.1]⟩

/-- The coordinates `0..r` of a vector. -/
noncomputable def emb (r : ℕ) (v : Fin (r + 1) → ℝ) : ℕ → ℝ :=
  fun i => if h : i < r + 1 then v ⟨i, h⟩ else 0

theorem emb_of (c : ℕ → ℝ) {i : ℕ} (hi : i ≤ r) : emb r (fun j => c j) i = c i := by
  simp [emb, Nat.lt_succ_of_le hi]

theorem feas_congr {c c' : ℕ → ℝ} (h : ∀ i ≤ r, c i = c' i) :
    Feas K lo hi r c → Feas K lo hi r c' := by
  rintro ⟨a0, a1, a2, a3, a4⟩
  have h0 := h 0 (Nat.zero_le _)
  refine ⟨h0 ▸ a0, h0 ▸ a1, fun i hi1 hi2 => ?_, fun i hi1 hi2 => ?_, fun i hi1 hi2 => ?_⟩
  · rw [← h i hi2]; exact a2 i hi1 hi2
  · rw [← slope_congr (h i hi2) (h (i - 1) (by omega))]; exact a3 i hi1 hi2
  · rw [← slope_congr (h i hi2.le) (h (i - 1) (by omega)),
      ← slope_congr (h (i + 1) hi2) (h (i + 1 - 1) (by omega))]
    exact a4 i hi1 hi2

theorem continuous_emb (i : ℕ) : Continuous fun v : Fin (r + 1) → ℝ => emb r v i := by
  unfold emb; split_ifs; exacts [continuous_apply _, continuous_const]

theorem isClosed_imp {X : Type*} [TopologicalSpace X] {p : Prop} {s : Set X} (hs : IsClosed s) :
    IsClosed {x | p → x ∈ s} := by
  by_cases hp : p <;> simp [hp, hs]

theorem bcall_compact : IsCompact (Bcall K lo hi r) := by
  set S : Set (Fin (r + 1) → ℝ) := {v | Feas K lo hi r (emb r v)}
  have himg : Bcall K lo hi r = (fun v => 1 - v 0) '' S := by
    ext δ
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun j => c j, feas_congr (fun i hi => (emb_of c hi).symm) hc, ?_⟩
      simp
    · rintro ⟨v, hv, rfl⟩
      exact ⟨emb r v, hv, by simp [emb]⟩
  have hcs : ∀ i, Continuous fun v : Fin (r + 1) → ℝ => cslope K (emb r v) i := fun i =>
    ((continuous_emb i).sub (continuous_emb (i - 1))).div_const _
  have hclosed : IsClosed S := by
    have : S = {v | 0 ≤ emb r v 0} ∩ {v | emb r v 0 ≤ 1} ∩
        (⋂ i, {v | 1 ≤ i → i ≤ r → v ∈ {v | lo i ≤ emb r v i} ∩ {v | emb r v i ≤ hi i} ∩
          {v | 0 ≤ emb r v i}}) ∩
        (⋂ i, {v | 1 ≤ i → i ≤ r → v ∈ {v | -1 ≤ cslope K (emb r v) i} ∩
          {v | cslope K (emb r v) i ≤ 0}}) ∩
        (⋂ i, {v | 1 ≤ i → i < r → v ∈ {v | cslope K (emb r v) i ≤ cslope K (emb r v) (i + 1)}}) := by
      ext v; simp [S, Feas, and_assoc]
    rw [this]
    refine (((isClosed_le continuous_const (continuous_emb 0)).inter
      (isClosed_le (continuous_emb 0) continuous_const)).inter (isClosed_iInter fun i => ?_)).inter
      (isClosed_iInter fun i => ?_) |>.inter (isClosed_iInter fun i => ?_)
    · exact isClosed_imp (isClosed_imp (((isClosed_le continuous_const (continuous_emb i)).inter
        (isClosed_le (continuous_emb i) continuous_const)).inter
        (isClosed_le continuous_const (continuous_emb i))))
    · exact isClosed_imp (isClosed_imp ((isClosed_le continuous_const (hcs i)).inter
        (isClosed_le (hcs i) continuous_const)))
    · exact isClosed_imp (isClosed_imp (isClosed_le (hcs i) (hcs (i + 1))))
  have hbox : S ⊆ Set.pi univ fun j : Fin (r + 1) =>
      Icc (if (j : ℕ) = 0 then 0 else lo j) (if (j : ℕ) = 0 then 1 else hi j) := by
    intro v hv j _
    obtain ⟨a0, a1, a2, -, -⟩ := hv
    have hj : emb r v j = v j := by simp [emb, j.2]
    by_cases h0 : (j : ℕ) = 0
    · have : j = 0 := Fin.ext h0
      subst this
      simp only [Fin.val_zero, ite_true]
      exact ⟨by simpa [emb] using a0, by simpa [emb] using a1⟩
    · simp only [h0, ite_false]
      obtain ⟨x1, x2, -⟩ := a2 j (Nat.one_le_iff_ne_zero.2 h0) (Nat.lt_succ_iff.1 j.2)
      rw [hj] at x1 x2
      exact ⟨x1, x2⟩
  have hS : IsCompact S :=
    (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hclosed hbox
  rw [himg]
  exact hS.image (continuous_const.sub (continuous_apply 0))

theorem bcall_shape : Bcall K lo hi r = ∅ ∨ ∃ a b, a ≤ b ∧ Bcall K lo hi r = Icc a b := by
  rcases (Bcall K lo hi r).eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · refine Or.inr ⟨_, _, ?_, eq_Icc_of_connected_compact ⟨h, bcall_convex.isPreconnected⟩
      bcall_compact⟩
    obtain ⟨x, hx⟩ := h
    exact (csInf_le bcall_compact.bddBelow hx).trans (le_csSup bcall_compact.bddAbove hx)

/-- Exact calls: `δ ∈ B_call` iff the `m`-free checks hold and `m = 1 − δ` meets the `s₁`
constraints. -/
theorem mem_exact (hS : Strikes K r) {c : ℕ → ℝ} {δ : ℝ} :
    δ ∈ Bcall K c c r ↔ Checks K c r ∧ 0 ≤ 1 - δ ∧ 1 - δ ≤ 1 ∧
      -1 ≤ (c 1 - (1 - δ)) / K 1 ∧ (c 1 - (1 - δ)) / K 1 ≤ 0 ∧
      (2 ≤ r → (c 1 - (1 - δ)) / K 1 ≤ cslope K c 2) := by
  have hr := hS.1
  constructor
  · rintro ⟨c', ⟨a0, a1, a2, a3, a4⟩, rfl⟩
    have hagree : ∀ i, 1 ≤ i → i ≤ r → c' i = c i := fun i h1 h2 =>
      le_antisymm (a2 i h1 h2).2.1 (a2 i h1 h2).1
    have hsl : ∀ i, 2 ≤ i → i ≤ r → cslope K c' i = cslope K c i := fun i h1 h2 =>
      slope_congr (hagree i (by omega) h2) (hagree (i - 1) (by omega) (by omega))
    have hs1 : cslope K c' 1 = (c 1 - c' 0) / K 1 := by rw [slope_one hS, hagree 1 le_rfl hr]
    simp only [sub_sub_cancel]
    refine ⟨⟨fun i h1 h2 => hagree i h1 h2 ▸ (a2 i h1 h2).2.2, fun i h1 h2 => ?_,
      fun i h1 h2 => ?_⟩, a0, a1, hs1 ▸ (a3 1 le_rfl hr).1, hs1 ▸ (a3 1 le_rfl hr).2,
      fun h2 => ?_⟩
    · rw [← hsl i h1 h2]; exact a3 i (by omega) h2
    · rw [← hsl i h1 h2.le, ← hsl (i + 1) (by omega) h2]; exact a4 i (by omega) h2
    · rw [← hs1, ← hsl 2 le_rfl h2]; exact a4 1 le_rfl (by omega)
  · rintro ⟨⟨hc0, hc1, hc2⟩, m0, m1, s1lo, s1hi, s12⟩
    set c' : ℕ → ℝ := fun i => if i = 0 then 1 - δ else c i
    have hagree : ∀ i, 1 ≤ i → c' i = c i := fun i h => by simp [c', show i ≠ 0 by omega]
    have hsl : ∀ i, 2 ≤ i → cslope K c' i = cslope K c i := fun i h =>
      slope_congr (hagree i (by omega)) (hagree (i - 1) (by omega))
    have hs1 : cslope K c' 1 = (c 1 - (1 - δ)) / K 1 := by
      rw [slope_one hS, hagree 1 le_rfl]; simp [c']
    refine ⟨c', ⟨by simpa [c'] using m0, by simpa [c'] using m1, fun i h1 h2 => ?_,
      fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩, by simp [c']⟩
    · rw [hagree i h1]; exact ⟨le_rfl, le_rfl, hc0 i h1 h2⟩
    · rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | hi
      · rw [hs1]; exact ⟨s1lo, s1hi⟩
      · rw [hsl i hi]; exact hc1 i hi h2
    · rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | hi
      · rw [hs1, hsl 2 le_rfl]; exact s12 (by omega)
      · rw [hsl i hi, hsl (i + 1) (by omega)]; exact hc2 i hi h2

open Classical in
theorem closed_form (hS : Strikes K r) (c : ℕ → ℝ) (hr : 2 ≤ r) :
    Bcall K c c r = if Checks K c r then
      Icc (1 - min 1 (c 1 + K 1)) (1 - max 0 (c 1 - K 1 * cslope K c 2)) else ∅ := by
  have hK := K1_pos hS
  ext δ
  rw [mem_exact hS]
  split_ifs with hch
  · simp only [hch, true_and, mem_Icc]
    have hs2 := (hch.2.1 2 le_rfl hr).2
    rw [le_div_iff₀ hK, div_le_iff₀ hK, div_le_iff₀ hK]
    constructor
    · rintro ⟨m0, m1, a, -, b⟩
      have b := b hr
      refine ⟨?_, ?_⟩
      · have : 1 - δ ≤ min 1 (c 1 + K 1) := le_min m1 (by linarith)
        linarith
      · have : max 0 (c 1 - K 1 * cslope K c 2) ≤ 1 - δ := max_le m0 (by nlinarith)
        linarith
    · rintro ⟨h1, h2⟩
      have e1 := (min_le_left 1 (c 1 + K 1))
      have e2 := (min_le_right 1 (c 1 + K 1))
      have e3 := (le_max_left 0 (c 1 - K 1 * cslope K c 2))
      have e4 := (le_max_right 0 (c 1 - K 1 * cslope K c 2))
      refine ⟨by linarith, by linarith, by linarith, ?_, fun _ => by linarith⟩
      have : K 1 * cslope K c 2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK.le hs2
      nlinarith
  · simp [hch]

open Classical in
theorem closed_form_one (hS : Strikes K 1) (c : ℕ → ℝ) :
    Bcall K c c 1 = if 0 ≤ c 1 then Icc (1 - min 1 (c 1 + K 1)) (1 - max 0 (c 1)) else ∅ := by
  have hK := K1_pos hS
  ext δ
  rw [mem_exact hS]
  have hch : Checks K c 1 ↔ 0 ≤ c 1 := by
    constructor
    · exact fun h => h.1 1 le_rfl le_rfl
    · intro h
      refine ⟨fun i h1 h2 => ?_, fun i h1 h2 => by omega, fun i h1 h2 => by omega⟩
      rw [show i = 1 by omega]; exact h
  split_ifs with h0
  · simp only [hch.2 h0, true_and, mem_Icc, show ¬ (2 ≤ 1) by omega, false_implies, and_true]
    rw [le_div_iff₀ hK, div_le_iff₀ hK]
    constructor
    · rintro ⟨m0, m1, a, b⟩
      have : 1 - δ ≤ min 1 (c 1 + K 1) := le_min m1 (by linarith)
      have : max 0 (c 1) ≤ 1 - δ := max_le m0 (by linarith)
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      have e1 := (min_le_left 1 (c 1 + K 1))
      have e2 := (min_le_right 1 (c 1 + K 1))
      have e3 := (le_max_left 0 (c 1))
      have e4 := (le_max_right 0 (c 1))
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · simp only [mem_empty_iff_false, iff_false, not_and]
    exact fun h => absurd (hch.1 h) h0

/-- OTM: raising `m` to `1` keeps every constraint. -/
theorem otm_bcall (hS : Strikes K r) (hK1 : 1 ≤ K 1) (hne : (Bcall K lo hi r).Nonempty) :
    (0 : ℝ) ∈ Bcall K lo hi r := by
  have hK := K1_pos hS
  obtain ⟨_, ⟨c, ⟨a0, a1, a2, a3, a4⟩, rfl⟩⟩ := hne
  have hr := hS.1
  set c' : ℕ → ℝ := fun i => if i = 0 then 1 else c i
  have hagree : ∀ i, 1 ≤ i → c' i = c i := fun i h => by simp [c', show i ≠ 0 by omega]
  have hsl : ∀ i, 2 ≤ i → cslope K c' i = cslope K c i := fun i h =>
    slope_congr (hagree i (by omega)) (hagree (i - 1) (by omega))
  have hs1 : cslope K c' 1 = (c 1 - 1) / K 1 := by rw [slope_one hS, hagree 1 le_rfl]; simp [c']
  have hs1old : cslope K c 1 = (c 1 - c 0) / K 1 := slope_one hS c
  have hle : cslope K c' 1 ≤ cslope K c 1 := by
    rw [hs1, hs1old]; exact div_le_div_of_nonneg_right (by linarith) hK.le
  have hge : -1 ≤ cslope K c' 1 := by
    rw [hs1, le_div_iff₀ hK]; linarith [(a2 1 le_rfl hr).2.2]
  refine ⟨c', ⟨by simp [c'], by simp [c'], fun i h1 h2 => hagree i h1 ▸ a2 i h1 h2,
    fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩, by simp [c']⟩
  · rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | hi
    · exact ⟨hge, hle.trans (a3 1 le_rfl hr).2⟩
    · rw [hsl i hi]; exact a3 i h1 h2
  · rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | hi
    · rw [hsl 2 le_rfl]; exact hle.trans (a4 1 le_rfl h2)
    · rw [hsl i hi, hsl (i + 1) (by omega)]; exact a4 i h1 h2

theorem feas_mono {lo' hi' : ℕ → ℝ} (hlo : ∀ i, lo' i ≤ lo i) (hhi : ∀ i, hi i ≤ hi' i)
    {c : ℕ → ℝ} (h : Feas K lo hi r c) : Feas K lo' hi' r c := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h
  exact ⟨a0, a1, fun i h1 h2 => ⟨(hlo i).trans (a2 i h1 h2).1, (a2 i h1 h2).2.1.trans (hhi i),
    (a2 i h1 h2).2.2⟩, a3, a4⟩

end Finite

/-! ## Terminal laws -/

section Laws

open scoped ENNReal

variable {K lo hi : ℕ → ℝ} {r : ℕ} {μ : Measure ℝ}

theorem law_nonneg (hμ : Law μ) : ∀ᵐ x ∂μ, 0 ≤ x := by
  have := measure_eq_zero_iff_ae_notMem.1 hμ.2.1
  filter_upwards [this] with x hx
  simpa using hx

theorem call_int (hμ : Law μ) (k : ℝ) : Integrable (fun x => max (x - k) 0) μ := by
  have := hμ.1
  refine Integrable.mono' (hμ.2.2.1.abs.add (integrable_const |k|))
    ((measurable_id.sub_const k).max measurable_const).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  simp only [Pi.add_apply, id]
  exact max_le (by linarith [le_abs_self x, neg_abs_le k]) (by positivity)

theorem callE_zero (hμ : Law μ) : callE μ 0 = ∫ x, x ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [law_nonneg hμ] with x hx
  simp [hx]

theorem mean_nonneg (hμ : Law μ) : 0 ≤ ∫ x, x ∂μ := integral_nonneg_of_ae (law_nonneg hμ)

theorem pw_conv (x a b c : ℝ) (hab : a < b) (hbc : b < c) :
    (max (x - b) 0 - max (x - a) 0) * (c - b) ≤ (max (x - c) 0 - max (x - b) 0) * (b - a) := by
  rcases le_or_gt x a with h1 | h1
  · rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
    simp
  rcases le_or_gt x b with h2 | h2
  · rw [max_eq_right (by linarith : x - b ≤ 0), max_eq_left (by linarith : 0 ≤ x - a),
      max_eq_right (by linarith : x - c ≤ 0)]
    nlinarith
  rcases le_or_gt x c with h3 | h3
  · rw [max_eq_left (by linarith : 0 ≤ x - b), max_eq_left (by linarith : 0 ≤ x - a),
      max_eq_right (by linarith : x - c ≤ 0)]
    nlinarith
  · rw [max_eq_left (by linarith : 0 ≤ x - b), max_eq_left (by linarith : 0 ≤ x - a),
      max_eq_left (by linarith : 0 ≤ x - c)]
    nlinarith

theorem K_lt (hS : Strikes K r) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) : K (i - 1) < K i := by
  have := hS.2.2 (i - 1) (by omega)
  rwa [show i - 1 + 1 = i by omega] at this

theorem K_mono (hS : Strikes K r) : ∀ i j, i ≤ j → j ≤ r → K i ≤ K j := by
  intro i j hij hj
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (by omega) (by omega)).trans (hS.2.2 j (by omega)).le
    · rw [le_antisymm hij h]

/-- (1) ⊆ (2). -/
theorem icall_sub (hS : Strikes K r) : Icall K lo hi r ⊆ Bcall K lo hi r := by
  rintro _ ⟨μ, hμ, hband, rfl⟩
  have := hμ.1
  set c : ℕ → ℝ := fun i => callE μ (K i)
  have hc0 : c 0 = ∫ x, x ∂μ := by simp only [c, hS.2.1, callE_zero hμ]
  have hdiff : ∀ a b, callE μ b - callE μ a = ∫ x, (max (x - b) 0 - max (x - a) 0) ∂μ :=
    fun a b => (integral_sub (call_int hμ b) (call_int hμ a)).symm
  refine ⟨c, ⟨hc0 ▸ mean_nonneg hμ, hc0 ▸ hμ.2.2.2, fun i h1 h2 => ⟨(hband i h1 h2).1,
    (hband i h1 h2).2, integral_nonneg fun _ => le_max_right _ _⟩, fun i h1 h2 => ?_,
    fun i h1 h2 => ?_⟩, by rw [hc0]⟩
  · have hlt := K_lt hS h1 h2
    have hD : 0 < K i - K (i - 1) := sub_pos.2 hlt
    have e := hdiff (K (i - 1)) (K i)
    simp only [cslope, c]
    constructor
    · rw [le_div_iff₀ hD, e]
      have : ∫ x, (-(K i - K (i - 1))) ∂μ ≤ ∫ x, (max (x - K i) 0 - max (x - K (i - 1)) 0) ∂μ :=
        integral_mono (integrable_const _) ((call_int hμ _).sub (call_int hμ _)) fun x => by
          simp only
          rcases le_total (x - K i) 0 with h | h <;> rcases le_total (x - K (i - 1)) 0 with h' | h'
          all_goals first
            | (rw [max_eq_right h, max_eq_right h']; linarith)
            | (rw [max_eq_right h, max_eq_left h']; linarith)
            | (rw [max_eq_left h, max_eq_right h']; linarith)
            | (rw [max_eq_left h, max_eq_left h']; linarith)
      simpa using this
    · rw [div_le_iff₀ hD, e, zero_mul]
      exact integral_nonpos fun x => by
        have : max (x - K i) 0 ≤ max (x - K (i - 1)) 0 := max_le_max (by linarith) le_rfl
        show max (x - K i) 0 - max (x - K (i - 1)) 0 ≤ 0
        linarith
  · have hab := K_lt hS h1 h2.le
    have hbc := K_lt hS (show 1 ≤ i + 1 by omega) h2
    rw [show i + 1 - 1 = i by omega] at hbc
    simp only [cslope, c, show i + 1 - 1 = i by omega]
    rw [div_le_div_iff₀ (sub_pos.2 hab) (sub_pos.2 hbc), hdiff, hdiff,
      ← integral_mul_const, ← integral_mul_const]
    exact integral_mono (((call_int hμ _).sub (call_int hμ _)).mul_const _)
      (((call_int hμ _).sub (call_int hμ _)).mul_const _)
      fun x => pw_conv x _ _ _ hab hbc

/-- The flat-call gap. -/
theorem no_flat_law : ¬ ∃ μ, Law μ ∧ callE μ (11 / 10) = 1 / 10 ∧ callE μ (7 / 5) = 1 / 10 := by
  rintro ⟨μ, hμ, h1, h2⟩
  have := hμ.1
  set g : ℝ → ℝ := fun x => max (x - 11 / 10) 0 - max (x - 7 / 5) 0
  have hg0 : 0 ≤ g := fun x => by
    simp only [g, Pi.zero_apply]
    have : max (x - 7 / 5) 0 ≤ max (x - 11 / 10) 0 := max_le_max (by linarith) le_rfl
    linarith
  have hgi : Integrable g μ := (call_int hμ _).sub (call_int hμ _)
  have hint : ∫ x, g x ∂μ = 0 := by
    simp only [g]; rw [integral_sub (call_int hμ _) (call_int hμ _)]
    simp only [callE] at h1 h2; rw [h1, h2]; ring
  have hae := (integral_eq_zero_iff_of_nonneg hg0 hgi).1 hint
  have hzero : ∀ᵐ x ∂μ, max (x - 7 / 5) 0 = 0 := by
    filter_upwards [hae] with x hx
    simp only [g, Pi.zero_apply] at hx
    by_contra hne
    have hx2 : 7 / 5 < x := by
      by_contra h; exact hne (max_eq_right (by linarith))
    rw [max_eq_left (by linarith), max_eq_left (by linarith)] at hx
    linarith
  have : callE μ (7 / 5) = 0 := by
    unfold callE; rw [integral_congr_ae hzero]; simp
  rw [this] at h2; norm_num at h2

/-- Integrals over a two-component mixture. -/
theorem integral_mix {ν₁ ν₂ : Measure ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {f : ℝ → ℝ}
    (h1 : Integrable f ν₁) (h2 : Integrable f ν₂) :
    ∫ x, f x ∂(ENNReal.ofReal a • ν₁ + ENNReal.ofReal b • ν₂) =
      a * ∫ x, f x ∂ν₁ + b * ∫ x, f x ∂ν₂ := by
  rw [integral_add_measure (h1.smul_measure ENNReal.ofReal_ne_top)
    (h2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, smul_eq_mul, smul_eq_mul]

theorem integral_mix_id {ν₁ ν₂ : Measure ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : Integrable id ν₁) (h2 : Integrable id ν₂) :
    ∫ x, x ∂(ENNReal.ofReal a • ν₁ + ENNReal.ofReal b • ν₂) =
      a * ∫ x, x ∂ν₁ + b * ∫ x, x ∂ν₂ :=
  integral_mix (f := id) ha hb h1 h2

theorem mix_law {ν₁ ν₂ : Measure ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (h0₁ : ν₁ (Iio 0) = 0)
    (h0₂ : ν₂ (Iio 0) = 0) (hi₁ : Integrable id ν₁) (hi₂ : Integrable id ν₂)
    (hm : a * ∫ x, x ∂ν₁ + b * ∫ x, x ∂ν₂ ≤ 1) :
    Law (ENNReal.ofReal a • ν₁ + ENNReal.ofReal b • ν₂) := by
  refine ⟨⟨?_⟩, ?_, (hi₁.smul_measure ENNReal.ofReal_ne_top).add_measure
    (hi₂.smul_measure ENNReal.ofReal_ne_top), ?_⟩
  · simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
  · simp [h0₁, h0₂]
  · rw [integral_mix_id ha hb hi₁ hi₂]; exact hm

/-- `I_call` is convex: mixtures of laws. -/
theorem icall_convex : Convex ℝ (Icall K lo hi r) := by
  rintro _ ⟨μ₁, h1, b1, rfl⟩ _ ⟨μ₂, h2, b2, rfl⟩ a b ha hb hab
  have := h1.1; have := h2.1
  refine ⟨ENNReal.ofReal a • μ₁ + ENNReal.ofReal b • μ₂, mix_law ha hb hab h1.2.1 h2.2.1 h1.2.2.1
    h2.2.2.1 ?_, fun i hi1 hi2 => ?_, ?_⟩
  · have := h1.2.2.2; have := h2.2.2.2; nlinarith
  · unfold callE
    rw [integral_mix ha hb (call_int h1 _) (call_int h2 _)]
    have hb1 := b1 i hi1 hi2; have hb2 := b2 i hi1 hi2
    simp only [callE] at hb1 hb2
    have : a = 1 - b := by linarith
    subst this
    exact ⟨comb_ge hb1.1 hb2.1 hb (by linarith), comb_le hb1.2 hb2.2 hb (by linarith)⟩
  · rw [integral_mix_id ha hb h1.2.2.1 h2.2.2.1, smul_eq_mul, smul_eq_mul]
    have : a = 1 - b := by linarith
    subst this; ring

/-- The lift (4): OTM calls cannot exclude zero in `I_call`. -/
theorem otm_icall (hS : Strikes K r) (hK1 : 1 ≤ K 1) (hne : (Icall K lo hi r).Nonempty) :
    (0 : ℝ) ∈ Icall K lo hi r := by
  obtain ⟨_, ⟨μ, hμ, hband, rfl⟩⟩ := hne
  have := hμ.1
  set m := ∫ x, x ∂μ
  rcases hμ.2.2.2.lt_or_eq with hm1 | hm1
  swap
  · exact ⟨μ, hμ, hband, by rw [hm1]; ring⟩
  set k := K 1
  set c1 := callE μ k
  have hc1 : 0 ≤ c1 := integral_nonneg fun _ => le_max_right _ _
  set A := k + c1
  have hA : 1 ≤ A := by linarith
  set θ := (1 - m) / (A - m)
  have hAm : 0 < A - m := by linarith
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hAm.le
  have hθ1 : θ ≤ 1 := (div_le_one hAm).2 (by linarith)
  have hmax : Measurable fun x : ℝ => max x k := measurable_id.max measurable_const
  set ν := μ.map fun x => max x k
  have hν : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hmax.aemeasurable).2 inferInstance
  have hmapI : ∀ f : ℝ → ℝ, Continuous f → Integrable (fun x => f (max x k)) μ →
      Integrable f ν ∧ ∫ x, f x ∂ν = ∫ x, f (max x k) ∂μ := fun f hf hi =>
    ⟨(integrable_map_measure hf.aestronglyMeasurable hmax.aemeasurable).2 hi,
      integral_map hmax.aemeasurable hf.aestronglyMeasurable⟩
  have hk0 : 0 < k := K1_pos hS
  have hmaxI : Integrable (fun x => max x k) μ := by
    have : (fun x => max x k) = fun x => k + max (x - k) 0 := by
      funext x; rcases le_total x k with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]; ring
      · rw [max_eq_left h, max_eq_left (by linarith)]; ring
    rw [this]; exact (integrable_const k).add (call_int hμ k)
  obtain ⟨hνid, hνmean⟩ := hmapI id continuous_id hmaxI
  have hν0 : ν (Iio 0) = 0 := by
    rw [Measure.map_apply hmax measurableSet_Iio]
    have : (fun x => max x k) ⁻¹' Iio 0 = ∅ := by
      ext x; simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
      exact hk0.le.trans (le_max_right _ _)
    rw [this, measure_empty]
  have hmeanν : ∫ x, x ∂ν = A := by
    rw [show (∫ x, x ∂ν) = ∫ x, id x ∂ν from rfl, hνmean]
    have : (fun x => id (max x k)) = fun x => k + max (x - k) 0 := by
      funext x; simp only [id]; rcases le_total x k with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]; ring
      · rw [max_eq_left h, max_eq_left (by linarith)]; ring
    rw [this, integral_add (integrable_const k) (call_int hμ k), integral_const]
    simp [A, c1, callE]
  have hcallν : ∀ i, 1 ≤ i → i ≤ r → callE ν (K i) = callE μ (K i) := fun i h1 h2 => by
    have hKi : k ≤ K i := K_mono hS 1 i h1 h2
    have hcont : Continuous fun x : ℝ => max (x - K i) 0 :=
      (continuous_id.sub continuous_const).max continuous_const
    have hpt : (fun x => max (max x k - K i) 0) = fun x => max (x - K i) 0 := by
      funext x; rcases le_total x k with h | h
      · rw [max_eq_right h, max_eq_right (by linarith), max_eq_right (by linarith)]
      · rw [max_eq_left h]
    unfold callE
    rw [(hmapI _ hcont (hpt ▸ call_int hμ (K i))).2, hpt]
  have hlaw := mix_law (sub_nonneg.2 hθ1) hθ0 (by ring) hμ.2.1 hν0 hμ.2.2.1 hνid (by
    rw [hmeanν]; simp only [θ]; field_simp; nlinarith)
  refine ⟨_, hlaw, fun i h1 h2 => ?_, ?_⟩
  · have hνi : Integrable (fun x => max (x - K i) 0) ν := by
      have hKi : k ≤ K i := K_mono hS 1 i h1 h2
      have hpt : (fun x => max (max x k - K i) 0) = fun x => max (x - K i) 0 := by
        funext x; rcases le_total x k with h | h
        · rw [max_eq_right h, max_eq_right (by linarith), max_eq_right (by linarith)]
        · rw [max_eq_left h]
      exact (hmapI _ ((continuous_id.sub continuous_const).max continuous_const)
        (hpt ▸ call_int hμ (K i))).1
    unfold callE
    rw [integral_mix (sub_nonneg.2 hθ1) hθ0 (call_int hμ _) hνi]
    have := hcallν i h1 h2
    unfold callE at this
    rw [this]
    have hb := hband i h1 h2
    unfold callE at hb
    constructor <;> nlinarith [hb.1, hb.2]
  · rw [integral_mix_id (sub_nonneg.2 hθ1) hθ0 hμ.2.2.1 hνid, hmeanν]
    simp only [θ]; field_simp; ring

end Laws

/-! ## The joint set, the fixture, ticks, widening -/

section Joint

variable {ι : Type} [Fintype ι] [Nonempty ι] {K lo hi : ℕ → ℝ} {r : ℕ} {M A L U : ι → ℝ}

theorem joint (hS : Strikes K r) (hM : ∀ j, 1 < M j) (hA : ∀ j, 0 ≤ A j ∧ A j < 1) :
    ((∃ j, up A U j < Standalone.OuterSetLev.lo L j) → Bjoint K lo hi r M A L U = ∅) ∧
    ((∀ j, Standalone.OuterSetLev.lo L j ≤ up A U j) →
      Bjoint K lo hi r M A L U = Bcall K lo hi r ∩ Icc (lower M L) 1 ∧
      ∀ bm bp, Bcall K lo hi r = Icc bm bp →
        Bjoint K lo hi r M A L U = Icc (max bm (lower M L)) bp) ∧
    (1 ≤ K 1 → (Bjoint K lo hi r M A L U).Nonempty →
      ((0 : ℝ) ∉ Bjoint K lo hi r M A L U ↔ ∃ j, 0 < L j)) := by
  obtain ⟨hE, hF, h0, -, -⟩ := Novel.OuterSetLev.proof ι M A L U hM hA
  refine ⟨fun h => by simp [Bjoint, hE h], fun h => ⟨by rw [Bjoint, (hF h).1], fun bm bp hb => ?_⟩,
    fun hK1 hne => ?_⟩
  · rw [Bjoint, (hF h).1, hb, Icc_inter_Icc]
    by_cases hbb : bm ≤ bp
    · have : bp ≤ 1 := (bcall_sub (hb ▸ (right_mem_Icc.2 hbb) : bp ∈ Bcall K lo hi r)).2
      rw [min_eq_left this]
    · rw [Icc_eq_empty (by intro h'; exact hbb (le_trans (le_max_left _ _) (h'.trans
        (min_le_left _ _)))), Icc_eq_empty (by intro h'; exact hbb ((le_max_left _ _).trans h'))]
  · obtain ⟨x, hxc, hxl⟩ := hne
    have h0c : (0 : ℝ) ∈ Bcall K lo hi r := otm_bcall hS hK1 ⟨x, hxc⟩
    have hfeas : ∀ j, Standalone.OuterSetLev.lo L j ≤ up A U j := by
      by_contra hn
      push Not at hn
      rw [hE hn] at hxl; exact hxl
    constructor
    · intro hn
      have : (0 : ℝ) ∉ Blev M A L U := fun h' => hn ⟨h0c, h'⟩
      rw [h0] at this
      push Not at this
      obtain ⟨j, hj⟩ := this
      refine ⟨j, ?_⟩
      by_contra hL
      push Not at hL
      have hU : 0 ≤ U j := (le_max_left 0 (L j)).trans ((hfeas j).trans (min_le_left _ _))
      exact absurd (hj hL) (not_lt.2 hU)
    · rintro ⟨j, hj⟩ ⟨-, h'⟩
      have := ((h0.1 h') j).1
      linarith

end Joint

theorem strikes_two {a b : ℝ} (ha : 0 < a) (hab : a < b) : Strikes (two a b) 2 := by
  refine ⟨by norm_num, by simp [two], fun i hi => ?_⟩
  interval_cases i <;> simp [two, ha, hab]

theorem fixture :
    Bcall (two (11 / 10) (7 / 5)) (two (9 / 40) (3 / 20)) (two (9 / 40) (3 / 20)) 2 = Icc 0 (1 / 2) ∧
    Icall (two (11 / 10) (7 / 5)) (two (9 / 40) (3 / 20)) (two (9 / 40) (3 / 20)) 2 =
      Icc 0 (1 / 2) ∧
    Bjoint (two (11 / 10) (7 / 5)) (two (9 / 40) (3 / 20)) (two (9 / 40) (3 / 20)) 2
      (fun _ : Unit => 4) (fun _ => 0) (fun _ => 1 / 5) (fun _ => 1 / 5) = Icc (1 / 20) (1 / 2) := by
  classical
  have hS : Strikes (two (11 / 10) (7 / 5)) 2 := strikes_two (by norm_num) (by norm_num)
  have hB : Bcall (two (11 / 10) (7 / 5)) (two (9 / 40) (3 / 20)) (two (9 / 40) (3 / 20)) 2 =
      Icc 0 (1 / 2) := by
    have hch : Checks (two (11 / 10) (7 / 5)) (two (9 / 40) (3 / 20)) 2 := by
      refine ⟨fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun i h1 h2 => by omega⟩
      · interval_cases i <;> norm_num [two]
      · interval_cases i; norm_num [two, cslope]
    rw [closed_form hS _ le_rfl]
    simp only [hch, ite_true]
    norm_num [two, cslope]
  -- The atom law `¾δ₀ + ¼δ₂`.
  set μ0 : Measure ℝ := ENNReal.ofReal (3 / 4) • Measure.dirac 0 + ENNReal.ofReal (1 / 4) •
    Measure.dirac 2
  have hd : ∀ y : ℝ, ∀ f : ℝ → ℝ, Integrable f (Measure.dirac y) := fun y f =>
    integrable_dirac (by simp)
  have hlaw0 : Law μ0 := mix_law (by norm_num) (by norm_num) (by norm_num) (by simp) (by simp)
    (hd 0 id) (hd 2 id) (by simp; norm_num)
  have hint0 : ∀ f : ℝ → ℝ, ∫ x, f x ∂μ0 = 3 / 4 * f 0 + 1 / 4 * f 2 := fun f => by
    rw [integral_mix (by norm_num) (by norm_num) (hd 0 f) (hd 2 f)]; simp
  have h12 : (1 / 2 : ℝ) ∈ Icall (two (11 / 10) (7 / 5)) (two (9 / 40) (3 / 20))
      (two (9 / 40) (3 / 20)) 2 := by
    refine ⟨μ0, hlaw0, fun i h1 h2 => ?_, ?_⟩
    · unfold callE; rw [hint0]
      interval_cases i <;> norm_num [two]
    · rw [hint0]; norm_num
  have h0 : (0 : ℝ) ∈ Icall (two (11 / 10) (7 / 5)) (two (9 / 40) (3 / 20))
      (two (9 / 40) (3 / 20)) 2 := otm_icall hS (by norm_num [two]) ⟨_, h12⟩
  have hI : Icall (two (11 / 10) (7 / 5)) (two (9 / 40) (3 / 20)) (two (9 / 40) (3 / 20)) 2 =
      Icc 0 (1 / 2) := by
    refine Subset.antisymm (hB ▸ icall_sub hS) fun x hx => ?_
    exact (convex_iff_ordConnected.1 icall_convex).out h0 h12 hx
  refine ⟨hB, hI, ?_⟩
  obtain ⟨-, -, -, -, hex⟩ := Novel.OuterSetLev.proof Unit (fun _ => 4) (fun _ => 0)
    (fun _ => 1 / 5) (fun _ => 1 / 5) (fun _ => by norm_num) (fun _ => by norm_num)
  rw [Bjoint, hB, (hex (fun _ => 1 / 5) fun _ => by norm_num).1, Icc_inter_Icc]
  norm_num

theorem ticks (h q : ℝ) (hh : 0 < h) : {c : ℝ | 0 ≤ c ∧ max h c = q} =
    if q = h then Icc 0 h else if h < q then {q} else ∅ := by
  ext c
  split_ifs with h1 h2
  · subst h1
    simp only [mem_ofPred_eq, mem_Icc, max_eq_left_iff]
  · simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨-, hc⟩
      rcases le_total c h with hch | hch
      · rw [max_eq_left hch] at hc; exact absurd hc.symm h1
      · rw [max_eq_right hch] at hc; exact hc
    · rintro rfl; exact ⟨hh.le.trans h2.le, max_eq_right h2.le⟩
  · simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hc0 hc
    have := le_max_left h c
    rw [hc] at this
    rcases this.lt_or_eq with h3 | h3
    · exact h2 h3
    · exact h1 h3.symm

theorem widen {K lo hi lo' hi' : ℕ → ℝ} {r : ℕ} (hlo : ∀ i, lo' i ≤ lo i) (hhi : ∀ i, hi i ≤ hi' i) :
    Bcall K lo hi r ⊆ Bcall K lo' hi' r ∧ Icall K lo hi r ⊆ Icall K lo' hi' r ∧
    ∀ {ι : Type} (M A L U L' U' : ι → ℝ), (∀ j, L' j ≤ L j) → (∀ j, U j ≤ U' j) →
      Bjoint K lo hi r M A L U ⊆ Bjoint K lo' hi' r M A L' U' := by
  have hB : Bcall K lo hi r ⊆ Bcall K lo' hi' r := by
    rintro _ ⟨c, hc, rfl⟩; exact ⟨c, feas_mono hlo hhi hc, rfl⟩
  refine ⟨hB, ?_, fun M A L U L' U' hL hU => ?_⟩
  · rintro _ ⟨μ, hμ, hb, rfl⟩
    exact ⟨μ, hμ, fun i h1 h2 => ⟨(hlo i).trans (hb i h1 h2).1, (hb i h1 h2).2.trans (hhi i)⟩, rfl⟩
  · rintro δ ⟨h1, h0, h1', z, hz⟩
    exact ⟨hB h1, h0, h1', z, fun j => ⟨(hL j).trans (hz j).1, (hz j).2.1.trans (hU j),
      (hz j).2.2⟩⟩

/-! ## Coverage -/

theorem coverage {ι : Type} [Fintype ι] [Nonempty ι] (K : ℕ → ℝ) (r : ℕ) (M A : ι → ℝ)
    {Ωo : Type} [MeasurableSpace Ωo] (P : Measure Ωo) [IsProbabilityMeasure P]
    (lo hi : ℕ → Ωo → ℝ) (L U : ι → Ωo → ℝ) (μ : Measure ℝ) (Cov : Set Ωo) (α : ℝ)
    (hS : Strikes K r) (hM : ∀ j, 1 < M j) (hA : ∀ j, 0 ≤ A j ∧ A j < 1) (hμ : Law μ)
    (hCm : MeasurableSet Cov)
    (hCov : ∀ ω ∈ Cov, (∀ i, 1 ≤ i → i ≤ r → lo i ω ≤ callE μ (K i) ∧ callE μ (K i) ≤ hi i ω) ∧
      1 - ∫ x, x ∂μ ∈ Blev M A (fun j => L j ω) (fun j => U j ω))
    (hP : 1 - α ≤ P.real Cov) :
    1 - α ≤ P.real {ω | 1 - ∫ x, x ∂μ ∈ Bcall K (fun i => lo i ω) (fun i => hi i ω) r} ∧
    1 - α ≤ P.real {ω | 1 - ∫ x, x ∂μ ∈
      Bjoint K (fun i => lo i ω) (fun i => hi i ω) r M A (fun j => L j ω) (fun j => U j ω)} ∧
    (∫ x, x ∂μ = 1 →
      P.real {ω | (Bcall K (fun i => lo i ω) (fun i => hi i ω) r).Nonempty ∧
        (0 : ℝ) ∉ Bcall K (fun i => lo i ω) (fun i => hi i ω) r} ≤ α ∧
      P.real {ω | (Bjoint K (fun i => lo i ω) (fun i => hi i ω) r M A (fun j => L j ω)
          (fun j => U j ω)).Nonempty ∧ (0 : ℝ) ∉ Bjoint K (fun i => lo i ω) (fun i => hi i ω) r
          M A (fun j => L j ω) (fun j => U j ω)} ≤ α) ∧
    (1 ≤ K 1 → ∀ ω, ¬ ((Bcall K (fun i => lo i ω) (fun i => hi i ω) r).Nonempty ∧
      (0 : ℝ) ∉ Bcall K (fun i => lo i ω) (fun i => hi i ω) r)) ∧
    (1 ≤ K 1 → ∀ ω, (Bjoint K (fun i => lo i ω) (fun i => hi i ω) r M A (fun j => L j ω)
      (fun j => U j ω)).Nonempty → (0 : ℝ) ∉ Bjoint K (fun i => lo i ω) (fun i => hi i ω) r
      M A (fun j => L j ω) (fun j => U j ω) → ∃ j, 0 < L j ω) := by
  have hcall : ∀ ω ∈ Cov, 1 - ∫ x, x ∂μ ∈ Bcall K (fun i => lo i ω) (fun i => hi i ω) r :=
    fun ω hω => icall_sub hS ⟨μ, hμ, (hCov ω hω).1, rfl⟩
  have hjoint : ∀ ω ∈ Cov, 1 - ∫ x, x ∂μ ∈
      Bjoint K (fun i => lo i ω) (fun i => hi i ω) r M A (fun j => L j ω) (fun j => U j ω) :=
    fun ω hω => ⟨hcall ω hω, (hCov ω hω).2⟩
  have hcompl : P.real Covᶜ ≤ α := by
    rw [probReal_compl_eq_one_sub hCm]; linarith
  refine ⟨hP.trans (measureReal_mono hcall), hP.trans (measureReal_mono hjoint), fun h1 => ⟨?_, ?_⟩,
    fun hK1 ω ⟨hne, hn⟩ => hn (otm_bcall hS hK1 hne), fun hK1 ω hne hn => ?_⟩
  · refine (measureReal_mono (s₂ := Covᶜ) fun ω hω hc => hω.2 ?_).trans hcompl
    have := hcall ω hc; rwa [h1, sub_self] at this
  · refine (measureReal_mono (s₂ := Covᶜ) fun ω hω hc => hω.2 ?_).trans hcompl
    have := hjoint ω hc; rwa [h1, sub_self] at this
  · exact ((joint hS hM hA).2.2 hK1 hne).1 hn

/-! ## The model application -/

theorem application (h06 : Standalone.D9HoldingPeriod.AX06.{0}) (Ω : Type) (mΩ : MeasurableSpace Ω)
    (Q : Measure Ω) (𝓕 : MeasureTheory.Filtration NNReal mΩ) (X : NNReal → Ω → ℝ) (T : NNReal)
    (hX : Standalone.D9HoldingPeriod.Setting Q 𝓕 X T) :
    Law (Q.map (X T)) ∧ (∀ K, callE (Q.map (X T)) K = ∫ ω, max (X T ω - K) 0 ∂Q) ∧
    1 - ∫ x, x ∂(Q.map (X T)) = Standalone.D9HoldingPeriod.δ Q X T ∧
    ∀ (K lo hi : ℕ → ℝ) (r : ℕ), Strikes K r →
      (∀ i, 1 ≤ i → i ≤ r → lo i ≤ ∫ ω, max (X T ω - K i) 0 ∂Q ∧
        ∫ ω, max (X T ω - K i) 0 ∂Q ≤ hi i) →
      Standalone.D9HoldingPeriod.δ Q X T ∈ Icall K lo hi r ∧
        Standalone.D9HoldingPeriod.δ Q X T ∈ Bcall K lo hi r := by
  have := hX.prob
  have hm : Measurable (X T) := (hX.adapted T).mono (𝓕.le T) le_rfl
  have hint := Novel.D9HoldingPeriod.integrable_X h06 hX (le_refl T)
  have hmapI : ∀ f : ℝ → ℝ, Continuous f →
      ∫ x, f x ∂(Q.map (X T)) = ∫ ω, f (X T ω) ∂Q := fun f hf =>
    integral_map hm.aemeasurable hf.aestronglyMeasurable
  have hlaw : Law (Q.map (X T)) := by
    refine ⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance, ?_,
      (integrable_map_measure continuous_id.aestronglyMeasurable hm.aemeasurable).2 hint, ?_⟩
    · rw [Measure.map_apply hm measurableSet_Iio]
      have : X T ⁻¹' Iio 0 = ∅ := by
        ext ω; simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
        exact hX.nonneg T ω
      rw [this, measure_empty]
    · rw [show (∫ x, x ∂(Q.map (X T))) = ∫ x, id x ∂(Q.map (X T)) from rfl, hmapI id continuous_id]
      exact Novel.D9HoldingPeriod.integral_X_le_one h06 hX
  have hcall : ∀ K, callE (Q.map (X T)) K = ∫ ω, max (X T ω - K) 0 ∂Q := fun K =>
    hmapI _ ((continuous_id.sub continuous_const).max continuous_const)
  have hdelta : 1 - ∫ x, x ∂(Q.map (X T)) = Standalone.D9HoldingPeriod.δ Q X T := by
    rw [show (∫ x, x ∂(Q.map (X T))) = ∫ x, id x ∂(Q.map (X T)) from rfl, hmapI id continuous_id]
    rfl
  refine ⟨hlaw, hcall, hdelta, fun K lo hi r hS hband => ?_⟩
  have hI : Standalone.D9HoldingPeriod.δ Q X T ∈ Icall K lo hi r :=
    ⟨_, hlaw, fun i h1 h2 => by rw [hcall]; exact hband i h1 h2, hdelta.symm⟩
  exact ⟨hI, icall_sub hS hI⟩

/-! ## The statement -/

theorem statement_holds : Standalone.D9IncompleteCalls.statement := by
  refine ⟨fun K lo hi r hS => ⟨icall_sub hS, bcall_sub, bcall_shape⟩,
    fun K c r hS hr => closed_form hS c hr, fun K c hS => closed_form_one hS c, ⟨?_, no_flat_law⟩,
    fun K lo hi r hS hK1 => ⟨otm_bcall hS hK1, otm_icall hS hK1⟩, ?_,
    fun K lo hi r M A L U hS hM hA => joint hS hM hA, fixture, fun h q hh => ticks h q hh,
    fun K lo hi lo' hi' r hlo hhi => widen hlo hhi,
    fun K r M A _ _ P _ lo hi L U μ Cov α hS hM hA hμ hCm hCov hP =>
      coverage K r M A P lo hi L U μ Cov α hS hM hA hμ hCm hCov hP,
    fun h06 Ω mΩ Q 𝓕 X T hX => application h06 Ω mΩ Q 𝓕 X T hX⟩
  · -- The gap: `m = 1/2` is feasible for the flat calls.
    have hS : Strikes (two (11 / 10) (7 / 5)) 2 := strikes_two (by norm_num) (by norm_num)
    rw [mem_exact hS]
    refine ⟨⟨fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun i h1 h2 => by omega⟩, ?_⟩
    · interval_cases i <;> norm_num [two]
    · interval_cases i; norm_num [two, cslope]
    · norm_num [two, cslope]
  · have hS : Strikes (two (1 / 4) 0) 1 := ⟨le_rfl, by simp [two], fun i hi => by
      interval_cases i; norm_num [two]⟩
    rw [closed_form_one hS]
    simp only [show (0 : ℝ) ≤ two (1 / 4) 0 1 by norm_num [two], ite_true]
    norm_num [two]

end Novel.D9IncompleteCalls
