import Standalone.D3PooledTail
import Novel.D3PowerTailProof

/-!
# Claim 015 (D3): proof

Proves `Standalone.D3PooledTail.statement` (`statement_holds`).

**Free scales** (`attain_p`, `attain_panel`). For a prescribed exponent `p` and a positive first
block `b`, claim 013's construction (the completion of a line at `R`) with `κ² = K_p/b` gives a
coefficient of `C_pow(R)` with tail `κ x^p` and `B₁ = b`. Done name by name, with one `p`, this
gives a shared panel. Claim 013's `B2_eq` then fixes every second block at `r^{2−2p} B₁`.

**Rectangles** (`qSet_eq`). Necessity: `B₂/B₁` with `B₁ ∈ [L₁, U₁]` and `B₂ ∈ [L₂, U₂]` lies in
`[L₂/U₁, U₂/L₁]`. Sufficiency: the witness `b₁ = max(L₁, L₂/q)`, with `B₂ = q b₁`. The interval
endpoints of the intersection are `Finset.sup'`/`inf'`. The exponent set is the preimage of
`[ℓ_*, u_*]` under `p ↦ r^{2−2p}`, inverted with `Real.log`. The label set uses claim 013's
`θ = 1_{q<1}`.

**Coverage.** On simultaneous coverage the true common ratio lies in every `[ℓᵢ(ω), uᵢ(ω)]`, so
under a null `u_*(ω) ≥ q ≥ 1` and the rule cannot reject. Bonferroni is Mathlib's finite union
bound. The two-name example is computed on `Fin 3` with masses `α, α, 1 − 2α`.

**Occupation pooling.** Claim 013's `part3` for each name, Mathlib's finite union bound
`measureReal_iUnion_fintype_le`, and `(⋃ Dᵢⁿ) Δ (⋃ Dᵢ) ⊆ ⋃ (Dᵢⁿ Δ Dᵢ)`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D3PooledTail

open Standalone.D8TailCompletions (Admissible θ completion)
open Standalone.D3PowerTail Standalone.D3PooledTail
open Novel.D3PowerTail (B1_eq B2_eq B1_pos K_pos theta_eq rpow_lt_one_iff' part3)

/-! ## Free scales -/

section Scales

variable {R r : ℝ}

/-- One name: any exponent `p` and any positive first block `b`. -/
theorem attain_p (hR : 0 < R) (hr : 1 < r) (p : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ σ, CPow R σ ∧ (∃ κ : ℝ, 0 < κ ∧ ∀ x, R ≤ x → σ x = κ * x ^ p) ∧ B1 R r σ = b := by
  set K := ∫ x in R..R * r, x ^ (1 - 2 * p)
  have hK : 0 < K := K_pos hR hr (1 - 2 * p)
  set κ := Real.sqrt (K / b)
  have hκ : 0 < κ := Real.sqrt_pos.2 (div_pos hK hb)
  have hκ2 : κ ^ 2 = K / b := Real.sq_sqrt (div_pos hK hb).le
  have hc0 : 0 < κ * R ^ (p - 1) := mul_pos hκ (Real.rpow_pos_of_pos hR _)
  set σ0 : ℝ → ℝ := fun x => κ * R ^ (p - 1) * x
  have hσ0pos : ∀ x, 0 < x → 0 < σ0 x := fun x hx => mul_pos hc0 hx
  have hσ0c : Continuous σ0 := continuous_const.mul continuous_id
  have hσ0 : Admissible σ0 := by
    refine ⟨hσ0c.measurable, fun x hx => (hσ0pos x hx).ne', fun a b ha _ => ?_⟩
    refine ContinuousOn.integrableOn_Icc (continuousOn_const.div (hσ0c.pow 2).continuousOn
      fun x hx => pow_ne_zero 2 (hσ0pos x (ha.trans_le hx.1)).ne')
  have hcc := Novel.D8TailCompletions.completion_pos_continuous hR hσ0c.continuousOn hσ0pos p
  set σ := completion σ0 R p
  have htail : ∀ x, R ≤ x → σ x = κ * x ^ p := fun x hx => by
    have hx0 : 0 < x := hR.trans_le hx
    show completion σ0 R p x = κ * x ^ p
    rw [Novel.D8TailCompletions.completion_eq_tail hR hx, Real.div_rpow hx0.le hR.le]
    simp only [σ0]
    rw [Real.rpow_sub_one hR.ne']
    have : 0 < R ^ p := Real.rpow_pos_of_pos hR p
    field_simp
  refine ⟨σ, ⟨(Novel.D8TailCompletions.compatible_completion hσ0 hR p).1, hcc.2, hcc.1, κ, p,
    hκ, htail⟩, ⟨κ, hκ, htail⟩, ?_⟩
  rw [B1_eq hκ htail hR hr]
  change (κ ^ 2)⁻¹ * K = b
  rw [hκ2]; field_simp

/-- The panel: one exponent, separate scales, prescribed first blocks. -/
theorem attain_panel {ι : Type*} {R : ι → ℝ} (hR : ∀ i, 0 < R i) (hr : 1 < r) (p : ℝ)
    {b : ι → ℝ} (hb : ∀ i, 0 < b i) :
    ∃ σ : ι → ℝ → ℝ, SharedP R σ p ∧ ∀ i, B1 (R i) r (σ i) = b i := by
  choose σ hσ hκ hB using fun i => attain_p (hR i) hr p (hb i)
  exact ⟨σ, ⟨hσ, hκ⟩, hB⟩

/-- Every second block is `r^{2−2p}` times the first, and the label is `1_{r^{2−2p} < 1}`. -/
theorem ratio_label {ι : Type*} {R : ι → ℝ} {σ : ι → ℝ → ℝ} {p : ℝ} (hR : ∀ i, 0 < R i)
    (hr : 1 < r) (h : SharedP R σ p) (i : ι) :
    B2 (R i) r (σ i) = r ^ (2 - 2 * p) * B1 (R i) r (σ i) ∧
    0 < B1 (R i) r (σ i) ∧
    B2 (R i) r (σ i) / B1 (R i) r (σ i) = r ^ (2 - 2 * p) ∧
    θ (R i) (σ i) = if r ^ (2 - 2 * p) < 1 then 1 else 0 := by
  obtain ⟨κ, hκ, ht⟩ := h.2 i
  have hb2 := B2_eq hκ ht (hR i) hr
  have hb1 := B1_pos hκ ht (hR i) hr
  have hq : B2 (R i) r (σ i) / B1 (R i) r (σ i) = r ^ (2 - 2 * p) := by
    rw [hb2, mul_div_assoc, div_self hb1.ne', mul_one]
  refine ⟨hb2, hb1, hq, ?_⟩
  rw [theta_eq (hR i) hr (h.1 i), ← hq]
  simp only [div_lt_one hb1]

/-- `r^{2−2p} = q` for `p = 1 − log q/(2 log r)`. -/
theorem rpow_p_of_q (hr : 1 < r) {q : ℝ} (hq : 0 < q) :
    r ^ (2 - 2 * (1 - Real.log q / (2 * Real.log r))) = q := by
  have hl : Real.log r ≠ 0 := (Real.log_pos hr).ne'
  have he : 2 - 2 * (1 - Real.log q / (2 * Real.log r)) = Real.log q / Real.log r := by
    field_simp; ring
  rw [he, Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hl, Real.exp_log hq]

/-- Any common positive ratio with any positive first blocks. -/
theorem attain_ratio {ι : Type*} {R : ι → ℝ} (hR : ∀ i, 0 < R i) (hr : 1 < r) {q : ℝ}
    (hq : 0 < q) {b : ι → ℝ} (hb : ∀ i, 0 < b i) :
    ∃ σ, SharedP R σ (1 - Real.log q / (2 * Real.log r)) ∧
      ∀ i, B1 (R i) r (σ i) = b i ∧ B2 (R i) r (σ i) = q * b i := by
  obtain ⟨σ, hσ, hB⟩ := attain_panel hR hr (1 - Real.log q / (2 * Real.log r)) hb
  refine ⟨σ, hσ, fun i => ⟨hB i, ?_⟩⟩
  rw [(ratio_label hR hr hσ i).1, rpow_p_of_q hr hq, hB i]

end Scales

/-! ## Exact observations -/

theorem first_blocks {ι : Type*} [Nonempty ι] {R : ι → ℝ} {r : ℝ} {b1 : ι → ℝ}
    (hR : ∀ i, 0 < R i) (hr : 1 < r) (hb : ∀ i, 0 < b1 i) :
    {n | ∃ σ, Shared R σ ∧ (∀ i, B1 (R i) r (σ i) = b1 i) ∧ ∀ i, θ (R i) (σ i) = n} = {0, 1} := by
  ext n
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun ⟨σ, _, _, hn⟩ => ?_, fun hn => ?_⟩
  · obtain ⟨i⟩ := ‹Nonempty ι›
    rw [← hn i, θ]; split_ifs <;> simp
  · rcases hn with rfl | rfl
    · obtain ⟨σ, hσ, hB⟩ := attain_panel hR hr 1 hb
      refine ⟨σ, ⟨1, hσ⟩, hB, fun i => ?_⟩
      rw [(ratio_label hR hr hσ i).2.2.2]
      simp
    · obtain ⟨σ, hσ, hB⟩ := attain_panel hR hr 2 hb
      refine ⟨σ, ⟨2, hσ⟩, hB, fun i => ?_⟩
      rw [(ratio_label hR hr hσ i).2.2.2]
      simp [(rpow_lt_one_iff' hr _).2 (by norm_num : (2 : ℝ) - 2 * 2 < 0)]

/-! ## Rectangles -/

section Rect

variable {ι : Type*} {R : ι → ℝ} {r : ℝ} {L1 U1 L2 U2 : ι → ℝ}

/-- Necessity for one name. -/
theorem ratio_mem {b1 b2 l1 u1 l2 u2 : ℝ} (hb1 : 0 < b1) (hb2 : 0 ≤ b2) (hl1 : 0 < l1)
    (h1 : b1 ∈ Icc l1 u1) (h2 : b2 ∈ Icc l2 u2) : b2 / b1 ∈ Icc (l2 / u1) (u2 / l1) := by
  have hu1 : 0 < u1 := hb1.trans_le h1.2
  constructor
  · calc l2 / u1 ≤ b2 / u1 := div_le_div_of_nonneg_right h2.1 hu1.le
      _ ≤ b2 / b1 := div_le_div_of_nonneg_left hb2 hb1 h1.2
  · calc b2 / b1 ≤ u2 / b1 := div_le_div_of_nonneg_right h2.2 hb1.le
      _ ≤ u2 / l1 := div_le_div_of_nonneg_left ((hb2.trans h2.2)) hl1 h1.1

theorem iInter_eq_Icc [Fintype ι] [Nonempty ι] :
    (⋂ i, Icc (ell U1 L2 i) (u L1 U2 i)) = Icc (ellStar U1 L2) (uStar L1 U2) := by
  ext q
  simp only [mem_iInter, mem_Icc, ellStar, uStar, Finset.sup'_le_iff, Finset.le_inf'_iff,
    Finset.mem_univ, true_implies]
  exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩

theorem qSet_eq [Nonempty ι] (hR : ∀ i, 0 < R i) (hr : 1 < r) (hL1 : ∀ i, 0 < L1 i)
    (h11 : ∀ i, L1 i ≤ U1 i) (hL2 : ∀ i, 0 < L2 i) (h22 : ∀ i, L2 i ≤ U2 i) :
    qSet R r L1 U1 L2 U2 = ⋂ i, Icc (ell U1 L2 i) (u L1 U2 i) := by
  ext q
  simp only [mem_iInter]
  constructor
  · rintro ⟨σ, ⟨p, hσ⟩, hrect, hq⟩ i
    have hb1 := (ratio_label hR hr hσ i).2.1
    rw [← hq i]
    exact ratio_mem hb1 ((hL2 i).le.trans (hrect i).2.1) (hL1 i) (hrect i).1 (hrect i).2
  · intro hmem
    obtain ⟨i0⟩ := ‹Nonempty ι›
    have hU1 : ∀ i, 0 < U1 i := fun i => (hL1 i).trans_le (h11 i)
    have hq : 0 < q := (div_pos (hL2 i0) (hU1 i0)).trans_le (hmem i0).1
    set b : ι → ℝ := fun i => max (L1 i) (L2 i / q)
    have hb : ∀ i, 0 < b i := fun i => (hL1 i).trans_le (le_max_left _ _)
    obtain ⟨σ, hσ, hB⟩ := attain_ratio hR hr hq hb
    refine ⟨σ, ⟨_, hσ⟩, fun i => ?_, fun i => ?_⟩
    · have hl := (hmem i).1
      have hu := (hmem i).2
      simp only [ell, u] at hl hu
      have hlq : L2 i ≤ q * U1 i := by rwa [div_le_iff₀ (hU1 i)] at hl
      have huq : q * L1 i ≤ U2 i := by rwa [le_div_iff₀ (hL1 i)] at hu
      rw [(hB i).1, (hB i).2]
      refine ⟨⟨le_max_left _ _, max_le (h11 i) ?_⟩, ⟨?_, ?_⟩⟩
      · rw [div_le_iff₀ hq]; linarith
      · calc L2 i = q * (L2 i / q) := by field_simp
          _ ≤ q * b i := mul_le_mul_of_nonneg_left (le_max_right _ _) hq.le
      · rcases le_total (L1 i) (L2 i / q) with h | h
        · rw [show b i = L2 i / q from max_eq_right h]; field_simp; exact h22 i
        · rw [show b i = L1 i from max_eq_left h]; exact huq
    · rw [(hB i).2, (hB i).1, mul_div_assoc, div_self (hb i).ne', mul_one]

/-- `ℓ_* ≤ r^y ≤ u_*` in exponent form. -/
theorem pSet_eq [Fintype ι] [Nonempty ι] (hR : ∀ i, 0 < R i) (hr : 1 < r)
    (hL1 : ∀ i, 0 < L1 i) (h11 : ∀ i, L1 i ≤ U1 i) (hL2 : ∀ i, 0 < L2 i) (h22 : ∀ i, L2 i ≤ U2 i) :
    pSet R r L1 U1 L2 U2 = Icc (1 - Real.log (uStar L1 U2) / (2 * Real.log r))
      (1 - Real.log (ellStar U1 L2) / (2 * Real.log r)) := by
  have hq := qSet_eq hR hr hL1 h11 hL2 h22
  rw [iInter_eq_Icc] at hq
  have hU1 : ∀ i, 0 < U1 i := fun i => (hL1 i).trans_le (h11 i)
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hℓ : 0 < ellStar U1 L2 :=
    (div_pos (hL2 i0) (hU1 i0)).trans_le (Finset.le_sup' (ell U1 L2) (Finset.mem_univ i0))
  have hu : 0 < uStar L1 U2 := by
    rw [uStar, Finset.lt_inf'_iff]
    exact fun i _ => div_pos ((hL2 i).trans_le (h22 i)) (hL1 i)
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hlr : 0 < Real.log r := Real.log_pos hr
  -- `p ∈ pSet ↔ r^{2−2p} ∈ [ℓ_*, u_*]`.
  have key : ∀ p, p ∈ pSet R r L1 U1 L2 U2 ↔ r ^ (2 - 2 * p) ∈ Icc (ellStar U1 L2) (uStar L1 U2) := by
    intro p
    constructor
    · rintro ⟨σ, hσ, hrect⟩
      rw [← hq]
      obtain ⟨i⟩ := ‹Nonempty ι›
      refine ⟨σ, ⟨p, hσ⟩, hrect, fun j => (ratio_label hR hr hσ j).2.2.1⟩
    · intro hmem
      rw [← hq] at hmem
      obtain ⟨σ, -, hrect, hσq⟩ := hmem
      -- Rebuild with exponent `p` and the same first blocks.
      have hb : ∀ i, 0 < B1 (R i) r (σ i) := fun i =>
        (hL1 i).trans_le (hrect i).1.1
      obtain ⟨σ', hσ', hB⟩ := attain_panel hR hr p hb
      refine ⟨σ', hσ', fun i => ?_⟩
      have h2 : B2 (R i) r (σ' i) = B2 (R i) r (σ i) := by
        rw [(ratio_label hR hr hσ' i).1, hB i, ← hσq i, div_mul_cancel₀ _ (hb i).ne']
      rw [hB i, h2]; exact hrect i
  ext p
  rw [key, mem_Icc, mem_Icc, ← Real.log_le_log_iff hℓ (Real.rpow_pos_of_pos hr0 _),
    ← Real.log_le_log_iff (Real.rpow_pos_of_pos hr0 _) hu, Real.log_rpow hr0]
  set c := Real.log r
  have h2c : 0 < 2 * c := by positivity
  have A : ∀ a, (1 - a / (2 * c) ≤ p ↔ (2 - 2 * p) * c ≤ a) := fun a => by
    have : (1 - a / (2 * c) ≤ p ↔ 1 - p ≤ a / (2 * c)) :=
      ⟨fun h => by linarith, fun h => by linarith⟩
    rw [this, le_div_iff₀ h2c]
    constructor <;> intro h <;> nlinarith
  have B : ∀ a, (p ≤ 1 - a / (2 * c) ↔ a ≤ (2 - 2 * p) * c) := fun a => by
    have : (p ≤ 1 - a / (2 * c) ↔ a / (2 * c) ≤ 1 - p) :=
      ⟨fun h => by linarith, fun h => by linarith⟩
    rw [this, div_le_iff₀ h2c]
    constructor <;> intro h <;> nlinarith
  rw [A, B]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem label_of_mem {σ : ι → ℝ → ℝ} (hR : ∀ i, 0 < R i) (hr : 1 < r) (hσ : Shared R σ)
    (i : ι) : θ (R i) (σ i) = if B2 (R i) r (σ i) / B1 (R i) r (σ i) < 1 then 1 else 0 := by
  obtain ⟨p, hp⟩ := hσ
  rw [(ratio_label hR hr hp i).2.2.2, (ratio_label hR hr hp i).2.2.1]

theorem rect_part [Fintype ι] [Nonempty ι] (hR : ∀ i, 0 < R i) (hr : 1 < r)
    (hL1 : ∀ i, 0 < L1 i) (h11 : ∀ i, L1 i ≤ U1 i) (hL2 : ∀ i, 0 < L2 i) (h22 : ∀ i, L2 i ≤ U2 i) :
    qSet R r L1 U1 L2 U2 = ⋂ i, Icc (ell U1 L2 i) (u L1 U2 i) ∧
    qSet R r L1 U1 L2 U2 = Icc (ellStar U1 L2) (uStar L1 U2) ∧
    (ellStar U1 L2 ≤ uStar L1 U2 →
      pSet R r L1 U1 L2 U2 = Icc (1 - Real.log (uStar L1 U2) / (2 * Real.log r))
        (1 - Real.log (ellStar U1 L2) / (2 * Real.log r)) ∧
      (0 ∈ labelSet R r L1 U1 L2 U2 ↔ 1 ≤ uStar L1 U2) ∧
      (1 ∈ labelSet R r L1 U1 L2 U2 ↔ ellStar U1 L2 < 1) ∧
      (uStar L1 U2 < 1 ↔ ∃ i, u L1 U2 i < 1)) ∧
    (uStar L1 U2 < ellStar U1 L2 → labelSet R r L1 U1 L2 U2 = ∅) ∧
    ∀ i, (u L1 U2 i < 1 ↔ U2 i < L1 i) := by
  have hq1 := qSet_eq hR hr hL1 h11 hL2 h22
  have hq2 : qSet R r L1 U1 L2 U2 = Icc (ellStar U1 L2) (uStar L1 U2) := hq1.trans iInter_eq_Icc
  obtain ⟨i0⟩ := ‹Nonempty ι›
  -- A label witness has its common ratio in `qSet`.
  have hwit : ∀ σ, Shared R σ → InRect R r L1 U1 L2 U2 σ →
      B2 (R i0) r (σ i0) / B1 (R i0) r (σ i0) ∈ qSet R r L1 U1 L2 U2 ∧
      ∀ i, θ (R i) (σ i) = if B2 (R i0) r (σ i0) / B1 (R i0) r (σ i0) < 1 then 1 else 0 := by
    intro σ hσ hrect
    obtain ⟨p, hp⟩ := hσ
    have hc : ∀ i, B2 (R i) r (σ i) / B1 (R i) r (σ i) =
        B2 (R i0) r (σ i0) / B1 (R i0) r (σ i0) := fun i => by
      rw [(ratio_label hR hr hp i).2.2.1, (ratio_label hR hr hp i0).2.2.1]
    refine ⟨⟨σ, ⟨p, hp⟩, hrect, hc⟩, fun i => ?_⟩
    rw [label_of_mem hR hr ⟨p, hp⟩ i, hc i]
  -- A ratio in `qSet` is realized with its label.
  have hreal : ∀ q ∈ qSet R r L1 U1 L2 U2, ∃ σ, Shared R σ ∧ InRect R r L1 U1 L2 U2 σ ∧
      ∀ i, θ (R i) (σ i) = if q < 1 then 1 else 0 := by
    rintro q ⟨σ, hσ, hrect, hσq⟩
    exact ⟨σ, hσ, hrect, fun i => by rw [label_of_mem hR hr hσ i, hσq i]⟩
  refine ⟨hq1, hq2, fun hne => ⟨pSet_eq hR hr hL1 h11 hL2 h22, ?_, ?_, ?_⟩, fun hemp => ?_,
    fun i => div_lt_one (hL1 i)⟩
  · constructor
    · rintro ⟨σ, hσ, hrect, h0⟩
      obtain ⟨hm, hθ⟩ := hwit σ hσ hrect
      rw [hq2] at hm
      have := hθ i0
      rw [h0 i0] at this
      split_ifs at this with h
      exact (not_lt.1 h).trans hm.2
    · intro h1
      obtain ⟨σ, hσ, hrect, hθ⟩ := hreal (uStar L1 U2) (by rw [hq2]; exact ⟨hne, le_rfl⟩)
      exact ⟨σ, hσ, hrect, fun i => by rw [hθ i]; simp [not_lt.2 h1]⟩
  · constructor
    · rintro ⟨σ, hσ, hrect, h0⟩
      obtain ⟨hm, hθ⟩ := hwit σ hσ hrect
      rw [hq2] at hm
      have := hθ i0
      rw [h0 i0] at this
      split_ifs at this with h
      exact hm.1.trans_lt h
    · intro h1
      obtain ⟨σ, hσ, hrect, hθ⟩ := hreal (ellStar U1 L2) (by rw [hq2]; exact ⟨le_rfl, hne⟩)
      exact ⟨σ, hσ, hrect, fun i => by rw [hθ i]; simp [h1]⟩
  · rw [uStar, Finset.inf'_lt_iff]
    simp
  · ext n
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨σ, hσ, hrect, -⟩
    have hm := (hwit σ hσ hrect).1
    rw [hq2] at hm
    exact absurd (hm.1.trans hm.2) (not_le.2 hemp)

end Rect

/-! ## Coverage -/

section Coverage

variable {ι : Type*} {R : ι → ℝ} {r : ℝ}

theorem coverage [Fintype ι] [Nonempty ι] (hR : ∀ i, 0 < R i) (hr : 1 < r) {σ : ι → ℝ → ℝ}
    (hσ : Shared R σ) (h0 : ∀ i, θ (R i) (σ i) = 0) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (L1 U1 L2 U2 : ι → Ω → ℝ) (α : ℝ)
    (hl1 : ∀ i, Measurable (L1 i)) (hu1 : ∀ i, Measurable (U1 i)) (hl2 : ∀ i, Measurable (L2 i))
    (hu2 : ∀ i, Measurable (U2 i)) (hpos : ∀ i ω, 0 < L1 i ω)
    (hcov : 1 - α ≤ P.real {ω | InRect R r (fun i => L1 i ω) (fun i => U1 i ω)
      (fun i => L2 i ω) (fun i => U2 i ω) σ}) :
    P.real {ω | rejects (fun i => L1 i ω) (fun i => U1 i ω) (fun i => L2 i ω)
      (fun i => U2 i ω)} ≤ α := by
  obtain ⟨p, hp⟩ := hσ
  have hq1 : 1 ≤ r ^ (2 - 2 * p) := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := (ratio_label hR hr hp i).2.2.2
    rw [h0 i] at this
    split_ifs at this with h
    exact not_lt.1 h
  set C := {ω | InRect R r (fun i => L1 i ω) (fun i => U1 i ω) (fun i => L2 i ω)
    (fun i => U2 i ω) σ}
  have hC : MeasurableSet C := by
    have : C = ⋂ i, (({ω | L1 i ω ≤ B1 (R i) r (σ i)} ∩ {ω | B1 (R i) r (σ i) ≤ U1 i ω}) ∩
        ({ω | L2 i ω ≤ B2 (R i) r (σ i)} ∩ {ω | B2 (R i) r (σ i) ≤ U2 i ω})) := by
      ext ω; simp [C, InRect, and_assoc]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      ((measurableSet_le (hl1 i) measurable_const).inter (measurableSet_le measurable_const (hu1 i))).inter
        ((measurableSet_le (hl2 i) measurable_const).inter (measurableSet_le measurable_const (hu2 i)))
  have hsub : {ω | rejects (fun i => L1 i ω) (fun i => U1 i ω) (fun i => L2 i ω)
      (fun i => U2 i ω)} ⊆ Cᶜ := fun ω hω hc => by
    have hle : r ^ (2 - 2 * p) ≤ uStar (fun i => L1 i ω) (fun i => U2 i ω) := by
      rw [uStar, Finset.le_inf'_iff]
      intro i _
      obtain ⟨hb2, hb1, hq, -⟩ := ratio_label hR hr hp i
      have hm := ratio_mem hb1 (by rw [hb2]; positivity) (hpos i ω) (hc i).1 (hc i).2
      rw [hq] at hm
      exact hm.2
    exact absurd (hω : rejects _ _ _ _).2 (not_lt.2 (hq1.trans hle))
  calc _ ≤ P.real Cᶜ := measureReal_mono hsub
    _ = 1 - P.real C := probReal_compl_eq_one_sub hC
    _ ≤ α := by linarith

theorem bonferroni [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (C : ι → Set Ω) (a : ι → ℝ) (α : ℝ) (hC : ∀ i, MeasurableSet (C i))
    (ha : ∀ i, P.real (C i)ᶜ ≤ a i) (hα : ∑ i, a i ≤ α) : 1 - α ≤ P.real (⋂ i, C i) := by
  have hm : MeasurableSet (⋂ i, C i) := MeasurableSet.iInter hC
  have h1 : P.real (⋂ i, C i)ᶜ ≤ ∑ i, a i := by
    rw [compl_iInter]
    exact (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun i _ => ha i)
  rw [probReal_compl_eq_one_sub hm] at h1
  linarith

end Coverage

/-! ## The two-name example -/

section Example

/-- Masses `α, α, 1 − 2α` on `Fin 3`. -/
noncomputable def exMeasure (α : ℝ) : Measure (Fin 3) :=
  ∑ j : Fin 3, ENNReal.ofReal (![α, α, 1 - 2 * α] j) • Measure.dirac j

theorem exMeasure_real {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) (S : Set (Fin 3)) :
    (exMeasure α).real S = ∑ j : Fin 3, S.indicator (fun j => ![α, α, 1 - 2 * α] j) j := by
  have hw : ∀ j : Fin 3, 0 ≤ ![α, α, 1 - 2 * α] j := by
    intro j; fin_cases j <;> simp <;> linarith
  rw [measureReal_def, exMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.toReal_sum (fun j _ => by simp [indicator]; split_ifs <;> simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul, indicator]
  split_ifs <;> simp [ENNReal.toReal_ofReal (hw j)]

theorem exMeasure_prob {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) :
    IsProbabilityMeasure (exMeasure α) := by
  constructor
  have h := exMeasure_real hα0 hα univ
  rw [Fin.sum_univ_three] at h
  simp only [indicator_univ] at h
  have h1 : (exMeasure α).real univ = 1 := by rw [h]; simp; ring
  have hfin : (exMeasure α) univ ≠ ∞ := by
    simp [exMeasure, Measure.coe_finsetSum]
  rw [← ENNReal.ofReal_toReal hfin, ← measureReal_def, h1, ENNReal.ofReal_one]

/-- The two-name bands: first `[1, 2]`, replaced by `[2, 2]` on name `i`'s bad event `{i}`;
second `[1, 1]`. -/
noncomputable def exL1 (i : Fin 2) (ω : Fin 3) : ℝ := if (ω : ℕ) = i then 2 else 1

theorem ex_rejects (ω : Fin 3) :
    rejects (fun i => exL1 i ω) (fun _ => 2) (fun _ => 1) (fun _ => 1) ↔ (ω : ℕ) < 2 := by
  have hu : ∀ i : Fin 2, u (fun i => exL1 i ω) (fun _ => (1 : ℝ)) i = 1 / exL1 i ω :=
    fun i => rfl
  have hell : ∀ i : Fin 2, ell (fun _ => (2 : ℝ)) (fun _ => (1 : ℝ)) i = 1 / 2 := fun i => rfl
  have hL : ∀ i, exL1 i ω = 1 ∨ exL1 i ω = 2 := fun i => by
    unfold exL1; split_ifs <;> simp
  have hle : ellStar (ι := Fin 2) (fun _ => (2 : ℝ)) (fun _ => 1) ≤
      uStar (fun i => exL1 i ω) (fun _ => 1) := by
    rw [ellStar, Finset.sup'_le_iff]
    intro i _
    rw [uStar, Finset.le_inf'_iff]
    intro j _
    rw [hell, hu]
    rcases hL j with h | h <;> rw [h] <;> norm_num
  rw [rejects, and_iff_right hle, uStar, Finset.inf'_lt_iff]
  simp only [Finset.mem_univ, true_and, hu]
  constructor
  · rintro ⟨i, hi⟩
    have : exL1 i ω = 2 := by
      rcases hL i with h | h
      · rw [h] at hi; norm_num at hi
      · exact h
    unfold exL1 at this
    split_ifs at this with h
    · have := i.2; omega
    · norm_num at this
  · intro hω
    refine ⟨⟨ω, hω⟩, ?_⟩
    simp [exL1]
    norm_num

theorem example_two (R : Fin 2 → ℝ) (r α : ℝ) (hR : ∀ i, 0 < R i) (hr : 1 < r) (hα0 : 0 < α)
    (hα : α ≤ 1 / 2) :
    ∃ σ : Fin 2 → ℝ → ℝ, Shared R σ ∧ (∀ i, θ (R i) (σ i) = 0) ∧
      (∀ i, B1 (R i) r (σ i) = 1 ∧ B2 (R i) r (σ i) = 1) ∧
      ∃ (P : Measure (Fin 3)) (_ : IsProbabilityMeasure P) (L1 U1 L2 U2 : Fin 2 → Fin 3 → ℝ),
        (∀ i, P.real {ω | B1 (R i) r (σ i) ∈ Icc (L1 i ω) (U1 i ω) ∧
          B2 (R i) r (σ i) ∈ Icc (L2 i ω) (U2 i ω)} = 1 - α) ∧
        P.real {ω | rejects (fun i => L1 i ω) (fun i => U1 i ω) (fun i => L2 i ω)
          (fun i => U2 i ω)} = 2 * α := by
  obtain ⟨σ, hσ, hB⟩ := attain_ratio (b := fun _ => 1) hR hr one_pos fun _ => one_pos
  have hB' : ∀ i, B1 (R i) r (σ i) = 1 ∧ B2 (R i) r (σ i) = 1 := fun i =>
    ⟨(hB i).1, by rw [(hB i).2]; ring⟩
  have hθ : ∀ i, θ (R i) (σ i) = 0 := fun i => by
    rw [label_of_mem hR hr ⟨_, hσ⟩ i, (hB' i).1, (hB' i).2]; norm_num
  refine ⟨σ, ⟨_, hσ⟩, hθ, hB', exMeasure α, exMeasure_prob hα0.le hα, exL1, fun _ _ => 2,
    fun _ _ => 1, fun _ _ => 1, fun i => ?_, ?_⟩
  · have hset : {ω | B1 (R i) r (σ i) ∈ Icc (exL1 i ω) 2 ∧ B2 (R i) r (σ i) ∈ Icc 1 1} =
        {ω : Fin 3 | (ω : ℕ) ≠ i} := by
      ext ω
      simp only [(hB' i).1, (hB' i).2, mem_Icc, le_refl, and_true, mem_ofPred_eq, exL1]
      split_ifs with h <;> simp [h]
    rw [hset, exMeasure_real hα0.le hα, Fin.sum_univ_three]
    fin_cases i <;> simp [indicator] <;> ring
  · have hset : {ω | rejects (fun i => exL1 i ω) (fun i => (fun _ _ => (2 : ℝ)) i ω)
        (fun i => (fun _ _ => (1 : ℝ)) i ω) (fun i => (fun _ _ => (1 : ℝ)) i ω)} =
        {ω : Fin 3 | (ω : ℕ) < 2} := by
      ext ω; exact ex_rejects ω
    rw [hset, exMeasure_real hα0.le hα, Fin.sum_univ_three]
    simp [indicator]
    ring

end Example

/-! ## Occupation pooling -/

section Pool

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem tendsto_real_of_symmDiff {A : ℕ → Set Ω} {B : Set Ω}
    (h : Tendsto (fun n => P.real (symmDiff (A n) B)) atTop (𝓝 0)) :
    Tendsto (fun n => P.real (A n)) atTop (𝓝 (P.real B)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h
  rw [Real.norm_eq_abs, abs_le]
  have h1 : P.real (A n) ≤ P.real B + P.real (symmDiff (A n) B) :=
    (measureReal_mono fun ω hω => by
      by_cases hB : ω ∈ B
      · exact Or.inl hB
      · exact Or.inr (Set.mem_symmDiff.2 (Or.inl ⟨hω, hB⟩))).trans (measureReal_union_le _ _)
  have h2 : P.real B ≤ P.real (A n) + P.real (symmDiff (A n) B) :=
    (measureReal_mono fun ω hω => by
      by_cases hA : ω ∈ A n
      · exact Or.inl hA
      · exact Or.inr (Set.mem_symmDiff.2 (Or.inr ⟨hω, hA⟩))).trans (measureReal_union_le _ _)
  constructor <;> linarith

theorem tendsto_sum_zero {ι : Type*} [Fintype ι] {f : ι → ℕ → ℝ}
    (h : ∀ i, Tendsto (f i) atTop (𝓝 0)) : Tendsto (fun n => ∑ i, f i n) atTop (𝓝 0) := by
  have := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ => h i
  simpa using this

theorem pool {ι : Type*} [Fintype ι] {R : ι → ℝ} {r : ℝ} {σ : ι → ℝ → ℝ} (hR : ∀ i, 0 < R i)
    (hr : 1 < r) (hσ : Shared R σ)
    (Bh1 Bh2 : ι → ℕ → Ω → ℝ) (D1 D2 Ds : ι → ℕ → Set Ω) (D : ι → Set Ω) (h : ℕ → ℝ)
    (hm1 : ∀ i n, Measurable (Bh1 i n)) (hm2 : ∀ i n, Measurable (Bh2 i n))
    (hDs : ∀ i n, MeasurableSet (Ds i n)) (_hD : ∀ i, MeasurableSet (D i))
    (hs1 : ∀ i n, Ds i n ⊆ D1 i n) (hs2 : ∀ i n, Ds i n ⊆ D2 i n)
    (ht1 : ∀ i, TightOn P (Bh1 i) (B1 (R i) r (σ i)) (D1 i))
    (ht2 : ∀ i, TightOn P (Bh2 i) (B2 (R i) r (σ i)) (D2 i))
    (hsd : ∀ i, Tendsto (fun n => P (symmDiff (Ds i n) (D i))) atTop (𝓝 0))
    (hh0 : Tendsto h atTop (𝓝 0))
    (hh : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * h n) atTop atTop) :
    ((∀ i, θ (R i) (σ i) = 0) →
      Tendsto (fun n => P.real (⋃ i, reject (Bh1 i) (Bh2 i) h (Ds i) n)) atTop (𝓝 0)) ∧
    ((∀ i, θ (R i) (σ i) = 1) →
      Tendsto (fun n => P.real (⋃ i, reject (Bh1 i) (Bh2 i) h (Ds i) n)) atTop
        (𝓝 (P.real (⋃ i, D i))) ∧
      (0 < P.real (⋃ i, D i) →
        Tendsto (fun n => P.real (⋃ i, reject (Bh1 i) (Bh2 i) h (Ds i) n) /
          P.real (⋃ i, Ds i n)) atTop (𝓝 1)) ∧
      ∀ i, P.real (D i) ≤ P.real (⋃ i, D i)) := by
  obtain ⟨p, hp⟩ := hσ
  have hpt := fun i => part3 (hR i) hr (hp.1 i) (Bh1 i) (Bh2 i) (D1 i) (D2 i) (Ds i) (D i) h
    (hm1 i) (hm2 i) (hDs i) (hs1 i) (hs2 i) (ht1 i) (ht2 i) (hsd i) hh0 hh
  set rej : ι → ℕ → Set Ω := fun i n => reject (Bh1 i) (Bh2 i) h (Ds i) n
  have hsdr : ∀ i, Tendsto (fun n => P.real (symmDiff (Ds i n) (D i))) atTop (𝓝 0) := fun i => by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hsd i)
    simpa [Function.comp_def, measureReal_def] using this
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · refine squeeze_zero (fun n => measureReal_nonneg) (fun n => measureReal_iUnion_fintype_le _)
      (tendsto_sum_zero fun i => (hpt i).1 (h0 i))
  · have hrejm : ∀ i n, MeasurableSet (rej i n) := fun i n =>
      (hDs i n).inter (measurableSet_lt measurable_const ((hm1 i n).sub (hm2 i n)))
    have hrejs : ∀ i n, rej i n ⊆ Ds i n := fun i n ω hω => hω.1
    -- Each name: `P(Dᵢⁿ \ {φᵢₙ = 1}) → 0`.
    have hmiss : ∀ i, Tendsto (fun n => P.real (Ds i n \ rej i n)) atTop (𝓝 0) := fun i => by
      have h1' := ((hpt i).2 (h1 i)).1
      have h2' := tendsto_real_of_symmDiff (hsdr i)
      have := h2'.sub h1'
      rw [sub_self] at this
      refine this.congr fun n => ?_
      rw [measureReal_sdiff (hrejs i n) (hrejm i n)]
    -- `P(D_union^n) → P(D_union)`.
    have hU : Tendsto (fun n => P.real (⋃ i, Ds i n)) atTop (𝓝 (P.real (⋃ i, D i))) := by
      refine tendsto_real_of_symmDiff (squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_)
        (tendsto_sum_zero hsdr))
      refine (measureReal_mono fun ω hω => ?_).trans (measureReal_iUnion_fintype_le _)
      rcases Set.mem_symmDiff.1 hω with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.1 ha
        exact mem_iUnion.2 ⟨i, Set.mem_symmDiff.2 (Or.inl ⟨hi, fun h => hb (mem_iUnion.2 ⟨i, h⟩)⟩)⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.1 ha
        exact mem_iUnion.2 ⟨i, Set.mem_symmDiff.2 (Or.inr ⟨hi, fun h => hb (mem_iUnion.2 ⟨i, h⟩)⟩)⟩
    have hgap : Tendsto (fun n => P.real ((⋃ i, Ds i n) \ ⋃ i, rej i n)) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) (tendsto_sum_zero hmiss)
      refine (measureReal_mono fun ω hω => ?_).trans (measureReal_iUnion_fintype_le _)
      obtain ⟨i, hi⟩ := mem_iUnion.1 hω.1
      exact mem_iUnion.2 ⟨i, hi, fun h => hω.2 (mem_iUnion.2 ⟨i, h⟩)⟩
    have hrej : Tendsto (fun n => P.real (⋃ i, rej i n)) atTop (𝓝 (P.real (⋃ i, D i))) := by
      have := hU.sub hgap
      rw [sub_zero] at this
      refine this.congr fun n => ?_
      rw [measureReal_sdiff (iUnion_mono fun i => hrejs i n) (MeasurableSet.iUnion fun i => hrejm i n)]
      ring
    refine ⟨hrej, fun hpos => ?_, fun i => measureReal_mono (subset_iUnion D i)⟩
    have := hrej.div hU hpos.ne'
    rwa [div_self hpos.ne'] at this

end Pool

/-! ## The statement -/

theorem statement_holds : Standalone.D3PooledTail.statement := by
  refine ⟨fun R r σ p hR hr h i => ⟨(ratio_label hR hr h i).2.2.1, (ratio_label hR hr h i).2.2.2⟩,
    fun R r b1 hR hr hb => ⟨fun p => attain_panel hR hr p hb, first_blocks hR hr hb⟩,
    fun R r q b1 hR hr hq hb => ?_,
    fun R r L1 U1 L2 U2 hR hr hL1 h11 hL2 h22 => rect_part hR hr hL1 h11 hL2 h22,
    fun R r σ hR hr hσ h0 Ω _ P _ L1 U1 L2 U2 α hl1 hu1 hl2 hu2 hpos hcov =>
      coverage hR hr hσ h0 P L1 U1 L2 U2 α hl1 hu1 hl2 hu2 hpos hcov,
    fun P _ C a α hC ha hα => bonferroni P C a α hC ha hα,
    fun R r α hR hr hα0 hα => example_two R r α hR hr hα0 hα,
    fun R r σ hR hr hσ Ω _ P _ Bh1 Bh2 D1 D2 Ds D h hm1 hm2 hDs hD hs1 hs2 ht1 ht2 hsd hh0 hh =>
      pool hR hr hσ Bh1 Bh2 D1 D2 Ds D h hm1 hm2 hDs hD hs1 hs2 ht1 ht2 hsd hh0 hh⟩
  obtain ⟨σ, hσ, hB⟩ := attain_ratio hR hr hq hb
  exact ⟨σ, ⟨_, hσ⟩, hB⟩

end Novel.D3PooledTail
