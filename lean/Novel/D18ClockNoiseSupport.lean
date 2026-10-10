import Standalone.D18ClockNoise
import Novel.D17ClockCellsProof
import Novel.D18BoundedNoiseProof

/-!
# Claim 066: the support mode

Claim 034's partition argument on claim 064's expanded cells.
* `WcsE` is claim 034's transition bound between expanded subcells: positive, at most one,
  dominating the one-step probability for every parameter in the box (`transition_holds`), and
  decreasing with the box (`Wclock_mono`).
* `Usup` is in `(0, 1]`, decreases with the state level (parent bound) and with the box.
* `Qh_le_Usup`: for every parameter in the box, the probability that the latent path stays in the
  expanded intervals of the labels (claim 064's `Qh` with the indicator emission) is at most `U`,
  from every state of the subcell. The first step is claim 064's `Qh_le_sum`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18ClockNoise

open Standalone.D18ClockNoise Standalone.D17ClockCells Standalone.D18BoundedNoise
  Standalone.D14FixedTick Novel.D17ClockCells Novel.D18BoundedNoise Novel.D14FixedTick

variable {δ a : ℝ} {B : Box}

theorem WcsE_bounds (hδ : 0 < δ) (ha : 0 ≤ a) (hB : B.Valid) {Δ v : ℝ} (hΔ : 0 < Δ) (hv : 0 < v)
    (ℓ z c z' d : ℕ) : 0 < WcsE δ a B Δ v ℓ z c z' d ∧ WcsE δ a B Δ v ℓ z c z' d ≤ 1 :=
  let h := transition_holds B _ _ _ _ Δ v hB (eslo_nonneg hδ ha ℓ z c)
    (eslo_lt hδ ha ℓ z (Nat.lt_succ_self c)) (eslo_nonneg hδ ha ℓ z' d)
    (eslo_lt hδ ha ℓ z' (Nat.lt_succ_self d)) hΔ hv
  ⟨h.1, h.2.1⟩

theorem step_le_WcsE (hδ : 0 < δ) (ha : 0 ≤ a) (hB : B.Valid) {Δ v : ℝ} (hΔ : 0 < Δ) (hv : 0 < v)
    {ℓ z c : ℕ} (z' d : ℕ) {x : ℝ} (hx : x ∈ esub δ a ℓ z c) {p : ℝ × ℝ} (hp : B.Mem p) :
    stepP (p.1 * Δ - p.2 * v / 2) (Real.sqrt (p.2 * v)) x (esub δ a ℓ z' d) ≤
      ENNReal.ofReal (WcsE δ a B Δ v ℓ z c z' d) :=
  (transition_holds B _ _ _ _ Δ v hB (eslo_nonneg hδ ha ℓ z c)
    (eslo_lt hδ ha ℓ z (Nat.lt_succ_self c)) (eslo_nonneg hδ ha ℓ z' d)
    (eslo_lt hδ ha ℓ z' (Nat.lt_succ_self d)) hΔ hv).2.2.1 x hx p hp

theorem WcsE_mono (hδ : 0 < δ) (ha : 0 ≤ a) (hB : B.Valid) {B' : Box} (hB' : B'.Valid)
    (hsub : B'.Sub B) {Δ v : ℝ} (hΔ : 0 < Δ) (hv : 0 < v) (ℓ z c z' d : ℕ) :
    WcsE δ a B' Δ v ℓ z c z' d ≤ WcsE δ a B Δ v ℓ z c z' d :=
  Wclock_mono hB hB' hsub (eslo_nonneg hδ ha ℓ z c) (eslo_lt hδ ha ℓ z (Nat.lt_succ_self c))
    (eslo_nonneg hδ ha ℓ z' d) (eslo_lt hδ ha ℓ z' (Nat.lt_succ_self d)) hΔ hv

theorem Usup_nil (ℓ : ℕ) (Δ vc : Fin 0 → ℝ) (z : ℕ) (v : Fin 0 → ℕ) (c : ℕ) :
    Usup δ a B ℓ 0 Δ vc z v c = 1 := by
  cases ℓ <;> simp [Usup]

theorem Usup_zero_succ {n : ℕ} (Δ vc : Fin (n + 1) → ℝ) (z : ℕ) (v : Fin (n + 1) → ℕ) (c : ℕ) :
    Usup δ a B 0 (n + 1) Δ vc z v c = min 1 (∑ d ∈ Finset.range (2 ^ 0),
      WcsE δ a B (Δ 0) (vc 0) 0 z c (v 0) d *
        Usup δ a B 0 n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d) := by
  rw [Usup]

theorem Usup_succ_succ (ℓ : ℕ) {n : ℕ} (Δ vc : Fin (n + 1) → ℝ) (z : ℕ) (v : Fin (n + 1) → ℕ)
    (c : ℕ) : Usup δ a B (ℓ + 1) (n + 1) Δ vc z v c =
      min (min 1 (∑ d ∈ Finset.range (2 ^ (ℓ + 1)), WcsE δ a B (Δ 0) (vc 0) (ℓ + 1) z c (v 0) d *
        Usup δ a B (ℓ + 1) n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d))
        (Usup δ a B ℓ (n + 1) Δ vc z v (c / 2)) := by
  rw [Usup]

theorem Usup_parent (ℓ : ℕ) {n : ℕ} (Δ vc : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (c : ℕ) :
    Usup δ a B (ℓ + 1) n Δ vc z v c ≤ Usup δ a B ℓ n Δ vc z v (c / 2) := by
  cases n with
  | zero => rw [Usup_nil, Usup_nil]
  | succ n => rw [Usup_succ_succ]; exact min_le_right _ _

theorem Usup_bounds (hδ : 0 < δ) (ha : 0 ≤ a) (hB : B.Valid) :
    ∀ (n ℓ : ℕ) (Δ vc : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (c : ℕ), (∀ j, 0 < Δ j) →
      (∀ j, 0 < vc j) → 0 < Usup δ a B ℓ n Δ vc z v c ∧ Usup δ a B ℓ n Δ vc z v c ≤ 1
  | 0, ℓ, Δ, vc, z, v, c, _, _ => by rw [Usup_nil]; exact ⟨one_pos, le_rfl⟩
  | n + 1, ℓ, Δ, vc, z, v, c, hΔ, hv => by
    have IH := Usup_bounds hδ ha hB n
    have hT : ∀ ℓ' c', 0 < ∑ d ∈ Finset.range (2 ^ ℓ'), WcsE δ a B (Δ 0) (vc 0) ℓ' z c' (v 0) d *
        Usup δ a B ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d := fun ℓ' c' =>
      Finset.sum_pos (fun d _ => mul_pos (WcsE_bounds hδ ha hB (hΔ 0) (hv 0) _ _ _ _ _).1
        (IH ℓ' _ _ _ _ d (fun j => hΔ _) (fun j => hv _)).1)
        ⟨0, Finset.mem_range.2 (pow_pos two_pos _)⟩
    induction ℓ generalizing c with
    | zero => rw [Usup_zero_succ]; exact ⟨lt_min one_pos (hT 0 c), min_le_left _ _⟩
    | succ ℓ ih =>
      rw [Usup_succ_succ]
      exact ⟨lt_min (lt_min one_pos (hT _ c)) (ih (c / 2)).1,
        (min_le_left _ _).trans (min_le_left _ _)⟩

theorem Usup_mono (hδ : 0 < δ) (ha : 0 ≤ a) (hB : B.Valid) {B' : Box} (hB' : B'.Valid)
    (hsub : B'.Sub B) :
    ∀ (n ℓ : ℕ) (Δ vc : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (c : ℕ), (∀ j, 0 < Δ j) →
      (∀ j, 0 < vc j) → Usup δ a B' ℓ n Δ vc z v c ≤ Usup δ a B ℓ n Δ vc z v c
  | 0, ℓ, Δ, vc, z, v, c, _, _ => by rw [Usup_nil, Usup_nil]
  | n + 1, ℓ, Δ, vc, z, v, c, hΔ, hv => by
    have IH := Usup_mono hδ ha hB hB' hsub n
    have hT : ∀ ℓ' c', ∑ d ∈ Finset.range (2 ^ ℓ'), WcsE δ a B' (Δ 0) (vc 0) ℓ' z c' (v 0) d *
          Usup δ a B' ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d ≤
        ∑ d ∈ Finset.range (2 ^ ℓ'), WcsE δ a B (Δ 0) (vc 0) ℓ' z c' (v 0) d *
          Usup δ a B ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d := fun ℓ' c' =>
      Finset.sum_le_sum fun d _ => mul_le_mul
        (WcsE_mono hδ ha hB hB' hsub (hΔ 0) (hv 0) _ _ _ _ _)
        (IH ℓ' _ _ _ _ d (fun j => hΔ _) (fun j => hv _))
        (Usup_bounds hδ ha hB' n ℓ' _ _ _ _ d (fun j => hΔ _) (fun j => hv _)).1.le
        (WcsE_bounds hδ ha hB (hΔ 0) (hv 0) _ _ _ _ _).1.le
    induction ℓ generalizing c with
    | zero => rw [Usup_zero_succ, Usup_zero_succ]; exact min_le_min le_rfl (hT 0 c)
    | succ ℓ ih =>
      rw [Usup_succ_succ, Usup_succ_succ]
      exact min_le_min (min_le_min le_rfl (hT _ c)) (ih (c / 2))

/-- The indicator emission of the expanded intervals. -/
noncomputable def hbox (δ a : ℝ) : ℕ → ℝ → ℝ := fun z y => (ecell δ a z).indicator 1 y

theorem hbox_meas (z : ℕ) : Measurable (hbox δ a z) := measurable_one.indicator measurableSet_Ico

theorem hbox_le_one (z : ℕ) (y : ℝ) : hbox δ a z y ≤ 1 := by
  by_cases hy : y ∈ ecell δ a z <;> simp [hbox, hy]

theorem hbox_out (z : ℕ) (y : ℝ) (_ : 0 ≤ y) (hy : y ∉ ecell δ a z) : hbox δ a z y = 0 := by
  simp [hbox, hy]

/-- The support suffix bound: for every parameter in the box, the latent path stays in the expanded
intervals with probability at most `U`, from every state of the subcell. -/
theorem Qh_le_Usup (hδ : 0 < δ) (ha : 0 ≤ a) (hB : B.Valid) :
    ∀ (n ℓ : ℕ) (Δ vc : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (c : ℕ), (∀ j, 0 < Δ j) →
      (∀ j, 0 < vc j) → c < 2 ^ ℓ → ∀ p, B.Mem p → ∀ x ∈ esub δ a ℓ z c,
        Qh (hbox δ a) (muC Δ vc p) (sdC vc p) v x ≤ ENNReal.ofReal (Usup δ a B ℓ n Δ vc z v c)
  | 0, ℓ, Δ, vc, z, v, c, _, _, _, p, _, x, _ => by
    rw [Usup_nil, ENNReal.ofReal_one]; exact Qh_le_one hbox_le_one _ _ v x
  | n + 1, ℓ, Δ, vc, z, v, c, hΔ, hv, hc, p, hp, x, hx => by
    have IH := Qh_le_Usup hδ ha hB n
    have hTq : ∀ ℓ' c', ∀ x ∈ esub δ a ℓ' z c', Qh (hbox δ a) (muC Δ vc p) (sdC vc p) v x ≤
        ENNReal.ofReal (∑ d ∈ Finset.range (2 ^ ℓ'), WcsE δ a B (Δ 0) (vc 0) ℓ' z c' (v 0) d *
          Usup δ a B ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d) := fun ℓ' c' x hx => by
      refine (Qh_le_sum (δ := δ) (a := a) (h := hbox δ a) hbox_meas hbox_out (muC Δ vc p) (sdC vc p)
        (esub_nonneg hδ ha hx) v (Finset.range (2 ^ ℓ')) (esub δ a ℓ' (v 0))
        (fun d => ENNReal.ofReal (Usup δ a B ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d))
        (fun _ => measurableSet_Ico) (esub_cover hδ ha ℓ' (v 0)) (fun d hd y hy _ => ?_)).trans ?_
      · calc ENNReal.ofReal (hbox δ a (v 0) y) *
              Qh (hbox δ a) (Fin.tail (muC Δ vc p)) (Fin.tail (sdC vc p)) (Fin.tail v) y
            ≤ 1 * Qh (hbox δ a) (muC (Fin.tail Δ) (Fin.tail vc) p) (sdC (Fin.tail vc) p)
                (Fin.tail v) y :=
              mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.2 (hbox_le_one _ _)) bot_le
          _ ≤ _ := by
              rw [one_mul]
              exact IH ℓ' _ _ _ _ d (fun j => hΔ _) (fun j => hv _) (Finset.mem_range.1 hd) p hp y hy
      · have hnn : ∀ d ∈ Finset.range (2 ^ ℓ'), 0 ≤ WcsE δ a B (Δ 0) (vc 0) ℓ' z c' (v 0) d *
            Usup δ a B ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d := fun d _ =>
          mul_nonneg (WcsE_bounds hδ ha hB (hΔ 0) (hv 0) _ _ _ _ _).1.le
            (Usup_bounds hδ ha hB n ℓ' _ _ _ _ d (fun j => hΔ _) (fun j => hv _)).1.le
        rw [ENNReal.ofReal_sum_of_nonneg hnn]
        refine Finset.sum_le_sum fun d _ => ?_
        rw [ENNReal.ofReal_mul (WcsE_bounds hδ ha hB (hΔ 0) (hv 0) _ _ _ _ _).1.le]
        gcongr
        exact step_le_WcsE hδ ha hB (hΔ 0) (hv 0) _ _ hx hp
    have h1 : ∀ x, Qh (hbox δ a) (muC Δ vc p) (sdC vc p) v x ≤ ENNReal.ofReal 1 := fun x => by
      rw [ENNReal.ofReal_one]; exact Qh_le_one hbox_le_one _ _ v x
    induction ℓ generalizing c x with
    | zero =>
      rw [Usup_zero_succ]
      exact le_ofReal_min (h1 x) (hTq 0 c x hx)
    | succ ℓ ih =>
      have hc2 : c / 2 < 2 ^ ℓ := by rw [pow_succ] at hc; omega
      rw [Usup_succ_succ]
      exact le_ofReal_min (le_ofReal_min (h1 x) (hTq _ c x hx))
        (ih (c / 2) hc2 x (esub_nest hδ ha ℓ z c hx))

/-! ## The maxima -/

theorem Bsup_bounds (hδ : 0 < δ) (ha : 0 ≤ a) (hB : B.Valid) (ℓ : ℕ) {n : ℕ} {Δ vc : Fin n → ℝ}
    (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < vc j) (z₀ : ℕ) (v : Fin n → ℕ) :
    0 < Bsup δ a B ℓ Δ vc z₀ v ∧ Bsup δ a B ℓ Δ vc z₀ v ≤ 1 :=
  ⟨(Usup_bounds hδ ha hB n ℓ Δ vc z₀ v 0 hΔ hv).1.trans_le (Finset.le_sup' _ (mem_range_pow ℓ)),
   Finset.sup'_le _ _ fun c _ => (Usup_bounds hδ ha hB n ℓ Δ vc z₀ v c hΔ hv).2⟩

theorem Bsup_succ_le (ℓ : ℕ) {n : ℕ} (Δ vc : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ) :
    Bsup δ a B (ℓ + 1) Δ vc z₀ v ≤ Bsup δ a B ℓ Δ vc z₀ v := by
  unfold Bsup
  refine Finset.sup'_le _ _ fun c hc => (Usup_parent ℓ Δ vc z₀ v c).trans ?_
  refine Finset.le_sup' (Usup δ a B ℓ n Δ vc z₀ v) (Finset.mem_range.2 ?_)
  have := Finset.mem_range.1 hc
  rw [pow_succ] at this; omega

theorem Bsup_mono (hδ : 0 < δ) (ha : 0 ≤ a) (hB : B.Valid) {B' : Box} (hB' : B'.Valid)
    (hsub : B'.Sub B) (ℓ : ℕ) {n : ℕ} {Δ vc : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < vc j)
    (z₀ : ℕ) (v : Fin n → ℕ) : Bsup δ a B' ℓ Δ vc z₀ v ≤ Bsup δ a B ℓ Δ vc z₀ v :=
  Finset.sup'_le _ _ fun c hc => (Usup_mono hδ ha hB hB' hsub n ℓ Δ vc z₀ v c hΔ hv).trans
    (Finset.le_sup' (Usup δ a B ℓ n Δ vc z₀ v) hc)

theorem Qh_le_Bsup (hδ : 0 < δ) (ha : 0 ≤ a) (hB : B.Valid) (ℓ : ℕ) {n : ℕ} {Δ vc : Fin n → ℝ}
    (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < vc j) {z₀ : ℕ} (v : Fin n → ℕ) {p : ℝ × ℝ} (hp : B.Mem p)
    {x : ℝ} (hx : x ∈ ecell δ a z₀) :
    Qh (hbox δ a) (muC Δ vc p) (sdC vc p) v x ≤ ENNReal.ofReal (Bsup δ a B ℓ Δ vc z₀ v) := by
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (esub_cover hδ ha ℓ z₀ hx)
  exact (Qh_le_Usup hδ ha hB n ℓ Δ vc z₀ v c hΔ hv (Finset.mem_range.1 hc) p hp x hxc).trans
    (ENNReal.ofReal_le_ofReal (Finset.le_sup' (Usup δ a B ℓ n Δ vc z₀ v) hc))

variable {n : ℕ} {Δ : Fin n → ℝ} {𝒱 : Finset (Fin n → ℝ)} {ℬ : Box}

/-- A supremum over the dyadic cover is the supremum over its indices. -/
theorem iSup_pcover (ℬ : Box) (h : ℕ) (f : Box → ℝ≥0∞) :
    ⨆ B ∈ pcover ℬ h, f B = ⨆ i ∈ Finset.range (2 ^ h), ⨆ k ∈ Finset.range (2 ^ h), f (pbox ℬ h i k) := by
  classical
  refine le_antisymm (iSup₂_le fun B hB => ?_) (iSup₂_le fun i hi => iSup₂_le fun k hk => ?_)
  · unfold pcover at hB
    obtain ⟨⟨i, k⟩, hik, rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨hi, hk⟩ := Finset.mem_product.1 hik
    exact le_iSup₂_of_le i hi (le_iSup₂_of_le k hk le_rfl)
  · refine le_iSup₂_of_le (pbox ℬ h i k) ?_ le_rfl
    unfold pcover
    exact Finset.mem_image.2 ⟨(i, k), Finset.mem_product.2 ⟨hi, hk⟩, rfl⟩

theorem DsupC_bounds (hδ : 0 < δ) (ha : 0 ≤ a) {C : Finset Box} (hC : C.Nonempty)
    (hCv : ∀ B ∈ C, B.Valid) (hΔ : ∀ j, 0 < Δ j) (h𝒱 : 𝒱.Nonempty) (hv : ∀ vc ∈ 𝒱, ∀ j, 0 < vc j)
    (ℓ z₀ : ℕ) (v : Fin n → ℕ) :
    0 < DsupC δ a C ℓ Δ 𝒱 z₀ v ∧ DsupC δ a C ℓ Δ 𝒱 z₀ v ≤ 1 := by
  obtain ⟨vc, hvc⟩ := h𝒱
  obtain ⟨B, hB⟩ := hC
  refine ⟨lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Bsup_bounds hδ ha (hCv B hB) ℓ hΔ (hv vc hvc) z₀ v).1)
    (le_iSup₂_of_le B hB (le_iSup₂_of_le vc hvc le_rfl)), iSup₂_le fun B hB => iSup₂_le fun vc hvc =>
    ENNReal.ofReal_le_one.2 (Bsup_bounds hδ ha (hCv B hB) ℓ hΔ (hv vc hvc) z₀ v).2⟩

theorem DsupC_ℓ_succ (C : Finset Box) (ℓ z₀ : ℕ) (v : Fin n → ℕ) :
    DsupC δ a C (ℓ + 1) Δ 𝒱 z₀ v ≤ DsupC δ a C ℓ Δ 𝒱 z₀ v :=
  iSup₂_mono fun _ _ => iSup₂_mono fun vc _ => ENNReal.ofReal_le_ofReal (Bsup_succ_le ℓ Δ vc z₀ v)

theorem DsupC_refine (hδ : 0 < δ) (ha : 0 ≤ a) {C C' : Finset Box} (hCv : ∀ B ∈ C, B.Valid)
    (hC' : Refines C' C) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ vc ∈ 𝒱, ∀ j, 0 < vc j) (ℓ z₀ : ℕ)
    (v : Fin n → ℕ) : DsupC δ a C' ℓ Δ 𝒱 z₀ v ≤ DsupC δ a C ℓ Δ 𝒱 z₀ v := by
  refine iSup₂_le fun B' hB' => iSup₂_le fun vc hvc => ?_
  obtain ⟨hv', B, hB, hsub⟩ := hC' B' hB'
  exact le_iSup₂_of_le B hB (le_iSup₂_of_le vc hvc (ENNReal.ofReal_le_ofReal
    (Bsup_mono hδ ha (hCv B hB) hv' hsub ℓ hΔ (hv vc hvc) z₀ v)))

theorem pcover_covers (hℬ : ℬ.Valid) (h : ℕ) : Covers ℬ (pcover ℬ h) := by
  classical
  refine ⟨fun B hB => ?_, fun p hp => ?_⟩
  · unfold pcover at hB
    obtain ⟨⟨i, k⟩, -, rfl⟩ := Finset.mem_image.1 hB
    exact pbox_valid hℬ h i k
  · obtain ⟨i, hi, k, hk, hpb⟩ := pbox_cover h hp
    exact ⟨pbox ℬ h i k, Finset.mem_image.2 ⟨(i, k), Finset.mem_product.2
      ⟨Finset.mem_range.2 hi, Finset.mem_range.2 hk⟩, rfl⟩, hpb⟩

theorem pcover_refines (hℬ : ℬ.Valid) (h : ℕ) : Refines (pcover ℬ (h + 1)) (pcover ℬ h) := by
  classical
  intro B' hB'
  unfold pcover at hB'
  obtain ⟨⟨i, k⟩, hik, rfl⟩ := Finset.mem_image.1 hB'
  obtain ⟨hi, hk⟩ := Finset.mem_product.1 hik
  have hi' : i / 2 < 2 ^ h := by have := Finset.mem_range.1 hi; rw [pow_succ] at this; omega
  have hk' : k / 2 < 2 ^ h := by have := Finset.mem_range.1 hk; rw [pow_succ] at this; omega
  exact ⟨pbox_valid hℬ _ _ _, pbox ℬ h (i / 2) (k / 2), Finset.mem_image.2 ⟨(i / 2, k / 2),
    Finset.mem_product.2 ⟨Finset.mem_range.2 hi', Finset.mem_range.2 hk'⟩, rfl⟩, pbox_nest hℬ h i k⟩

/-! ## Zero radius: claim 034's ordinary-cell recursion -/

theorem WcsE_zero_noise : WcsE δ 0 = Wcs δ := by
  funext B Δ v ℓ z c z' d
  unfold WcsE Wcs; rw [eslo_zero_noise]

theorem Usup_zero_noise :
    ∀ (n ℓ : ℕ) (Δ vc : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (c : ℕ),
      Usup δ 0 B ℓ n Δ vc z v c = Uc δ B ℓ n Δ vc z v c
  | 0, ℓ, Δ, vc, z, v, c => by rw [Usup_nil, Uc_nil]
  | n + 1, ℓ, Δ, vc, z, v, c => by
    induction ℓ generalizing c with
    | zero =>
      rw [Usup_zero_succ, Uc_zero_succ]
      simp only [WcsE_zero_noise, Usup_zero_noise n]
    | succ ℓ ih =>
      rw [Usup_succ_succ, Uc_succ_succ, ih]
      simp only [WcsE_zero_noise, Usup_zero_noise n]

theorem Bsup_zero_noise (ℓ : ℕ) (Δ vc : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ) :
    Bsup δ 0 B ℓ Δ vc z₀ v = Bc δ B ℓ Δ vc z₀ v := by
  unfold Bsup Bc
  congr 1; funext c; exact Usup_zero_noise n ℓ Δ vc z₀ v c

theorem DsupC_zero_noise (h ℓ z₀ : ℕ) (v : Fin n → ℕ) :
    DsupC δ 0 (pcover ℬ h) ℓ Δ 𝒱 z₀ v = Dclock δ ℬ h ℓ Δ 𝒱 z₀ v := by
  unfold DsupC Dclock
  rw [iSup_pcover]
  simp only [Bsup_zero_noise]

end Novel.D18ClockNoise
