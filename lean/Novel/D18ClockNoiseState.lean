import Novel.D18ClockNoiseSupport
import Novel.D18SignNoiseProof

/-!
# Claim 066: the state mode

Claim 065's sign recursion `UsW` with claim 034's transition bound `Wclock B` and step data
`(Δ_j, v_j)`.
* `Wclock_ok`, `Wclock_dom`: claim 034's part 1 gives claim 065's two transition hypotheses — the
  bound is in `(0, 1]` and dominates the Gaussian step with mean `bΔ − wv/2` and standard deviation
  `√(wv)` for every `(b, w)` in the box. So claim 065's suffix bound `Qg_le_UsW` applies.
* `UsW_mono_W`: `U` is monotone in the transition bound; with `Wclock_mono`, a child box gives a
  smaller state bound (parameter refinement).
* `UsW_ge_Uc`: at zero radius each sign's `U` is at least claim 034's (the sign weights sum to at
  least one).
* `UsW_allzero_le'`: at `a = δ`, `β = 0`, the all-zero path's state bound is at most
  `((1 + ρ)/2)^n`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18ClockNoise

open Standalone.D18ClockNoise Standalone.D17ClockCells Standalone.D18SignNoise
  Standalone.D14FixedTick Novel.D17ClockCells Novel.D18SignNoise Novel.D14FixedTick

variable {δ a ρ β : ℝ}

theorem Wclock_ok {B : Box} (hB : B.Valid) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    WOk (Wclock B) p q := fun _ _ _ _ ha hab hc hcd =>
  let h := transition_holds B _ _ _ _ p q hB ha hab hc hcd hp hq
  ⟨h.1, h.2.1⟩

theorem Wclock_dom {B : Box} (hB : B.Valid) {bp : ℝ × ℝ} (hbp : B.Mem bp) {p q : ℝ} (hp : 0 < p)
    (hq : 0 < q) : WDom (Wclock B) (bp.1 * p - bp.2 * q / 2) (Real.sqrt (bp.2 * q)) p q :=
  fun _ _ _ _ ha hab hc hcd x hx =>
    (transition_holds B _ _ _ _ p q hB ha hab hc hcd hp hq).2.2.1 x hx bp hbp

/-- `U` is monotone in the transition bound. -/
theorem UsW_mono_W (hδ : 0 < δ) (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {W W' : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ} :
    ∀ (n ℓ : ℕ) (p q : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (h : Bool) (d : ℕ),
      (∀ j, WOk W' (p j) (q j)) →
      (∀ j a' b c d', 0 ≤ a' → a' < b → 0 ≤ c → c < d' → W' a' b c d' (p j) (q j) ≤ W a' b c d' (p j) (q j)) →
      Feas δ a z h → UsW δ a ρ β W' ℓ n p q z v h d ≤ UsW δ a ρ β W ℓ n p q z v h d
  | 0, ℓ, p, q, z, v, h, d, _, _, _ => by rw [UsW_nil, UsW_nil]
  | n + 1, ℓ, p, q, z, v, h, d, hW', hle, hf => by
    have IH := UsW_mono_W hδ ha hρ0 hρ1 (W := W) (W' := W') n
    have hT : ∀ ℓ' d', ∑ t ∈ feasT δ a (v 0), ∑ e ∈ Finset.range (2 ^ ℓ'),
          FsW δ a ρ β W' (p 0) (q 0) ℓ' z h d' (v 0) t e *
            UsW δ a ρ β W' ℓ' n (Fin.tail p) (Fin.tail q) (v 0) (Fin.tail v) t e ≤
        ∑ t ∈ feasT δ a (v 0), ∑ e ∈ Finset.range (2 ^ ℓ'),
          FsW δ a ρ β W (p 0) (q 0) ℓ' z h d' (v 0) t e *
            UsW δ a ρ β W ℓ' n (Fin.tail p) (Fin.tail q) (v 0) (Fin.tail v) t e := fun ℓ' d' =>
      Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun e _ => by
        have hft := mem_feasT.1 ht
        have hA := (Abar_pos (β := β) hρ0 hρ1 h t (b := islo δ a ℓ' z h (d' + 1))
          (d := islo δ a ℓ' (v 0) t (e + 1)) (islo_nonneg hf ℓ' d') (islo_nonneg hft ℓ' e)).le
        have hWle := hle 0 _ _ _ _ (islo_nonneg hf ℓ' d') (islo_lt hf ℓ' (Nat.lt_succ_self d'))
          (islo_nonneg hft ℓ' e) (islo_lt hft ℓ' (Nat.lt_succ_self e))
        have hF : FsW δ a ρ β W' (p 0) (q 0) ℓ' z h d' (v 0) t e ≤
            FsW δ a ρ β W (p 0) (q 0) ℓ' z h d' (v 0) t e := by
          unfold FsW; exact mul_le_mul_of_nonneg_right hWle hA
        have hF0 := (FsW_bounds (β := β) hρ0 hρ1 (hW' 0) hf d' (v 0) hft e (ℓ := ℓ')).1.le
        have hU0 := (UsW_pos (β := β) hδ ha hρ0 hρ1 n ℓ' (Fin.tail p) (Fin.tail q) (v 0)
          (Fin.tail v) t e (fun j => hW' _) hft).le
        exact mul_le_mul hF (IH ℓ' (Fin.tail p) (Fin.tail q) (v 0) (Fin.tail v) t e (fun j => hW' _)
          (fun j => hle _) hft) hU0
          (hF0.trans hF)
    induction ℓ generalizing d with
    | zero => rw [UsW_zero_succ, UsW_zero_succ]; exact min_le_min le_rfl (hT 0 d)
    | succ ℓ ih =>
      rw [UsW_succ_succ, UsW_succ_succ]
      exact min_le_min (min_le_min le_rfl (hT _ d)) (ih (d / 2))

/-- At zero radius, each sign's state bound is at least claim 034's. -/
theorem UsW_ge_Uc (hδ : 0 < δ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {B : Box} (hB : B.Valid) :
    ∀ (n ℓ : ℕ) (Δ vc : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (h : Bool) (d : ℕ), (∀ j, 0 < Δ j) →
      (∀ j, 0 < vc j) → Uc δ B ℓ n Δ vc z v d ≤ UsW δ 0 ρ β (Wclock B) ℓ n Δ vc z v h d
  | 0, ℓ, Δ, vc, z, v, h, d, _, _ => by rw [UsW_nil, Uc_nil]
  | n + 1, ℓ, Δ, vc, z, v, h, d, hΔ, hv => by
    have IH := UsW_ge_Uc hδ hρ0 hρ1 hB n
    have hT : ∀ ℓ' d', ∑ e ∈ Finset.range (2 ^ ℓ'), Wcs δ B (Δ 0) (vc 0) ℓ' z d' (v 0) e *
        Uc δ B ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) e ≤
        ∑ t ∈ feasT δ 0 (v 0), ∑ e ∈ Finset.range (2 ^ ℓ'),
          FsW δ 0 ρ β (Wclock B) (Δ 0) (vc 0) ℓ' z h d' (v 0) t e *
            UsW δ 0 ρ β (Wclock B) ℓ' n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) t e :=
      fun ℓ' d' => by
      rw [feasT_zero_radius hδ, Finset.sum_comm]
      refine Finset.sum_le_sum fun e _ => ?_
      have hFs : ∀ t, FsW δ 0 ρ β (Wclock B) (Δ 0) (vc 0) ℓ' z h d' (v 0) t e =
          Wcs δ B (Δ 0) (vc 0) ℓ' z d' (v 0) e * Abar ρ β h t (slo δ ℓ' z d') (slo δ ℓ' z (d' + 1))
            (slo δ ℓ' (v 0) e) (slo δ ℓ' (v 0) (e + 1)) := fun t => by
        unfold FsW Wcs; simp only [islo_zero_radius hδ]
      rw [Fintype.sum_bool, hFs, hFs]
      have hW := (Wcs_bounds hδ hB (hΔ 0) (hv 0) ℓ' z d' (v 0) e).1.le
      have hUc := (Uc_bounds hδ hB n ℓ' (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) e
        (fun j => hΔ _) (fun j => hv _)).1.le
      have h1 := IH ℓ' (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) true e (fun j => hΔ _)
        (fun j => hv _)
      have h2 := IH ℓ' (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) false e (fun j => hΔ _)
        (fun j => hv _)
      have hA := Abar_sum (β := β) hρ1 h (slo δ ℓ' z d') (slo δ ℓ' z (d' + 1)) (slo δ ℓ' (v 0) e)
        (slo δ ℓ' (v 0) (e + 1))
      have hA1 := (Abar_pos (β := β) hρ0 hρ1 h true (b := slo δ ℓ' z (d' + 1))
        (d := slo δ ℓ' (v 0) (e + 1)) (slo_nonneg hδ ℓ' z d') (slo_nonneg hδ ℓ' (v 0) e)).le
      have hA2 := (Abar_pos (β := β) hρ0 hρ1 h false (b := slo δ ℓ' z (d' + 1))
        (d := slo δ ℓ' (v 0) (e + 1)) (slo_nonneg hδ ℓ' z d') (slo_nonneg hδ ℓ' (v 0) e)).le
      have k1 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hW hA1)
      have k2 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hW hA2)
      nlinarith [mul_nonneg hW hUc]
    induction ℓ generalizing d with
    | zero =>
      rw [UsW_zero_succ, Uc_zero_succ]
      exact min_le_min le_rfl (hT 0 d)
    | succ ℓ ih =>
      rw [UsW_succ_succ, Uc_succ_succ]
      exact min_le_min (min_le_min le_rfl (hT _ d)) (ih (d / 2))

/-- On the all-zero path at `a = δ`, `β = 0`, the state bound is at most `((1 + ρ)/2)^n`. -/
theorem UsW_allzero_le' (hδ : 0 < δ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {W : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ} :
    ∀ (n ℓ : ℕ) (p q : Fin n → ℝ) (d : ℕ), (∀ j, WOk W (p j) (q j)) →
      UsW δ δ ρ 0 W ℓ n p q 0 (fun _ => 0) false d ≤ ((1 + ρ) / 2) ^ n
  | 0, ℓ, p, q, d, _ => by rw [UsW_nil, pow_zero]
  | n + 1, ℓ, p, q, d, hW => by
    have IH := UsW_allzero_le' hδ hρ0 hρ1 (W := W) n
    have hr0 : 0 ≤ (1 + ρ) / 2 := by linarith
    induction ℓ generalizing d with
    | zero =>
      rw [UsW_zero_succ]
      refine (min_le_right _ _).trans ?_
      simp only [feasT_allzero hδ, Finset.sum_singleton, pow_zero, Finset.range_one]
      have hFr : FsW δ δ ρ 0 W (p 0) (q 0) 0 0 false d 0 false 0 ≤ (1 + ρ) / 2 := by
        have hW1 := hW 0 _ _ _ _ (islo_nonneg (feas_false hδ hδ.le 0) 0 d)
          (islo_lt (feas_false hδ hδ.le 0) 0 (Nat.lt_succ_self d))
          (islo_nonneg (feas_false hδ hδ.le 0) 0 0)
          (islo_lt (feas_false hδ hδ.le 0) 0 (Nat.lt_succ_self 0))
        unfold FsW
        simp only [Abar_beta0, ↓reduceIte]
        exact mul_le_of_le_one_left hr0 hW1.2
      have hU := IH 0 (Fin.tail p) (Fin.tail q) 0 (fun j => hW _)
      have hU0 := UsW_pos (β := 0) (W := W) hδ hδ.le hρ0 hρ1 n 0 (Fin.tail p) (Fin.tail q) 0
        (fun _ => 0) false 0 (fun j => hW _) (feas_false hδ hδ.le 0)
      change FsW δ δ ρ 0 W (p 0) (q 0) 0 0 false d 0 false 0 *
        UsW δ δ ρ 0 W 0 n (Fin.tail p) (Fin.tail q) 0 (fun _ => 0) false 0 ≤ _
      rw [pow_succ']
      exact mul_le_mul hFr hU hU0.le hr0
    | succ ℓ ih => exact (UsW_parent ℓ _ _ 0 _ false d).trans (ih (d / 2))

end Novel.D18ClockNoise
