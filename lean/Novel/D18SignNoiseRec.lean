import Novel.D18SignNoiseSign

/-!
# Claim 065: the recursion (4), deterministically

* The recursion is stated for any per-step bound `W` in `(0, 1]` (`WOk`); claim 065 uses claim 031's
  `Wm` (`Wm_ok`).
* `UsW_bounds`: from a feasible source, every `U` lies in `(0, 1]`. Each factor `W Ā` is positive,
  and the negative sign is always a feasible target.
* `UsW_parent`, `Dstate_succ_le`: refinement weakly lowers the bound.
* `UsW_ge_Ub`: at zero radius, every sign's `U` is at least claim 031's. Both sign intervals are
  claim 031's cells, and the rows of `Ā` sum to at least one.
* `UsW_allzero_le`: at `a = δ`, `β = 0` on the all-zero path, `U ≤ ((1 + ρ)/2)^n` at every level.
  Only the negative sign is feasible, `W ≤ 1` and `Ā = (1 + ρ)/2`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18SignNoise

open Standalone.D18SignNoise Standalone.D18BoundedNoise Standalone.D14FixedTick Standalone.D14Cell
  Novel.D14FixedTick

variable {δ a ρ β : ℝ} {W : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ}

/-- `W` is a per-step bound in `(0, 1]` between nonempty intervals of `[0, ∞)`, at step data
`(p, q)`. -/
def WOk (W : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (p q : ℝ) : Prop :=
  ∀ a b c d, 0 ≤ a → a < b → 0 ≤ c → c < d → 0 < W a b c d p q ∧ W a b c d p q ≤ 1

/-- `W` at step data `(p, q)` bounds the Gaussian step with mean `μ` and standard deviation `s`
from every source in `[a, b)` to `[c, d)`. -/
def WDom (W : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (μ s p q : ℝ) : Prop :=
  ∀ a b c d, 0 ≤ a → a < b → 0 ≤ c → c < d → ∀ x ∈ Ico a b,
    stepP μ s x (Ico c d) ≤ ENNReal.ofReal (W a b c d p q)

theorem Wm_ok {s : ℝ} (hs : 0 < s) (μ : ℝ) : WOk Wm μ s := fun _ _ _ _ ha hab hc hcd =>
  let h := interval_holds (μ := μ) ha hab hc hcd hs
  ⟨h.2.2.1, h.2.2.2⟩

theorem Wm_dom {s : ℝ} (hs : 0 < s) (μ : ℝ) : WDom Wm μ s μ s := fun _ _ _ _ ha hab hc hcd =>
  (interval_holds (μ := μ) ha hab hc hcd hs).1

theorem UsW_nil (ℓ : ℕ) (p q : Fin 0 → ℝ) (z : ℕ) (v : Fin 0 → ℕ) (h : Bool) (d : ℕ) :
    UsW δ a ρ β W ℓ 0 p q z v h d = 1 := by
  cases ℓ <;> simp [UsW]

theorem UsW_zero_succ {n : ℕ} (p q : Fin (n + 1) → ℝ) (z : ℕ) (v : Fin (n + 1) → ℕ) (h : Bool)
    (d : ℕ) : UsW δ a ρ β W 0 (n + 1) p q z v h d =
      min 1 (∑ t ∈ feasT δ a (v 0), ∑ e ∈ Finset.range (2 ^ 0),
        FsW δ a ρ β W (p 0) (q 0) 0 z h d (v 0) t e *
          UsW δ a ρ β W 0 n (Fin.tail p) (Fin.tail q) (v 0) (Fin.tail v) t e) := by
  rw [UsW]

theorem UsW_succ_succ (ℓ : ℕ) {n : ℕ} (p q : Fin (n + 1) → ℝ) (z : ℕ) (v : Fin (n + 1) → ℕ)
    (h : Bool) (d : ℕ) : UsW δ a ρ β W (ℓ + 1) (n + 1) p q z v h d =
      min (min 1 (∑ t ∈ feasT δ a (v 0), ∑ e ∈ Finset.range (2 ^ (ℓ + 1)),
        FsW δ a ρ β W (p 0) (q 0) (ℓ + 1) z h d (v 0) t e *
          UsW δ a ρ β W (ℓ + 1) n (Fin.tail p) (Fin.tail q) (v 0) (Fin.tail v) t e))
        (UsW δ a ρ β W ℓ (n + 1) p q z v h (d / 2)) := by
  rw [UsW]

theorem UsW_parent (ℓ : ℕ) {n : ℕ} (p q : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (h : Bool) (d : ℕ) :
    UsW δ a ρ β W (ℓ + 1) n p q z v h d ≤ UsW δ a ρ β W ℓ n p q z v h (d / 2) := by
  cases n with
  | zero => rw [UsW_nil, UsW_nil]
  | succ n => rw [UsW_succ_succ]; exact min_le_right _ _

theorem UsW_le_one : ∀ (ℓ n : ℕ) (p q : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (h : Bool) (d : ℕ),
    UsW δ a ρ β W ℓ n p q z v h d ≤ 1
  | ℓ, 0, p, q, z, v, h, d => by rw [UsW_nil]
  | 0, n + 1, p, q, z, v, h, d => by rw [UsW_zero_succ]; exact min_le_left _ _
  | ℓ + 1, n + 1, p, q, z, v, h, d => by
    rw [UsW_succ_succ]; exact (min_le_left _ _).trans (min_le_left _ _)

/-- The factor `W Ā` between feasible subcells is in `(0, 1]`. -/
theorem FsW_bounds (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {p q : ℝ} (hW : WOk W p q) {ℓ z : ℕ} {h : Bool}
    (hf : Feas δ a z h) (d z' : ℕ) {t : Bool} (hf' : Feas δ a z' t) (e : ℕ) :
    0 < FsW δ a ρ β W p q ℓ z h d z' t e ∧ FsW δ a ρ β W p q ℓ z h d z' t e ≤ 1 := by
  have hW' := hW _ _ _ _ (islo_nonneg hf ℓ d) (islo_lt hf ℓ (Nat.lt_succ_self d))
    (islo_nonneg hf' ℓ e) (islo_lt hf' ℓ (Nat.lt_succ_self e))
  have hA := Abar_pos (β := β) hρ0 hρ1 h t (b := islo δ a ℓ z h (d + 1))
    (d := islo δ a ℓ z' t (e + 1)) (islo_nonneg hf ℓ d) (islo_nonneg hf' ℓ e)
  have hA1 := Abar_le_one (β := β) hρ0 hρ1 h t (islo δ a ℓ z h d) (islo δ a ℓ z h (d + 1))
    (islo δ a ℓ z' t e) (islo δ a ℓ z' t (e + 1))
  unfold FsW
  exact ⟨mul_pos hW'.1 hA, by nlinarith [hW'.1]⟩

/-- From a feasible source, every `U` is positive. -/
theorem UsW_pos (hδ : 0 < δ) (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∀ (n ℓ : ℕ) (p q : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (h : Bool) (d : ℕ),
      (∀ j, WOk W (p j) (q j)) → Feas δ a z h → 0 < UsW δ a ρ β W ℓ n p q z v h d
  | 0, ℓ, p, q, z, v, h, d, _, _ => by rw [UsW_nil]; exact one_pos
  | n + 1, ℓ, p, q, z, v, h, d, hW, hf => by
    have IH := UsW_pos hδ ha hρ0 hρ1 n
    have hT : ∀ ℓ' d', 0 < ∑ t ∈ feasT δ a (v 0), ∑ e ∈ Finset.range (2 ^ ℓ'),
        FsW δ a ρ β W (p 0) (q 0) ℓ' z h d' (v 0) t e *
          UsW δ a ρ β W ℓ' n (Fin.tail p) (Fin.tail q) (v 0) (Fin.tail v) t e := fun ℓ' d' => by
      have hterm : ∀ t ∈ feasT δ a (v 0), ∀ e, 0 ≤ FsW δ a ρ β W (p 0) (q 0) ℓ' z h d' (v 0) t e *
          UsW δ a ρ β W ℓ' n (Fin.tail p) (Fin.tail q) (v 0) (Fin.tail v) t e := fun t ht e =>
        mul_nonneg (FsW_bounds hρ0 hρ1 (hW 0) hf d' (v 0) (mem_feasT.1 ht) e).1.le
          (IH ℓ' _ _ _ _ t e (fun j => hW _) (mem_feasT.1 ht)).le
      refine Finset.sum_pos' (fun t ht => Finset.sum_nonneg fun e _ => hterm t ht e)
        ⟨false, false_mem_feasT hδ ha _, Finset.sum_pos' (fun e _ => hterm _
          (false_mem_feasT hδ ha _) e) ⟨0, Finset.mem_range.2 (pow_pos two_pos _), mul_pos
            (FsW_bounds hρ0 hρ1 (hW 0) hf d' (v 0) (feas_false hδ ha _) 0).1
            (IH ℓ' _ _ _ _ false 0 (fun j => hW _) (feas_false hδ ha _))⟩⟩
    induction ℓ generalizing d with
    | zero => rw [UsW_zero_succ]; exact lt_min one_pos (hT 0 d)
    | succ ℓ ih => rw [UsW_succ_succ]; exact lt_min (lt_min one_pos (hT _ d)) (ih (d / 2))

theorem UsW_bounds (hδ : 0 < δ) (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n ℓ : ℕ}
    {p q : Fin n → ℝ} (hW : ∀ j, WOk W (p j) (q j)) {z : ℕ} (v : Fin n → ℕ) {h : Bool}
    (hf : Feas δ a z h) (d : ℕ) :
    0 < UsW δ a ρ β W ℓ n p q z v h d ∧ UsW δ a ρ β W ℓ n p q z v h d ≤ 1 :=
  ⟨UsW_pos hδ ha hρ0 hρ1 n ℓ p q z v h d hW hf, UsW_le_one ℓ n p q z v h d⟩

/-! ## The maxima -/

theorem Dstate_bounds (hδ : 0 < δ) (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ}
    {Δ : Fin n → ℝ} {Γ : Finset (ℝ × ℝ)} (hΔ : ∀ j, 0 < Δ j) (hΓ : Γ.Nonempty)
    (hΓκ : ∀ θ ∈ Γ, 0 < θ.2) (ℓ z₀ : ℕ) (v : Fin n → ℕ) :
    0 < Dstate δ a ρ β ℓ Δ Γ z₀ v ∧ Dstate δ a ρ β ℓ Δ Γ z₀ v ≤ 1 := by
  obtain ⟨θ, hθ⟩ := hΓ
  refine ⟨(ENNReal.ofReal_pos.2 (UsW_pos (W := Wm) hδ ha hρ0 hρ1 n ℓ (muθ Δ θ) (sθ Δ θ) z₀ v false 0
    (fun j => Wm_ok (Novel.D14Cell.sθ_pos hΔ (hΓκ θ hθ) j) _) (feas_false hδ ha z₀))).trans_le
    (le_iSup₂_of_le θ hθ (le_iSup₂_of_le false (false_mem_feasT hδ ha z₀)
      (le_iSup₂_of_le 0 (Finset.mem_range.2 (pow_pos two_pos ℓ)) le_rfl))), ?_⟩
  exact iSup₂_le fun θ _ => iSup₂_le fun h _ => iSup₂_le fun d _ =>
    ENNReal.ofReal_le_one.2 (UsW_le_one ℓ n _ _ z₀ v h d)

theorem Dstate_succ_le (ℓ : ℕ) {n : ℕ} (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (z₀ : ℕ)
    (v : Fin n → ℕ) : Dstate δ a ρ β (ℓ + 1) Δ Γ z₀ v ≤ Dstate δ a ρ β ℓ Δ Γ z₀ v := by
  refine iSup₂_le fun θ hθ => iSup₂_le fun h hh => iSup₂_le fun d hd => ?_
  have hd2 : d / 2 < 2 ^ ℓ := by have := Finset.mem_range.1 hd; rw [pow_succ] at this; omega
  exact (ENNReal.ofReal_le_ofReal (UsW_parent ℓ _ _ z₀ v h d)).trans
    (le_iSup₂_of_le θ hθ (le_iSup₂_of_le h hh (le_iSup₂_of_le (d / 2) (Finset.mem_range.2 hd2)
      le_rfl)))

/-! ## Zero radius -/

theorem Fs_zero_radius (hδ : 0 < δ) (μ s : ℝ) (ℓ z : ℕ) (h : Bool) (d z' : ℕ) (t : Bool) (e : ℕ) :
    FsW δ 0 ρ β Wm μ s ℓ z h d z' t e = Wsub δ μ s ℓ z d z' e *
      Abar ρ β h t (slo δ ℓ z d) (slo δ ℓ z (d + 1)) (slo δ ℓ z' e) (slo δ ℓ z' (e + 1)) := by
  unfold FsW Wsub; simp only [islo_zero_radius hδ]

theorem feasT_zero_radius (hδ : 0 < δ) (z : ℕ) : feasT δ 0 z = Finset.univ :=
  Finset.eq_univ_of_forall fun t => mem_feasT.2 (feas_zero_radius hδ z t)

/-- At zero radius, each sign's `U` is at least claim 031's. -/
theorem UsW_ge_Ub (hδ : 0 < δ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∀ (n ℓ : ℕ) (μ s : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (h : Bool) (d : ℕ), (∀ j, 0 < s j) →
      d < 2 ^ ℓ → Ub δ ℓ n μ s z v d ≤ UsW δ 0 ρ β Wm ℓ n μ s z v h d
  | 0, ℓ, μ, s, z, v, h, d, _, _ => by rw [UsW_nil, Ub_nil]
  | n + 1, ℓ, μ, s, z, v, h, d, hs, hd => by
    have IH := UsW_ge_Ub hδ hρ0 hρ1 n
    have hT : ∀ ℓ' d', ∑ e ∈ Finset.range (2 ^ ℓ'), Wsub δ (μ 0) (s 0) ℓ' z d' (v 0) e *
        Ub δ ℓ' n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) e ≤
        ∑ t ∈ feasT δ 0 (v 0), ∑ e ∈ Finset.range (2 ^ ℓ'),
          FsW δ 0 ρ β Wm (μ 0) (s 0) ℓ' z h d' (v 0) t e *
            UsW δ 0 ρ β Wm ℓ' n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) t e := fun ℓ' d' => by
      rw [feasT_zero_radius hδ, Finset.sum_comm]
      refine Finset.sum_le_sum fun e he => ?_
      have he' := Finset.mem_range.1 he
      rw [Fintype.sum_bool, Fs_zero_radius hδ, Fs_zero_radius hδ]
      have hW := (Wsub_bounds hδ (μ := μ 0) (hs 0) ℓ' z d' (v 0) e).1.le
      have hUb := (bounds_aux hδ n ℓ' (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) e (fun j => hs _) he').1.le
      have h1 := IH ℓ' (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) true e (fun j => hs _) he'
      have h2 := IH ℓ' (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) false e (fun j => hs _) he'
      have hA := Abar_sum (β := β) hρ1 h (slo δ ℓ' z d') (slo δ ℓ' z (d' + 1)) (slo δ ℓ' (v 0) e)
        (slo δ ℓ' (v 0) (e + 1))
      have hA1 := (Abar_pos (β := β) hρ0 hρ1 h true (b := slo δ ℓ' z (d' + 1))
        (d := slo δ ℓ' (v 0) (e + 1)) (slo_nonneg hδ ℓ' z d') (slo_nonneg hδ ℓ' (v 0) e)).le
      have hA2 := (Abar_pos (β := β) hρ0 hρ1 h false (b := slo δ ℓ' z (d' + 1))
        (d := slo δ ℓ' (v 0) (e + 1)) (slo_nonneg hδ ℓ' z d') (slo_nonneg hδ ℓ' (v 0) e)).le
      have k1 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hW hA1)
      have k2 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hW hA2)
      nlinarith [mul_nonneg hW hUb]
    induction ℓ generalizing d with
    | zero =>
      rw [UsW_zero_succ, Ub_zero_succ]
      exact min_le_min le_rfl (hT 0 d)
    | succ ℓ ih =>
      have hd2 : d / 2 < 2 ^ ℓ := by rw [pow_succ] at hd; omega
      rw [UsW_succ_succ, Ub_succ_succ]
      exact min_le_min (min_le_min le_rfl (hT _ d)) (ih (d / 2) hd2)

/-! ## The all-zero path at `a = δ`, `β = 0` -/

theorem feasT_allzero (hδ : 0 < δ) : feasT δ δ 0 = {false} := by
  ext t
  rw [mem_feasT, Finset.mem_singleton]
  cases t
  · simp only [iff_true]; exact feas_false hδ hδ.le 0
  · simp only [Bool.true_eq_false, iff_false]
    unfold Feas ilo ihi sg mhi
    simp only [↓reduceIte, CharP.cast_eq_zero, zero_add, one_mul]
    linarith

/-- On the all-zero path at `a = δ`, `β = 0`, `U ≤ ((1 + ρ)/2)^n` at every level. -/
theorem UsW_allzero_le (hδ : 0 < δ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∀ (n ℓ : ℕ) (μ s : Fin n → ℝ) (d : ℕ), (∀ j, 0 < s j) →
      UsW δ δ ρ 0 Wm ℓ n μ s 0 (fun _ => 0) false d ≤ ((1 + ρ) / 2) ^ n
  | 0, ℓ, μ, s, d, _ => by rw [UsW_nil, pow_zero]
  | n + 1, ℓ, μ, s, d, hs => by
    have IH := UsW_allzero_le hδ hρ0 hρ1 n
    have hr0 : 0 ≤ (1 + ρ) / 2 := by linarith
    induction ℓ generalizing d with
    | zero =>
      rw [UsW_zero_succ]
      refine (min_le_right _ _).trans ?_
      simp only [feasT_allzero hδ, Finset.sum_singleton, pow_zero, Finset.range_one]
      have hFr : FsW δ δ ρ 0 Wm (μ 0) (s 0) 0 0 false d 0 false 0 ≤ (1 + ρ) / 2 := by
        have hW := interval_holds (μ := μ 0) (islo_nonneg (feas_false hδ hδ.le 0) 0 d)
          (islo_lt (feas_false hδ hδ.le 0) 0 (Nat.lt_succ_self d))
          (islo_nonneg (feas_false hδ hδ.le 0) 0 0)
          (islo_lt (feas_false hδ hδ.le 0) 0 (Nat.lt_succ_self 0)) (hs 0)
        unfold FsW
        simp only [Abar_beta0, ↓reduceIte]
        exact mul_le_of_le_one_left hr0 hW.2.2.2
      have hU := IH 0 (Fin.tail μ) (Fin.tail s) 0 (fun j => hs _)
      have hU0 := UsW_pos (β := 0) (W := Wm) hδ hδ.le hρ0 hρ1 n 0 (Fin.tail μ) (Fin.tail s) 0
        (fun _ => 0) false 0 (fun j => Wm_ok (hs _) _) (feas_false hδ hδ.le 0)
      change FsW δ δ ρ 0 Wm (μ 0) (s 0) 0 0 false d 0 false 0 *
        UsW δ δ ρ 0 Wm 0 n (Fin.tail μ) (Fin.tail s) 0 (fun _ => 0) false 0 ≤ _
      rw [pow_succ']
      exact mul_le_mul hFr hU hU0.le hr0
    | succ ℓ ih => exact (UsW_parent ℓ _ _ 0 _ false d).trans (ih (d / 2))

end Novel.D18SignNoise
