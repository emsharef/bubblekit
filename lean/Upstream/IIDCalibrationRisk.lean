import Upstream.ExchangeableScoreQuantile
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.GetD

/-!
# AX-66  IID calibration-conditional error bound for an unsmoothed rank cutoff

Ledger entry AX-66 (`ledger/AXIOMS.md`). Source: [vovk2013conditional], Theorem 1(a),
equations (7)–(8), printed p. 354, with the unsmoothed predictor (2)–(4), p. 352, and
(E, δ)-validity, pp. 353–354. Only the sufficient condition of part (a) is imported.

Mathlib has no conformal-prediction result, so the source theorem enters as a model-indexed hypothesis
structure (rule 6). The general calibration theorem is not reconstructed.

## Objects (all concrete)

* **The scores.** A Borel probability `ν` on real scores, and calibration size `n`. The calibration
  law is the product `ν^n` (`calLaw`, Mathlib's `Measure.pi`).
* **The cutoff is AX-65's, reused exactly** (`Upstream.kcal`, `Upstream.qcal`).
  `k_cal = ⌈(n + 1)(1 − α)⌉`. `q_cal` is the `k_cal`-th smallest calibration score with repetitions,
  in `WithTop ℝ`, and `+∞` when `k_cal = n + 1`.
* **The risk.** `R_cal(c) = ν{s : s > q_cal(c)}` (`Rcal`): strict exceedance, so equality with a
  finite cutoff is accepted.
* **The binomial sum.** `r_cal = ⌊α(n + 1) − 1⌋ ∈ {−1, …, n − 1}` (`rcal`).
  `B_cal(n, E, r) = Σ_(j=0)^r C(n, j) E^j (1 − E)^(n−j)` (`Bcal`), which is the empty sum `0` at
  `r = −1`.

## The field

`risk_bound`: take a probability `ν`, `n > 0`, and deterministic `α, E_cal, δ_cal ∈ (0, 1)`. If
`B_cal(n, E_cal, r_cal) ≤ δ_cal`, then `ν^n{c : R_cal(c) > E_cal} ≤ δ_cal`. The binomial sum and the
product law are concrete; the field is not a free predicate standing for the bound.

## Convention checks

* `measurable_Rcal`: `R_cal` is a measurable function of the calibration vector. In the finite
  branch, `q_cal ≤ x` iff at least `k_cal` calibration scores are `≤ x` (`getElem_le_iff_countP`),
  so `q_cal` is measurable. `R_cal = ν(q_cal, ∞)` is antitone in it, and `0` in the infinite branch.
* `rcal_ge`, `rcal_le`: `−1 ≤ r_cal ≤ n − 1`.
* `sub_rcal_eq_kcal`: the indexing identity `n − r_cal = k_cal`. So `r_cal = −1` is exactly the
  infinite-cutoff branch.
* `Bcal_neg_one`: the empty sum at `r_cal = −1`. `Bcal_full`: `B_cal(n, E, n) = 1`, a binomial CDF.
  `Bcal_pos`: `B_cal(n, E, r) > 0` for `r ≥ 0`, so the premise is a real constraint.
* `Rcal_top`: in the infinite branch `R_cal = 0`, so the bad-risk event is empty.

## Instance: genuine (the ledger's `ν = Dirac(0)`)

`diracInstance n`, for every `n`: with `ν = δ₀`, `ν^n = δ₀` on `ℝ^n` (`calLaw_dirac`).
* **The cutoff at the zero vector.** It is `0` in the finite branch and `+∞` in the infinite branch
  (`dirac_qcal_finite`, `dirac_qcal_top`). Either way the strict-exceedance risk is `0`, and the
  bad-risk event has probability `0`.
* **Premises.** `dirac_premises` checks them: the binomial premise holds at `α < 1/(n + 1)`, where
  `B_cal = 0`.

This model validates no financial window law and supplies no iid sampling for any application.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Upstream

/-! ## Objects -/

/-- The calibration law `ν^n`. -/
noncomputable def calLaw (ν : Measure ℝ) (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => ν

/-- `R_cal(c) = ν{s : s > q_cal(c)}`. -/
noncomputable def Rcal (ν : Measure ℝ) (n : ℕ) (α : ℝ) (c : Fin n → ℝ) : ℝ≥0∞ :=
  ν {s | qcal n α c < (s : WithTop ℝ)}

/-- `r_cal = ⌊α(n + 1) − 1⌋`. -/
noncomputable def rcal (n : ℕ) (α : ℝ) : ℤ := ⌊α * ((n : ℝ) + 1) - 1⌋

/-- `B_cal(n, E, r) = Σ_(j=0)^r C(n, j) E^j (1 − E)^(n−j)`; empty for `r < 0`. -/
noncomputable def Bcal (n : ℕ) (E : ℝ) (r : ℤ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1).toNat, (n.choose j : ℝ) * E ^ j * (1 - E) ^ (n - j)

/-- AX-66 for one model `(ν, n)`. -/
structure IIDCalibrationRisk (ν : Measure ℝ) (n : ℕ) : Prop where
  /-- Theorem 1(a), with a singleton label and conformity score minus the real score. -/
  risk_bound : IsProbabilityMeasure ν → 0 < n →
    ∀ α E δ : ℝ, 0 < α → α < 1 → 0 < E → E < 1 → 0 < δ → δ < 1 →
      Bcal n E (rcal n α) ≤ δ →
        calLaw ν n {c | ENNReal.ofReal E < Rcal ν n α c} ≤ ENNReal.ofReal δ

/-! ## Order statistics and measurability -/

/-- In a sorted list, the `k`-th smallest entry is `≤ x` iff at least `k` entries are `≤ x`. -/
theorem getElem_le_iff_countP {l : List ℝ} (hl : l.Pairwise (· ≤ ·)) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ l.length) (x : ℝ) :
    l[k - 1]'(by omega) ≤ x ↔ k ≤ l.countP (fun y => decide (y ≤ x)) := by
  rw [List.pairwise_iff_getElem] at hl
  have hsplit := fun m => (List.countP_append (p := fun y => decide (y ≤ x))
    (l₁ := l.take m) (l₂ := l.drop m))
  constructor
  · intro h
    have hle : ∀ y ∈ l.take k, decide (y ≤ x) = true := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
      rw [List.getElem_take]
      have hj' : j < k := by simp at hj; omega
      simp only [decide_eq_true_eq]
      rcases Nat.lt_or_ge j (k - 1) with h' | h'
      · exact (hl j (k - 1) _ _ h').trans h
      · have : j = k - 1 := by omega
        subst this
        exact h
    have h1 := List.countP_eq_length.mpr hle
    have h2 : (l.take k).length = k := by simp; omega
    have := hsplit k
    rw [List.take_append_drop] at this
    omega
  · intro h
    by_contra hlt
    push Not at hlt
    have h0 : (l.drop (k - 1)).countP (fun y => decide (y ≤ x)) = 0 := by
      refine List.countP_eq_zero.mpr fun y hy => ?_
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
      rw [List.getElem_drop]
      simp only [decide_eq_true_eq, not_le]
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0
        simpa using hlt
      · exact hlt.trans_le (hl (k - 1) (k - 1 + i) _ _ (by omega))
    have h1 : (l.take (k - 1)).countP (fun y => decide (y ≤ x)) ≤ k - 1 :=
      List.countP_le_length.trans (by simp)
    have := hsplit (k - 1)
    rw [List.take_append_drop] at this
    omega

theorem sortedCal_pairwise {n : ℕ} (s : Fin n → ℝ) : (sortedCal s).Pairwise (· ≤ ·) := by
  simpa [sortedCal] using List.pairwise_mergeSort' (· ≤ ·) (List.ofFn s)

theorem countP_ofFn {n : ℕ} (p : ℝ → Bool) (c : Fin n → ℝ) :
    (List.ofFn c).countP p = ∑ i, if p (c i) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.countP_cons, ih, Fin.sum_univ_succ]
    ring

/-- The `k`-th smallest calibration score, as a real (`0` default out of range). -/
noncomputable def ostat {n : ℕ} (k : ℕ) (c : Fin n → ℝ) : ℝ := (sortedCal c).getD (k - 1) 0

theorem measurable_ostat {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) :
    Measurable (ostat (n := n) k) := by
  refine measurable_of_Iic fun x => ?_
  have hset : ostat (n := n) k ⁻¹' Iic x =
      (fun c : Fin n → ℝ => ∑ i, if decide (c i ≤ x) then 1 else 0) ⁻¹' Ici k := by
    ext c
    have hlen : k ≤ (sortedCal c).length := by rw [length_sortedCal]; exact hk
    simp only [mem_preimage, mem_Iic, mem_Ici, ostat]
    rw [List.getD_eq_getElem _ _ (show k - 1 < (sortedCal c).length by omega),
      getElem_le_iff_countP (sortedCal_pairwise c) hk1 hlen,
      show (sortedCal c).countP (fun y => decide (y ≤ x)) = (List.ofFn c).countP _ from
        (List.mergeSort_perm _ _).countP_eq _, countP_ofFn]
  rw [hset]
  refine (Finset.measurable_sum _ fun i _ => ?_) measurableSet_Ici
  simp only [decide_eq_true_eq]
  exact Measurable.ite (measurableSet_le (measurable_pi_apply i) measurable_const) measurable_const
    measurable_const

theorem measurable_Rcal (ν : Measure ℝ) (n : ℕ) {α : ℝ} (hα1 : α < 1) :
    Measurable (Rcal ν n α) := by
  by_cases h : kcal n α ≤ n
  · have hk1 := one_le_kcal (n := n) hα1
    have hR : Rcal ν n α = (fun q => ν (Ioi q)) ∘ ostat (kcal n α) := by
      funext c
      obtain ⟨hi, hq⟩ := qcal_eq_coe hα1 h c
      simp only [Rcal, Function.comp, ostat, hq, WithTop.coe_lt_coe]
      rw [List.getD_eq_getElem _ _ hi]
      rfl
    rw [hR]
    exact (Antitone.measurable fun q q' hqq' => measure_mono (Ioi_subset_Ioi hqq')).comp
      (measurable_ostat hk1 h)
  · have : Rcal ν n α = fun _ => 0 := by
      funext c
      simp [Rcal, qcal_top h]
    rw [this]
    exact measurable_const

/-! ## Convention checks -/

theorem rcal_ge {n : ℕ} {α : ℝ} (hα : 0 < α) : -1 ≤ rcal n α := by
  unfold rcal
  rw [Int.le_floor]
  push_cast
  have : 0 < α * ((n : ℝ) + 1) := by positivity
  linarith

theorem rcal_le {n : ℕ} {α : ℝ} (hα1 : α < 1) : rcal n α ≤ n - 1 := by
  unfold rcal
  rw [Int.floor_le_iff]
  push_cast
  have : α * ((n : ℝ) + 1) < (n : ℝ) + 1 := by nlinarith
  linarith

/-- The indexing identity `n − r_cal = k_cal`. -/
theorem sub_rcal_eq_kcal {n : ℕ} {α : ℝ} (hα1 : α < 1) : (n : ℤ) - rcal n α = kcal n α := by
  have hpos : 0 ≤ ((n : ℝ) + 1) * (1 - α) := mul_nonneg (by positivity) (by linarith)
  unfold rcal kcal
  rw [Int.natCast_ceil_eq_ceil hpos, show ((n : ℝ) + 1) * (1 - α) =
    ((n + 1 : ℤ) : ℝ) + -(α * ((n : ℝ) + 1)) by push_cast; ring, Int.ceil_intCast_add,
    Int.ceil_neg, show α * ((n : ℝ) + 1) - 1 = α * ((n : ℝ) + 1) + ((-1 : ℤ) : ℝ) by
      push_cast; ring, Int.floor_add_intCast]
  ring

theorem Bcal_neg_one (n : ℕ) (E : ℝ) : Bcal n E (-1) = 0 := by
  simp [Bcal]

/-- `B_cal(n, E, n) = 1`: the full binomial sum. -/
theorem Bcal_full (n : ℕ) (E : ℝ) : Bcal n E n = 1 := by
  have h := add_pow E (1 - E) n
  rw [Bcal, show ((n : ℤ) + 1).toNat = n + 1 by omega]
  calc _ = ∑ m ∈ Finset.range (n + 1), E ^ m * (1 - E) ^ (n - m) * (n.choose m : ℝ) :=
        Finset.sum_congr rfl fun j _ => by ring
    _ = (E + (1 - E)) ^ n := h.symm
    _ = 1 := by ring

theorem Bcal_pos (n : ℕ) {E : ℝ} (hE0 : 0 ≤ E) (hE1 : E < 1) {r : ℤ} (hr : 0 ≤ r) :
    0 < Bcal n E r := by
  rw [Bcal]
  have hE : 0 < 1 - E := by linarith
  calc (0 : ℝ) < (n.choose 0 : ℝ) * E ^ 0 * (1 - E) ^ (n - 0) := by simp; positivity
    _ ≤ _ := by
      refine Finset.single_le_sum (f := fun j => (n.choose j : ℝ) * E ^ j * (1 - E) ^ (n - j))
        (fun j _ => ?_) (Finset.mem_range.mpr (by omega))
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hE0 _)) (pow_nonneg hE.le _)

/-- In the infinite branch the risk vanishes, so the bad-risk event is empty. -/
theorem Rcal_top (ν : Measure ℝ) {n : ℕ} {α : ℝ} (h : ¬ kcal n α ≤ n) (c : Fin n → ℝ) :
    Rcal ν n α c = 0 := by
  simp [Rcal, qcal_top h]

/-! ## The Dirac witness -/

/-- The product of point masses at `0` is the point mass at the zero vector. -/
theorem calLaw_dirac (n : ℕ) : calLaw (Measure.dirac 0) n = Measure.dirac 0 := by
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.dirac_apply]
  simp only [indicator, mem_univ_pi, Pi.one_apply, Measure.dirac_apply, Pi.zero_apply]
  classical
  by_cases h : ∀ i, (0 : ℝ) ∈ s i
  · have h0 : (0 : Fin n → ℝ) ∈ univ.pi s := fun i _ => h i
    simp [h0, h]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have h0 : (0 : Fin n → ℝ) ∉ univ.pi s := fun h' => hi (h' i (mem_univ i))
    simp only [h0, ite_false]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

/-- At the zero vector every finite cutoff is `0`. -/
theorem dirac_qcal_eq (n : ℕ) (α : ℝ) (x : ℝ) (h : qcal n α (0 : Fin n → ℝ) = (x : WithTop ℝ)) :
    x = 0 := by
  have hx := qcal_mem h
  rw [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  rfl

/-- The finite branch: the cutoff at the zero vector is the real `0`. -/
theorem dirac_qcal_finite {n : ℕ} {α : ℝ} (hα1 : α < 1) (h : kcal n α ≤ n) :
    qcal n α (0 : Fin n → ℝ) = ((0 : ℝ) : WithTop ℝ) := by
  obtain ⟨hi, hq⟩ := qcal_eq_coe hα1 h (0 : Fin n → ℝ)
  rw [hq, dirac_qcal_eq n α _ hq]

/-- The infinite branch: `α < 1/(n + 1)` gives the cutoff `+∞`. -/
theorem dirac_qcal_top {n : ℕ} {α : ℝ} (hα : 0 < α) (hsmall : α < 1 / ((n : ℝ) + 1)) :
    qcal n α (0 : Fin n → ℝ) = ⊤ :=
  qcal_top (by rw [kcal_eq_succ hα hsmall]; omega) _

/-- The risk at the zero vector is `0`: no score exceeds the cutoff. -/
theorem dirac_Rcal_zero (n : ℕ) (α : ℝ) : Rcal (Measure.dirac 0) n α 0 = 0 := by
  rw [Rcal, Measure.dirac_apply]
  simp only [indicator, mem_ofPred_eq]
  split_ifs with hlt
  swap
  · rfl
  exfalso
  cases hq : qcal n α (0 : Fin n → ℝ) with
  | top => rw [hq] at hlt; exact (not_top_lt hlt)
  | coe y =>
    rw [hq, dirac_qcal_eq n α y hq] at hlt
    exact lt_irrefl _ hlt

/-- **Genuine** instance at `ν = δ₀`, for every calibration size. -/
theorem diracInstance (n : ℕ) : IIDCalibrationRisk (Measure.dirac 0) n where
  risk_bound _ _ α E δ _ _ _ _ _ _ _ := by
    rw [calLaw_dirac, Measure.dirac_apply]
    simp only [indicator, mem_ofPred_eq, dirac_Rcal_zero, not_lt_zero, ite_false]
    exact zero_le

/-- The witness meets every premise of the field, the binomial premise included (at
`α < 1/(n + 1)`, where `B_cal = 0`). -/
theorem dirac_premises (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (Measure.dirac (0 : ℝ)) ∧ 0 < n ∧
      Bcal n (1 / 2) (rcal n (1 / (2 * ((n : ℝ) + 1)))) ≤ 1 / 2 := by
  refine ⟨inferInstance, hn, ?_⟩
  have hr : rcal n (1 / (2 * ((n : ℝ) + 1))) = -1 := by
    unfold rcal
    rw [Int.floor_eq_iff]
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have : 1 / (2 * ((n : ℝ) + 1)) * ((n : ℝ) + 1) = 1 / 2 := by field_simp
    rw [this]
    norm_num
  rw [hr, Bcal_neg_one]
  norm_num

end Upstream
