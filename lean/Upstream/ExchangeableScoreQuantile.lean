import Mathlib.Probability.Distributions.Bernoulli

/-!
# AX-65  Exchangeable-score quantile bound

Ledger entry AX-65 (`ledger/AXIOMS.md`). Source: [tibshirani2019conformal], §1.1, Lemma 1, printed
p. 2 (quantile convention on pp. 1–2). Only the lower coverage bound is imported; the upper bound,
which needs almost surely distinct scores, is not.

Mathlib has no exchangeability or conformal-quantile result, so the source theorem enters as a
model-indexed hypothesis structure (rule 6); the general theorem is not reconstructed.

## Objects

* `n` is the calibration size `n_cal` (positive in the field's premise); the scores are
  `S : Fin (n + 1) → Ω → ℝ`, the calibration scores `S i.castSucc` and the evaluation score
  `S (Fin.last n)`.
* `PermInvariant P S`: the joint law of `(S_1, …, S_(n+1))` is unchanged by **every** permutation of
  the `n + 1` coordinates (the actual exchangeability premise).
* `kcal n α = ⌈(n + 1)(1 − α)⌉`.
* `qcal n α s ∈ ℝ ∪ {+∞}` (`WithTop ℝ`): the `k_cal`-th smallest calibration score, counting
  repetitions (the `k_cal`-th entry of the sorted list of all `n` calibration scores), when
  `k_cal ≤ n`; and `+∞` when `k_cal = n + 1`, never a real default.
* The rejection event is strict exceedance, `q_cal < S_(n+1)` in `WithTop ℝ`: equality with a finite
  cutoff is accepted, and the infinite cutoff is never exceeded.

## The field

`rank_bound`: for a probability `P`, positive `n`, measurable scores with a permutation-invariant
joint law, and every deterministic `0 < α < 1`, `P(S_(n+1) > q_cal) ≤ α`. The event's probability
averages over all scores, calibration included. No bare p-value bound replaces the field.

## Convention checks

* `one_le_kcal`, `kcal_le_succ`: `1 ≤ k_cal ≤ n + 1` for `0 < α < 1`, so the `+∞` branch is exactly
  `k_cal = n + 1`.
* `qcal_eq_coe`: when `k_cal ≤ n`, the cutoff is the real `k_cal`-th entry of the sorted calibration
  list (`length_sortedCal`: all `n` scores, repetitions kept); the `⊤` default of the list lookup is
  never used there.
* `kcal_eq_succ`, `qcal_top`: `α < 1/(n + 1)` gives `k_cal = n + 1`, hence the cutoff `+∞`.
* `qcal_mem`: every finite cutoff is one of the calibration scores.

## Instance: genuine (the ledger's shared-bit witness)

`sharedBit_instance`: on two points with the fair probability, every one of `n_cal + 1 = 20` scores
equals the same random bit. The score vector is a nonconstant random vector, perfectly dependent;
permutation invariance holds pointwise (`sharedBit_permInvariant`); every score is measurable; every
cutoff is the common bit or `+∞`, so the strict-exceedance event is empty for every allowed `α`
(`sharedBit_event_empty`). Both bit values have probability one half (`fairBit_true`,
`sharedBit_nonconstant`). This exercises ties and the infinite branch (`kcal_eq_succ`: `α < 1/20`
gives `k_cal = 20`). It is not evidence about independent continuous scores or financial windows,
and it supplies no exchangeability for any application.
-/

open MeasureTheory ProbabilityTheory Set

namespace Upstream

/-! ## Order statistics -/

/-- `k_cal = ⌈(n + 1)(1 − α)⌉`. -/
noncomputable def kcal (n : ℕ) (α : ℝ) : ℕ := ⌈((n : ℝ) + 1) * (1 - α)⌉₊

/-- The calibration scores sorted increasingly, with every repetition retained. -/
noncomputable def sortedCal {n : ℕ} (s : Fin n → ℝ) : List ℝ :=
  (List.ofFn s).mergeSort fun a b => decide (a ≤ b)

/-- `q_cal`: the `k_cal`-th smallest calibration score if `k_cal ≤ n`, and `+∞` otherwise. -/
noncomputable def qcal (n : ℕ) (α : ℝ) (s : Fin n → ℝ) : WithTop ℝ :=
  if kcal n α ≤ n then
    ((sortedCal s)[kcal n α - 1]?).elim ⊤ fun x => (x : WithTop ℝ)
  else ⊤

/-- The joint law of the score vector is invariant under every permutation of its coordinates. -/
def PermInvariant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (S : Fin (n + 1) → Ω → ℝ) : Prop :=
  ∀ σ : Equiv.Perm (Fin (n + 1)),
    P.map (fun ω i => S (σ i) ω) = P.map (fun ω i => S i ω)

/-- AX-65 for one model `(P, n, S)`. -/
structure ExchangeableScoreQuantile {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (S : Fin (n + 1) → Ω → ℝ) : Prop where
  /-- Lemma 1's lower coverage bound, in complement form at `β = 1 − α`. -/
  rank_bound : IsProbabilityMeasure P → 0 < n → (∀ i, Measurable (S i)) → PermInvariant P S →
    ∀ α : ℝ, 0 < α → α < 1 →
      P {ω | qcal n α (fun i => S i.castSucc ω) < ((S (Fin.last n) ω : ℝ) : WithTop ℝ)} ≤
        ENNReal.ofReal α

/-! ## Convention checks -/

/-- `k_cal ≥ 1` for `α < 1`. -/
theorem one_le_kcal {n : ℕ} {α : ℝ} (hα1 : α < 1) : 1 ≤ kcal n α := by
  unfold kcal
  exact Nat.one_le_iff_ne_zero.2 fun h => by
    rw [Nat.ceil_eq_zero] at h
    have : 0 < ((n : ℝ) + 1) * (1 - α) := mul_pos (by positivity) (by linarith)
    linarith

/-- `α < 1/(n + 1)` forces `k_cal = n + 1`, hence the infinite cutoff and no rejection. -/
theorem kcal_eq_succ {n : ℕ} {α : ℝ} (hα : 0 < α) (hsmall : α < 1 / ((n : ℝ) + 1)) :
    kcal n α = n + 1 := by
  unfold kcal
  rw [Nat.ceil_eq_iff (by omega)]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  push_cast
  constructor
  · have : ((n : ℝ) + 1) * α < 1 := by rwa [lt_div_iff₀ hn, mul_comm] at hsmall
    nlinarith
  · nlinarith

/-- `k_cal ≤ n + 1` for `α > 0`, so the infinite branch is exactly `k_cal = n + 1`. -/
theorem kcal_le_succ {n : ℕ} {α : ℝ} (hα : 0 < α) : kcal n α ≤ n + 1 := by
  unfold kcal
  rw [Nat.ceil_le]
  push_cast
  have : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  nlinarith

theorem length_sortedCal {n : ℕ} (s : Fin n → ℝ) : (sortedCal s).length = n := by
  simp [sortedCal]

/-- In the finite branch the cutoff is a real calibration order statistic, never the default. -/
theorem qcal_eq_coe {n : ℕ} {α : ℝ} (hα1 : α < 1) (h : kcal n α ≤ n) (s : Fin n → ℝ) :
    ∃ hi : kcal n α - 1 < (sortedCal s).length,
      qcal n α s = (((sortedCal s)[kcal n α - 1]'hi : ℝ) : WithTop ℝ) := by
  have hi : kcal n α - 1 < (sortedCal s).length := by
    rw [length_sortedCal]; have := one_le_kcal (n := n) hα1; omega
  refine ⟨hi, ?_⟩
  simp [qcal, List.getElem?_eq_getElem hi, h]

theorem qcal_top {n : ℕ} {α : ℝ} (h : ¬ kcal n α ≤ n) (s : Fin n → ℝ) : qcal n α s = ⊤ := by
  unfold qcal; exact ite_eq_right_iff.2 fun h' => absurd h' h

/-- Every finite cutoff is one of the calibration scores (repetitions counted). -/
theorem qcal_mem {n : ℕ} {α : ℝ} {s : Fin n → ℝ} {x : ℝ} (h : qcal n α s = (x : WithTop ℝ)) :
    x ∈ List.ofFn s := by
  unfold qcal at h
  split_ifs at h
  · cases hx : (sortedCal s)[kcal n α - 1]? with
    | none => simp [hx] at h
    | some y =>
      simp only [hx, Option.elim_some, WithTop.coe_eq_coe] at h
      subst h
      exact (List.mem_mergeSort.1 (List.mem_of_getElem? hx))
  · simp at h

/-! ## The shared-bit witness -/

/-- The fair probability on two points. -/
noncomputable def fairBit : Measure Bool :=
  bernoulliMeasure true false ⟨1 / 2, by norm_num, by norm_num⟩

instance : IsProbabilityMeasure fairBit := by unfold fairBit; infer_instance

/-- Each value of the bit has probability one half. -/
theorem fairBit_true : fairBit {true} = 2⁻¹ := by
  rw [fairBit, bernoulliMeasure_apply _ (measurableSet_singleton _)]
  simp only [Set.mem_singleton_iff, ite_true, Bool.false_eq_true, ite_false]
  have h : unitInterval.toNNReal ⟨1 / 2, by norm_num, by norm_num⟩ = 2⁻¹ :=
    NNReal.eq (by simp [unitInterval.toNNReal]; rfl)
  rw [h, ENNReal.coe_inv two_ne_zero]
  rfl

/-- Every score is the same random bit. -/
def sharedBit (n : ℕ) : Fin (n + 1) → Bool → ℝ := fun _ b => if b then 1 else 0

theorem sharedBit_measurable (n : ℕ) (i : Fin (n + 1)) : Measurable (sharedBit n i) :=
  measurable_of_countable _

theorem sharedBit_permInvariant (n : ℕ) : PermInvariant fairBit (sharedBit n) := fun _ => rfl

/-- The score vector is not almost surely constant. -/
theorem sharedBit_nonconstant (n : ℕ) : sharedBit n 0 true ≠ sharedBit n 0 false := by
  simp [sharedBit]

/-- The strict-exceedance event is empty: a finite cutoff equals the common bit. -/
theorem sharedBit_event_empty (n : ℕ) (α : ℝ) :
    {b | qcal n α (fun i => sharedBit n i.castSucc b) <
      ((sharedBit n (Fin.last n) b : ℝ) : WithTop ℝ)} = ∅ := by
  ext b
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
  cases hq : qcal n α (fun i => sharedBit n i.castSucc b) with
  | top => exact le_top
  | coe x =>
    have hx := qcal_mem hq
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [sharedBit]

/-- **Genuine** instance at `n_cal = 19` (the ledger's witness). -/
theorem sharedBit_instance : ExchangeableScoreQuantile fairBit 19 (sharedBit 19) where
  rank_bound _ _ _ _ α _ _ := by
    rw [sharedBit_event_empty, measure_empty]; exact zero_le

/-- The witness meets every premise of the field. -/
theorem sharedBit_premises :
    IsProbabilityMeasure fairBit ∧ 0 < 19 ∧ (∀ i, Measurable (sharedBit 19 i)) ∧
      PermInvariant fairBit (sharedBit 19) :=
  ⟨inferInstance, by norm_num, sharedBit_measurable 19, sharedBit_permInvariant 19⟩

end Upstream
