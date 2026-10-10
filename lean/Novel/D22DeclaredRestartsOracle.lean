import Novel.D22DeclaredRestartsScores

/-!
# Claim 040: each anchor under claim 039's oracle

Fix the training labels `u` and let `μ` be the actual conditional law of the scored labels. For
anchor `r`, take the forecast that is `μ`'s own predictive mass before the anchor and the anchor's
forecast `q_r` from it on. Its oracle product (claim 039's `Qg/cm`) is `1` before the anchor and
`μ(C_(o_r)) Q_(r,t)^pred / μ(C_t)` after it. The null gives `μ(C_t) = ∫ G_(θ,t) dν ≤ D^restart_(r,t)
μ(C_(o_r))` (reconditioning the mixture at the anchor), so the anchor score is at most this oracle
product (`Er_le_oracle`), to which claim 039's oracle bounds (from AX-62, proved from Mathlib)
apply.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D22DeclaredRestarts

open Standalone.D22DeclaredRestarts Standalone.D22FilteredSequential Standalone.D19FilteredLikelihood
  Standalone.D17ClockCells Novel.D22FilteredSequential

variable {n : ℕ}

/-- `μ`'s predictive mass before the anchor `o`, and the forecast `qa` from it on. -/
noncomputable def qmix (μ : Measure (Fin n → ℕ)) (o : ℕ) (qa : ℕ → (Fin n → ℕ) → ℕ → ℝ) :
    ℕ → (Fin n → ℕ) → ℕ → ℝ :=
  fun i y z => if h : i < n ∧ i < o then
      (μ (Cy (i + 1) (Function.update y ⟨i, h.1⟩ z))).toReal / cm μ i y
    else qa i y z

section Mix

variable (μ : Measure (Fin n → ℕ)) [IsProbabilityMeasure μ] (hμ : ∀ y, μ {y} ≠ 0) (o : ℕ)
  (qa : ℕ → (Fin n → ℕ) → ℕ → ℝ) (hqp : ∀ i y y', Agree i y y' → qa i y = qa i y')
  (hq0 : ∀ i y z, 0 ≤ qa i y z) (hq1 : ∀ i y, ∑' z, ENNReal.ofReal (qa i y z) = 1)

omit [IsProbabilityMeasure μ] in
include hqp in
theorem qmix_pred (i : ℕ) (y y' : Fin n → ℕ) (h : Agree i y y') : qmix μ o qa i y = qmix μ o qa i y' := by
  funext z
  unfold qmix
  split_ifs with hi
  · have hc : Cy (i + 1) (Function.update y ⟨i, hi.1⟩ z) = Cy (i + 1) (Function.update y' ⟨i, hi.1⟩ z) :=
      Cy_eq ((agree_succ_fin ⟨i, hi.1⟩).2 ⟨fun j hj => by
        have hne : j ≠ ⟨i, hi.1⟩ := fun e => by rw [e] at hj; exact lt_irrefl _ hj
        rw [Function.update_of_ne hne, Function.update_of_ne hne]; exact h j hj, by simp⟩)
    rw [hc, show cm μ i y = cm μ i y' by unfold cm; rw [Cy_eq h]]
  · rw [hqp i y y' h]

omit [IsProbabilityMeasure μ] in
include hq0 in
theorem qmix_nonneg (i : ℕ) (y : Fin n → ℕ) (z : ℕ) : 0 ≤ qmix μ o qa i y z := by
  unfold qmix; split_ifs
  · exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · exact hq0 i y z

include hμ hq1 in
theorem qmix_norm (i : ℕ) (y : Fin n → ℕ) : ∑' z, ENNReal.ofReal (qmix μ o qa i y z) = 1 := by
  unfold qmix
  split_ifs with hi
  · have hpos := cm_pos μ hμ i y
    have hfin : ∀ z, μ (Cy (i + 1) (Function.update y ⟨i, hi.1⟩ z)) ≠ ⊤ := fun z => measure_ne_top _ _
    simp_rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_toReal (hfin _), cm,
      ENNReal.ofReal_toReal (measure_ne_top μ _), div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right]
    have hU := Cy_iUnion (n := n) ⟨i, hi.1⟩ y
    have hD := Cy_disjoint (n := n) ⟨i, hi.1⟩ y
    rw [← measure_iUnion hD fun _ => MeasurableSet.of_discrete]
    simp only at hU
    rw [← hU]
    exact ENNReal.mul_inv_cancel (Cy_ne_zero μ hμ i y) (measure_ne_top _ _)
  · exact hq1 i y

theorem cm_zero (y : Fin n → ℕ) : cm μ 0 y = 1 := by simp [cm, Cy_zero]

/-- One more factor of a forecast product. -/
theorem Qg_succ (q : ℕ → (Fin n → ℕ) → ℕ → ℝ) {t : ℕ} (ht : t < n) (y : Fin n → ℕ) :
    Qg q (t + 1) y = Qg q t y * q t y (y ⟨t, ht⟩) := by
  have h := prod_lt_succ (fun j : Fin n => q j y (y j)) ⟨t, ht⟩
  simp only [Fin.val_succ, Fin.val_castSucc] at h
  exact h

include hμ in
/-- Before the anchor the mixed product is the cylinder mass. -/
theorem Qg_before : ∀ t, t ≤ o → t ≤ n → ∀ y, Qg (qmix μ o qa) t y = cm μ t y
  | 0, _, _, y => by rw [cm_zero]; simp [Qg]
  | t + 1, hto, htn, y => by
    rw [Qg_succ _ (by omega), Qg_before t (by omega) (by omega) y]
    have hq : qmix μ o qa t y (y ⟨t, by omega⟩) = cm μ (t + 1) y / cm μ t y := by
      unfold qmix
      rw [dite_eq_left_of_eq_true (eq_true ⟨by omega, by omega⟩), Function.update_eq_self]
      rfl
    rw [hq]
    field_simp [(cm_pos μ hμ t y).ne']

end Mix

section After

variable {k : ℕ} (μ : Measure (Fin n → ℕ)) [IsProbabilityMeasure μ] (hμ : ∀ y, μ {y} ≠ 0)
  (q : Fc k n) (u : Fin k → ℕ) (o : Fin n)

/-- The anchor product at a natural time. -/
noncomputable def QrN (t : ℕ) (y : Fin n → ℕ) : ℝ :=
  ∏ i : Fin n, if (o : ℕ) ≤ i ∧ (i : ℕ) < t then q i u y (y i) else 1

theorem Qr_eq (t : Fin (n + 1)) (y : Fin n → ℕ) : Qr q o t u y = QrN q u o t y := rfl

/-- One more factor of an anchor product. -/
theorem QrN_succ {t : ℕ} (ht : t < n) (hot : (o : ℕ) ≤ t) (y : Fin n → ℕ) :
    QrN q u o (t + 1) y = QrN q u o t y * q t u y (y ⟨t, ht⟩) := by
  unfold QrN
  have hsplit : ∀ i : Fin n, (if (o : ℕ) ≤ i ∧ (i : ℕ) < t + 1 then q i u y (y i) else 1) =
      (if (o : ℕ) ≤ i ∧ (i : ℕ) < t then q i u y (y i) else 1) *
        (if i = ⟨t, ht⟩ then q i u y (y i) else 1) := fun i => by
    by_cases hi : i = ⟨t, ht⟩
    · subst hi; simp [hot]
    · have : (i : ℕ) ≠ t := fun h => hi (Fin.ext h)
      have h2 : (i : ℕ) < t + 1 ↔ (i : ℕ) < t := by omega
      simp [hi, h2]
  rw [Finset.prod_congr rfl fun i _ => hsplit i, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

theorem QrN_anchor (y : Fin n → ℕ) : QrN q u o o y = 1 :=
  Finset.prod_eq_one fun i _ => by
    have : ¬ ((o : ℕ) ≤ i ∧ (i : ℕ) < o) := by omega
    simp only [this, ↓reduceIte]

include hμ in
/-- From the anchor on, the mixed product is `μ(C_o) Q^pred`. -/
theorem Qg_after (y : Fin n → ℕ) : ∀ m : ℕ, (o : ℕ) + m ≤ n →
    Qg (qmix μ o (fun i y z => q i u y z)) ((o : ℕ) + m) y = cm μ o y * QrN q u o ((o : ℕ) + m) y
  | 0, _ => by
    simp only [add_zero]
    rw [Qg_before μ hμ o _ _ le_rfl o.isLt.le y, QrN_anchor, mul_one]
  | m + 1, ht => by
    rw [← add_assoc, Qg_succ _ (by omega), Qg_after y m (by omega),
      QrN_succ q u o (by omega) (by omega) y, mul_assoc]
    congr 2
    unfold qmix
    rw [dite_eq_right_of_eq_false (eq_false (by omega))]

end After

end Novel.D22DeclaredRestarts
