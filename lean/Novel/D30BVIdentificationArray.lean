import Standalone.D30BVIdentification

/-!
# Claim 071, part 2 and the deterministic remarks of part 1

* (3): `C_grid − β Q_grid = Σ (a_j − a_(j−1)) d_j + Σ (e_j − e_(j−1)) d_j`. The first sum is at most
  `V_time w_grid`. Finite summation by parts rewrites the second as `Σ_j e_j c_j` with
  coefficients `c_0 = −d_1`, `c_n = d_n` and `c_j = d_j − d_(j+1)` in between (`abel_sum`), whose
  absolute values sum to `H_grid` (`Hg_eq`); so it is at most `ε_L H_grid`.
* Sharpness: one jump of size `V_time` in `a` at a largest `|d_k|`, and `e_j = ε_L sign(c_j)`.
* The decision rule, its size and its power (4) follow from (3) and the union bound.
* The elasticity and the Lipschitz variation bound are one-line calculus facts.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D30BVIdentification

open Standalone.D30BVIdentification

variable {m : ℕ}

/-- The summation-by-parts coefficient of `e_j`. -/
noncomputable def coef (d : Fin (m + 1) → ℝ) (j : Fin (m + 2)) : ℝ :=
  (if h : (j : ℕ) < m + 1 then -d ⟨j, h⟩ else 0) + (if h : 0 < (j : ℕ) then d ⟨j - 1, by omega⟩ else 0)

theorem abel_sum (e : Fin (m + 2) → ℝ) (d : Fin (m + 1) → ℝ) :
    ∑ i, (e i.succ - e i.castSucc) * d i = ∑ j, e j * coef d j := by
  have h1 : ∑ j : Fin (m + 2), e j * (if h : (j : ℕ) < m + 1 then -d ⟨j, h⟩ else 0) =
      -∑ i : Fin (m + 1), e i.castSucc * d i := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.val_last, lt_irrefl,
      mul_zero, add_zero, mul_neg, Finset.sum_neg_distrib]
  have h2 : ∑ j : Fin (m + 2), e j * (if h : 0 < (j : ℕ) then d ⟨j - 1, by omega⟩ else 0) =
      ∑ i : Fin (m + 1), e i.succ * d i := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, lt_irrefl, ↓reduceDIte, mul_zero, zero_add, Fin.val_succ,
      Nat.succ_pos, Nat.add_sub_cancel, Fin.eta]
  unfold coef
  simp_rw [mul_add, Finset.sum_add_distrib, h1, h2, sub_mul, Finset.sum_sub_distrib]
  ring

theorem coef_zero (d : Fin (m + 1) → ℝ) : coef d 0 = -d 0 := by
  simp [coef]

theorem coef_last (d : Fin (m + 1) → ℝ) : coef d (Fin.last (m + 1)) = d (Fin.last m) := by
  simp [coef]; rfl

theorem coef_mid (d : Fin (m + 1) → ℝ) (i : Fin m) :
    coef d i.succ.castSucc = d i.castSucc - d i.succ := by
  unfold coef
  rw [dif_pos (by simp), dif_pos (by simp)]
  have h1 : (⟨((i.succ.castSucc : Fin (m + 2)) : ℕ), by simp⟩ : Fin (m + 1)) = i.succ :=
    Fin.ext (by simp)
  have h2 : (⟨((i.succ.castSucc : Fin (m + 2)) : ℕ) - 1, by simp⟩ : Fin (m + 1)) = i.castSucc :=
    Fin.ext (by simp)
  rw [h1, h2]; ring

theorem Hg_eq (x : Fin (m + 2) → ℝ) : Hg x = ∑ j, |coef (dif x) j| := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, coef_zero, Fin.succ_last, coef_last, abs_neg]
  simp_rw [Fin.succ_castSucc, coef_mid]
  unfold Hg
  ring

theorem dif_lhat (a : Fin (m + 2) → ℝ) (β : ℝ) (x e : Fin (m + 2) → ℝ) (i : Fin (m + 1)) :
    dif (lhat a β x e) i = dif a i + β * dif x i + dif e i := by
  unfold dif lhat; ring

/-- `C_grid − β Q_grid` splits into the time and error contributions. -/
theorem Cg_sub (a : Fin (m + 2) → ℝ) (β : ℝ) (x e : Fin (m + 2) → ℝ) :
    Cg (lhat a β x e) x - β * Qg x =
      ∑ i, dif a i * dif x i + ∑ j, e j * coef (dif x) j := by
  unfold Cg Qg
  simp_rw [dif_lhat, add_mul, Finset.sum_add_distrib]
  rw [← abel_sum]
  simp only [dif, Finset.mul_sum]
  ring_nf

theorem le_wg (x : Fin (m + 2) → ℝ) (i : Fin (m + 1)) : |dif x i| ≤ wg x :=
  Finset.le_sup' (fun i => |dif x i|) (Finset.mem_univ i)

theorem num_bound {a e x : Fin (m + 2) → ℝ} {V ε : ℝ} (h : Acc V ε a e) (β : ℝ) :
    |Cg (lhat a β x e) x - β * Qg x| ≤ V * wg x + ε * Hg x := by
  rw [Cg_sub]
  have hw0 : 0 ≤ wg x := (abs_nonneg _).trans (le_wg x 0)
  have hε : 0 ≤ ε := (abs_nonneg _).trans (h.2 0)
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · calc |∑ i, dif a i * dif x i| ≤ ∑ i, |dif a i| * wg x :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (le_wg x i) (abs_nonneg _))
      _ = (∑ i, |dif a i|) * wg x := by rw [Finset.sum_mul]
      _ ≤ V * wg x := mul_le_mul_of_nonneg_right h.1 hw0
  · rw [Hg_eq, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (h.2 j) (abs_nonneg _))

theorem arrayBound_holds : Standalone.D30BVIdentification.arrayBound := by
  intro m x a e β V ε h hQ
  unfold bhat rg
  rw [show Cg (lhat a β x e) x / Qg x - β = (Cg (lhat a β x e) x - β * Qg x) / Qg x by
    field_simp, abs_div, abs_of_pos hQ]
  exact div_le_div_of_nonneg_right (num_bound h β) hQ.le

/-- `s(z) z = |z|`, `|s(z)| = 1`. -/
noncomputable def sgn (z : ℝ) : ℝ := if 0 ≤ z then 1 else -1

theorem sgn_mul (z : ℝ) : sgn z * z = |z| := by
  unfold sgn; split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [abs_of_neg (not_le.1 h)]; ring

theorem abs_sgn (z : ℝ) : |sgn z| = 1 := by unfold sgn; split_ifs <;> simp

theorem Qg_pos {x : Fin (m + 2) → ℝ} (h : ∃ i j, x i ≠ x j) : 0 < Qg x := by
  by_contra hle
  have h0 : ∀ i, dif x i = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (dif x i)).1
      (le_antisymm (not_lt.1 hle) (Finset.sum_nonneg fun i _ => sq_nonneg _)) i (Finset.mem_univ _)
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this
  have hc : ∀ j : Fin (m + 2), x j = x 0 := fun j => by
    induction j using Fin.induction with
    | zero => rfl
    | succ i ih => have := h0 i; unfold dif at this; linarith
  obtain ⟨i, j, hij⟩ := h
  exact hij (by rw [hc i, hc j])

theorem sharp_holds : Standalone.D30BVIdentification.sharp := by
  intro m x β V ε hV hε hx
  refine ⟨Qg_pos hx, ?_⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i => |dif x i|
  set a : Fin (m + 2) → ℝ := fun j => if (j : ℕ) ≤ k then 0 else V * sgn (dif x k)
  set e : Fin (m + 2) → ℝ := fun j => ε * sgn (coef (dif x) j)
  have hda : ∀ i, dif a i = if i = k then V * sgn (dif x k) else 0 := fun i => by
    simp only [dif, a, Fin.val_succ, Fin.val_castSucc]
    by_cases hi : i = k
    · subst hi; simp
    · rcases lt_or_gt_of_ne (fun h => hi (Fin.ext h) : (i : ℕ) ≠ k) with h | h
      · rw [if_pos (by omega), if_pos (by omega), if_neg hi]; ring
      · rw [if_neg (by omega), if_neg (by omega), if_neg hi]; ring
  refine ⟨a, e, ⟨?_, fun j => ?_⟩, ?_⟩
  · simp_rw [hda]
    rw [Finset.sum_eq_single k (fun i _ hi => by rw [if_neg hi, abs_zero]) (by simp), if_pos rfl,
      abs_mul, abs_sgn, mul_one, abs_of_nonneg hV]
  · simp only [e, abs_mul, abs_sgn, mul_one, abs_of_nonneg hε, le_refl]
  · rw [Cg_sub]
    simp_rw [hda]
    rw [Finset.sum_eq_single k (fun i _ hi => by rw [if_neg hi, zero_mul]) (by simp), if_pos rfl,
      Hg_eq, Finset.mul_sum, wg, hk]
    simp only [e]
    congr 1
    · rw [mul_assoc, sgn_mul]
    · exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc, sgn_mul]

theorem decision_holds : Standalone.D30BVIdentification.decision := by
  intro m x a e β V ε h hQ
  have hb := abs_le.1 (arrayBound_holds m x a e β V ε h hQ)
  have hr : 0 ≤ rg V ε x := (abs_nonneg _).trans (arrayBound_holds m x a e β V ε h hQ)
  exact ⟨fun hβ => by linarith [hb.2], fun hβ => by linarith [hb.1]⟩

theorem measurableSet_acc {Ω : Type} [MeasurableSpace Ω] {a e : Ω → Fin (m + 2) → ℝ}
    (ha : Measurable a) (he : Measurable e) (V ε : ℝ) :
    MeasurableSet {ω | Acc V ε (a ω) (e ω)} := by
  have h1 : Measurable fun ω => ∑ i, |dif (a ω) i| :=
    Finset.measurable_sum _ fun i _ => continuous_abs.measurable.comp
      (((measurable_pi_apply _).comp ha).sub ((measurable_pi_apply _).comp ha))
  have h2 : MeasurableSet {ω | ∀ j, |e ω j| ≤ ε} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le (continuous_abs.measurable.comp ((measurable_pi_apply j).comp he))
        measurable_const
  exact (measurableSet_le h1 measurable_const).inter h2

theorem test_holds : Standalone.D30BVIdentification.test := by
  intro Ω _ P _ m x a e β V ε δ hx ha he hacc rej
  have hA := measurableSet_acc ha he V ε
  have hcompl : P {ω | Acc V ε (a ω) (e ω)}ᶜ ≤ ENNReal.ofReal δ := by
    rw [prob_compl_eq_one_sub hA]
    refine tsub_le_iff_right.2 (le_trans ?_ (add_le_add le_rfl hacc))
    calc (1 : ℝ≥0∞) = ENNReal.ofReal (δ + (1 - δ)) := by rw [add_sub_cancel, ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal δ + ENNReal.ofReal (1 - δ) := ENNReal.ofReal_add_le
  refine ⟨fun hβ => le_trans (measure_mono fun ω hω => ?_) hcompl, ?_⟩
  · intro hacc'
    exact absurd hω.2 (not_lt.2 ((decision_holds m _ _ _ β V ε hacc' hω.1).1 hβ))
  · calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ P (rej ∪ {ω | Acc V ε (a ω) (e ω)}ᶜ ∪ {ω | Qg (x ω) = 0 ∨ β ≤ 2 * rg V ε (x ω)}) :=
          measure_mono fun ω _ => by
            by_cases hacc' : Acc V ε (a ω) (e ω)
            · by_cases hbad : Qg (x ω) = 0 ∨ β ≤ 2 * rg V ε (x ω)
              · exact Or.inr hbad
              · push Not at hbad
                have hQ : 0 < Qg (x ω) :=
                  lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hbad.1)
                exact Or.inl (Or.inl ⟨hQ, (decision_holds m _ _ _ β V ε hacc' hQ).2 hbad.2⟩)
            · exact Or.inl (Or.inr hacc')
      _ ≤ P rej + P {ω | Acc V ε (a ω) (e ω)}ᶜ + P {ω | Qg (x ω) = 0 ∨ β ≤ 2 * rg V ε (x ω)} :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ P rej + ENNReal.ofReal δ + P {ω | Qg (x ω) = 0 ∨ β ≤ 2 * rg V ε (x ω)} := by
          gcongr

theorem sampled_holds : Standalone.D30BVIdentification.sampled := by
  intro m a T V t hV ht hmem hvar
  set u : ℕ → ℝ := fun i => t ⟨min i (m + 1), by omega⟩
  have hu : Monotone u := fun i j hij => ht (Fin.le_def.2 (by simp; omega))
  have hsum := eVariationOn.sum_le (f := a) (n := m + 1) hu fun i => hmem _
  have he : ∑ i ∈ Finset.range (m + 1), edist (a (u (i + 1))) (a (u i)) =
      ENNReal.ofReal (∑ i : Fin (m + 1), |dif (fun j => a (t j)) i|) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [edist_dist, Real.dist_eq]
    simp only [dif, u]
    have h1 : (⟨min ((i : ℕ) + 1) (m + 1), by omega⟩ : Fin (m + 2)) = i.succ :=
      Fin.ext (by simp only [Fin.val_succ]; omega)
    have h2 : (⟨min (i : ℕ) (m + 1), by omega⟩ : Fin (m + 2)) = i.castSucc :=
      Fin.ext (by simp only [Fin.val_castSucc]; omega)
    rw [h1, h2]
  rw [he] at hsum
  exact (ENNReal.ofReal_le_ofReal_iff hV).1 (hsum.trans hvar)

theorem oracle_holds : Standalone.D30BVIdentification.oracle := by
  intro m x V; simp [rg]

theorem elasticity_holds : Standalone.D30BVIdentification.elasticity := by
  intro a β s₀ t x hs₀
  have hf : (fun x => Real.log (sigmaF a β s₀ t (Real.exp x))) =
      fun x => x + (a t + β * (x - Real.log s₀)) / 2 := by
    funext x
    unfold sigmaF
    rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp,
      Real.log_div (Real.exp_pos _).ne' hs₀.ne', Real.log_exp]
  rw [hf]
  have h := (hasDerivAt_id' x).add (((((hasDerivAt_id' x).sub_const (Real.log s₀)).const_mul β).const_add
    (a t)).div_const 2)
  convert h using 1
  ring

theorem lipschitz_holds : Standalone.D30BVIdentification.lipschitz := by
  intro a Lt T hL hT h
  have h1 := h.comp_eVariationOn_le (g := id) (s := Icc 0 T) (mapsTo_id _)
  have h2 : eVariationOn (id : ℝ → ℝ) (Icc 0 T) ≤ ENNReal.ofReal (T - 0) := by
    have := (monotoneOn_id (s := Icc (0 : ℝ) T)).eVariationOn_eq ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩
    rw [Set.inter_self] at this
    exact this.le
  calc eVariationOn a (Icc 0 T) = eVariationOn (a ∘ id) (Icc 0 T) := rfl
    _ ≤ (Real.toNNReal Lt : ℝ≥0∞) * eVariationOn id (Icc 0 T) := h1
    _ ≤ (Real.toNNReal Lt : ℝ≥0∞) * ENNReal.ofReal (T - 0) := by gcongr
    _ = ENNReal.ofReal (Lt * T) := by
        rw [sub_zero, ENNReal.ofReal_mul hL]; rfl

end Novel.D30BVIdentification
