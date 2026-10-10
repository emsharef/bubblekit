import Novel.D19CenteredQuadratureBox

/-!
# Claim 038: the coefficients (7)

* Summation by parts (`sum_Dinc`) gives `Lin(u) = Σ_i G_i u_i` with `G_i = q_(i+1) − q_i`,
  `q_j = e_j/(wv_j)` and `q_(J+1) = 0`.
* On a midpoint path in the observed cells, `|q_j| ≤ C_j(B)` for every parameter of `B`, so
  `|G_i| ≤ C_i(B) + C_(i+1)(B)` with `C_(J+1) = 0` and `Σ G_i² r_i²/2 ≤ ε^+` (`G_sum_le`).
* On the subcell, `|u_j − u_(j−1)| ≤ r_j + r_(j−1)`, so `H(u) ≤ ε^−` (`quadT_le`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D19CenteredQuadrature

open Standalone.D19CenteredQuadrature Standalone.D19FilteredLikelihood Standalone.D19CondSensitivity
  Standalone.D17ClockCells Novel.D19FilteredLikelihood Novel.D19CondSensitivity

variable {m : ℕ}

/-- Summation by parts with `u_0 = 0` and `a_(J+1) = 0`. -/
theorem sum_Dinc : ∀ {m : ℕ} (a u : Fin m → ℝ),
    ∑ j, a j * Dinc u j = ∑ i, u i * (a i - (Fin.snoc a 0 : Fin (m + 1) → ℝ) i.succ)
  | 0, _, _ => by simp
  | m + 1, a, u => by
    unfold Dinc inc
    simp only [mul_sub, Finset.sum_sub_distrib, Fin.cons_succ]
    have h1 : ∑ j : Fin (m + 1), a j * (Fin.cons 0 u : Fin (m + 2) → ℝ) j.castSucc =
        ∑ k : Fin m, a k.succ * u k.castSucc := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.castSucc_zero, Fin.cons_zero, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Fin.succ_castSucc, Fin.cons_succ]
    have h2 : ∑ i : Fin (m + 1), u i * (Fin.snoc a 0 : Fin (m + 2) → ℝ) i.succ =
        ∑ k : Fin m, a k.succ * u k.castSucc := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.succ_last, Fin.snoc_last, mul_zero, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fin.succ_castSucc, Fin.snoc_castSucc, mul_comm]
    rw [h1, h2]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- `q_j = e_j/(wv_j)`. -/
noncomputable def qRes (Δ v : Fin m → ℝ) (b w c : ℝ) (t : Fin m → ℝ) : Fin m → ℝ :=
  fun j => eRes Δ v b w c t j / (w * v j)

/-- `G_i = q_(i+1) − q_i`, with `q_(J+1) = 0`. -/
noncomputable def Gco (Δ v : Fin m → ℝ) (b w c : ℝ) (t : Fin m → ℝ) : Fin m → ℝ :=
  fun i => (Fin.snoc (qRes Δ v b w c t) 0 : Fin (m + 1) → ℝ) i.succ - qRes Δ v b w c t i

theorem linT_eq (Δ v : Fin m → ℝ) (b w c : ℝ) (t u : Fin m → ℝ) :
    linT Δ v b w c t u = ∑ i, Gco Δ v b w c t i * u i := by
  have h : ∑ j, eRes Δ v b w c t j * Dinc u j / (w * v j) =
      ∑ j, qRes Δ v b w c t j * Dinc u j :=
    Finset.sum_congr rfl fun j _ => by unfold qRes; ring
  unfold linT
  rw [h, sum_Dinc, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold Gco; ring

/-- A path whose points lie in the closed observed cells, from `log s`. -/
def InCl (δ s : ℝ) (z : Fin m → ℕ) (t : Fin m → ℝ) : Prop :=
  ∀ k, aP δ s z k ≤ (Fin.cons (Real.log s) t : Fin (m + 1) → ℝ) k ∧
    (Fin.cons (Real.log s) t : Fin (m + 1) → ℝ) k ≤ dP δ s z k

theorem qRes_le {δ s : ℝ} (Δ v : Fin m → ℝ) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B : Box}
    (hB : B.Valid) {b w : ℝ} (hbw : B.Mem (b, w)) {z : Fin m → ℕ} {t : Fin m → ℝ}
    (ht : InCl δ s z t) (j : Fin m) :
    |qRes Δ v b w (Real.log s) t j| ≤ Cj δ s Δ v B z j := by
  have hw : 0 < w := hB.2.1.trans_le hbw.2.1
  have hvj := hv j
  have hΔj := hΔ j
  have hR : |inc (Fin.cons (Real.log s) t) j| ≤ Rmax δ s z j := by
    unfold inc Rmax
    have h1 := ht j.succ
    have h2 := ht j.castSucc
    exact abs_le_max_of_mem (by linarith [h1.1, h2.2]) (by linarith [h1.2, h2.1])
  have hb : |b| ≤ Bmax B := abs_le_max_of_mem hbw.1.1 hbw.1.2
  have he : |eRes Δ v b w (Real.log s) t j| ≤ Rmax δ s z j + Bmax B * Δ j + B.wH * v j / 2 := by
    unfold eRes
    have hwv : w * v j / 2 ≤ B.wH * v j / 2 := by
      have := mul_le_mul_of_nonneg_right hbw.2.2 hvj.le; linarith
    calc |inc (Fin.cons (Real.log s) t) j - (b * Δ j - w * v j / 2)|
        ≤ |inc (Fin.cons (Real.log s) t) j| + |b * Δ j| + |w * v j / 2| := by
          have := abs_sub (inc (Fin.cons (Real.log s) t) j) (b * Δ j - w * v j / 2)
          have := abs_sub (b * Δ j) (w * v j / 2)
          linarith
      _ ≤ _ := by
          rw [abs_mul, abs_of_pos hΔj, abs_of_pos (by positivity : 0 < w * v j / 2)]
          have := mul_le_mul_of_nonneg_right hb hΔj.le
          linarith
  unfold qRes Cj
  rw [abs_div, abs_of_pos (mul_pos hw hvj)]
  have hnum : 0 ≤ Rmax δ s z j + Bmax B * Δ j + B.wH * v j / 2 := (abs_nonneg _).trans he
  calc |eRes Δ v b w (Real.log s) t j| / (w * v j)
      ≤ (Rmax δ s z j + Bmax B * Δ j + B.wH * v j / 2) / (w * v j) :=
        div_le_div_of_nonneg_right he (mul_pos hw hvj).le
    _ ≤ _ := div_le_div_of_nonneg_left hnum (mul_pos hB.2.1 hvj)
        (mul_le_mul_of_nonneg_right hbw.2.1 hvj.le)

theorem Gco_le {δ s : ℝ} (Δ v : Fin m → ℝ) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B : Box}
    (hB : B.Valid) {b w : ℝ} (hbw : B.Mem (b, w)) {z : Fin m → ℕ} {t : Fin m → ℝ}
    (ht : InCl δ s z t) (i : Fin m) :
    |Gco Δ v b w (Real.log s) t i| ≤ Cpad δ s Δ v B z i.castSucc + Cpad δ s Δ v B z i.succ := by
  have hpad : ∀ k : Fin (m + 1), |(Fin.snoc (qRes Δ v b w (Real.log s) t) 0 : Fin (m + 1) → ℝ) k| ≤
      Cpad δ s Δ v B z k := fun k => by
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp [Cpad]
    · unfold Cpad; rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact qRes_le Δ v hΔ hv hB hbw ht j
  have h1 := hpad i.succ
  have h2 := qRes_le Δ v hΔ hv hB hbw ht i
  have h3 : Cpad δ s Δ v B z i.castSucc = Cj δ s Δ v B z i := by unfold Cpad; rw [Fin.snoc_castSucc]
  unfold Gco
  rw [h3]
  exact (abs_sub _ _).trans (by linarith)

/-- `Σ G_i² r_i²/2 ≤ ε^+` with `r_i = h_i/2`. -/
theorem G_sum_le {δ s : ℝ} (M : ℕ) (Δ v : Fin m → ℝ) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j)
    {B : Box} (hB : B.Valid) {b w : ℝ} (hbw : B.Mem (b, w)) {z : Fin m → ℕ} {t : Fin m → ℝ}
    (ht : InCl δ s z t) :
    ∑ i, Gco Δ v b w (Real.log s) t i ^ 2 * (hP δ M z i.succ / 2) ^ 2 / 2 ≤
      epsPlus δ s M Δ v B z := by
  unfold epsPlus
  refine Finset.sum_le_sum fun i _ => ?_
  have h := Gco_le Δ v hΔ hv hB hbw ht i
  have hsq : Gco Δ v b w (Real.log s) t i ^ 2 ≤
      (Cpad δ s Δ v B z i.castSucc + Cpad δ s Δ v B z i.succ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have := sq_nonneg (hP δ M z i.succ / 2)
  nlinarith

/-- On the subcell, `H(u) ≤ ε^−`. -/
theorem quadT_le {δ : ℝ} (M : ℕ) {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) {B : Box} (hB : B.Valid)
    {w : ℝ} (hw : B.wL ≤ w) (z : Fin m → ℕ) (hh : ∀ k, 0 ≤ hP δ M z k) {u : Fin m → ℝ}
    (hu : ∀ i, |u i| ≤ hP δ M z i.succ / 2) : quadT v w u ≤ epsMinus δ M v B z := by
  have hc : ∀ k : Fin (m + 1), |(Fin.cons 0 u : Fin (m + 1) → ℝ) k| ≤ hP δ M z k / 2 := fun k => by
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero, abs_zero]; have := hh 0; linarith
    · rw [Fin.cons_succ]; exact hu j
  unfold quadT epsMinus
  refine Finset.sum_le_sum fun j _ => ?_
  have hvj := hv j
  have hwL := hB.2.1
  have hD : |Dinc u j| ≤ hP δ M z j.castSucc / 2 + hP δ M z j.succ / 2 := by
    unfold Dinc inc
    have := abs_sub ((Fin.cons 0 u : Fin (m + 1) → ℝ) j.succ) ((Fin.cons 0 u : Fin (m + 1) → ℝ) j.castSucc)
    linarith [hc j.succ, hc j.castSucc]
  have hsq : Dinc u j ^ 2 ≤ (hP δ M z j.castSucc / 2 + hP δ M z j.succ / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hD 2
  calc Dinc u j ^ 2 / (2 * (w * v j))
      ≤ (hP δ M z j.castSucc / 2 + hP δ M z j.succ / 2) ^ 2 / (2 * (w * v j)) :=
        div_le_div_of_nonneg_right hsq (by have := hwL.trans_le hw; positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_right hw hvj.le])

end Novel.D19CenteredQuadrature
