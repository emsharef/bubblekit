import Novel.D19CenteredQuadratureShear
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Claim 038: one tensor subcell

On a box `t ± r` of log-price paths, with `y = t + u`:
* (6): `log P(t + u) − log P(t) = Lin(u) − H(u)` (`pdens_shift`), with `Lin` linear in `u` and
  `H(u) = Σ_j (u_j − u_(j−1))²/(2wv_j)` (`u_0 = 0`), so `Lin(−u) = −Lin(u)` and `H(−u) = H(u)`.
* The lower bound (`box_lower`): the reflection `y ↦ 2t − y` preserves the box and Lebesgue measure,
  and `e^a + e^(−a) ≥ 2`, so the integral is at least `e^(−sup H) P(t) vol`.
* The upper bound (`box_upper`): dropping `−H`, the exponential of `Lin(u) = Σ_i G_i u_i` is a
  product over the coordinates. Each coordinate's integral is at most `2r_i e^(G_i² r_i²/2)`, by the
  same reflection and Mathlib's `Real.cosh_le_exp_half_sq`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D19CenteredQuadrature

open Standalone.D19CenteredQuadrature Standalone.D19FilteredLikelihood Standalone.D19CondSensitivity
  Novel.D19CondSensitivity

/-- Fubini for a product of one-variable functions, as a lower integral. -/
theorem lintegral_fin_prod {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e := measurePreserving_piFinSuccAbove μ 0
    rw [← e.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    rw [lintegral_prod_mul (f := f 0) (g := fun x : Fin n → ℝ => ∏ i, f i.succ (x i))
      (hf 0).aemeasurable (Finset.measurable_prod _ fun (i : Fin n) _ =>
        (hf i.succ).comp (measurable_pi_apply i)).aemeasurable,
      ih (fun i => μ i.succ) (fun i => f i.succ) fun i => hf i.succ]

variable {m : ℕ}

theorem lintegral_box_prod (t r : Fin m → ℝ) (f : Fin m → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ y in Icc (t - r) (t + r), ∏ i, f i (y i) =
      ∏ i, ∫⁻ x in Icc (t i - r i) (t i + r i), f i x := by
  rw [← pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  exact lintegral_fin_prod _ f hf

theorem reflect_preimage (t r : Fin m → ℝ) :
    (fun y => (t + t) + -y) ⁻¹' Icc (t - r) (t + r) = Icc (t - r) (t + r) := by
  ext y
  simp only [mem_preimage, mem_Icc, Pi.le_def, Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun i => by linarith [h1 i, h2 i], fun i => by linarith [h1 i, h2 i]⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun i => by linarith [h1 i, h2 i], fun i => by linarith [h1 i, h2 i]⟩

/-- The reflection `y ↦ 2t − y` of the box. -/
theorem lintegral_reflect (t r : Fin m → ℝ) {f : (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in Icc (t - r) (t + r), f ((t + t) + -y) = ∫⁻ y in Icc (t - r) (t + r), f y := by
  have hp := (measurePreserving_add_left (volume : Measure (Fin m → ℝ)) (t + t)).comp
    (Measure.measurePreserving_neg (volume : Measure (Fin m → ℝ)))
  have h := hp.setLIntegral_comp_preimage (measurableSet_Icc (a := t - r) (b := t + r)) hf
  rw [show ((fun x => (t + t) + x) ∘ Neg.neg : (Fin m → ℝ) → Fin m → ℝ) = fun y => (t + t) + -y from rfl,
    reflect_preimage] at h
  exact h

theorem lintegral_reflect₁ (c r : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in Icc (c - r) (c + r), f ((c + c) + -x) = ∫⁻ x in Icc (c - r) (c + r), f x := by
  have hp := (measurePreserving_add_left (volume : Measure ℝ) (c + c)).comp
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  have h := hp.setLIntegral_comp_preimage (measurableSet_Icc (a := c - r) (b := c + r)) hf
  have hpre : (fun x => (c + c) + -x) ⁻¹' Icc (c - r) (c + r) = Icc (c - r) (c + r) := by
    ext x; simp only [mem_preimage, mem_Icc]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [show ((fun x => (c + c) + x) ∘ Neg.neg : ℝ → ℝ) = fun x => (c + c) + -x from rfl, hpre] at h
  exact h

theorem two_le_exp_add_exp_neg (a : ℝ) : 2 ≤ Real.exp a + Real.exp (-a) := by
  have := Real.one_le_cosh a
  rw [Real.cosh_eq] at this
  linarith

/-- One coordinate of the upper bound: `∫_(c−r)^(c+r) e^(g(x−c)) dx ≤ 2r e^(g²r²/2)`. -/
theorem lintegral_exp_lin (c g r : ℝ) :
    ∫⁻ x in Icc (c - r) (c + r), ENNReal.ofReal (Real.exp (g * (x - c))) ≤
      ENNReal.ofReal (Real.exp (g ^ 2 * r ^ 2 / 2)) * ENNReal.ofReal (2 * r) := by
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (g * (x - c))) := by fun_prop
  have hrefl := lintegral_reflect₁ c r hmeas
  have hneg : ∀ x : ℝ, g * ((c + c) + -x - c) = -(g * (x - c)) := fun x => by ring
  simp only [hneg] at hrefl
  set I := ∫⁻ x in Icc (c - r) (c + r), ENNReal.ofReal (Real.exp (g * (x - c)))
  have hsum : I + I ≤ 2 * (ENNReal.ofReal (Real.exp (g ^ 2 * r ^ 2 / 2)) * ENNReal.ofReal (2 * r)) := by
    calc I + I = ∫⁻ x in Icc (c - r) (c + r), (ENNReal.ofReal (Real.exp (g * (x - c))) +
          ENNReal.ofReal (Real.exp (-(g * (x - c))))) := by
          rw [lintegral_add_left hmeas]; nth_rw 2 [← hrefl]
      _ ≤ ∫⁻ _x in Icc (c - r) (c + r), 2 * ENNReal.ofReal (Real.exp (g ^ 2 * r ^ 2 / 2)) := by
          refine setLIntegral_mono' measurableSet_Icc fun x hx => ?_
          rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
            show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hx' : (x - c) ^ 2 ≤ r ^ 2 := sq_le_sq' (by linarith [hx.1]) (by linarith [hx.2])
          have hc := Real.cosh_le_exp_half_sq (g * (x - c))
          rw [Real.cosh_eq] at hc
          have hmono : Real.exp ((g * (x - c)) ^ 2 / 2) ≤ Real.exp (g ^ 2 * r ^ 2 / 2) :=
            Real.exp_le_exp.2 (by rw [mul_pow]; have := sq_nonneg g; nlinarith)
          linarith
      _ = 2 * (ENNReal.ofReal (Real.exp (g ^ 2 * r ^ 2 / 2)) * ENNReal.ofReal (2 * r)) := by
          rw [setLIntegral_const, Real.volume_Icc, mul_assoc]; congr 3; ring
  rw [← two_mul] at hsum
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 hsum

/-! ## The expansion (6) -/

/-- The increments `u_j − u_(j−1)` of a displacement, with `u_0 = 0`. -/
noncomputable def Dinc (u : Fin m → ℝ) : Fin m → ℝ := inc (Fin.cons 0 u)

/-- The residuals `e_j = t_j − t_(j−1) − bΔ_j + wv_j/2` of a path `(c, t)`. -/
noncomputable def eRes (Δ v : Fin m → ℝ) (b w c : ℝ) (t : Fin m → ℝ) : Fin m → ℝ :=
  fun j => inc (Fin.cons c t) j - (b * Δ j - w * v j / 2)

/-- The linear term of (6). -/
noncomputable def linT (Δ v : Fin m → ℝ) (b w c : ℝ) (t u : Fin m → ℝ) : ℝ :=
  -∑ j, eRes Δ v b w c t j * Dinc u j / (w * v j)

/-- `H(u)` of (6). -/
noncomputable def quadT (v : Fin m → ℝ) (w : ℝ) (u : Fin m → ℝ) : ℝ :=
  ∑ j, Dinc u j ^ 2 / (2 * (w * v j))

theorem cons_add (c : ℝ) (t u : Fin m → ℝ) :
    (Fin.cons c (t + u) : Fin (m + 1) → ℝ) = Fin.cons c t + Fin.cons 0 u := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem inc_add (Y Y' : Fin (m + 1) → ℝ) : inc (Y + Y') = inc Y + inc Y' := by
  funext j; simp only [inc, Pi.add_apply]; ring

theorem cons_neg (u : Fin m → ℝ) : (Fin.cons 0 (-u) : Fin (m + 1) → ℝ) = -Fin.cons 0 u := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem Dinc_neg (u : Fin m → ℝ) : Dinc (-u) = -Dinc u := by
  unfold Dinc
  rw [cons_neg]
  funext j; simp only [inc, Pi.neg_apply]; ring

theorem quadT_nonneg {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) {w : ℝ} (hw : 0 < w) (u : Fin m → ℝ) :
    0 ≤ quadT v w u :=
  Finset.sum_nonneg fun j _ => by have := hv j; positivity

theorem pdens_shift (Δ : Fin m → ℝ) {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) (b : ℝ) {w : ℝ} (hw : 0 < w)
    (c : ℝ) (t u : Fin m → ℝ) :
    pdens Δ v b w c (t + u) = pdens Δ v b w c t * Real.exp (linT Δ v b w c t u - quadT v w u) := by
  unfold pdens
  rw [← Real.exp_add]
  congr 1
  rw [cons_add, inc_add]
  unfold ll lphi linT quadT
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hwv : 0 < w * v j := mul_pos hw (hv j)
  simp only [Pi.add_apply, eRes, Dinc]
  field_simp
  ring

theorem linT_neg (Δ v : Fin m → ℝ) (b w c : ℝ) (t u : Fin m → ℝ) :
    linT Δ v b w c t (-u) = -linT Δ v b w c t u := by
  unfold linT; rw [Dinc_neg]
  simp only [Pi.neg_apply, mul_neg, neg_div, Finset.sum_neg_distrib, neg_neg]

theorem quadT_neg (v : Fin m → ℝ) (w : ℝ) (u : Fin m → ℝ) : quadT v w (-u) = quadT v w u := by
  unfold quadT; rw [Dinc_neg]; simp only [Pi.neg_apply, neg_sq]

theorem pdens_nonneg (Δ v : Fin m → ℝ) (b w c : ℝ) (y : Fin m → ℝ) : 0 ≤ pdens Δ v b w c y :=
  (Real.exp_pos _).le

theorem measurable_pdens' (Δ v : Fin m → ℝ) (b w c : ℝ) :
    Measurable fun y => ENNReal.ofReal (pdens Δ v b w c y) :=
  (continuous_pdens Δ v b w c).measurable.ennreal_ofReal

theorem near_of_mem_Icc {t r y : Fin m → ℝ} (hy : y ∈ Icc (t - r) (t + r)) (i : Fin m) :
    |(y - t) i| ≤ r i := by
  have h1 := hy.1 i; have h2 := hy.2 i
  simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 ⊢
  rw [abs_le]; constructor <;> linarith

/-- The lower bound on one box: `e^(−ε) P(t) vol ≤ ∫_box P`, if `H ≤ ε` on the box. -/
theorem box_lower (Δ : Fin m → ℝ) {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) (b : ℝ) {w : ℝ} (hw : 0 < w)
    (c : ℝ) (t r : Fin m → ℝ) {ε : ℝ} (hH : ∀ u, (∀ i, |u i| ≤ r i) → quadT v w u ≤ ε) :
    ENNReal.ofReal (pdens Δ v b w c t * Real.exp (-ε)) * volume (Icc (t - r) (t + r)) ≤
      ∫⁻ y in Icc (t - r) (t + r), ENNReal.ofReal (pdens Δ v b w c y) := by
  have hF := measurable_pdens' Δ v b w c
  have hrefl := lintegral_reflect t r hF
  set I := ∫⁻ y in Icc (t - r) (t + r), ENNReal.ofReal (pdens Δ v b w c y)
  have hP := pdens_nonneg Δ v b w c t
  have hsum : 2 * (ENNReal.ofReal (pdens Δ v b w c t * Real.exp (-ε)) *
      volume (Icc (t - r) (t + r))) ≤ I + I := by
    calc 2 * (ENNReal.ofReal (pdens Δ v b w c t * Real.exp (-ε)) * volume (Icc (t - r) (t + r)))
        = ∫⁻ _y in Icc (t - r) (t + r), 2 * ENNReal.ofReal (pdens Δ v b w c t * Real.exp (-ε)) := by
          rw [setLIntegral_const, mul_assoc]
      _ ≤ ∫⁻ y in Icc (t - r) (t + r), (ENNReal.ofReal (pdens Δ v b w c y) +
            ENNReal.ofReal (pdens Δ v b w c ((t + t) + -y))) := by
          refine setLIntegral_mono' measurableSet_Icc fun y hy => ?_
          set u := y - t
          have hyu : y = t + u := by simp [u]
          have hyu' : (t + t) + -y = t + -u := by simp only [u]; abel
          have hHu := hH u (near_of_mem_Icc hy)
          rw [hyu', hyu, pdens_shift Δ hv b hw, pdens_shift Δ hv b hw, linT_neg, quadT_neg,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          set L := linT Δ v b w c t u
          set H := quadT v w u
          have h2 := two_le_exp_add_exp_neg L
          have he : Real.exp (-ε) ≤ Real.exp (-H) := Real.exp_le_exp.2 (by linarith)
          have hsplit : pdens Δ v b w c t * Real.exp (L - H) + pdens Δ v b w c t * Real.exp (-L - H) =
              pdens Δ v b w c t * Real.exp (-H) * (Real.exp L + Real.exp (-L)) := by
            rw [sub_eq_add_neg, sub_eq_add_neg, Real.exp_add, Real.exp_add]; ring
          rw [hsplit]
          calc 2 * (pdens Δ v b w c t * Real.exp (-ε)) ≤ 2 * (pdens Δ v b w c t * Real.exp (-H)) := by
                gcongr
            _ ≤ pdens Δ v b w c t * Real.exp (-H) * (Real.exp L + Real.exp (-L)) := by
                have : 0 ≤ pdens Δ v b w c t * Real.exp (-H) := by positivity
                nlinarith
      _ = I + I := by
          rw [lintegral_add_left hF, hrefl]
  rw [← two_mul] at hsum
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 hsum

/-- The upper bound on one box: `∫_box P ≤ e^(Σ G_i² r_i²/2) P(t) vol`, if `Lin(u) = Σ G_i u_i`. -/
theorem box_upper (Δ : Fin m → ℝ) {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) (b : ℝ) {w : ℝ} (hw : 0 < w)
    (c : ℝ) (t r : Fin m → ℝ) (G : Fin m → ℝ)
    (hG : ∀ u, linT Δ v b w c t u = ∑ i, G i * u i) :
    ∫⁻ y in Icc (t - r) (t + r), ENNReal.ofReal (pdens Δ v b w c y) ≤
      ENNReal.ofReal (pdens Δ v b w c t * Real.exp (∑ i, G i ^ 2 * r i ^ 2 / 2)) *
        volume (Icc (t - r) (t + r)) := by
  have hP := pdens_nonneg Δ v b w c t
  have hmeas : ∀ i, Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (G i * (x - t i))) :=
    fun i => by fun_prop
  calc ∫⁻ y in Icc (t - r) (t + r), ENNReal.ofReal (pdens Δ v b w c y)
      ≤ ∫⁻ y in Icc (t - r) (t + r), ENNReal.ofReal (pdens Δ v b w c t) *
          ∏ i, ENNReal.ofReal (Real.exp (G i * (y i - t i))) := by
        refine setLIntegral_mono' measurableSet_Icc fun y _ => ?_
        have hs := pdens_shift Δ hv b hw c t (y - t)
        rw [add_sub_cancel] at hs
        rw [hs, ← ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul hP, ← Real.exp_sum]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hP)
        rw [hG]
        have := quadT_nonneg hv hw (y - t)
        simp only [Pi.sub_apply] at this ⊢
        linarith
    _ = ENNReal.ofReal (pdens Δ v b w c t) *
          ∏ i, ∫⁻ x in Icc (t i - r i) (t i + r i), ENNReal.ofReal (Real.exp (G i * (x - t i))) := by
        rw [lintegral_const_mul (ENNReal.ofReal (pdens Δ v b w c t))
          (f := fun y : Fin m → ℝ => ∏ i, ENNReal.ofReal (Real.exp (G i * (y i - t i))))
          (Finset.measurable_prod _ fun (i : Fin m) _ => (hmeas i).comp (measurable_pi_apply i)),
          lintegral_box_prod t r _ hmeas]
    _ ≤ ENNReal.ofReal (pdens Δ v b w c t) *
          ∏ i, (ENNReal.ofReal (Real.exp (G i ^ 2 * r i ^ 2 / 2)) * ENNReal.ofReal (2 * r i)) := by
        gcongr with i
        exact lintegral_exp_lin (t i) (G i) (r i)
    _ = _ := by
        rw [Finset.prod_mul_distrib, Real.volume_Icc_pi, ← mul_assoc,
          ← ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le, ← Real.exp_sum,
          ← ENNReal.ofReal_mul hP]
        congr 2
        funext i
        simp only [Pi.add_apply, Pi.sub_apply]
        ring_nf

end Novel.D19CenteredQuadrature
