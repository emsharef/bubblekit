import Standalone.D17ClockCells
import Novel.D14FixedTickProof

/-!
# Claim 034: the scale optimum (3)

For `0 < l < r`, `k(s) = Φ(r/s) − Φ(l/s)` increases in `s` below
`s₀ = √((r² − l²)/(2 log(r/l)))` and decreases above it. In the variable `t = log s`, the derivative
`e^{−t}(l φ(l e^{−t}) − r φ(r e^{−t}))` has the sign of `(r² − l²)e^{−2t} − 2 log(r/l)`. So claim 029's
`unimodal_real` gives the maximum over `[s_L, s_H]` at `s₀` clipped to that interval.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D17ClockCells

open Novel.GaussianCell

theorem φ_mul (x y : ℝ) : x * φ y = (Real.sqrt (2 * Real.pi))⁻¹ * (x * Real.exp (-y ^ 2 / 2)) := by
  rw [φ_eq]; ring

/-- `r φ(r u) ≤ l φ(l u)` exactly when `2 log(r/l) ≤ (r² − l²) u²`. -/
theorem φ_cmp {l r u : ℝ} (hl : 0 < l) (hr : 0 < r) :
    r * φ (r * u) ≤ l * φ (l * u) ↔ 2 * Real.log (r / l) ≤ (r ^ 2 - l ^ 2) * u ^ 2 := by
  have hc : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  rw [φ_mul, φ_mul, mul_le_mul_iff_of_pos_left hc,
    ← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul hr.ne' (by positivity),
    Real.log_mul hl.ne' (by positivity), Real.log_exp, Real.log_exp, Real.log_div hr.ne' hl.ne']
  constructor <;> intro h <;> nlinarith

/-- `l φ(l u) ≤ r φ(r u)` exactly when `(r² − l²) u² ≤ 2 log(r/l)`. -/
theorem φ_cmp' {l r u : ℝ} (hl : 0 < l) (hr : 0 < r) :
    l * φ (l * u) ≤ r * φ (r * u) ↔ (r ^ 2 - l ^ 2) * u ^ 2 ≤ 2 * Real.log (r / l) := by
  have hc : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  rw [φ_mul, φ_mul, mul_le_mul_iff_of_pos_left hc,
    ← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul hr.ne' (by positivity),
    Real.log_mul hl.ne' (by positivity), Real.log_exp, Real.log_exp, Real.log_div hr.ne' hl.ne']
  constructor <;> intro h <;> nlinarith

theorem log_ratio_pos {l r : ℝ} (hl : 0 < l) (hlr : l < r) : 0 < Real.log (r / l) :=
  Real.log_pos ((one_lt_div hl).2 hlr)

/-- The unclipped optimum. -/
noncomputable def s0 (l r : ℝ) : ℝ := Real.sqrt ((r ^ 2 - l ^ 2) / (2 * Real.log (r / l)))

theorem s0_pos {l r : ℝ} (hl : 0 < l) (hlr : l < r) : 0 < s0 l r := by
  have := log_ratio_pos hl hlr
  exact Real.sqrt_pos.2 (div_pos (by nlinarith) (by positivity))

theorem s0_sq {l r : ℝ} (hl : 0 < l) (hlr : l < r) :
    s0 l r ^ 2 = (r ^ 2 - l ^ 2) / (2 * Real.log (r / l)) := by
  have := log_ratio_pos hl hlr
  exact Real.sq_sqrt (div_nonneg (by nlinarith) (by positivity))

theorem log_clip {A B x : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hx : 0 < x) :
    min (Real.log B) (max (Real.log A) (Real.log x)) = Real.log (min B (max A x)) := by
  rcases le_total A x with h1 | h1
  · rw [max_eq_right (Real.log_le_log hA h1), max_eq_right h1]
    rcases le_total B x with h2 | h2
    · rw [min_eq_left (Real.log_le_log (hA.trans_le hAB) h2), min_eq_left h2]
    · rw [min_eq_right (Real.log_le_log hx h2), min_eq_right h2]
  · rw [max_eq_left (Real.log_le_log hx h1), max_eq_left h1,
      min_eq_right (Real.log_le_log hA hAB), min_eq_right hAB]

/-- (3): the scale maximum over `[s_L, s_H]` sits at the clipped optimum. -/
theorem scale_le {l r : ℝ} (hl : 0 < l) (hlr : l < r) {sL sH s : ℝ} (hsL : 0 < sL)
    (hsLH : sL ≤ sH) (hs : s ∈ Icc sL sH) :
    Φ (r / s) - Φ (l / s) ≤
      Φ (r / min sH (max sL (s0 l r))) - Φ (l / min sH (max sL (s0 l r))) := by
  have hr : 0 < r := hl.trans hlr
  set f : ℝ → ℝ := fun t => Φ (r * Real.exp (-t)) - Φ (l * Real.exp (-t))
  set f' : ℝ → ℝ := fun t => Real.exp (-t) * (l * φ (l * Real.exp (-t)) - r * φ (r * Real.exp (-t)))
  have hd : ∀ t, HasDerivAt f (f' t) t := fun t => by
    have he : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    have h1 := (hasDerivAt_Φ (r * Real.exp (-t))).comp t (he.const_mul r)
    have h2 := (hasDerivAt_Φ (l * Real.exp (-t))).comp t (he.const_mul l)
    refine (h1.sub h2).congr_deriv ?_
    simp only [f']; ring
  have hfs : ∀ x, 0 < x → f (Real.log x) = Φ (r / x) - Φ (l / x) := fun x hx => by
    simp only [f, Real.exp_neg, Real.exp_log hx, div_eq_mul_inv]
  have h0 := s0_pos hl hlr
  have hg := log_ratio_pos hl hlr
  have hid : ∀ t, (r ^ 2 - l ^ 2) * (Real.exp (-t)) ^ 2 =
      2 * Real.log (r / l) * (Real.exp (Real.log (s0 l r) - t)) ^ 2 := fun t => by
    have e : Real.exp (Real.log (s0 l r) - t) = s0 l r * Real.exp (-t) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log h0]
    rw [e, mul_pow, s0_sq hl hlr]
    field_simp
  have hup : ∀ t, t ≤ Real.log (s0 l r) → 0 ≤ f' t := fun t ht => by
    refine mul_nonneg (Real.exp_pos _).le (sub_nonneg.2 ((φ_cmp hl hr).2 ?_))
    rw [hid]
    have h1 : 1 ≤ Real.exp (Real.log (s0 l r) - t) := Real.one_le_exp (by linarith)
    have h2 : 1 ≤ Real.exp (Real.log (s0 l r) - t) ^ 2 := one_le_pow₀ h1
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * Real.log (r / l))]
  have hdown : ∀ t, Real.log (s0 l r) ≤ t → f' t ≤ 0 := fun t ht => by
    refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.2 ((φ_cmp' hl hr).2 ?_))
    rw [hid]
    have h1 : Real.exp (Real.log (s0 l r) - t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h3 : Real.exp (Real.log (s0 l r) - t) ^ 2 ≤ 1 := pow_le_one₀ (Real.exp_pos _).le h1
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * Real.log (r / l))]
  have hs0 : 0 < s := hsL.trans_le hs.1
  have := unimodal_real hd hup hdown (Real.log_le_log hsL hsLH)
    ⟨Real.log_le_log hsL hs.1, Real.log_le_log hs0 hs.2⟩
  rw [log_clip hsL hsLH (s0_pos hl hlr), hfs _ hs0, hfs _ (lt_min (hsL.trans_le hsLH)
    (lt_max_of_lt_left hsL))] at this
  exact this

end Novel.D17ClockCells
