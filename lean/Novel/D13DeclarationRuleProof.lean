import Standalone.D13Declaration
import Novel.D14GaussianProof
import Novel.D13DriftRectProfileProof

/-!
# Claim 058, part 3: proof of the earlier likelihood rectangle

Proves `Standalone.D13Declaration.rule` (`rule_holds`).
* **(12).** The log of the product Normal density is a sum of logs, and the weighted residual
  identity `Σ (z_j − m d_j)²/d_j = Q + τ(a − m)²` gives (12).
* **The variance roots.** `H^var` has derivative `(Q − n w)/(2w²)`, so it is strictly increasing up
  to `Q/n` and strictly decreasing after (`strictMonoOn_of_deriv_pos`). Explicit points below `L`
  on each side, and the intermediate value theorem, give the roots, and the variance set is
  `[w₋, w₊]`. `L < H^max` because `q` is a family member and `δ < 1`.
* **Containment.** (12) bounds the drift deviation by `M`.
* **Measurability.** On `Q > 0`, `w₋ < t` iff some rational `r < t` lies in the variance set, which
  is a countable union of Borel sets (`measurable_of_Iio`). Similarly for `w₊`.
* **(10).** The non-retained event lies in `{h_true < δ q}`, whose mass is at most `∫ δ q = δ`.
* **`n ≥ 2`.** `Q = 0` forces `z ∈ ℝ d`, a proper subspace, which is Lebesgue-null.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal

namespace Novel.D13DeclarationRule

open Standalone.D13Declaration Standalone.D14Misspecification

variable {n : ℕ} {d : Fin n → ℝ}

theorem tau_pos (hn : 0 < n) (hd : ∀ j, 0 < d j) : 0 < tauD d :=
  Finset.sum_pos (fun j _ => hd j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- The weighted residual identity. -/
theorem resid (hn : 0 < n) (hd : ∀ j, 0 < d j) (z : Fin n → ℝ) (m : ℝ) :
    ∑ j, (z j - m * d j) ^ 2 / d j = QD d z + tauD d * (aD d z - m) ^ 2 := by
  have hτ := tau_pos hn hd
  have hterm : ∀ j, (z j - m * d j) ^ 2 / d j = (z j - aD d z * d j) ^ 2 / d j +
      2 * (aD d z - m) * (z j - aD d z * d j) + (aD d z - m) ^ 2 * d j := fun j => by
    have := (hd j).ne'
    field_simp; ring
  have hsum0 : ∑ j, (z j - aD d z * d j) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    show ∑ j, z j - (∑ j, z j) / tauD d * tauD d = 0
    rw [div_mul_cancel₀ _ hτ.ne', sub_self]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum0,
    mul_zero, add_zero]
  unfold QD tauD; ring

/-- (12): the log density. -/
theorem log_densR (hn : 0 < n) (hd : ∀ j, 0 < d j) (z : Fin n → ℝ) (b : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Real.log (densR d b κ z) =
      Hvar d z (κ ^ 2) - tauD d * (aD d z - b + κ ^ 2 / 2) ^ 2 / (2 * κ ^ 2) := by
  have hw : 0 < κ ^ 2 := by positivity
  have hv : ∀ j, ((κ ^ 2 * d j).toNNReal : ℝ) = κ ^ 2 * d j := fun j =>
    Real.coe_toNNReal _ (mul_pos hw (hd j)).le
  have hfac : ∀ j, gaussianPDFReal ((b - κ ^ 2 / 2) * d j) (κ ^ 2 * d j).toNNReal (z j) ≠ 0 :=
    fun j => (gaussianPDFReal_pos _ _ _ (Novel.D14Gaussian.var_ne (hd j) hκ)).ne'
  have hlog : ∀ j, Real.log (gaussianPDFReal ((b - κ ^ 2 / 2) * d j) (κ ^ 2 * d j).toNNReal (z j)) =
      -(1 / 2) * Real.log (2 * π) - (1 / 2) * Real.log (κ ^ 2) - (1 / 2) * Real.log (d j) -
        (z j - (b - κ ^ 2 / 2) * d j) ^ 2 / d j / (2 * κ ^ 2) := fun j => by
    have hdj := hd j
    rw [gaussianPDFReal, hv, Real.log_mul (inv_ne_zero (Real.sqrt_pos.2 (by positivity)).ne')
      (Real.exp_pos _).ne', Real.log_inv, Real.log_exp, Real.log_sqrt (by positivity),
      Real.log_mul (by positivity : (2 * π) ≠ 0) (mul_pos hw hdj).ne', Real.log_mul hw.ne' hdj.ne']
    field_simp
    ring
  unfold densR
  rw [Real.log_prod (fun j _ => hfac j)]
  simp_rw [hlog]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, resid hn hd z]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold Hvar CD
  rw [← Finset.mul_sum]
  field_simp
  ring


/-! ## The variance profile -/

section Roots

theorem Hvar_deriv (z : Fin n → ℝ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (Hvar d z) ((QD d z - n * w) / (2 * w ^ 2)) w := by
  have h := (Novel.D13DriftRect.hasDeriv_fam (n : ℝ) (QD d z) 0 hw).const_add (CD d)
  have hf : (fun w => CD d + (-((n : ℝ) / 2) * Real.log w - QD d z / (2 * w) - 0 * w)) = Hvar d z := by
    funext w; unfold Hvar; ring
  rw [hf] at h
  convert h using 1; ring

theorem Hvar_cont (z : Fin n → ℝ) : ContinuousOn (Hvar d z) (Ioi 0) := fun w hw =>
  (Hvar_deriv z hw).continuousAt.continuousWithinAt

theorem Hvar_mono (hn : 0 < n) (z : Fin n → ℝ) :
    StrictMonoOn (Hvar d z) (Ioc 0 (QD d z / n)) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine strictMonoOn_of_deriv_pos (convex_Ioc _ _) ((Hvar_cont z).mono fun w hw => hw.1)
    fun w hw => ?_
  rw [interior_Ioc] at hw
  rw [(Hvar_deriv z hw.1).deriv]
  have : n * w < QD d z := by have := hw.2; rw [lt_div_iff₀ hnr] at this; linarith
  have := hw.1
  apply div_pos (by linarith) (by positivity)

theorem Hvar_anti (hn : 0 < n) (z : Fin n → ℝ) (hQ : 0 < QD d z) :
    StrictAntiOn (Hvar d z) (Ici (QD d z / n)) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hp : 0 < QD d z / n := div_pos hQ hnr
  refine strictAntiOn_of_deriv_neg (convex_Ici _)
    ((Hvar_cont z).mono fun w hw => hp.trans_le hw) fun w hw => ?_
  rw [interior_Ici] at hw
  have hw0 : 0 < w := hp.trans hw
  rw [(Hvar_deriv z hw0).deriv]
  have : QD d z < n * w := by have h' : QD d z / n < w := hw; rw [div_lt_iff₀ hnr] at h'; linarith
  apply div_neg_of_neg_of_pos (by linarith) (by positivity)

theorem Hvar_le_max (hn : 0 < n) (z : Fin n → ℝ) (hQ : 0 < QD d z) {w : ℝ} (hw : 0 < w) :
    Hvar d z w ≤ Hvar d z (QD d z / n) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hp : 0 < QD d z / n := div_pos hQ hnr
  rcases le_total w (QD d z / n) with h | h
  · exact (Hvar_mono hn z).monotoneOn ⟨hw, h⟩ ⟨hp, le_rfl⟩ h
  · exact (Hvar_anti hn z hQ).antitoneOn (le_refl (QD d z / n)) h h

variable {b0 κ0 δ : ℝ}

theorem L_lt_max (hn : 0 < n) (hd : ∀ j, 0 < d j) (hκ0 : 0 < κ0) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (z : Fin n → ℝ) (hQ : 0 < QD d z) : Ldec d b0 κ0 δ z < Hvar d z (QD d z / n) := by
  have hl := log_densR hn hd z b0 hκ0
  have hτ := tau_pos hn hd
  have h1 : Real.log (densR d b0 κ0 z) ≤ Hvar d z (κ0 ^ 2) := by
    rw [hl]; have : 0 ≤ tauD d * (aD d z - b0 + κ0 ^ 2 / 2) ^ 2 / (2 * κ0 ^ 2) := by positivity
    linarith
  have h2 := Hvar_le_max hn z hQ (by positivity : 0 < κ0 ^ 2)
  have h3 : Real.log δ < 0 := Real.log_neg hδ0 hδ1
  unfold Ldec; linarith

/-- A variance below `Q/n` with profile below `L`. -/
theorem left_pt (hn : 0 < n) (z : Fin n → ℝ) (hQ : 0 < QD d z) (L : ℝ) :
    ∃ w, 0 < w ∧ w < QD d z / n ∧ Hvar d z w < L := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hp : 0 < QD d z / n := div_pos hQ hnr
  set K := |L - CD d| + 1
  set t := 2 * (n + K) / QD d z + 1 / Real.sqrt (QD d z / n) + 1 with ht
  have hK : 0 < K := by positivity
  have hsp := Real.sqrt_pos.2 hp
  have ht1 : 1 ≤ t := by have : 0 ≤ 2 * (n + K) / QD d z + 1 / Real.sqrt (QD d z / n) := by positivity
                         linarith
  have ht0 : 0 < t := by linarith
  refine ⟨1 / t ^ 2, by positivity, ?_, ?_⟩
  · have : 1 / Real.sqrt (QD d z / n) < t := by
      have : 0 ≤ 2 * (n + K) / QD d z := by positivity
      linarith
    rw [div_lt_iff₀ hsp] at this
    rw [div_lt_iff₀ (by positivity)]
    have h2 : (Real.sqrt (QD d z / n)) ^ 2 = QD d z / n := Real.sq_sqrt hp.le
    nlinarith
  · unfold Hvar
    have hlog : Real.log (1 / t ^ 2) = -(2 * Real.log t) := by
      rw [one_div, Real.log_inv, Real.log_pow]; push_cast; ring
    have hlt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht0
    have hq : QD d z / (2 * (1 / t ^ 2)) = QD d z * t ^ 2 / 2 := by field_simp
    rw [hlog, hq]
    have hbig : (n + K) * t ≤ QD d z * t ^ 2 / 2 := by
      have : 2 * (n + K) / QD d z ≤ t := by
        have : 0 ≤ 1 / Real.sqrt (QD d z / n) := by positivity
        linarith
      rw [div_le_iff₀ hQ] at this
      nlinarith
    have hKL : CD d - K < L := by
      have := le_abs_self (L - CD d); have := neg_abs_le (L - CD d); linarith
    nlinarith

/-- A variance above `Q/n` with profile below `L`. -/
theorem right_pt (hn : 0 < n) (z : Fin n → ℝ) (hQ : 0 < QD d z) (L : ℝ) :
    ∃ w, QD d z / n < w ∧ Hvar d z w < L := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set K := |L - CD d| + 1
  set w := max (QD d z / n + 1) (Real.exp (2 * K / n))
  have hw0 : 0 < w := lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  refine ⟨w, lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  have hlog : 2 * K / n ≤ Real.log w := by
    rw [Real.le_log_iff_exp_le hw0]; exact le_max_right _ _
  have hlog' : K ≤ (n : ℝ) / 2 * Real.log w := by
    rw [div_le_iff₀ hnr] at hlog; nlinarith
  have hq : 0 ≤ QD d z / (2 * w) := by positivity
  have hKL : CD d - K < L := by
    have := le_abs_self (L - CD d); have := neg_abs_le (L - CD d); linarith
  unfold Hvar; nlinarith

end Roots

/-! ## The roots, containment and the rectangle -/

section Rect

variable {b0 κ0 δ : ℝ}

theorem QD_nonneg (hd : ∀ j, 0 < d j) (z : Fin n → ℝ) : 0 ≤ QD d z :=
  Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hd j).le

theorem densR_pos (hd : ∀ j, 0 < d j) {b κ : ℝ} (hκ : 0 < κ) (z : Fin n → ℝ) : 0 < densR d b κ z :=
  Finset.prod_pos fun j _ => gaussianPDFReal_pos _ _ _ (Novel.D14Gaussian.var_ne (hd j) hκ)

theorem roots (hn : 0 < n) (hd : ∀ j, 0 < d j) (hκ0 : 0 < κ0) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (z : Fin n → ℝ) (hQ : 0 < QD d z) :
    0 < wlo d b0 κ0 δ z ∧ wlo d b0 κ0 δ z < QD d z / n ∧ QD d z / n < whi d b0 κ0 δ z ∧
      Hvar d z (wlo d b0 κ0 δ z) = Ldec d b0 κ0 δ z ∧
      Hvar d z (whi d b0 κ0 δ z) = Ldec d b0 κ0 δ z ∧
      ∀ w, 0 < w → (Ldec d b0 κ0 δ z ≤ Hvar d z w ↔ w ∈ Icc (wlo d b0 κ0 δ z) (whi d b0 κ0 δ z)) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set L := Ldec d b0 κ0 δ z
  set p := QD d z / n
  have hp : 0 < p := div_pos hQ hnr
  have hLm : L < Hvar d z p := L_lt_max hn hd hκ0 hδ0 hδ1 z hQ
  obtain ⟨w1, hw1, hw1p, hH1⟩ := left_pt hn z hQ L
  obtain ⟨w2, hw2p, hH2⟩ := right_pt hn z hQ L
  obtain ⟨r1, hr1I, hr1⟩ := intermediate_value_Icc hw1p.le
    ((Hvar_cont z).mono fun w hw => hw1.trans_le hw.1) ⟨hH1.le, hLm.le⟩
  obtain ⟨r2, hr2I, hr2⟩ := intermediate_value_Icc' hw2p.le
    ((Hvar_cont z).mono fun w hw => hp.trans_le hw.1) ⟨hH2.le, hLm.le⟩
  have hr10 : 0 < r1 := hw1.trans_le hr1I.1
  have hr1p : r1 < p := lt_of_le_of_ne hr1I.2 fun h => by rw [h] at hr1; linarith
  have hpr2 : p < r2 := lt_of_le_of_ne hr2I.1 fun h => by rw [← h] at hr2; linarith
  have hchar : ∀ w, 0 < w → (L ≤ Hvar d z w ↔ w ∈ Icc r1 r2) := by
    intro w hw
    constructor
    · intro hL
      by_contra hnot
      rcases not_and_or.1 hnot with h | h
      · push Not at h
        have := (Hvar_mono hn z) ⟨hw, h.le.trans hr1p.le⟩ ⟨hr10, hr1p.le⟩ h
        linarith
      · push Not at h
        have := (Hvar_anti hn z hQ) (show p ≤ r2 from hpr2.le) (show p ≤ w from hpr2.le.trans h.le) h
        linarith
    · rintro ⟨h1, h2⟩
      rcases le_total w p with h | h
      · have := (Hvar_mono hn z).monotoneOn ⟨hr10, hr1p.le⟩ ⟨hw, h⟩ h1; linarith
      · have := (Hvar_anti hn z hQ).antitoneOn h hpr2.le h2; linarith
  have hset : Wset d b0 κ0 δ z = Icc r1 r2 := by
    ext w
    exact ⟨fun hw => (hchar w hw.1).1 hw.2,
      fun hw => ⟨hr10.trans_le hw.1, (hchar w (hr10.trans_le hw.1)).2 hw⟩⟩
  have hlo : wlo d b0 κ0 δ z = r1 := by
    unfold wlo; rw [hset, csInf_Icc (hr1p.trans hpr2).le]
  have hhi : whi d b0 κ0 δ z = r2 := by
    unfold whi; rw [hset, csSup_Icc (hr1p.trans hpr2).le]
  rw [hlo, hhi]
  exact ⟨hr10, hr1p, hpr2, hr1, hr2, hchar⟩

theorem contain (hn : 0 < n) (hd : ∀ j, 0 < d j) (hκ0 : 0 < κ0) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (z : Fin n → ℝ) (hQ : 0 < QD d z) {b κ : ℝ} (hκ : 0 < κ)
    (hle : δ * densR d b0 κ0 z ≤ densR d b κ z) :
    b ∈ Icc (rbLo d b0 κ0 δ z) (rbHi d b0 κ0 δ z) ∧ κ ∈ Icc (rsLo d b0 κ0 δ z) (rsHi d b0 κ0 δ z) := by
  obtain ⟨hlo0, hlop, hphi, -, -, hchar⟩ := roots (b0 := b0) hn hd hκ0 hδ0 hδ1 z hQ
  have hτ := tau_pos hn hd
  have hq := densR_pos hd hκ0 (b := b0) z
  set w := κ ^ 2 with hwdef
  have hw : 0 < w := by positivity
  have hlog : Ldec d b0 κ0 δ z ≤ Real.log (densR d b κ z) := by
    unfold Ldec
    rw [← Real.log_mul hδ0.ne' hq.ne']
    exact Real.log_le_log (by positivity) hle
  rw [log_densR hn hd z b hκ] at hlog
  set T := tauD d * (aD d z - b + w / 2) ^ 2 / (2 * w)
  have hT : 0 ≤ T := by positivity
  have hwI := (hchar w hw).1 (by linarith)
  have hmax := Hvar_le_max hn z hQ hw
  set G := Hvar d z (QD d z / n) - Ldec d b0 κ0 δ z
  have hG : 0 ≤ G := by linarith
  have hsq : (aD d z - b + w / 2) ^ 2 ≤ 2 * whi d b0 κ0 δ z * G / tauD d := by
    have h1 : T ≤ G := by linarith
    have h2 : tauD d * (aD d z - b + w / 2) ^ 2 ≤ G * (2 * w) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * w)).1 h1; linarith
    rw [le_div_iff₀ hτ]
    nlinarith [mul_le_mul_of_nonneg_left hwI.2 hG]
  have habs : |aD d z - b + w / 2| ≤ Mdec d b0 κ0 δ z := Real.abs_le_sqrt hsq
  have hκs : Real.sqrt w = κ := by rw [hwdef, Real.sqrt_sq hκ.le]
  unfold rbLo rbHi rsLo rsHi
  simp only [hQ, ↓reduceIte]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have := (abs_le.1 habs).2; linarith [hwI.1]
  · have := (abs_le.1 habs).1; linarith [hwI.2]
  · rw [← hκs]; exact Real.sqrt_le_sqrt hwI.1
  · rw [← hκs]; exact Real.sqrt_le_sqrt hwI.2

theorem rect (hn : 0 < n) (hd : ∀ j, 0 < d j) (hκ0 : 0 < κ0) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (z : Fin n → ℝ) :
    rbLo d b0 κ0 δ z ≤ rbHi d b0 κ0 δ z ∧ 0 < rsLo d b0 κ0 δ z ∧
      rsLo d b0 κ0 δ z ≤ rsHi d b0 κ0 δ z := by
  unfold rbLo rbHi rsLo rsHi
  by_cases hQ : 0 < QD d z
  · obtain ⟨hlo0, hlop, hphi, -, -, -⟩ := roots (b0 := b0) hn hd hκ0 hδ0 hδ1 z hQ
    simp only [hQ, ↓reduceIte]
    have hM : 0 ≤ Mdec d b0 κ0 δ z := Real.sqrt_nonneg _
    exact ⟨by linarith, Real.sqrt_pos.2 hlo0, Real.sqrt_le_sqrt (hlop.trans hphi).le⟩
  · simp only [hQ, ↓reduceIte]
    norm_num

end Rect


/-! ## Measurability, coverage and the fallback event -/

section Meas

variable {b0 κ0 δ : ℝ}

theorem meas_aD : Measurable (aD d) :=
  (Finset.measurable_sum _ fun j _ => measurable_pi_apply j).div_const _

theorem meas_QD : Measurable (QD d) :=
  Finset.measurable_sum _ fun j _ =>
    (((measurable_pi_apply j).sub (meas_aD.mul_const _)).pow_const 2).div_const _

theorem meas_L : Measurable (Ldec d b0 κ0 δ) :=
  measurable_const.add (Real.measurable_log.comp Novel.D14Gaussian.densR_meas)

theorem meas_Hvar_const (w : ℝ) : Measurable fun z => Hvar d z w :=
  measurable_const.sub (meas_QD.div_const _)

theorem meas_Hmax : Measurable fun z => Hvar d z (QD d z / n) :=
  (measurable_const.sub (measurable_const.mul (Real.measurable_log.comp (meas_QD.div_const _)))).sub
    (meas_QD.div (measurable_const.mul (meas_QD.div_const _)))

theorem meas_member (r : ℝ) : MeasurableSet {z : Fin n → ℝ | 0 < r ∧ Ldec d b0 κ0 δ z ≤ Hvar d z r} :=
  (MeasurableSet.const _).inter (measurableSet_le meas_L (meas_Hvar_const r))

open Classical in
theorem meas_wlo (hn : 0 < n) (hd : ∀ j, 0 < d j) (hκ0 : 0 < κ0) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Measurable fun z => if 0 < QD d z then wlo d b0 κ0 δ z else 0 := by
  refine measurable_of_Iio fun t => ?_
  have hset : (fun z => if 0 < QD d z then wlo d b0 κ0 δ z else 0) ⁻¹' Iio t =
      ({z | 0 < QD d z} ∩ ⋃ r : ℚ, {z | (r : ℝ) < t ∧ 0 < (r : ℝ) ∧
        Ldec d b0 κ0 δ z ≤ Hvar d z r}) ∪ ({z | ¬ 0 < QD d z} ∩ {_z | (0 : ℝ) < t}) := by
    ext z
    by_cases hQ : 0 < QD d z
    · obtain ⟨hlo0, hlop, hphi, -, -, hchar⟩ := roots (b0 := b0) hn hd hκ0 hδ0 hδ1 z hQ
      simp only [mem_preimage, hQ, ↓reduceIte, mem_Iio, mem_union, mem_inter_iff, mem_ofPred_eq,
        true_and, mem_iUnion, not_true_eq_false, false_and, or_false]
      constructor
      · intro ht
        obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (lt_min ht (hlop.trans hphi))
        have hr0 : 0 < (r : ℝ) := hlo0.trans hr1
        exact ⟨r, (hr2.trans_le (min_le_left _ _)), hr0,
          (hchar r hr0).2 ⟨hr1.le, (hr2.trans_le (min_le_right _ _)).le⟩⟩
      · rintro ⟨r, hrt, hr0, hrL⟩
        exact ((hchar r hr0).1 hrL).1.trans_lt hrt
    · simp [hQ, not_lt.1 hQ]
  rw [hset]
  exact ((measurableSet_lt measurable_const meas_QD).inter
    (MeasurableSet.iUnion (ι := ℚ) fun r => (MeasurableSet.const _).inter (meas_member (r : ℝ)))).union
    ((measurableSet_lt measurable_const meas_QD).compl.inter (MeasurableSet.const _))

open Classical in
theorem meas_whi (hn : 0 < n) (hd : ∀ j, 0 < d j) (hκ0 : 0 < κ0) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Measurable fun z => if 0 < QD d z then whi d b0 κ0 δ z else 0 := by
  refine measurable_of_Ioi fun t => ?_
  have hset : (fun z => if 0 < QD d z then whi d b0 κ0 δ z else 0) ⁻¹' Ioi t =
      ({z | 0 < QD d z} ∩ ⋃ r : ℚ, {z | t < (r : ℝ) ∧ 0 < (r : ℝ) ∧
        Ldec d b0 κ0 δ z ≤ Hvar d z r}) ∪ ({z | ¬ 0 < QD d z} ∩ {_z | t < (0 : ℝ)}) := by
    ext z
    by_cases hQ : 0 < QD d z
    · obtain ⟨hlo0, hlop, hphi, -, -, hchar⟩ := roots (b0 := b0) hn hd hκ0 hδ0 hδ1 z hQ
      simp only [mem_preimage, hQ, ↓reduceIte, mem_Ioi, mem_union, mem_inter_iff, mem_ofPred_eq,
        true_and, mem_iUnion, not_true_eq_false, false_and, or_false]
      constructor
      · intro ht
        obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt ht (hlop.trans hphi))
        have hr0 : 0 < (r : ℝ) := hlo0.trans_le ((le_max_right _ _).trans hr1.le)
        exact ⟨r, (le_max_left _ _).trans_lt hr1, hr0,
          (hchar r hr0).2 ⟨((le_max_right _ _).trans hr1.le), hr2.le⟩⟩
      · rintro ⟨r, hrt, hr0, hrL⟩
        exact hrt.trans_le ((hchar r hr0).1 hrL).2
    · simp [hQ, not_lt.1 hQ]
  rw [hset]
  exact ((measurableSet_lt measurable_const meas_QD).inter
    (MeasurableSet.iUnion (ι := ℚ) fun r => (MeasurableSet.const _).inter (meas_member (r : ℝ)))).union
    ((measurableSet_lt measurable_const meas_QD).compl.inter (MeasurableSet.const _))

theorem meas_rule (hn : 0 < n) (hd : ∀ j, 0 < d j) (hκ0 : 0 < κ0) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Measurable (rbLo d b0 κ0 δ) ∧ Measurable (rbHi d b0 κ0 δ) ∧ Measurable (rsLo d b0 κ0 δ) ∧
      Measurable (rsHi d b0 κ0 δ) := by
  classical
  have hlo := meas_wlo (b0 := b0) hn hd hκ0 hδ0 hδ1
  have hhi := meas_whi (b0 := b0) hn hd hκ0 hδ0 hδ1
  set wl := fun z => if 0 < QD d z then wlo d b0 κ0 δ z else 0
  set wh := fun z => if 0 < QD d z then whi d b0 κ0 δ z else 0
  have hS : MeasurableSet {z : Fin n → ℝ | 0 < QD d z} := measurableSet_lt measurable_const meas_QD
  have hM : Measurable fun z => Real.sqrt (2 * wh z * (Hvar d z (QD d z / n) -
      Ldec d b0 κ0 δ z) / tauD d) :=
    (((measurable_const.mul hhi).mul (meas_Hmax.sub meas_L)).div_const _).sqrt
  have e1 : rbLo d b0 κ0 δ = fun z => if 0 < QD d z then aD d z + wl z / 2 -
      Real.sqrt (2 * wh z * (Hvar d z (QD d z / n) - Ldec d b0 κ0 δ z) / tauD d) else 0 := by
    funext z; unfold rbLo Mdec; by_cases h : 0 < QD d z <;> simp [h, wl, wh]
  have e2 : rbHi d b0 κ0 δ = fun z => if 0 < QD d z then aD d z + wh z / 2 +
      Real.sqrt (2 * wh z * (Hvar d z (QD d z / n) - Ldec d b0 κ0 δ z) / tauD d) else 0 := by
    funext z; unfold rbHi Mdec; by_cases h : 0 < QD d z <;> simp [h, wh]
  have e3 : rsLo d b0 κ0 δ = fun z => if 0 < QD d z then Real.sqrt (wl z) else 1 := by
    funext z; unfold rsLo; by_cases h : 0 < QD d z <;> simp [h, wl]
  have e4 : rsHi d b0 κ0 δ = fun z => if 0 < QD d z then Real.sqrt (wh z) else 1 := by
    funext z; unfold rsHi; by_cases h : 0 < QD d z <;> simp [h, wh]
  rw [e1, e2, e3, e4]
  exact ⟨Measurable.ite hS ((meas_aD.add (hlo.div_const 2)).sub hM) measurable_const,
    Measurable.ite hS ((meas_aD.add (hhi.div_const 2)).add hM) measurable_const,
    Measurable.ite hS hlo.sqrt measurable_const, Measurable.ite hS hhi.sqrt measurable_const⟩

theorem lawR_prob (b κ : ℝ) : IsProbabilityMeasure (lawR d b κ) := by
  unfold lawR; infer_instance

theorem coverage (hn : 0 < n) (hd : ∀ j, 0 < d j) (hκ0 : 0 < κ0) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {b κ : ℝ} (hκ : 0 < κ) :
    lawR d b κ {z | ¬ Retained d b0 κ0 δ b κ z} ≤ ENNReal.ofReal δ := by
  have hsub : {z | ¬ Retained d b0 κ0 δ b κ z} ⊆ {z | densR d b κ z < δ * densR d b0 κ0 z} := by
    intro z hz
    simp only [Retained, not_or, mem_ofPred_eq] at hz ⊢
    have hQ : 0 < QD d z := lt_of_le_of_ne (QD_nonneg hd z) (Ne.symm hz.1)
    by_contra hlt
    exact hz.2 (contain hn hd hκ0 hδ0 hδ1 z hQ hκ (not_lt.1 hlt))
  have hS : MeasurableSet {z | densR d b κ z < δ * densR d b0 κ0 z} :=
    measurableSet_lt Novel.D14Gaussian.densR_meas (Novel.D14Gaussian.densR_meas.const_mul _)
  refine (measure_mono hsub).trans ?_
  have := lawR_prob (d := d) b0 κ0
  rw [Novel.D14Gaussian.lawR_eq hd hκ, withDensity_apply _ hS]
  calc ∫⁻ z in {z | densR d b κ z < δ * densR d b0 κ0 z}, ENNReal.ofReal (densR d b κ z)
      ≤ ∫⁻ z in {z | densR d b κ z < δ * densR d b0 κ0 z}, ENNReal.ofReal (δ * densR d b0 κ0 z) :=
        setLIntegral_mono' hS fun z hz => ENNReal.ofReal_le_ofReal (le_of_lt hz)
    _ ≤ ∫⁻ z, ENNReal.ofReal (δ * densR d b0 κ0 z) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal δ * ∫⁻ z, ENNReal.ofReal (densR d b0 κ0 z) := by
        simp_rw [ENNReal.ofReal_mul hδ0.le]
        exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp Novel.D14Gaussian.densR_meas)
    _ = ENNReal.ofReal δ := by
        have h1 : ∫⁻ z, ENNReal.ofReal (densR d b0 κ0 z) = 1 := by
          have h := measure_univ (μ := lawR d b0 κ0)
          rwa [Novel.D14Gaussian.lawR_eq hd hκ0, withDensity_apply _ MeasurableSet.univ,
            Measure.restrict_univ] at h
        rw [h1, mul_one]

theorem fallback_null (hn : 2 ≤ n) (hd : ∀ j, 0 < d j) {b κ : ℝ} (hκ : 0 < κ) :
    lawR d b κ {z | QD d z = 0} = 0 := by
  have hsub : {z : Fin n → ℝ | QD d z = 0} ⊆ (Submodule.span ℝ {d} : Set (Fin n → ℝ)) := by
    intro z hz
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      div_nonneg (sq_nonneg (z j - aD d z * d j)) (hd j).le).1 hz
    have : z = aD d z • d := by
      funext j
      have := hzero j (Finset.mem_univ _)
      rw [div_eq_zero_iff, or_iff_left (hd j).ne', sq_eq_zero_iff, sub_eq_zero] at this
      simp [this]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have hne : Submodule.span ℝ {d} ≠ ⊤ := by
    intro h
    have hd0 : d ≠ 0 := fun h0 => by
      have := hd ⟨0, by omega⟩; rw [h0] at this; simp at this
    have h1 := finrank_span_singleton (K := ℝ) hd0
    rw [h, finrank_top, Module.finrank_fin_fun] at h1
    omega
  have hvol : (volume : Measure (Fin n → ℝ)) (Submodule.span ℝ {d} : Set (Fin n → ℝ)) = 0 :=
    Measure.addHaar_submodule volume _ hne
  rw [Novel.D14Gaussian.lawR_eq hd hκ]
  exact withDensity_absolutelyContinuous _ _ (measure_mono_null hsub hvol)

end Meas

theorem rule_holds : Standalone.D13Declaration.rule := by
  intro n d b0 κ0 δ hn hd hκ0 hδ0 hδ1
  obtain ⟨m1, m2, m3, m4⟩ := meas_rule (b0 := b0) hn hd hκ0 hδ0 hδ1
  exact ⟨fun z hQ => roots hn hd hκ0 hδ0 hδ1 z hQ, fun z b κ hκ => log_densR hn hd z b hκ,
    fun z hQ b κ hκ hle => contain hn hd hκ0 hδ0 hδ1 z hQ hκ hle,
    fun z => rect hn hd hκ0 hδ0 hδ1 z, m1, m2, m3, m4,
    measurableSet_eq_fun meas_QD measurable_const,
    fun b κ hκ => coverage hn hd hκ0 hδ0 hδ1 hκ, fun h2 b κ hκ => fallback_null h2 hd hκ⟩

end Novel.D13DeclarationRule
