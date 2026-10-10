import Novel.D23JointSwitchesNest

/-!
# Claim 070, (11): the calendar cost of free daily drifts on a segment

For the calendar shape, claim 033 gives `H = K = 0`, so on each day `gV(b, w) ≤ exp(φ_d(w))` with
`φ_d(w) = −(n_d/2) log(2πw) − c_d − Q_d/(2w)`, attained at that day's drift (`gV_cal_le`). Free daily
drifts with one common scale therefore have profile `max_w exp(Σ_d φ_d(w))`, attained at
`w = Q_within/N_I` (`PswSeg_val`); claim 033's common-drift profile on the concatenated segment has
the same form with the pooled `Q` (claim 068's `logDv_cal`). Their difference is (11).
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23JointSwitches

open Standalone.D23JointSwitches Standalone.D23DailyProfile Standalone.D17ClockDrift
  Standalone.D13DriftNull Standalone.CEVSupport Novel.D17ClockDrift Novel.D23DailyProfile

/-- One day's calendar profile in the scale. -/
noncomputable def phiC {m : ℕ} (Δ₁ : Fin m → ℝ) (y0 : ℝ) (z : Fin m → ℝ) (w : ℝ) : ℝ :=
  -((m : ℝ) / 2) * Real.log (2 * π * w) - c0 Δ₁ z - Qv Δ₁ Δ₁ y0 z / (2 * w)

theorem gV_cal {m : ℕ} {Δ₁ : Fin m → ℝ} (hm : 0 < m) (hΔ₁ : ∀ j, 0 < Δ₁ j) {y0 : ℝ}
    {z : Fin m → ℝ} (hp : PosPath y0 z) (b : ℝ) {w : ℝ} (hw : 0 < w) :
    gV Δ₁ Δ₁ b w y0 z = Real.exp (phiC Δ₁ y0 z w -
      Av Δ₁ Δ₁ * (b - (Bv Δ₁ Δ₁ y0 z + w * (∑ j, Δ₁ j) / 2) / Av Δ₁ Δ₁) ^ 2 / (2 * w)) := by
  rw [log_gV hm hΔ₁ hΔ₁ hp b hw]
  congr 1
  unfold phi phiC
  rw [Hv_cal hm hΔ₁, Kv_cal hm hΔ₁ y0 z]
  ring

theorem gV_cal_le {m : ℕ} {Δ₁ : Fin m → ℝ} (hm : 0 < m) (hΔ₁ : ∀ j, 0 < Δ₁ j) {y0 : ℝ}
    {z : Fin m → ℝ} (hp : PosPath y0 z) (b : ℝ) {w : ℝ} (hw : 0 < w) :
    gV Δ₁ Δ₁ b w y0 z ≤ Real.exp (phiC Δ₁ y0 z w) := by
  rw [gV_cal hm hΔ₁ hp b hw]
  refine Real.exp_le_exp.2 (sub_le_self _ ?_)
  have := Av_pos hm hΔ₁ hΔ₁
  positivity

theorem gV_cal_eq {m : ℕ} {Δ₁ : Fin m → ℝ} (hm : 0 < m) (hΔ₁ : ∀ j, 0 < Δ₁ j) {y0 : ℝ}
    {z : Fin m → ℝ} (hp : PosPath y0 z) {w : ℝ} (hw : 0 < w) :
    gV Δ₁ Δ₁ ((Bv Δ₁ Δ₁ y0 z + w * (∑ j, Δ₁ j) / 2) / Av Δ₁ Δ₁) w y0 z = Real.exp (phiC Δ₁ y0 z w) := by
  rw [gV_cal hm hΔ₁ hp _ hw, sub_self, sq, zero_mul, mul_zero, zero_div, sub_zero]

variable {D : ℕ} {n : Fin D → ℕ} {Δ : Fam n}

section Seg

variable (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) {s : ℝ} {y : Arr n} (hy : AllPos s y)
  {ℓ : ℕ} (e : Fin ℓ → Fin D)
include hn hΔ hy

omit hy in
/-- The summed scale profile of a segment: `−(N/2) log(2πw) − Σc_d − Q_within/(2w)`. -/
theorem sum_phiC (w : ℝ) :
    ∑ j, phiC (Δ (e j)) (start s y (e j)) (toR y (e j)) w =
      -((NSeg n e : ℝ) / 2) * Real.log (2 * π * w) - ∑ j, c0 (Δ (e j)) (toR y (e j)) -
        Qwithin Δ e s y / (2 * w) := by
  unfold phiC Qwithin NSeg
  simp only [Finset.sum_sub_distrib, Nat.cast_sum, Finset.sum_div, Finset.sum_mul, Finset.sum_neg_distrib,
    neg_mul, Qd_eq hn hΔ]

/-- Claim 069's segment profile for the calendar shape. -/
theorem PswSeg_val (hℓ : 0 < ℓ) (hQ : 0 < Qwithin Δ e s y) :
    PswSeg Δ Δ e s y = ENNReal.ofReal (Real.exp (-((NSeg n e : ℝ) / 2) *
      Real.log (2 * π * (Qwithin Δ e s y / NSeg n e)) - ∑ j, c0 (Δ (e j)) (toR y (e j)) -
        (NSeg n e : ℝ) / 2)) := by
  have hN : (0 : ℝ) < NSeg n e := by
    have := N_pos hℓ (fun j => hn (e j)); exact_mod_cast this
  set Qw := Qwithin Δ e s y
  set N : ℝ := (NSeg n e : ℝ)
  set C := ∑ j, c0 (Δ (e j)) (toR y (e j))
  have hp : ∀ j, PosPath (start s y (e j)) (toR y (e j)) := fun j => posPath_block hy hn (e j)
  have hw0 : 0 < Qw / N := div_pos hQ hN
  -- The maximum over the scale.
  have hmax : ∀ w, 0 < w → -(N / 2) * Real.log (2 * π * w) - C - Qw / (2 * w) ≤
      -(N / 2) * Real.log (2 * π * (Qw / N)) - C - N / 2 := fun w hw => by
    have hgap := log_gap_nonneg (div_pos hw hw0)
    rw [Real.log_mul (by positivity) hw.ne', Real.log_mul (by positivity) hw0.ne',
      Real.log_div hw.ne' hw0.ne'] at *
    have : 1 / (w / (Qw / N)) = Qw / (N * w) := by field_simp
    rw [this] at hgap
    have hQN : Qw / (2 * w) = (N / 2) * (Qw / (N * w)) := by field_simp
    rw [hQN]
    nlinarith
  unfold PswSeg
  refine le_antisymm (iSup_le fun b => iSup_le fun w => iSup_le fun hw => ?_) ?_
  · rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => gV_nonneg _ _ _ _]
    refine ENNReal.ofReal_le_ofReal ((Finset.prod_le_prod₀ (fun j _ => gV_nonneg _ _ _ _)
      fun j _ => gV_cal_le (hn _) (hΔ _) (hp j) (b j) hw).trans ?_)
    rw [← Real.exp_sum, sum_phiC hn hΔ e]
    exact Real.exp_le_exp.2 (hmax w hw)
  · refine le_iSup₂_of_le (fun j => (Bv (Δ (e j)) (Δ (e j)) (start s y (e j)) (toR y (e j)) +
      Qw / N * (∑ i, Δ (e j) i) / 2) / Av (Δ (e j)) (Δ (e j))) (Qw / N) (le_iSup_of_le hw0 (le_of_eq ?_))
    rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => gV_nonneg _ _ _ _]
    congr 1
    rw [Finset.prod_congr rfl fun j _ => gV_cal_eq (hn _) (hΔ _) (hp j) hw0, ← Real.exp_sum,
      sum_phiC hn hΔ e]
    congr 1
    have : Qw / (2 * (Qw / N)) = N / 2 := by field_simp
    rw [this]

end Seg

section Cons

variable (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) {s : ℝ} {y : Arr n} (hy : AllPos s y)
  {a ℓ : ℕ} (h : a + ℓ ≤ D) (hℓ : 0 < ℓ)
include hn hΔ hy hℓ

omit hy in
/-- The calendar form of (4). -/
theorem Qcal_eq :
    Qv (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) Δ) (start s y ⟨a, by omega⟩) (concatY (cons a ℓ h) y) =
      Qwithin Δ (cons a ℓ h) s y +
        ∑ j, Td Δ (cons a ℓ h j) * (ahat Δ s y (cons a ℓ h j) - ahatSeg Δ (cons a ℓ h) s y) ^ 2 := by
  rw [Qv_concat hn hΔ hΔ h hℓ s y]
  have hA : Av (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) Δ) = ∑ j, Td Δ (cons a ℓ h j) := by
    rw [Av_concat h]; exact Finset.sum_congr rfl fun j _ => Av_cal (hΔ _)
  have hB : Bv (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) Δ) (start s y ⟨a, by omega⟩)
      (concatY (cons a ℓ h) y) = ∑ j, Sd s y (cons a ℓ h j) := by
    rw [Bv_concat hn h hℓ s y]; exact Finset.sum_congr rfl fun j _ => Bv_cal (hΔ _) _ _
  rw [hA, hB]
  unfold Qwithin ahatSeg ahat
  congr 1
  · exact Finset.sum_congr rfl fun j _ => Qd_eq hn hΔ _
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Av_cal (hΔ _), Bv_cal (hΔ _)]
    rfl

omit hn hΔ hy hℓ in
theorem c0_concat :
    ∑ j, c0 (Δ (cons a ℓ h j)) (toR y (cons a ℓ h j)) =
      (1 / 2) * ∑ k, Real.log (concat (cons a ℓ h) Δ k) + ∑ k, Real.log (concatY (cons a ℓ h) y k) := by
  unfold c0
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [show concat (cons a ℓ h) Δ = flatR (n := fun j => n (cons a ℓ h j)) (segF (cons a ℓ h) Δ) from rfl,
    show concatY (cons a ℓ h) y = flatR (n := fun j => n (cons a ℓ h j)) (segF (cons a ℓ h) (toR y)) from rfl,
    sum_flat (n := fun j => n (cons a ℓ h j)), sum_flat (n := fun j => n (cons a ℓ h j))]
  simp only [flatR_e]
  rfl

/-- (11) on one consecutive segment. -/
theorem seg_cal (hQ : 0 < Qwithin Δ (cons a ℓ h) s y) :
    0 < PswSeg Δ Δ (cons a ℓ h) s y ∧ PswSeg Δ Δ (cons a ℓ h) s y < ⊤ ∧
    0 < PsegE Δ Δ (cons a ℓ h) s y ∧ PsegE Δ Δ (cons a ℓ h) s y < ⊤ ∧
    Real.log (PswSeg Δ Δ (cons a ℓ h) s y).toReal - Real.log (PsegE Δ Δ (cons a ℓ h) s y).toReal =
      (NSeg n (cons a ℓ h) : ℝ) / 2 * Real.log
        (Qv (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) Δ) (start s y ⟨a, by omega⟩)
          (concatY (cons a ℓ h) y) / Qwithin Δ (cons a ℓ h) s y) ∧
    0 ≤ Real.log (PswSeg Δ Δ (cons a ℓ h) s y).toReal - Real.log (PsegE Δ Δ (cons a ℓ h) s y).toReal := by
  have hcal := Qcal_eq (s := s) (y := y) hn hΔ h hℓ
  obtain ⟨Qp, hQpe⟩ : ∃ Qp, Qv (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) Δ) (start s y ⟨a, by omega⟩)
      (concatY (cons a ℓ h) y) = Qp := ⟨_, rfl⟩
  rw [hQpe] at hcal ⊢
  have hge : Qwithin Δ (cons a ℓ h) s y ≤ Qp := by
    have : 0 ≤ ∑ j, Td Δ (cons a ℓ h j) * (ahat Δ s y (cons a ℓ h j) - ahatSeg Δ (cons a ℓ h) s y) ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (T_pos (hn _) (hΔ _)).le (sq_nonneg _)
    linarith
  have hQp : 0 < Qp := hQ.trans_le hge
  have hm := m_pos hn h hℓ
  have hN : (0 : ℝ) < NSeg n (cons a ℓ h) := by exact_mod_cast hm
  have hsw := PswSeg_val hn hΔ hy (cons a ℓ h) hℓ hQ
  have hse : PsegE Δ Δ (cons a ℓ h) s y = ENNReal.ofReal (Real.exp (logDv (concat (cons a ℓ h) Δ)
      (concat (cons a ℓ h) Δ) (start s y ⟨a, by omega⟩) (concatY (cons a ℓ h) y))) := by
    rw [PsegE_eq hn hΔ hΔ h hℓ hy]
    exact Dv_fin (posPath_concat hn h hℓ hy) (hQpe ▸ hQp)
  have hlog : Real.log (PswSeg Δ Δ (cons a ℓ h) s y).toReal - Real.log (PsegE Δ Δ (cons a ℓ h) s y).toReal =
      (NSeg n (cons a ℓ h) : ℝ) / 2 * Real.log (Qp / Qwithin Δ (cons a ℓ h) s y) := by
    rw [hsw, hse, ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      Real.log_exp, Real.log_exp, logDv_cal hm (concat_pos hΔ (cons a ℓ h)) _ _ (hQpe ▸ hQp), hQpe,
      c0_concat (y := y) h, Real.log_div hQp.ne' hQ.ne']
    have h2 : (0 : ℝ) < 2 * π := by positivity
    unfold NSeg at hN ⊢
    rw [Real.log_mul h2.ne' (div_pos hQ hN).ne', Real.log_mul h2.ne' (div_pos hQp hN).ne',
      Real.log_div hQ.ne' hN.ne', Real.log_div hQp.ne' hN.ne']
    ring
  refine ⟨by rw [hsw]; exact ENNReal.ofReal_pos.2 (Real.exp_pos _), by rw [hsw]; exact ENNReal.ofReal_lt_top,
    by rw [hse]; exact ENNReal.ofReal_pos.2 (Real.exp_pos _), by rw [hse]; exact ENNReal.ofReal_lt_top,
    hlog, ?_⟩
  rw [hlog]
  exact mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div hQ).2 hge))

end Cons

theorem calendar_holds : Standalone.D23JointSwitches.calendar := by
  intro D n Δ hn hΔ s y hy
  refine ⟨fun a ℓ h hℓ hQ => ?_, fun c hc => ?_⟩
  · obtain ⟨_, h2, _, h4, h5, h6⟩ := seg_cal hn hΔ hy h hℓ hQ
    exact ⟨Qcal_eq hn hΔ h hℓ, h2, h4, h5, h6⟩
  · have hseg : ∀ i, 0 < PswSeg Δ Δ (c.embedding i) s y ∧ PswSeg Δ Δ (c.embedding i) s y < ⊤ ∧
        0 < PsegE Δ Δ (c.embedding i) s y ∧ PsegE Δ Δ (c.embedding i) s y < ⊤ := fun i => by
      have hQ := hc i
      rw [emb_cons] at hQ ⊢
      obtain ⟨h1, h2, h3, h4, -⟩ := seg_cal hn hΔ hy (comp_le c i) (c.one_le_blocksFun i) hQ
      exact ⟨h1, h2, h3, h4⟩
    have hR : ∀ {f : Fin c.length → ℝ≥0∞}, (∀ i, 0 < f i ∧ f i < ⊤) →
        Real.log (∏ i, f i).toReal = ∑ i, Real.log (f i).toReal := fun {f} hf => by
      rw [ENNReal.toReal_prod, Real.log_prod]
      exact fun i _ => (ENNReal.toReal_pos (hf i).1.ne' (hf i).2.ne).ne'
    rw [Ppart, hR fun i => ⟨(hseg i).1, (hseg i).2.1⟩, hR fun i => ⟨(hseg i).2.2.1, (hseg i).2.2.2⟩,
      ← Finset.sum_sub_distrib]

end Novel.D23JointSwitches
