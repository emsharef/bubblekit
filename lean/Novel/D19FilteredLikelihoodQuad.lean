import Novel.D19FilteredLikelihoodPrev

/-!
# Claim 036, part 2: the relative integration bound (6)

By induction on the string: for every subcell `l` of the current cell,
`e^{−ε} A_l ≤ α(subcell l) ≤ e^{ε} A_l` (`quad_aux`).
* `α_m` lives on the previous partition, so a transition integral splits into the previous
  subcells (`decomp`).
* From a previous subcell around `t'` into the current subcell around `t`, the log return lies in
  the step's return range and is within `r_prev + r` of `t − t'`; so the transition density is
  within `exp(±C_j (r_prev + r))` of its value at `t − t'` (`pdf_ratio`), and the transition mass
  within that factor of `h φ(t − t')` (`Ptr_density`).
* Summing over the current subcells gives (6); no transition matrix is normalized.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick Standalone.D17ClockCells

variable {δ s : ℝ}

theorem decomp (hδ : 0 < δ) (hs : 0 < s) {M : ℕ} (hM : 0 < M) {m : ℕ} (μ σ : Fin m → ℝ)
    (z : Fin m → ℕ) (hz : ∀ j, 1 ≤ z j) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂(alphaF δ s m μ σ z) =
      ∑ l ∈ Finset.range M, ∫⁻ x in prevSet δ s M m z l, f x ∂(alphaF δ s m μ σ z) := by
  have hU : MeasurableSet (⋃ l ∈ Finset.range M, prevSet δ s M m z l) :=
    Finset.measurableSet_biUnion _ fun l _ => measurableSet_prevSet M m z l
  rw [← lintegral_add_compl f hU, setLIntegral_measure_zero _ _ (alpha_conc hδ hs hM m μ σ z hz),
    add_zero, lintegral_biUnion_finset₀ (fun l _ l' _ h => (prevSet_disj h).aedisjoint)
      (fun l _ => (measurableSet_prevSet M m z l).nullMeasurableSet)]

theorem msg_nonneg (M : ℕ) : ∀ (m : ℕ) (μ σ : Fin m → ℝ) (z : Fin m → ℕ), (∀ j, 1 ≤ z j) →
    0 < δ → ∀ l, 0 ≤ msg δ s M m μ σ z l
  | 0, _, _, _, _, _, l => by show 0 ≤ (if l = 0 then (1 : ℝ) else 0); split_ifs <;> norm_num
  | m + 1, μ, σ, z, hz, hδ, l => by
    show 0 ≤ (lD δ (z (Fin.last m)) - lA δ (z (Fin.last m))) / M * _
    refine mul_nonneg (div_nonneg (sub_nonneg.2 (lA_lt_lD hδ (hz _)).le) (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun l' _ => mul_nonneg
        (msg_nonneg M m _ _ _ (fun j => hz _) hδ l') (gaussianPDFReal_nonneg _ _ _))

theorem abs_le_max_of_mem {lo hi y : ℝ} (h1 : lo ≤ y) (h2 : y ≤ hi) : |y| ≤ max |lo| |hi| := by
  rw [abs_le]
  constructor
  · have : -|lo| ≤ lo := neg_abs_le lo
    linarith [le_max_left |lo| |hi|]
  · have : hi ≤ |hi| := le_abs_self hi
    linarith [le_max_right |lo| |hi|]

/-- The step's density factor is at most `C_j`. -/
theorem factor_le_Cj {B : Box} (hB : B.Valid) {b w : ℝ} (hbw : B.Mem (b, w)) {Δ v R : ℝ}
    (hΔ : 0 < Δ) (hv : 0 < v) (hR : 0 ≤ R) :
    (R + |b * Δ - w * v / 2|) / (w * v) ≤ (R + Bmax B * Δ + B.wH * v / 2) / (B.wL * v) := by
  have hw : 0 < w := hB.2.1.trans_le hbw.2.1
  have hb : |b| ≤ Bmax B := abs_le_max_of_mem hbw.1.1 hbw.1.2
  have hB0 : 0 ≤ Bmax B := (abs_nonneg b).trans hb
  have e1 : |b * Δ| = |b| * Δ := by rw [abs_mul, abs_of_pos hΔ]
  have e2 : |w * v / 2| = w * v / 2 := abs_of_pos (by positivity)
  have hμ : |b * Δ - w * v / 2| ≤ Bmax B * Δ + B.wH * v / 2 := by
    calc |b * Δ - w * v / 2| ≤ |b * Δ| + |w * v / 2| := abs_sub _ _
      _ = |b| * Δ + w * v / 2 := by rw [e1, e2]
      _ ≤ Bmax B * Δ + B.wH * v / 2 := by
          have h1 := mul_le_mul_of_nonneg_right hb hΔ.le
          have h2 := mul_le_mul_of_nonneg_right hbw.2.2 hv.le
          linarith
  have hnum : 0 ≤ R + Bmax B * Δ + B.wH * v / 2 := by
    have := hB.2.1.trans_le hB.2.2; positivity
  calc (R + |b * Δ - w * v / 2|) / (w * v) ≤ (R + Bmax B * Δ + B.wH * v / 2) / (w * v) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left hnum (mul_pos hB.2.1 hv)
        (mul_le_mul_of_nonneg_right hbw.2.1 hv.le)

theorem sdF_sq {m : ℕ} {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) {w : ℝ} (hw : 0 < w) (j : Fin m) :
    sdF v w j ^ 2 = w * v j := Real.sq_sqrt (mul_pos hw (hv j)).le

theorem Cj_nonneg {m : ℕ} {Δ v : Fin m → ℝ} {B : Box} (hB : B.Valid) (hΔ : ∀ j, 0 < Δ j)
    (hv : ∀ j, 0 < v j) (z : Fin m → ℕ) (j : Fin m) : 0 ≤ Cj δ s Δ v B z j := by
  unfold Cj
  have h1 : 0 ≤ Rmax δ s z j := le_max_of_le_left (abs_nonneg _)
  have h2 : 0 ≤ Bmax B := le_max_of_le_left (abs_nonneg _)
  have := hΔ j; have := hv j; have := hB.2.1; have := hB.2.1.trans_le hB.2.2
  positivity

theorem prevW_nonneg (hδ : 0 < δ) {M : ℕ} (hM : 0 < M) : ∀ {m : ℕ} {z : Fin m → ℕ},
    (∀ j, 1 ≤ z j) → 0 ≤ prevW δ M m z
  | 0, _, _ => le_rfl
  | _ + 1, _, hz => (wd_pos hδ hM (hz _)).le

theorem sub_top_le (hδ : 0 < δ) {M z l : ℕ} (hM : 0 < M) (hz : 1 ≤ z) (hl : l < M) :
    lA δ z + l * wd δ M z + wd δ M z ≤ lD δ z := by
  have hlM : ((l : ℝ) + 1) ≤ M := by exact_mod_cast hl
  have h : ((l : ℝ) + 1) * wd δ M z ≤ lD δ z - lA δ z := by
    unfold wd; rw [mul_div_assoc', div_le_iff₀ (by exact_mod_cast hM)]
    nlinarith [lA_lt_lD hδ hz]
  linarith

/-- One step: from a previous subcell into subcell `l` of the current cell, the transition mass is
within `exp(±κ)` of `h φ(t_l − t')`. -/
theorem step_bounds (hδ : 0 < δ) (hs : 0 < s) {M : ℕ} (hM : 0 < M) {B : Box} (hB : B.Valid)
    {b w : ℝ} (hbw : B.Mem (b, w)) {m : ℕ} (Δ v : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℕ)
    (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) (hz : ∀ j, 1 ≤ z j) {l l' : ℕ} (hl : l < M)
    (hl' : l' < M) {x : ℝ} (hx : x ∈ prevSet δ s M m (Fin.init z) l') :
    ENNReal.ofReal (Real.exp (-(Cj δ s Δ v B z (Fin.last m) *
        (prevW δ M m (Fin.init z) / 2 + wd δ M (z (Fin.last m)) / 2))) *
      gaussianPDFReal (muF Δ v b w (Fin.last m)) (sdF v w (Fin.last m) ^ 2).toNNReal
        (tMid δ M (z (Fin.last m)) l - lastMid δ s M m (Fin.init z) l') * wd δ M (z (Fin.last m))) ≤
      Ptr (muF Δ v b w (Fin.last m)) (sdF v w (Fin.last m)) x (psub δ M (z (Fin.last m)) l) ∧
    Ptr (muF Δ v b w (Fin.last m)) (sdF v w (Fin.last m)) x (psub δ M (z (Fin.last m)) l) ≤
      ENNReal.ofReal (Real.exp (Cj δ s Δ v B z (Fin.last m) *
        (prevW δ M m (Fin.init z) / 2 + wd δ M (z (Fin.last m)) / 2)) *
      gaussianPDFReal (muF Δ v b w (Fin.last m)) (sdF v w (Fin.last m) ^ 2).toNNReal
        (tMid δ M (z (Fin.last m)) l - lastMid δ s M m (Fin.init z) l') * wd δ M (z (Fin.last m))) := by
  have hw : 0 < w := hB.2.1.trans_le hbw.2.1
  set zl := z (Fin.last m)
  set z' := Fin.init z
  set μL := muF Δ v b w (Fin.last m)
  set ρ := prevW δ M m z' / 2 + wd δ M zl / 2
  set C := Cj δ s Δ v B z (Fin.last m)
  set R := Rmax δ s z (Fin.last m)
  set var := w * v (Fin.last m)
  have hvar0 : 0 < var := mul_pos hw (hv _)
  have hwd := wd_pos hδ hM (hz (Fin.last m))
  have hρ0 : 0 ≤ ρ := by
    have := prevW_nonneg hδ hM (m := m) (z := z') (fun j => hz _); simp only [ρ]; positivity
  obtain ⟨hx0, hxn, hxa, hxd⟩ := prevSet_props hs hx hl' (fun j => hz _) hδ hM
  obtain ⟨hma, hmd⟩ := lastMid_mem (δ := δ) (s := s) hl' (fun j => hz _) hδ hM (z := z')
  obtain ⟨hta, htd⟩ := tMid_mem hδ hM (hz (Fin.last m)) hl
  set lo := lA δ zl + l * wd δ M zl
  have hlo : lA δ zl ≤ lo := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hwd.le)
  have hhi : lo + wd δ M zl ≤ lD δ zl := sub_top_le hδ hM (hz _) hl
  have hset : {t : ℝ | Real.exp t ∈ psub δ M zl l} = Ico lo (lo + wd δ M zl) := by
    ext t
    simp only [psub, mem_ofPred_eq, Real.exp_pos, true_and, Real.log_exp, mem_Ico, lo]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  have hvol : volume (Ico lo (lo + wd δ M zl)) = ENNReal.ofReal (wd δ M zl) := by
    rw [Real.volume_Ico]; congr 1; ring
  have hR : R = max |lA δ zl - prevD δ s m z'| |lD δ zl - prevA δ s m z'| := Rmax_last z
  have hbound : ∀ t ∈ Ico lo (lo + wd δ M zl), |t - Real.log x| ≤ R ∧
      |tMid δ M zl l - lastMid δ s M m z' l'| ≤ R ∧
      |(t - Real.log x) - (tMid δ M zl l - lastMid δ s M m z' l')| ≤ ρ := fun t ht => by
    refine ⟨?_, ?_, ?_⟩
    · rw [hR]; exact abs_le_max_of_mem (by linarith [ht.1]) (by linarith [ht.2])
    · rw [hR]; exact abs_le_max_of_mem (by linarith) (by linarith)
    · have h1 : |t - tMid δ M zl l| ≤ wd δ M zl / 2 := by
        rw [abs_le]; unfold tMid; simp only [lo] at ht
        have := ht.1; have := ht.2; unfold wd at *; constructor <;> nlinarith
      calc |(t - Real.log x) - (tMid δ M zl l - lastMid δ s M m z' l')|
          = |(t - tMid δ M zl l) - (Real.log x - lastMid δ s M m z' l')| := by ring_nf
        _ ≤ |t - tMid δ M zl l| + |Real.log x - lastMid δ s M m z' l'| := abs_sub _ _
        _ ≤ ρ := by simp only [ρ]; linarith
  have hfac : (R + |μL|) / var ≤ C :=
    factor_le_Cj hB hbw (hΔ _) (hv _) (le_max_of_le_left (abs_nonneg _))
  have hexp : Real.exp (ρ * ((R + |μL|) / var)) ≤ Real.exp (C * ρ) :=
    Real.exp_le_exp.2 (by rw [mul_comm C]; exact mul_le_mul_of_nonneg_left hfac hρ0)
  have hpdf0 := gaussianPDFReal_nonneg μL var.toNNReal (tMid δ M zl l - lastMid δ s M m z' l')
  rw [Ptr_density μL (sdF_pos hv hw _).ne' hx0 (measurableSet_psub M zl l), hset,
    show sdF v w (Fin.last m) ^ 2 = var from sdF_sq hv hw _]
  constructor
  · calc ENNReal.ofReal (Real.exp (-(C * ρ)) * gaussianPDFReal μL var.toNNReal
          (tMid δ M zl l - lastMid δ s M m z' l') * wd δ M zl)
        = ∫⁻ _t in Ico lo (lo + wd δ M zl), ENNReal.ofReal (Real.exp (-(C * ρ)) *
            gaussianPDFReal μL var.toNNReal (tMid δ M zl l - lastMid δ s M m z' l')) := by
          rw [setLIntegral_const, hvol, ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le hpdf0)]
      _ ≤ _ := setLIntegral_mono (by fun_prop) fun t ht => by
          obtain ⟨h1, h2, h12⟩ := hbound t ht
          refine ENNReal.ofReal_le_ofReal ?_
          have h21 : |(tMid δ M zl l - lastMid δ s M m z' l') - (t - Real.log x)| ≤ ρ := by
            rw [abs_sub_comm]; exact h12
          have := pdf_ratio (ρ := ρ) μL hvar0 h2 h1 h21
          rw [Real.exp_neg, ← div_eq_inv_mul, div_le_iff₀ (Real.exp_pos _)]
          calc _ ≤ _ := this
            _ ≤ Real.exp (C * ρ) * gaussianPDFReal μL var.toNNReal (t - Real.log x) :=
                mul_le_mul_of_nonneg_right hexp (gaussianPDFReal_nonneg _ _ _)
            _ = _ := mul_comm _ _
  · calc ∫⁻ t in Ico lo (lo + wd δ M zl), ENNReal.ofReal (gaussianPDFReal μL var.toNNReal
          (t - Real.log x))
        ≤ ∫⁻ _t in Ico lo (lo + wd δ M zl), ENNReal.ofReal (Real.exp (C * ρ) *
            gaussianPDFReal μL var.toNNReal (tMid δ M zl l - lastMid δ s M m z' l')) :=
          setLIntegral_mono (by fun_prop) fun t ht => by
            obtain ⟨h1, h2, h12⟩ := hbound t ht
            exact ENNReal.ofReal_le_ofReal ((pdf_ratio (ρ := ρ) μL hvar0 h1 h2 h12).trans
              (mul_le_mul_of_nonneg_right hexp hpdf0))
      _ = _ := by
          rw [setLIntegral_const, hvol, ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le hpdf0)]

/-- (6) on every subcell, by induction on the string. -/
theorem quad_aux (hδ : 0 < δ) (hs : 0 < s) {M : ℕ} (hM : 0 < M) {B : Box} (hB : B.Valid) {b w : ℝ}
    (hbw : B.Mem (b, w)) : ∀ (m : ℕ) (Δ v : Fin m → ℝ) (z : Fin m → ℕ), (∀ j, 0 < Δ j) →
    (∀ j, 0 < v j) → (∀ j, 1 ≤ z j) → ∀ l < M,
      ENNReal.ofReal (Real.exp (-epsQ δ s M Δ v B z) * msg δ s M m (muF Δ v b w) (sdF v w) z l) ≤
        alphaF δ s m (muF Δ v b w) (sdF v w) z (prevSet δ s M m z l) ∧
      alphaF δ s m (muF Δ v b w) (sdF v w) z (prevSet δ s M m z l) ≤
        ENNReal.ofReal (Real.exp (epsQ δ s M Δ v B z) * msg δ s M m (muF Δ v b w) (sdF v w) z l)
  | 0, Δ, v, z, _, _, _, l, _ => by
    have he : epsQ δ s M Δ v B z = 0 := by simp [epsQ]
    rw [he, neg_zero, Real.exp_zero, one_mul]
    show ENNReal.ofReal (if l = 0 then 1 else 0) ≤ (Measure.dirac s) (if l = 0 then {s} else ∅) ∧
      (Measure.dirac s) (if l = 0 then {s} else ∅) ≤ ENNReal.ofReal (if l = 0 then 1 else 0)
    split_ifs
    · simp
    · simp
  | m + 1, Δ, v, z, hΔ, hv, hz, l, hl => by
    have IH := quad_aux hδ hs hM hB hbw m (Fin.init Δ) (Fin.init v) (Fin.init z) (fun j => hΔ _)
      (fun j => hv _) (fun j => hz _)
    set κ := Cj δ s Δ v B z (Fin.last m) * (prevW δ M m (Fin.init z) / 2 + wd δ M (z (Fin.last m)) / 2)
    set ε' := epsQ δ s M (Fin.init Δ) (Fin.init v) B (Fin.init z)
    have hε : epsQ δ s M Δ v B z = ε' + κ := by rw [epsQ_succ, hP_last_castSucc, hP_last_succ]
    set pdf0 : ℕ → ℝ := fun l' => gaussianPDFReal (muF Δ v b w (Fin.last m))
      (sdF v w (Fin.last m) ^ 2).toNNReal (tMid δ M (z (Fin.last m)) l - lastMid δ s M m (Fin.init z) l')
    set msg' := msg δ s M m (Fin.init (muF Δ v b w)) (Fin.init (sdF v w)) (Fin.init z)
    have hmsg : msg δ s M (m + 1) (muF Δ v b w) (sdF v w) z l =
        wd δ M (z (Fin.last m)) * ∑ l' ∈ Finset.range M, msg' l' * pdf0 l' := rfl
    have hmsg0 : ∀ l', 0 ≤ msg' l' := msg_nonneg M m _ _ _ (fun j => hz _) hδ
    have hpdf0 : ∀ l', 0 ≤ pdf0 l' := fun l' => gaussianPDFReal_nonneg _ _ _
    have hwd := (wd_pos hδ hM (hz (Fin.last m))).le
    have hα : alphaF δ s (m + 1) (muF Δ v b w) (sdF v w) z (prevSet δ s M (m + 1) z l) =
        ∫⁻ x, Ptr (muF Δ v b w (Fin.last m)) (sdF v w (Fin.last m)) x (psub δ M (z (Fin.last m)) l)
          ∂(alphaF δ s m (Fin.init (muF Δ v b w)) (Fin.init (sdF v w)) (Fin.init z)) := by
      show ((alphaF δ s m _ _ _).bind _).restrict (mcell δ (z (Fin.last m))) (psub δ M (z (Fin.last m)) l) = _
      rw [Measure.restrict_apply (measurableSet_psub M _ l),
        inter_eq_left.2 (psub_sub_mcell hδ hM (hz _) hl),
        Measure.bind_apply (measurableSet_psub M _ l) (Kernel.aemeasurable _)]
    rw [hα, decomp hδ hs hM _ _ (Fin.init z) (fun j => hz _)]
    have hsumU : ∑ l' ∈ Finset.range M, Real.exp κ * pdf0 l' * wd δ M (z (Fin.last m)) *
        (Real.exp ε' * msg' l') = Real.exp (epsQ δ s M Δ v B z) *
          msg δ s M (m + 1) (muF Δ v b w) (sdF v w) z l := by
      rw [hmsg, hε, Real.exp_add, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l' _ => by ring
    have hsumL : ∑ l' ∈ Finset.range M, Real.exp (-κ) * pdf0 l' * wd δ M (z (Fin.last m)) *
        (Real.exp (-ε') * msg' l') = Real.exp (-epsQ δ s M Δ v B z) *
          msg δ s M (m + 1) (muF Δ v b w) (sdF v w) z l := by
      rw [hmsg, hε, neg_add, Real.exp_add, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l' _ => by ring
    constructor
    · rw [← hsumL, ENNReal.ofReal_sum_of_nonneg fun l' _ => by
        have := hmsg0 l'; have := hpdf0 l'; positivity]
      refine Finset.sum_le_sum fun l' hl' => ?_
      have hl'' := Finset.mem_range.1 hl'
      rw [ENNReal.ofReal_mul (by have := hpdf0 l'; positivity)]
      calc ENNReal.ofReal (Real.exp (-κ) * pdf0 l' * wd δ M (z (Fin.last m))) *
            ENNReal.ofReal (Real.exp (-ε') * msg' l')
          ≤ ENNReal.ofReal (Real.exp (-κ) * pdf0 l' * wd δ M (z (Fin.last m))) *
            alphaF δ s m (Fin.init (muF Δ v b w)) (Fin.init (sdF v w)) (Fin.init z)
              (prevSet δ s M m (Fin.init z) l') := mul_le_mul_right (IH l' hl'').1 _
        _ = ∫⁻ _x in prevSet δ s M m (Fin.init z) l', ENNReal.ofReal (Real.exp (-κ) * pdf0 l' *
              wd δ M (z (Fin.last m))) ∂(alphaF δ s m (Fin.init (muF Δ v b w)) (Fin.init (sdF v w))
                (Fin.init z)) := by rw [setLIntegral_const]
        _ ≤ _ := setLIntegral_mono' (measurableSet_prevSet M m _ l') fun x hx =>
            (step_bounds hδ hs hM hB hbw Δ v z hΔ hv hz hl hl'' hx).1
    · rw [← hsumU, ENNReal.ofReal_sum_of_nonneg fun l' _ => by
        have := hmsg0 l'; have := hpdf0 l'; positivity]
      refine Finset.sum_le_sum fun l' hl' => ?_
      have hl'' := Finset.mem_range.1 hl'
      rw [ENNReal.ofReal_mul (by have := hpdf0 l'; positivity)]
      calc ∫⁻ x in prevSet δ s M m (Fin.init z) l', Ptr (muF Δ v b w (Fin.last m))
            (sdF v w (Fin.last m)) x (psub δ M (z (Fin.last m)) l)
            ∂(alphaF δ s m (Fin.init (muF Δ v b w)) (Fin.init (sdF v w)) (Fin.init z))
          ≤ ∫⁻ _x in prevSet δ s M m (Fin.init z) l', ENNReal.ofReal (Real.exp κ * pdf0 l' *
              wd δ M (z (Fin.last m))) ∂(alphaF δ s m (Fin.init (muF Δ v b w)) (Fin.init (sdF v w))
                (Fin.init z)) := setLIntegral_mono' (measurableSet_prevSet M m _ l') fun x hx =>
            (step_bounds hδ hs hM hB hbw Δ v z hΔ hv hz hl hl'' hx).2
        _ = ENNReal.ofReal (Real.exp κ * pdf0 l' * wd δ M (z (Fin.last m))) *
            alphaF δ s m (Fin.init (muF Δ v b w)) (Fin.init (sdF v w)) (Fin.init z)
              (prevSet δ s M m (Fin.init z) l') := by rw [setLIntegral_const]
        _ ≤ _ := mul_le_mul_right (IH l' hl'').2 _

/-- Part 2: (6). -/
theorem quad_holds : Standalone.D19FilteredLikelihood.quad := by
  intro δ s m M Δ v B b w z hδ hs hM hΔ hv hB hbw hz
  have hw : 0 < w := hB.2.1.trans_le hbw.2.1
  have hq := quad_aux hδ hs hM hB hbw m Δ v z hΔ hv hz
  set α := alphaF δ s m (muF Δ v b w) (sdF v w) z
  have hmsg0 : ∀ l, 0 ≤ msg δ s M m (muF Δ v b w) (sdF v w) z l := msg_nonneg M m _ _ _ hz hδ
  have huniv : α univ = ∑ l ∈ Finset.range M, α (prevSet δ s M m z l) := by
    have := decomp hδ hs hM (muF Δ v b w) (sdF v w) z hz (fun _ => 1)
    simp only [lintegral_one, Measure.restrict_apply MeasurableSet.univ, univ_inter] at this
    simpa [setLIntegral_const] using this
  have hL : Lz δ s (muF Δ v b w) (sdF v w) z = (α univ).toReal := by
    unfold Lz; rw [alpha_univ hδ hs.le]
  have hfin : α univ ≠ ⊤ := by rw [alpha_univ hδ hs.le]; exact walk_ne_top _ _ s z
  have hup : α univ ≤ ENNReal.ofReal (Real.exp (epsQ δ s M Δ v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z) := by
    rw [huniv, Qs, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun l _ =>
      mul_nonneg (Real.exp_pos _).le (hmsg0 l)]
    exact Finset.sum_le_sum fun l hl => (hq l (Finset.mem_range.1 hl)).2
  have hlo : ENNReal.ofReal (Real.exp (-epsQ δ s M Δ v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z) ≤
      α univ := by
    rw [huniv, Qs, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun l _ =>
      mul_nonneg (Real.exp_pos _).le (hmsg0 l)]
    exact Finset.sum_le_sum fun l hl => (hq l (Finset.mem_range.1 hl)).1
  have hQ0 : 0 ≤ Qs δ s M (muF Δ v b w) (sdF v w) z := Finset.sum_nonneg fun l _ => hmsg0 l
  have hupR : Lz δ s (muF Δ v b w) (sdF v w) z ≤
      Real.exp (epsQ δ s M Δ v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z := by
    rw [hL]; exact ENNReal.toReal_le_of_le_ofReal (by positivity) hup
  have hloR : Real.exp (-epsQ δ s M Δ v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z ≤
      Lz δ s (muF Δ v b w) (sdF v w) z := by
    rw [hL]; exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hlo
  have hLpos := Lz_pos hδ hs (muF Δ v b w) (sdF v w) (fun j => sdF_pos hv hw j) z
  refine ⟨?_, hloR, hupR⟩
  by_contra hQ
  have hQ' : Qs δ s M (muF Δ v b w) (sdF v w) z = 0 := le_antisymm (not_lt.1 hQ) hQ0
  rw [hQ', mul_zero] at hupR
  linarith

end Novel.D19FilteredLikelihood
