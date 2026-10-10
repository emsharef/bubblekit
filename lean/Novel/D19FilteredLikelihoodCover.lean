import Novel.D19FilteredLikelihoodParam

/-!
# Claim 036, part 3: covering the continuous family

* `alpha_param`: for two parameters of a box within `(ρ_b, ρ_w)` of each other, on an all-positive
  string, `α_θ ≤ exp(ρ_b L_b + ρ_w L_w) α_θ'` as measures. By induction, using the one-step log
  density bound (`lpdf_diff`) on the step's return range and the previous partition.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick Standalone.D17ClockCells

variable {δ s : ℝ}

/-- The per-step factor of `L_w`. -/
noncomputable def Lwj (δ s : ℝ) {m : ℕ} (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) (j : Fin m) : ℝ :=
  1 / (2 * B.wL) + (Rmax δ s z j + Bmax B * Δ j) ^ 2 / (2 * B.wL ^ 2 * v j) + v j / 8

/-- The parameter allowance for radii `(ρ_b, ρ_w)`. -/
noncomputable def etaR (δ s : ℝ) {m : ℕ} (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) (ρb ρw : ℝ) : ℝ :=
  ∑ j, (ρb * (Δ j * Cj δ s Δ v B z j) + ρw * Lwj δ s Δ v B z j)

theorem etaR_succ {m : ℕ} (Δ v : Fin (m + 1) → ℝ) (B : Box) (z : Fin (m + 1) → ℕ) (ρb ρw : ℝ) :
    etaR δ s Δ v B z ρb ρw = etaR δ s (Fin.init Δ) (Fin.init v) B (Fin.init z) ρb ρw +
      (ρb * (Δ (Fin.last m) * Cj δ s Δ v B z (Fin.last m)) + ρw * Lwj δ s Δ v B z (Fin.last m)) := by
  unfold etaR
  rw [Fin.sum_univ_castSucc]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Lwj; rw [Cj_castSucc, Rmax_castSucc]; rfl

theorem etaR_eq {m : ℕ} (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) :
    etaR δ s Δ v B z ((B.bH - B.bL) / 2) ((B.wH - B.wL) / 2) = etaQ δ s Δ v B z := by
  unfold etaR etaQ Lb Lw Lwj
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- One step under a parameter change, from the previous partition. -/
theorem step_param (hδ : 0 < δ) (hs : 0 < s) {M : ℕ} (hM : 0 < M) {B : Box} (hB : B.Valid)
    {b₁ w₁ b₂ w₂ ρb ρw : ℝ} (h1 : B.Mem (b₁, w₁)) (h2 : B.Mem (b₂, w₂)) (hρb : |b₁ - b₂| ≤ ρb)
    (hρw : |w₁ - w₂| ≤ ρw) {m : ℕ} (Δ v : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℕ)
    (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) (hz : ∀ j, 1 ≤ z j) {x : ℝ}
    (hx : x ∈ ⋃ l ∈ Finset.range M, prevSet δ s M m (Fin.init z) l) {A : Set ℝ}
    (hA : MeasurableSet A) :
    Ptr (muF Δ v b₁ w₁ (Fin.last m)) (sdF v w₁ (Fin.last m)) x (A ∩ mcell δ (z (Fin.last m))) ≤
      ENNReal.ofReal (Real.exp (ρb * (Δ (Fin.last m) * Cj δ s Δ v B z (Fin.last m)) +
        ρw * Lwj δ s Δ v B z (Fin.last m))) *
      Ptr (muF Δ v b₂ w₂ (Fin.last m)) (sdF v w₂ (Fin.last m)) x (A ∩ mcell δ (z (Fin.last m))) := by
  obtain ⟨l', hl', hxl⟩ := mem_iUnion₂.1 hx
  obtain ⟨hx0, -, hxa, hxd⟩ := prevSet_props hs hxl (Finset.mem_range.1 hl') (fun j => hz _) hδ hM
  have hw1 : 0 < w₁ := hB.2.1.trans_le h1.2.1
  have hw2 : 0 < w₂ := hB.2.1.trans_le h2.2.1
  have hAC : MeasurableSet (A ∩ mcell δ (z (Fin.last m))) := hA.inter measurableSet_Ico
  set c := ρb * (Δ (Fin.last m) * Cj δ s Δ v B z (Fin.last m)) + ρw * Lwj δ s Δ v B z (Fin.last m)
  rw [Ptr_density _ (sdF_pos hv hw1 _).ne' hx0 hAC, Ptr_density _ (sdF_pos hv hw2 _).ne' hx0 hAC,
    sdF_sq hv hw1, sdF_sq hv hw2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' (Real.measurable_exp hAC) fun t ht => ?_
  have hR : |t - Real.log x| ≤ Rmax δ s z (Fin.last m) := by
    have ht' := (mem_mcell_iff hδ (hz _) (Real.exp_pos t)).1 ht.2
    rw [Real.log_exp] at ht'
    rw [Rmax_last]
    exact abs_le_max_of_mem (by linarith [ht'.1]) (by linarith [ht'.2])
  have hd := lpdf_diff hB h1 h2 (hΔ (Fin.last m)) (hv (Fin.last m)) hR
  have hb0 : 0 ≤ Δ (Fin.last m) * Cj δ s Δ v B z (Fin.last m) :=
    mul_nonneg (hΔ _).le (Cj_nonneg hB hΔ hv z _)
  have hw0 : 0 ≤ Lwj δ s Δ v B z (Fin.last m) := by
    unfold Lwj; have := hB.2.1; have := hv (Fin.last m); positivity
  have hle : lpdf (Δ (Fin.last m)) (v (Fin.last m)) b₁ w₁ (t - Real.log x) ≤
      c + lpdf (Δ (Fin.last m)) (v (Fin.last m)) b₂ w₂ (t - Real.log x) := by
    have h3 := le_abs_self (lpdf (Δ (Fin.last m)) (v (Fin.last m)) b₁ w₁ (t - Real.log x) -
      lpdf (Δ (Fin.last m)) (v (Fin.last m)) b₂ w₂ (t - Real.log x))
    have h4 := mul_le_mul_of_nonneg_right hρb hb0
    have h5 := mul_le_mul_of_nonneg_right hρw hw0
    unfold Cj Lwj at *
    simp only [c, Cj, Lwj]
    linarith
  rw [show muF Δ v b₁ w₁ (Fin.last m) = b₁ * Δ (Fin.last m) - w₁ * v (Fin.last m) / 2 from rfl,
    show muF Δ v b₂ w₂ (Fin.last m) = b₂ * Δ (Fin.last m) - w₂ * v (Fin.last m) / 2 from rfl,
    pdf_eq_exp (hv _) hw1, pdf_eq_exp (hv _) hw2, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hle)

/-- The forward measures under a parameter change. -/
theorem alpha_param (hδ : 0 < δ) (hs : 0 < s) {M : ℕ} (hM : 0 < M) {B : Box} (hB : B.Valid)
    {b₁ w₁ b₂ w₂ ρb ρw : ℝ} (h1 : B.Mem (b₁, w₁)) (h2 : B.Mem (b₂, w₂)) (hρb : |b₁ - b₂| ≤ ρb)
    (hρw : |w₁ - w₂| ≤ ρw) : ∀ (m : ℕ) (Δ v : Fin m → ℝ) (z : Fin m → ℕ), (∀ j, 0 < Δ j) →
    (∀ j, 0 < v j) → (∀ j, 1 ≤ z j) → ∀ A, MeasurableSet A →
    alphaF δ s m (muF Δ v b₁ w₁) (sdF v w₁) z A ≤
      ENNReal.ofReal (Real.exp (etaR δ s Δ v B z ρb ρw)) * alphaF δ s m (muF Δ v b₂ w₂) (sdF v w₂) z A
  | 0, Δ, v, z, _, _, _, A, _ => by
    have : etaR δ s Δ v B z ρb ρw = 0 := by simp [etaR]
    rw [this, Real.exp_zero, ENNReal.ofReal_one, one_mul]; rfl
  | m + 1, Δ, v, z, hΔ, hv, hz, A, hA => by
    have IH := alpha_param hδ hs hM hB h1 h2 hρb hρw m (Fin.init Δ) (Fin.init v) (Fin.init z)
      (fun j => hΔ _) (fun j => hv _) (fun j => hz _)
    set α₁ := alphaF δ s m (Fin.init (muF Δ v b₁ w₁)) (Fin.init (sdF v w₁)) (Fin.init z)
    set α₂ := alphaF δ s m (Fin.init (muF Δ v b₂ w₂)) (Fin.init (sdF v w₂)) (Fin.init z)
    set η' := etaR δ s (Fin.init Δ) (Fin.init v) B (Fin.init z) ρb ρw
    set c := ρb * (Δ (Fin.last m) * Cj δ s Δ v B z (Fin.last m)) + ρw * Lwj δ s Δ v B z (Fin.last m)
    have hAC : MeasurableSet (A ∩ mcell δ (z (Fin.last m))) := hA.inter measurableSet_Ico
    set f₁ := fun x => Ptr (muF Δ v b₁ w₁ (Fin.last m)) (sdF v w₁ (Fin.last m)) x
      (A ∩ mcell δ (z (Fin.last m)))
    set f₂ := fun x => Ptr (muF Δ v b₂ w₂ (Fin.last m)) (sdF v w₂ (Fin.last m)) x
      (A ∩ mcell δ (z (Fin.last m)))
    have hf₂ : Measurable f₂ := Kernel.measurable_coe _ hAC
    have hα : ∀ (b w : ℝ), alphaF δ s (m + 1) (muF Δ v b w) (sdF v w) z A =
        ∫⁻ x, Ptr (muF Δ v b w (Fin.last m)) (sdF v w (Fin.last m)) x (A ∩ mcell δ (z (Fin.last m)))
          ∂(alphaF δ s m (Fin.init (muF Δ v b w)) (Fin.init (sdF v w)) (Fin.init z)) := fun b w => by
      show ((alphaF δ s m _ _ _).bind _).restrict (mcell δ (z (Fin.last m))) A = _
      rw [Measure.restrict_apply hA, Measure.bind_apply hAC (Kernel.aemeasurable _)]
    set U := ⋃ l ∈ Finset.range M, prevSet δ s M m (Fin.init z) l
    have hU : MeasurableSet U := Finset.measurableSet_biUnion _ fun l _ => measurableSet_prevSet M m _ l
    have hconc := alpha_conc hδ hs hM m (Fin.init (muF Δ v b₁ w₁)) (Fin.init (sdF v w₁)) (Fin.init z)
      (fun j => hz _)
    have hle : α₁ ≤ ENNReal.ofReal (Real.exp η') • α₂ :=
      Measure.le_iff.2 fun B' hB' => by
        rw [Measure.smul_apply, smul_eq_mul]
        exact IH B' hB'
    rw [hα, hα, etaR_succ, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
    calc ∫⁻ x, f₁ x ∂α₁ = ∫⁻ x in U, f₁ x ∂α₁ := by
          rw [← lintegral_add_compl f₁ hU, setLIntegral_measure_zero _ _ hconc, add_zero]
      _ ≤ ∫⁻ x in U, ENNReal.ofReal (Real.exp c) * f₂ x ∂α₁ :=
          setLIntegral_mono' hU fun x hx => step_param hδ hs hM hB h1 h2 hρb hρw Δ v z hΔ hv hz hx hA
      _ = ∫⁻ x, U.indicator (fun x => ENNReal.ofReal (Real.exp c) * f₂ x) x ∂α₁ :=
          (lintegral_indicator hU _).symm
      _ ≤ ∫⁻ x, U.indicator (fun x => ENNReal.ofReal (Real.exp c) * f₂ x) x
            ∂(ENNReal.ofReal (Real.exp η') • α₂) := lintegral_mono' hle le_rfl
      _ = ENNReal.ofReal (Real.exp η') *
            ∫⁻ x, U.indicator (fun x => ENNReal.ofReal (Real.exp c) * f₂ x) x ∂α₂ :=
          lintegral_smul_measure _ _
      _ ≤ ENNReal.ofReal (Real.exp η') * ∫⁻ x, ENNReal.ofReal (Real.exp c) * f₂ x ∂α₂ := by
          exact mul_le_mul_right (lintegral_mono fun x =>
            indicator_le_self (s := U) (fun x => ENNReal.ofReal (Real.exp c) * f₂ x) x) _
      _ = _ := by rw [lintegral_const_mul _ hf₂]

theorem ctr_mem {B : Box} (hB : B.Valid) : B.Mem (ctr B) := by
  unfold ctr
  exact ⟨⟨by linarith [hB.1], by linarith [hB.1]⟩, ⟨by linarith [hB.2.2], by linarith [hB.2.2]⟩⟩

theorem near_ctr {B : Box} {p : ℝ × ℝ} (hp : B.Mem p) :
    |p.1 - (ctr B).1| ≤ (B.bH - B.bL) / 2 ∧ |p.2 - (ctr B).2| ≤ (B.wH - B.wL) / 2 := by
  unfold ctr
  constructor <;> rw [abs_le] <;> constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]

/-- The label mass under a parameter change within a box. -/
theorem Lz_param (hδ : 0 < δ) (hs : 0 < s) {M : ℕ} (hM : 0 < M) {B : Box} (hB : B.Valid)
    {p q : ℝ × ℝ} (hp : B.Mem p) (hq : B.Mem q) (hpq1 : |p.1 - q.1| ≤ (B.bH - B.bL) / 2)
    (hpq2 : |p.2 - q.2| ≤ (B.wH - B.wL) / 2) {m : ℕ} (Δ v : Fin m → ℝ) (z : Fin m → ℕ)
    (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) (hz : ∀ j, 1 ≤ z j) :
    Lz δ s (muF Δ v p.1 p.2) (sdF v p.2) z ≤
      Real.exp (etaQ δ s Δ v B z) * Lz δ s (muF Δ v q.1 q.2) (sdF v q.2) z := by
  have h := alpha_param hδ hs hM hB hp hq hpq1 hpq2 m Δ v z hΔ hv hz univ MeasurableSet.univ
  rw [alpha_univ hδ hs.le, alpha_univ hδ hs.le, etaR_eq] at h
  unfold Lz
  rw [← ENNReal.toReal_ofReal (Real.exp_pos (etaQ δ s Δ v B z)).le, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (walk_ne_top _ _ s z)) h

theorem all_pos_left {K n : ℕ} {u : Fin K → ℕ} {y : Fin n → ℕ} (h : ∀ j, 1 ≤ Fin.append u y j) :
    ∀ j, 1 ≤ u j := fun j => by have := h (Fin.castAdd n j); rwa [Fin.append_left] at this

/-- (8) for one box and clock, and the lower bound at its center. -/
theorem box_bounds (hδ : 0 < δ) (hs : 0 < s) {M : ℕ} (hM : 0 < M) {K n : ℕ} (Δ v : Fin (K + n) → ℝ)
    (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {B : Box} (hB : B.Valid) (u : Fin K → ℕ) (y : Fin n → ℕ)
    (hz : ∀ j, 1 ≤ Fin.append u y j) {p : ℝ × ℝ} (hp : B.Mem p) :
    gF δ s Δ v p.1 p.2 u y ≤ term δ s M Δ v B u y ∧
      termLow δ s M Δ v B u y ≤ gF δ s Δ v (ctr B).1 (ctr B).2 u y := by
  have hc := ctr_mem hB
  have hu := all_pos_left hz
  obtain ⟨hp1, hp2⟩ := near_ctr hp
  have hcp1 : |(ctr B).1 - p.1| ≤ (B.bH - B.bL) / 2 := by rw [abs_sub_comm]; exact hp1
  have hcp2 : |(ctr B).2 - p.2| ≤ (B.wH - B.wL) / 2 := by rw [abs_sub_comm]; exact hp2
  have hwp : 0 < p.2 := hB.2.1.trans_le hp.2.1
  have hwc : 0 < (ctr B).2 := hB.2.1.trans_le hc.2.1
  set z := Fin.append u y
  set εN := epsQ δ s M Δ v B z
  set εk := epsQ δ s M (trn Δ) (trn v) B u
  set ηN := etaQ δ s Δ v B z
  set ηk := etaQ δ s (trn Δ) (trn v) B u
  have qN := quad_holds δ s (K + n) M Δ v B (ctr B).1 (ctr B).2 z hδ hs hM hΔ hv hB hc hz
  have qk := quad_holds δ s K M (trn Δ) (trn v) B (ctr B).1 (ctr B).2 u hδ hs hM (fun j => hΔ _)
    (fun j => hv _) hB hc hu
  have pN := Lz_param hδ hs hM hB hp hc hp1 hp2 Δ v z hΔ hv hz
  have pk := Lz_param hδ hs hM hB hc hp hcp1 hcp2 (trn Δ) (trn v) u (fun j => hΔ _) (fun j => hv _) hu
  have hLkp := Lz_pos hδ hs (muF (trn Δ) (trn v) p.1 p.2) (sdF (trn v) p.2) (fun j => sdF_pos (fun j => hv _) hwp j) u
  have hLkc := Lz_pos hδ hs (muF (trn Δ) (trn v) (ctr B).1 (ctr B).2) (sdF (trn v) (ctr B).2)
    (fun j => sdF_pos (fun j => hv _) hwc j) u
  have hLNc := Lz_pos hδ hs (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (fun j => sdF_pos hv hwc j) z
  set LNp := Lz δ s (muF Δ v p.1 p.2) (sdF v p.2) z
  set Lkp := Lz δ s (muF (trn Δ) (trn v) p.1 p.2) (sdF (trn v) p.2) u
  set LNc := Lz δ s (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) z
  set Lkc := Lz δ s (muF (trn Δ) (trn v) (ctr B).1 (ctr B).2) (sdF (trn v) (ctr B).2) u
  set QN := Qs δ s M (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) z
  set Qk := Qs δ s M (muF (trn Δ) (trn v) (ctr B).1 (ctr B).2) (sdF (trn v) (ctr B).2) u
  have hgp : gF δ s Δ v p.1 p.2 u y = LNp / Lkp := rfl
  have hgc : gF δ s Δ v (ctr B).1 (ctr B).2 u y = LNc / Lkc := rfl
  constructor
  · have hle1 := gF_le_one hδ hs Δ v hv p.1 hwp u y
    refine le_min hle1 ?_
    show LNp / Lkp ≤ Real.exp (εN + εk + ηN + ηk) * QN / Qk
    rw [div_le_div_iff₀ hLkp qk.1]
    -- `L_N(p) Q_k ≤ e^{η_N} L_N(c) e^{ε_k} L_k(c) ≤ … ≤ e^{…} Q_N L_k(p)`.
    have a1 : LNp ≤ Real.exp ηN * (Real.exp εN * QN) := pN.trans (mul_le_mul_of_nonneg_left qN.2.2 (Real.exp_pos _).le)
    have a2 : Real.exp (-εk) * Qk ≤ Lkc := qk.2.1
    have a3 : Lkc ≤ Real.exp ηk * Lkp := pk
    have hQk : Qk ≤ Real.exp εk * Real.exp ηk * Lkp := by
      have : Qk ≤ Real.exp εk * Lkc := by
        rw [← div_le_iff₀' (Real.exp_pos _)]
        rw [Real.exp_neg, ← div_eq_inv_mul] at a2
        calc Qk / Real.exp εk = Real.exp (-εk) * Qk := by rw [Real.exp_neg, div_eq_inv_mul]
          _ ≤ Lkc := qk.2.1
      calc Qk ≤ Real.exp εk * Lkc := this
        _ ≤ Real.exp εk * (Real.exp ηk * Lkp) := mul_le_mul_of_nonneg_left a3 (Real.exp_pos _).le
        _ = _ := by ring
    calc LNp * Qk ≤ (Real.exp ηN * (Real.exp εN * QN)) * (Real.exp εk * Real.exp ηk * Lkp) :=
          mul_le_mul a1 hQk qk.1.le
            (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le qN.1.le))
      _ = Real.exp (εN + εk + ηN + ηk) * QN * Lkp := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
  · rw [hgc]
    show Real.exp (-(εN + εk)) * QN / Qk ≤ LNc / Lkc
    rw [div_le_div_iff₀ qk.1 hLkc]
    have b1 : Real.exp (-εN) * QN ≤ LNc := qN.2.1
    have b2 : Lkc ≤ Real.exp εk * Qk := qk.2.2
    calc Real.exp (-(εN + εk)) * QN * Lkc ≤ Real.exp (-(εN + εk)) * QN * (Real.exp εk * Qk) :=
          mul_le_mul_of_nonneg_left b2 (mul_nonneg (Real.exp_pos _).le qN.1.le)
      _ = (Real.exp (-εN) * QN * Qk) * (Real.exp (-εk) * Real.exp εk) := by
          rw [neg_add, Real.exp_add]; ring
      _ = Real.exp (-εN) * QN * Qk := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ LNc * Qk := mul_le_mul_of_nonneg_right b1 qk.1.le

theorem term_le_one (δ s : ℝ) (M : ℕ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box) (u : Fin K → ℕ)
    (y : Fin n → ℕ) : term δ s M Δ v B u y ≤ 1 := min_le_left _ _

theorem cover_holds : Standalone.D19FilteredLikelihood.cover := by
  intro δ s M K n Δ 𝒱 ℬ C u y hδ hs hM hΔ h𝒱 hv hℬ hC
  have hex := (exact_holds.2.2.2.2.2 δ s K n Δ 𝒱 ℬ u y hδ hs hΔ h𝒱 hv hℬ)
  obtain ⟨⟨θ, hθ, hθe⟩, hmax, hDpos, hDle⟩ := hex
  have hsup1 : (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (term δ s M Δ v B u y)) ≤ 1 :=
    iSup₂_le fun B _ => iSup₂_le fun v _ => ENNReal.ofReal_le_one.2 (term_le_one δ s M Δ v B u y)
  have hsupT : (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (term δ s M Δ v B u y)) ≠ ⊤ :=
    (hsup1.trans_lt ENNReal.one_lt_top).ne
  refine ⟨fun hz B hB v hvv p hp => box_bounds hδ hs hM Δ v hΔ (hv v hvv) (hC.1 B hB).1 u y hz hp,
    ?_, ?_, fun hz => ?_⟩
  · -- `D_filter ≤ D_cert`.
    unfold Dcert
    split_ifs with hz
    · rw [← hθe]
      obtain ⟨B, hB, hθB⟩ := hC.2 θ.2 hθ.2
      have h1 := (box_bounds hδ hs hM Δ θ.1 hΔ (hv _ hθ.1) (hC.1 B hB).1 u y hz hθB).1
      have h0 : 0 ≤ term δ s M Δ θ.1 B u y :=
        le_min zero_le_one (h1.trans' (gF_nonneg δ s Δ θ.1 θ.2.1 θ.2.2 u y) |> fun h => by
          exact (gF_nonneg δ s Δ θ.1 θ.2.1 θ.2.2 u y).trans (h1.trans (min_le_right _ _)))
      refine h1.trans ?_
      rw [← ENNReal.toReal_ofReal h0]
      exact ENNReal.toReal_mono hsupT (le_iSup₂_of_le B hB (le_iSup₂_of_le θ.1 hθ.1 le_rfl))
    · exact hDle
  · -- `D_cert ≤ 1`.
    unfold Dcert
    split_ifs
    · exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hsup1)
    · exact le_rfl
  · -- The lower bound.
    unfold Dlow
    refine ENNReal.toReal_le_of_le_ofReal hDpos.le (iSup₂_le fun B hB => iSup₂_le fun v hvv => ?_)
    refine ENNReal.ofReal_le_ofReal ((box_bounds hδ hs hM Δ v hΔ (hv v hvv) (hC.1 B hB).1 u y hz
      (ctr_mem (hC.1 B hB).1)).2.trans ?_)
    have hcB := ctr_mem (hC.1 B hB).1
    have hsub := (hC.1 B hB).2
    exact hmax (v, ctr B) ⟨hvv, ⟨hsub.1.trans hcB.1.1, hcB.1.2.trans hsub.2.1⟩,
      ⟨hsub.2.2.1.trans hcB.2.1, hcB.2.2.trans hsub.2.2.2⟩⟩

end Novel.D19FilteredLikelihood
