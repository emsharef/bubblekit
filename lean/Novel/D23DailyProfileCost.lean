import Novel.D23DailyProfileValid

/-!
# Claim 068, part 3: the cost of nuisance resets

* `refine`: a common-parameter choice for a group of blocks is one admissible choice of independent
  daily parameters, so the grouped profile is at most `P_day`; claim 033's full-record density is the
  product of the block densities at common parameters (`gV_flat`), so its profile is too.
* `calendar`: for `u_d = Δ_d`, claim 033 gives `H = K = 0` and `w* = Q_d/n_d`, so
  `log P_d = −(n_d/2) log(2πQ_d/n_d) − ½ Σ log Δ − Σ log y − n_d/2`. Weighted centering gives the
  full record's `Q` (`Qflat_eq`), and the difference of the logs is (6). It is nonnegative because the
  common profile is at most `P_day`; equality forces every block factor at the common optimum to
  equal its block maximum, hence (claim 033's unique optimizer) every block optimum
  `(â_d + Q_d/(2n_d), Q_d/n_d)` to be the common one, and conversely.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23DailyProfile

open Standalone.D23DailyProfile Standalone.D17ClockDrift Standalone.D13DriftNull Standalone.CEVSupport
  Novel.D17ClockDrift

variable {D : ℕ} {n : Fin D → ℕ}

theorem N_pos (hD : 0 < D) (hn : ∀ d, 0 < n d) : 0 < ∑ d, n d :=
  lt_of_lt_of_le (hn ⟨0, hD⟩) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))

theorem flatR_pos {Δ : (d : Fin D) → Fin (n d) → ℝ} (hΔ : ∀ d j, 0 < Δ d j) (k : Fin (∑ d, n d)) :
    0 < flatR Δ k := hΔ _ _

/-- A full-record clock's profile is at most `P_day` when its restrictions are retained. -/
theorem Dv_flat_le {Δ : (d : Fin D) → Fin (n d) → ℝ} {𝒰 : (d : Fin D) → Finset (Fin (n d) → ℝ)}
    (hD : 0 < D) (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) (hu : ∀ d, ∀ u ∈ 𝒰 d, ∀ j, 0 < u j)
    {s : ℝ} {y : Arr n} (hy : AllPos s y) {v : Fin (∑ d, n d) → ℝ} (hv : ∀ k, 0 < v k)
    (hr : ∀ d, restr v d ∈ 𝒰 d) : Dv (flatR Δ) v s (flatR (toR y)) ≤ Pday 𝒰 Δ s y := by
  rw [← sup_eq (N_pos hD hn) (flatR_pos hΔ) hv]
  refine iSup_le fun b => iSup_le fun w => iSup_le fun hw => ?_
  rw [gV_flat Δ v b w hy hn, ENNReal.ofReal_prod_of_nonneg fun d _ => gV_nonneg _ _ _ _]
  exact jointG_le hn hΔ hu (fun d => (restr v d, b, w)) fun d => ⟨hr d, hw⟩

theorem refine_holds : Standalone.D23DailyProfile.refine := by
  intro D n Δ 𝒰 hD hn hΔ h𝒰 hu s y hy
  refine ⟨fun D' G 𝒲 h𝒲 => ?_, fun 𝒱 hv hr => ?_⟩
  · have hle : Pgrp Δ G 𝒲 s y ≤ Pday 𝒰 Δ s y :=
      iSup_le fun sh => iSup_le fun hsh => iSup_le fun bw => iSup_le fun hbw =>
        jointG_le hn hΔ hu (fun d => (sh d, (bw (G d)).1, (bw (G d)).2)) fun d => ⟨h𝒲 sh hsh d, hbw _⟩
    exact ⟨hle, fun q => ENNReal.div_le_div_left hle _⟩
  · have hle : 𝒱.sup (fun v => Dv (flatR Δ) v s (flatR (toR y))) ≤ Pday 𝒰 Δ s y :=
      Finset.sup_le fun v hvv => Dv_flat_le hD hn hΔ hu hy (hv v hvv) (hr v hvv)
    exact ⟨hle, fun q => ENNReal.div_le_div_left hle _⟩

/-! ## The calendar shape on one block -/

section Cal

variable {m : ℕ} {Δ₁ : Fin m → ℝ} (hm : 0 < m) (hΔ₁ : ∀ j, 0 < Δ₁ j) (y0 : ℝ) (y : Fin m → ℝ)
include hm hΔ₁

theorem T_pos : 0 < ∑ j, Δ₁ j := Finset.sum_pos (fun j _ => hΔ₁ j) ⟨⟨0, hm⟩, Finset.mem_univ _⟩

omit hm in
theorem Av_cal : Av Δ₁ Δ₁ = ∑ j, Δ₁ j := by
  unfold Av; refine Finset.sum_congr rfl fun j _ => ?_
  have := (hΔ₁ j).ne'; field_simp

omit hm in
theorem Bv_cal : Bv Δ₁ Δ₁ y0 y = ∑ j, ret y0 y j := by
  unfold Bv; refine Finset.sum_congr rfl fun j _ => ?_
  have := (hΔ₁ j).ne'; field_simp

theorem Hv_cal : Hv Δ₁ Δ₁ = 0 := by
  unfold Hv; rw [Av_cal hΔ₁]
  have := (T_pos hm hΔ₁).ne'; field_simp; ring

theorem Kv_cal : Kv Δ₁ Δ₁ y0 y = 0 := by
  unfold Kv; rw [Av_cal hΔ₁, Bv_cal hΔ₁]
  have := (T_pos hm hΔ₁).ne'; field_simp; ring

/-- The calendar `Q` is the centered weighted sum of squares. -/
theorem Qv_cal : Qv Δ₁ Δ₁ y0 y =
    ∑ j, (ret y0 y j - (∑ j, ret y0 y j) / (∑ j, Δ₁ j) * Δ₁ j) ^ 2 / Δ₁ j := by
  have hT := T_pos hm hΔ₁
  unfold Qv Cv
  rw [Av_cal hΔ₁, Bv_cal hΔ₁]
  generalize hS : ∑ j, ret y0 y j = S
  generalize hTT : ∑ j, Δ₁ j = T at hT
  have hterm : ∀ j, (ret y0 y j - S / T * Δ₁ j) ^ 2 / Δ₁ j =
      ret y0 y j ^ 2 / Δ₁ j - 2 * (S / T) * ret y0 y j + (S / T) ^ 2 * Δ₁ j := fun j => by
    have := (hΔ₁ j).ne'; field_simp; ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hS, hTT]
  field_simp
  ring

theorem wstar_cal : wstar Δ₁ Δ₁ y0 y = Qv Δ₁ Δ₁ y0 y / m := by
  unfold wstar
  rw [Hv_cal hm hΔ₁, zero_mul, add_zero, Real.sqrt_sq (Nat.cast_nonneg _)]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp; ring

theorem bstar_cal : bstar Δ₁ Δ₁ y0 y =
    (∑ j, ret y0 y j) / (∑ j, Δ₁ j) + Qv Δ₁ Δ₁ y0 y / (2 * m) := by
  unfold bstar
  rw [wstar_cal hm hΔ₁, Av_cal hΔ₁, Bv_cal hΔ₁]
  have := (T_pos hm hΔ₁).ne'
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

theorem logDv_cal (hQ : 0 < Qv Δ₁ Δ₁ y0 y) : logDv Δ₁ Δ₁ y0 y =
    -((m : ℝ) / 2) * Real.log (2 * π * (Qv Δ₁ Δ₁ y0 y / m)) - (1 / 2) * ∑ j, Real.log (Δ₁ j) -
      ∑ j, Real.log (y j) - m / 2 := by
  unfold logDv
  rw [wstar_cal hm hΔ₁, Hv_cal hm hΔ₁, Kv_cal hm hΔ₁]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have := hQ.ne'
  field_simp
  ring

end Cal

/-- One block's weighted decomposition around a common rate `a`. -/
theorem block_decomp {m : ℕ} {Δ₁ R : Fin m → ℝ} (hm : 0 < m) (hΔ₁ : ∀ j, 0 < Δ₁ j) (a : ℝ) :
    ∑ j, (R j - a * Δ₁ j) ^ 2 / Δ₁ j =
      ∑ j, (R j - (∑ j, R j) / (∑ j, Δ₁ j) * Δ₁ j) ^ 2 / Δ₁ j +
        (∑ j, Δ₁ j) * ((∑ j, R j) / (∑ j, Δ₁ j) - a) ^ 2 := by
  have hT := T_pos hm hΔ₁
  set S := ∑ j, R j
  set T := ∑ j, Δ₁ j
  set ad := S / T
  have hterm : ∀ j, (R j - a * Δ₁ j) ^ 2 / Δ₁ j = (R j - ad * Δ₁ j) ^ 2 / Δ₁ j +
      2 * (ad - a) * (R j - ad * Δ₁ j) + (ad - a) ^ 2 * Δ₁ j := fun j => by
    have := (hΔ₁ j).ne'; field_simp; ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h0 : S - ad * T = 0 := by simp only [ad]; field_simp; ring
  rw [h0]; ring

/-! ## (6) -/

section Calendar

variable {Δ : (d : Fin D) → Fin (n d) → ℝ} (hD : 0 < D) (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j)
  {s : ℝ} {y : Arr n} (hy : AllPos s y)
include hn hΔ

theorem Qd_eq (d : Fin D) : Qv (Δ d) (Δ d) (start s y d) (toR y d) = Qd Δ s y d := by
  rw [Qv_cal (hn d) (hΔ d)]; rfl

omit hn hΔ in
theorem S_flat : ∑ k, ret s (flatR (toR y)) k = ∑ d, Sd s y d := by
  rw [sum_flat]; simp only [ret_flat]; rfl

omit hn hΔ in
theorem T_flat : ∑ k, flatR Δ k = ∑ d, Td Δ d := by
  rw [sum_flat]; simp only [flatR_e]; rfl

include hD in
theorem Qflat_eq : Qv (flatR Δ) (flatR Δ) s (flatR (toR y)) = Qtot Δ s y := by
  rw [Qv_cal (N_pos hD hn) (flatR_pos hΔ), S_flat, T_flat, sum_flat]
  simp only [ret_flat, flatR_e]
  unfold Qtot
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [block_decomp (hn d) (hΔ d)]
  rfl

include hD in
theorem Qtot_pos (hQ : ∀ d, 0 < Qd Δ s y d) : 0 < Qtot Δ s y := by
  unfold Qtot
  have h1 : 0 < ∑ d, Qd Δ s y d := Finset.sum_pos (fun d _ => hQ d) ⟨⟨0, hD⟩, Finset.mem_univ _⟩
  have h2 : 0 ≤ ∑ d, Td Δ d * (ahat Δ s y d - ahatAll Δ s y) ^ 2 :=
    Finset.sum_nonneg fun d _ => mul_nonneg (T_pos (hn d) (hΔ d)).le (sq_nonneg _)
  linarith

include hy in
theorem Pday_cal (hQ : ∀ d, 0 < Qd Δ s y d) :
    Pday (fun d => {Δ d}) Δ s y =
      ∏ d, ENNReal.ofReal (Real.exp (logDv (Δ d) (Δ d) (start s y d) (toR y d))) := by
  unfold Pday Pd
  refine Finset.prod_congr rfl fun d _ => ?_
  rw [Finset.sup_singleton]
  exact Dv_fin (posPath_block hy hn d) ((Qd_eq hn hΔ d).symm ▸ hQ d)

include hD hy in
theorem Pc_cal (hQ : ∀ d, 0 < Qd Δ s y d) :
    Dv (flatR Δ) (flatR Δ) s (flatR (toR y)) =
      ENNReal.ofReal (Real.exp (logDv (flatR Δ) (flatR Δ) s (flatR (toR y)))) :=
  Dv_fin (posPath_flat hy)
    ((Qflat_eq hD hn hΔ).symm ▸ Qtot_pos hD hn hΔ hQ)

include hD in
/-- The difference of the log profiles is (6). -/
theorem logs_eq (hQ : ∀ d, 0 < Qd Δ s y d) :
    ∑ d, logDv (Δ d) (Δ d) (start s y d) (toR y d) - logDv (flatR Δ) (flatR Δ) s (flatR (toR y)) =
      Jday Δ s y := by
  have hN := N_pos hD hn
  have hQt := Qtot_pos hD hn hΔ hQ
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hd : ∀ d, logDv (Δ d) (Δ d) (start s y d) (toR y d) =
      -((n d : ℝ) / 2) * Real.log (2 * π) - (n d : ℝ) / 2 * Real.log (Qd Δ s y d / n d) -
        (1 / 2) * ∑ j, Real.log (Δ d j) - ∑ j, Real.log (toR y d j) - (n d : ℝ) / 2 := fun d => by
    have hnd : (0 : ℝ) < n d := by exact_mod_cast hn d
    rw [logDv_cal (hn d) (hΔ d) _ _ ((Qd_eq hn hΔ d).symm ▸ hQ d), Qd_eq hn hΔ d,
      Real.log_mul hpi.ne' (div_pos (hQ d) hnd).ne']
    ring
  have hf : logDv (flatR Δ) (flatR Δ) s (flatR (toR y)) =
      -(((∑ d, n d : ℕ) : ℝ) / 2) * Real.log (2 * π) -
        ((∑ d, n d : ℕ) : ℝ) / 2 * Real.log (Qtot Δ s y / (∑ d, n d : ℕ)) -
        (1 / 2) * ∑ d, ∑ j, Real.log (Δ d j) - ∑ d, ∑ j, Real.log (toR y d j) -
        ((∑ d, n d : ℕ) : ℝ) / 2 := by
    have hNr : (0 : ℝ) < (∑ d, n d : ℕ) := by exact_mod_cast hN
    rw [logDv_cal hN (flatR_pos hΔ) _ _ ((Qflat_eq hD hn hΔ).symm ▸ hQt), Qflat_eq hD hn hΔ,
      Real.log_mul hpi.ne' (div_pos hQt hNr).ne', sum_flat, sum_flat (f := fun k => Real.log _)]
    simp only [flatR_e]
    ring
  rw [Finset.sum_congr rfl fun d _ => hd d, hf]
  unfold Jday
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.sum_div]
  push_cast
  ring

end Calendar

theorem restr_flatR {D : ℕ} {n : Fin D → ℕ} (x : (d : Fin D) → Fin (n d) → ℝ) (d : Fin D) :
    restr (flatR x) d = x d := by
  funext j; exact flatR_e x d j

theorem calendar_holds : Standalone.D23DailyProfile.calendar := by
  intro D n Δ hD hn hΔ s y hy hQ
  have hN := N_pos hD hn
  have hp := posPath_block hy hn
  have hpf := posPath_flat hy
  set A : Fin D → ℝ := fun d => logDv (Δ d) (Δ d) (start s y d) (toR y d)
  set Af := logDv (flatR Δ) (flatR Δ) s (flatR (toR y))
  have hPd := Pday_cal hn hΔ hy hQ
  have hPc := Pc_cal hD hn hΔ hy hQ
  have hPdR : (Pday (fun d => {Δ d}) Δ s y).toReal = Real.exp (∑ d, A d) := by
    rw [hPd, ENNReal.toReal_prod, Real.exp_sum]
    exact Finset.prod_congr rfl fun d _ => ENNReal.toReal_ofReal (Real.exp_pos _).le
  have hPcR : (Dv (flatR Δ) (flatR Δ) s (flatR (toR y))).toReal = Real.exp Af := by
    rw [hPc, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hlog : Real.log (Pday (fun d => {Δ d}) Δ s y).toReal -
      Real.log (Dv (flatR Δ) (flatR Δ) s (flatR (toR y))).toReal = Jday Δ s y := by
    rw [hPdR, hPcR, Real.log_exp, Real.log_exp]
    exact logs_eq hD hn hΔ hQ
  -- The common profile is at most `P_day`.
  have hle : Dv (flatR Δ) (flatR Δ) s (flatR (toR y)) ≤ Pday (fun d => {Δ d}) Δ s y :=
    Dv_flat_le hD hn hΔ (fun d u hu => by rw [Finset.mem_singleton.1 hu]; exact hΔ d) hy
      (flatR_pos hΔ) fun d => by rw [restr_flatR]; exact Finset.mem_singleton_self _
  have hPdT : Pday (fun d => {Δ d}) Δ s y < ⊤ := by
    rw [hPd]; exact ENNReal.prod_lt_top fun d _ => ENNReal.ofReal_lt_top
  have hPcT : Dv (flatR Δ) (flatR Δ) s (flatR (toR y)) < ⊤ := by rw [hPc]; exact ENNReal.ofReal_lt_top
  have hAle : Af ≤ ∑ d, A d := by
    have := ENNReal.toReal_mono hPdT.ne hle
    rw [hPdR, hPcR] at this
    exact Real.exp_le_exp.1 this
  have hJ : Jday Δ s y = ∑ d, A d - Af := (logs_eq hD hn hΔ hQ).symm
  -- The block densities at common parameters.
  have hprod : ∀ b w, gV (flatR Δ) (flatR Δ) b w s (flatR (toR y)) =
      ∏ d, gV (Δ d) (Δ d) b w (start s y d) (toR y d) := fun b w => by
    rw [gV_flat Δ (flatR Δ) b w hy hn]
    simp only [restr_flatR]
  have hQd : ∀ d, 0 < Qv (Δ d) (Δ d) (start s y d) (toR y d) := fun d => (Qd_eq hn hΔ d).symm ▸ hQ d
  have hQf : 0 < Qv (flatR Δ) (flatR Δ) s (flatR (toR y)) :=
    (Qflat_eq hD hn hΔ).symm ▸ Qtot_pos hD hn hΔ hQ
  refine ⟨Qflat_eq hD hn hΔ, hPdT, hPcT, hlog, by rw [hJ]; linarith, ⟨fun h0 => ?_, fun ⟨ha, hq⟩ => ?_⟩⟩
  · -- Equality forces every block optimum to be the common one.
    have hsum : ∑ d, A d = Af := by rw [hJ] at h0; linarith
    set b0 := bstar (flatR Δ) (flatR Δ) s (flatR (toR y))
    set w0 := wstar (flatR Δ) (flatR Δ) s (flatR (toR y))
    have hw0 : 0 < w0 := wstar_pos hN hQf
    have hatt := gV_attain hN (flatR_pos hΔ) (flatR_pos hΔ) hpf hQf
    have hopt : ∀ d, (b0, w0) = (bstar (Δ d) (Δ d) (start s y d) (toR y d),
        wstar (Δ d) (Δ d) (start s y d) (toR y d)) := by
      by_contra hne
      push Not at hne
      obtain ⟨d₀, hd₀⟩ := hne
      have hlt : ∏ d, gV (Δ d) (Δ d) b0 w0 (start s y d) (toR y d) < ∏ d, Real.exp (A d) :=
        Finset.prod_lt_prod₀ (fun d _ => gV_pos (Δ₁ := Δ d) (hΔ d) (hp d) b0 hw0)
          (fun d _ => (gV_lt (hn d) (hΔ d) (hΔ d) (hp d) (hQd d) b0 hw0).1)
          ⟨d₀, Finset.mem_univ _, (gV_lt (hn d₀) (hΔ d₀) (hΔ d₀) (hp d₀) (hQd d₀) b0 hw0).2 hd₀⟩
      rw [← hprod, hatt, ← Real.exp_sum, hsum] at hlt
      exact lt_irrefl _ hlt
    have hw : ∀ d, Qd Δ s y d / n d = w0 := fun d => by
      have := congrArg Prod.snd (hopt d)
      simp only at this
      rw [this, wstar_cal (hn d) (hΔ d), Qd_eq hn hΔ d]
    have hb : ∀ d, ahat Δ s y d = b0 - w0 / 2 := fun d => by
      have := congrArg Prod.fst (hopt d)
      simp only at this
      rw [this, bstar_cal (hn d) (hΔ d), Qd_eq hn hΔ d, ← hw d]
      have : (n d : ℝ) ≠ 0 := by exact_mod_cast (hn d).ne'
      unfold ahat Sd Td
      field_simp
      ring
    exact ⟨fun d d' => by rw [hb, hb], fun d d' => by rw [hw, hw]⟩
  · -- Conversely, the common block optimum attains every block maximum.
    set d₀ : Fin D := ⟨0, hD⟩
    set w := Qd Δ s y d₀ / n d₀
    set b := ahat Δ s y d₀ + w / 2
    have hw : 0 < w := div_pos (hQ d₀) (by exact_mod_cast hn d₀)
    have hopt : ∀ d, gV (Δ d) (Δ d) b w (start s y d) (toR y d) = Real.exp (A d) := fun d => by
      have hbd : bstar (Δ d) (Δ d) (start s y d) (toR y d) = b := by
        rw [bstar_cal (hn d) (hΔ d), Qd_eq hn hΔ d]
        have : Qd Δ s y d / (2 * n d) = (Qd Δ s y d / n d) / 2 := by ring
        rw [this, hq d d₀]
        exact congrArg (· + w / 2) (ha d d₀)
      have hwd : wstar (Δ d) (Δ d) (start s y d) (toR y d) = w := by
        rw [wstar_cal (hn d) (hΔ d), Qd_eq hn hΔ d, hq d d₀]
      rw [← hbd, ← hwd]
      exact gV_attain (hn d) (hΔ d) (hΔ d) (hp d) (hQd d)
    have hup := (gV_lt hN (flatR_pos hΔ) (flatR_pos hΔ) hpf hQf b hw).1
    rw [hprod, Finset.prod_congr rfl fun d _ => hopt d, ← Real.exp_sum] at hup
    have := Real.exp_le_exp.1 hup
    rw [hJ]; linarith

end Novel.D23DailyProfile
