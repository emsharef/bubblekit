import Novel.D30VariationProfileCert

/-!
# Claim 072, part 1: the time-only interpretation

* **(2) for continuous schedules.** On each grid interval the average of `exp(a_time)` is a value
  `exp(a_time(ξ_j))` (extreme values and the intermediate value theorem), so `z_j = a_time(ξ_j)` with
  ordered `ξ_j`, and the variation of `a_time` bounds `Σ|z_(j+1) − z_j|`.
* **Step schedules.** `aStep z = z ∘ idx` with a monotone index map, so its variation is at most that
  of `z` on `Fin (m + 1)`, which is `Σ|Dz|` by telescoping.
* **The grid law.** `log(G_(T_(j+1))/G_(T_j)) = (W_(T_(j+1)) − W_(T_j)) − (T_(j+1) − T_j)/2`.
  Mathlib's pre-Brownian motion has independent Gaussian increments with variance the time step, so
  the returns are independent `N(−v_j/2, v_j)` with `v_j = Δ_j e^(z_j)`: (1).
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal Interval

namespace Novel.D30VariationProfile

open Standalone.D30VariationProfile

variable {m : ℕ} {Δ : Fin (m + 1) → ℝ}

/-! ## The grid -/

theorem tg_eq (Δ : Fin (m + 1) → ℝ) (j : ℕ) : tg Δ j = psum Δ j := rfl

theorem tg_succ (Δ : Fin (m + 1) → ℝ) (j : Fin (m + 1)) : tg Δ (j + 1) = tg Δ j + Δ j :=
  psum_succ Δ j

theorem tg_zero (Δ : Fin (m + 1) → ℝ) : tg Δ 0 = 0 := by simp [tg]

theorem tg_mono (hΔ : ∀ j, 0 ≤ Δ j) {i i' : ℕ} (h : i ≤ i') : tg Δ i ≤ tg Δ i' :=
  Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢; omega)
    fun k _ _ => hΔ k

theorem tg_nonneg (hΔ : ∀ j, 0 ≤ Δ j) (i : ℕ) : 0 ≤ tg Δ i := by
  rw [← tg_zero Δ]; exact tg_mono hΔ (Nat.zero_le _)

/-! ## The mean value of a continuous function on an interval -/

theorem exists_avg {f : ℝ → ℝ} {p q : ℝ} (hpq : p < q) (hf : ContinuousOn f (Icc p q)) :
    ∃ ξ ∈ Icc p q, ∫ x in p..q, f x = (q - p) * f ξ := by
  obtain ⟨xm, hxm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hpq.le) hf
  obtain ⟨xM, hxM, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hpq.le) hf
  have hI := hf.intervalIntegrable_of_Icc (μ := volume) hpq.le
  have h1 : (q - p) * f xm ≤ ∫ x in p..q, f x := by
    have := intervalIntegral.integral_mono_on hpq.le (intervalIntegrable_const (μ := volume)) hI
      fun x hx => (hmin hx : f xm ≤ f x)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using this
  have h2 : ∫ x in p..q, f x ≤ (q - p) * f xM := by
    have := intervalIntegral.integral_mono_on hpq.le hI (intervalIntegrable_const (μ := volume))
      fun x hx => (hmax hx : f x ≤ f xM)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using this
  have hqp : 0 < q - p := sub_pos.2 hpq
  set avg := (∫ x in p..q, f x) / (q - p)
  have havg : avg ∈ uIcc (f xm) (f xM) := Icc_subset_uIcc ⟨by
    rw [le_div_iff₀ hqp]; linarith, by rw [div_le_iff₀ hqp]; linarith⟩
  obtain ⟨ξ, hξ, hfξ⟩ := intermediate_value_uIcc (hf.mono (uIcc_subset_Icc hxm hxM)) havg
  refine ⟨ξ, uIcc_subset_Icc hxm hxM hξ, ?_⟩
  rw [hfξ]; simp only [avg]; field_simp

/-! ## Integrals over the grid -/

/-- From the pieces `∫_(t_j)^(t_(j+1)) e^(a) = Δ_j e^(w_j)`: (2) recovers `w`, and `A(t_j)` is the
operational grid. -/
theorem Aint_tg (hΔ : ∀ j, 0 < Δ j) {a : ℝ → ℝ} {w : Fin (m + 1) → ℝ}
    (hint : ∀ j : Fin (m + 1), IntervalIntegrable (fun s => Real.exp (a s)) volume (tg Δ j)
      (tg Δ (j + 1)))
    (hval : ∀ j : Fin (m + 1), ∫ s in tg Δ j..tg Δ (j + 1), Real.exp (a s) = Δ j * Real.exp (w j)) :
    zOf Δ a = w ∧ ∀ j ≤ m + 1, Aint a (tg Δ j) = tg (fun k => Δ k * Real.exp (w k)) j := by
  have key : ∀ j ≤ m + 1, IntervalIntegrable (fun s => Real.exp (a s)) volume 0 (tg Δ j) ∧
      Aint a (tg Δ j) = tg (fun k => Δ k * Real.exp (w k)) j := by
    intro j hj
    induction j with
    | zero => simp [tg_zero, Aint]
    | succ j ih =>
      obtain ⟨hI, hA⟩ := ih (by omega)
      set J : Fin (m + 1) := ⟨j, by omega⟩
      have hJ : (J : ℕ) = j := rfl
      have hI' := hint J
      rw [hJ] at hI'
      refine ⟨hI.trans hI', ?_⟩
      unfold Aint at hA ⊢
      rw [← intervalIntegral.integral_add_adjacent_intervals hI hI', hA, ← hJ, hval J, tg_succ]
  refine ⟨funext fun j => ?_, fun j hj => (key j hj).2⟩
  unfold zOf
  rw [(key (j + 1) (by omega)).2, (key j (by omega)).2, tg_succ, add_sub_cancel_left,
    mul_div_cancel_left₀ _ (hΔ j).ne', Real.log_exp]

/-! ## Continuous schedules -/

theorem cont_part (hΔ : ∀ j, 0 < Δ j) {V : ℝ} (hV : 0 ≤ V) {a : ℝ → ℝ}
    (ha : ContinuousOn a (Icc 0 (tg Δ (m + 1))))
    (hvar : eVariationOn a (Icc 0 (tg Δ (m + 1))) ≤ ENNReal.ofReal V) :
    zOf Δ a ∈ ZV V ∧ ∀ j ≤ m + 1, Aint a (tg Δ j) = tg (fun k => Δ k * Real.exp (zOf Δ a k)) j := by
  have hΔ0 : ∀ j, 0 ≤ Δ j := fun j => (hΔ j).le
  have hsub : ∀ j : Fin (m + 1), Icc (tg Δ j) (tg Δ (j + 1)) ⊆ Icc 0 (tg Δ (m + 1)) := fun j =>
    Icc_subset_Icc (tg_nonneg hΔ0 _) (tg_mono hΔ0 (by omega))
  have hlt : ∀ j : Fin (m + 1), tg Δ j < tg Δ (j + 1) := fun j => by rw [tg_succ]; linarith [hΔ j]
  have hξ : ∀ j : Fin (m + 1), ∃ ξ ∈ Icc (tg Δ j) (tg Δ (j + 1)),
      ∫ s in tg Δ j..tg Δ (j + 1), Real.exp (a s) = Δ j * Real.exp (a ξ) := fun j => by
    obtain ⟨ξ, h1, h2⟩ := exists_avg (hlt j) (Real.continuous_exp.comp_continuousOn (ha.mono (hsub j)))
    simp only [Function.comp_apply] at h2
    exact ⟨ξ, h1, by rw [h2, tg_succ]; ring_nf⟩
  choose ξ hξI hξv using hξ
  obtain ⟨hz, hA⟩ := Aint_tg hΔ (w := fun j => a (ξ j)) (fun j =>
    (Real.continuous_exp.comp_continuousOn (ha.mono (hsub j))).intervalIntegrable_of_Icc
      (hlt j).le) hξv
  refine ⟨?_, by rw [hz]; exact hA⟩
  rw [hz]
  -- The ordered points `ξ_j` bound the sum by the variation.
  set u : ℕ → ℝ := fun i => ξ ⟨min i m, by omega⟩
  have hξmono : Monotone ξ := fun j j' h => by
    rcases eq_or_lt_of_le h with rfl | hl
    · exact le_rfl
    · calc ξ j ≤ tg Δ (j + 1) := (hξI j).2
        _ ≤ tg Δ j' := tg_mono hΔ0 (Fin.lt_def.1 hl)
        _ ≤ ξ j' := (hξI j').1
  have hmono : Monotone u := hξmono.comp fun i i' h => Fin.mk_le_mk.2 (min_le_min_right m h)
  have hmem : ∀ i, u i ∈ Icc 0 (tg Δ (m + 1)) := fun i => hsub _ (hξI _)
  have hsum := eVariationOn.sum_le (f := a) (n := m) hmono hmem
  have heq : ∑ i ∈ Finset.range m, edist (a (u (i + 1))) (a (u i)) =
      ENNReal.ofReal (∑ i : Fin m, |Dz (fun j => a (ξ j)) i|) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _,
      ← Fin.sum_univ_eq_sum_range (fun i => edist (a (u (i + 1))) (a (u i)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : u (i + 1) = ξ i.succ := by
      simp only [u]; congr 1; ext; simp
    have h2 : u i = ξ i.castSucc := by
      simp only [u]; congr 1; ext; simp
    rw [h1, h2, edist_dist, Real.dist_eq]
    rfl
  rw [heq] at hsum
  exact (ENNReal.ofReal_le_ofReal_iff hV).1 (hsum.trans hvar)

/-! ## Step schedules -/

/-- The interval index `#{k : t_(k+1) < s}`. -/
noncomputable def idx (Δ : Fin (m + 1) → ℝ) (s : ℝ) : Fin (m + 1) :=
  ⟨(Finset.univ.filter fun k : Fin m => tg Δ (k + 1) < s).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

theorem aStep_eq (Δ z : Fin (m + 1) → ℝ) : aStep Δ z = z ∘ idx Δ := rfl

theorem idx_mono (Δ : Fin (m + 1) → ℝ) : Monotone (idx Δ) := fun s s' h => by
  unfold idx
  refine Fin.mk_le_mk.2 (Finset.card_le_card fun k hk => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  linarith

theorem idx_eq (hΔ : ∀ j, 0 < Δ j) (j : Fin (m + 1)) {s : ℝ} (hs : s ∈ Ioc (tg Δ j) (tg Δ (j + 1))) :
    idx Δ s = j := by
  have hΔ0 : ∀ j, 0 ≤ Δ j := fun j => (hΔ j).le
  have hf : (Finset.univ.filter fun k : Fin m => tg Δ (k + 1) < s) =
      Finset.univ.filter fun k : Fin m => (k : ℕ) < j := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hk
      have : tg Δ (j + 1) ≤ tg Δ (k + 1) := tg_mono hΔ0 (by omega)
      linarith [hs.2]
    · intro h
      have : tg Δ (k + 1) ≤ tg Δ j := tg_mono hΔ0 (by omega)
      linarith [hs.1]
  unfold idx
  ext
  simp only [hf, Fin.card_filter_val_lt]
  omega

/-- The variation of `z` on `Fin (m + 1)` is at most `Σ|Dz|`. -/
noncomputable def Wv (z : Fin (m + 1) → ℝ) (b : ℕ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < b), |Dz z k|

theorem abs_sub_le_Wv (z : Fin (m + 1) → ℝ) {a b : Fin (m + 1)} (hab : a ≤ b) :
    |z b - z a| ≤ Wv z b - Wv z a := by
  have hsub : (Finset.univ.filter fun k : Fin m => (k : ℕ) < a) ⊆
      Finset.univ.filter fun k : Fin m => (k : ℕ) < b := fun k hk => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact lt_of_lt_of_le hk (Fin.le_def.1 hab)
  have e : z b - z a = ∑ k ∈ (Finset.univ.filter fun k : Fin m => (k : ℕ) < b) \
      Finset.univ.filter (fun k : Fin m => (k : ℕ) < a), Dz z k := by
    rw [Finset.sum_sdiff_eq_sub hsub, ← sub_zero_eq, ← sub_zero_eq]; ring
  have e' : Wv z b - Wv z a = ∑ k ∈ (Finset.univ.filter fun k : Fin m => (k : ℕ) < b) \
      Finset.univ.filter (fun k : Fin m => (k : ℕ) < a), |Dz z k| := by
    unfold Wv; rw [Finset.sum_sdiff_eq_sub hsub]
  rw [e, e']
  exact Finset.abs_sum_le_sum_abs _ _

theorem Wv_le (z : Fin (m + 1) → ℝ) (b : ℕ) : Wv z b ≤ ∑ i, |Dz z i| :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => abs_nonneg _

theorem Wv_mono (z : Fin (m + 1) → ℝ) {b b' : ℕ} (h : b ≤ b') : Wv z b ≤ Wv z b' :=
  Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢; omega)
    fun _ _ _ => abs_nonneg _

theorem eVar_fin_le (z : Fin (m + 1) → ℝ) :
    eVariationOn z univ ≤ ENNReal.ofReal (∑ i, |Dz z i|) := by
  refine iSup_le fun ⟨n, u, hu, _⟩ => ?_
  have h : ∀ n, ∑ i ∈ Finset.range n, edist (z (u (i + 1))) (z (u i)) ≤
      ENNReal.ofReal (Wv z (u n) - Wv z (u 0)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : edist (z (u (n + 1))) (z (u n)) ≤ ENNReal.ofReal (Wv z (u (n + 1)) - Wv z (u n)) := by
        rw [edist_dist, Real.dist_eq]
        exact ENNReal.ofReal_le_ofReal (abs_sub_le_Wv z (hu (Nat.le_succ n)))
      calc _ ≤ ENNReal.ofReal (Wv z (u n) - Wv z (u 0)) +
            ENNReal.ofReal (Wv z (u (n + 1)) - Wv z (u n)) := add_le_add ih h1
        _ = ENNReal.ofReal (Wv z (u (n + 1)) - Wv z (u 0)) := by
          rw [← ENNReal.ofReal_add (sub_nonneg.2 (Wv_mono z (Fin.le_def.1 (hu (Nat.zero_le n)))))
            (sub_nonneg.2 (Wv_mono z (Fin.le_def.1 (hu (Nat.le_succ n)))))]
          congr 1; ring
  refine (h n).trans (ENNReal.ofReal_le_ofReal ?_)
  have := Wv_le z (u n)
  have : 0 ≤ Wv z (u 0) := Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

theorem step_part (hΔ : ∀ j, 0 < Δ j) {V : ℝ} {z : Fin (m + 1) → ℝ} (hz : z ∈ ZV V) :
    eVariationOn (aStep Δ z) (Icc 0 (tg Δ (m + 1))) ≤ ENNReal.ofReal V ∧ zOf Δ (aStep Δ z) = z ∧
      ∀ j ≤ m + 1, Aint (aStep Δ z) (tg Δ j) = tg (fun k => Δ k * Real.exp (z k)) j := by
  have hΔ0 : ∀ j, 0 ≤ Δ j := fun j => (hΔ j).le
  refine ⟨?_, ?_⟩
  · rw [aStep_eq]
    exact (eVariationOn.comp_le_of_monotoneOn z (idx Δ) ((idx_mono Δ).monotoneOn _) (mapsTo_univ _ _)).trans
      ((eVar_fin_le z).trans (ENNReal.ofReal_le_ofReal hz))
  have hpt : ∀ j : Fin (m + 1), ∀ s ∈ Ι (tg Δ j) (tg Δ (j + 1)),
      Real.exp (aStep Δ z s) = Real.exp (z j) := fun j s hs => by
    rw [uIoc_of_le (tg_mono hΔ0 (Nat.le_succ _))] at hs
    rw [aStep_eq, Function.comp_apply, idx_eq hΔ j hs]
  have hint : ∀ j : Fin (m + 1), IntervalIntegrable (fun s => Real.exp (aStep Δ z s)) volume
      (tg Δ j) (tg Δ (j + 1)) := fun j =>
    (intervalIntegrable_const (μ := volume) (c := Real.exp (z j))).congr
      fun s hs => (hpt j s hs).symm
  have hval : ∀ j : Fin (m + 1), ∫ s in tg Δ j..tg Δ (j + 1), Real.exp (aStep Δ z s) =
      Δ j * Real.exp (z j) := fun j => by
    rw [intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => hpt j s hs),
      intervalIntegral.integral_const, tg_succ, smul_eq_mul]
    ring
  exact Aint_tg hΔ hint hval

/-! ## The grid law -/

theorem Rgrid_eq {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) {s₀ : ℝ} (hs₀ : 0 < s₀) (hΔ : ∀ j, 0 < Δ j)
    (z : Fin (m + 1) → ℝ) (ω : Ω) (j : Fin (m + 1)) :
    Rgrid W s₀ Δ z ω j =
      (W (tg (fun k => Δ k * Real.exp (z k)) (j + 1)).toNNReal ω -
        W (tg (fun k => Δ k * Real.exp (z k)) j).toNNReal ω) - Δ j * Real.exp (z j) / 2 := by
  have h0 : ∀ i, 0 ≤ tg (fun k => Δ k * Real.exp (z k)) i := tg_nonneg fun k =>
    (mul_pos (hΔ k) (Real.exp_pos _)).le
  unfold Rgrid
  simp only
  rw [mul_div_mul_left _ _ hs₀.ne', ← Real.exp_sub, Real.log_exp, Real.coe_toNNReal _ (h0 _),
    Real.coe_toNNReal _ (h0 _), tg_succ]
  ring

theorem grid_law {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} (hW : IsPreBrownianReal W P) {s₀ : ℝ} (hs₀ : 0 < s₀) (hΔ : ∀ j, 0 < Δ j)
    (z : Fin (m + 1) → ℝ) : HasLaw (fun ω j => Rgrid W s₀ Δ z ω j) (nullLaw Δ z) P := by
  set w : Fin (m + 1) → ℝ := fun k => Δ k * Real.exp (z k)
  have hw : ∀ k, 0 < w k := fun k => mul_pos (hΔ k) (Real.exp_pos _)
  set T : ℕ → ℝ≥0 := fun i => (tg w i).toNNReal
  set incr : Fin (m + 1) → Ω → ℝ := fun j ω => W (T (j + 1)) ω - W (T j) ω
  set g : Fin (m + 1) → ℝ → ℝ := fun j x => x - w j / 2
  have hR : (fun ω j => Rgrid W s₀ Δ z ω j) = fun ω j => g j (incr j ω) := by
    funext ω j; exact Rgrid_eq W hs₀ hΔ z ω j
  have hlaw : ∀ j, HasLaw (incr j) (gaussianReal 0 (w j).toNNReal) P := fun j => by
    have h := hW.hasLaw_sub (T (j + 1)) (T j)
    have hT : ∀ i, (T i : ℝ) = tg w i := fun i =>
      Real.coe_toNNReal _ (tg_nonneg (fun k => (hw k).le) _)
    have e : nndist (T (j + 1)).1 (T j).1 = (w j).toNNReal := by
      apply NNReal.eq
      rw [coe_nndist, Real.dist_eq]
      change |(T (j + 1) : ℝ) - T j| = ((w j).toNNReal : ℝ)
      rw [hT, hT, tg_succ, add_sub_cancel_left, abs_of_pos (hw j), Real.coe_toNNReal _ (hw j).le]
    rw [e] at h
    exact h
  have hind : iIndepFun incr P := by
    have h := hW.hasIndepIncrements (m + 1) (fun i : Fin (m + 2) => T i) (fun i i' h =>
      Real.toNNReal_le_toNNReal (tg_mono (fun k => (hw k).le) (Fin.le_def.1 h)))
    have e : incr = fun (i : Fin (m + 1)) ω => W ((fun i : Fin (m + 2) => T i) i.succ) ω -
        W ((fun i : Fin (m + 2) => T i) i.castSucc) ω := by
      funext i ω; simp [incr, Fin.val_succ]
    rw [e]; exact h
  have hind' := hind.comp g fun j => measurable_id.sub_const _
  have hae : ∀ j, AEMeasurable (fun ω => g j (incr j ω)) P := fun j =>
    (measurable_id.sub_const _).comp_aemeasurable (hlaw j).aemeasurable
  refine ⟨?_, ?_⟩
  · rw [hR]; exact AEMeasurable.of_eval hae
  · rw [hR, (iIndepFun_iff_map_fun_eq_pi_map hae).1 hind']
    unfold nullLaw
    congr 1
    funext j
    have e : (fun ω => g j (incr j ω)) = (fun x => x + -(w j / 2)) ∘ incr j := by
      funext ω; simp [g, sub_eq_add_neg]
    rw [e, ← AEMeasurable.map_map_of_aemeasurable (measurable_add_const _).aemeasurable
      (hlaw j).aemeasurable, (hlaw j).map_eq, gaussianReal_map_add_const, zero_add]
    congr 1
    simp only [w]; ring

theorem interpretation_holds : Standalone.D30VariationProfile.interpretation := by
  intro m Δ V hΔ hV
  exact ⟨fun a ha hvar => cont_part hΔ hV ha hvar, fun z hz => step_part hΔ hz,
    fun P _ W s₀ z hW hs₀ => grid_law hW hs₀ hΔ z⟩

end Novel.D30VariationProfile
