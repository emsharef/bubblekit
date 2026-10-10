import Novel.D30VariationProfileScalar
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Metrizable.Basic

/-!
# Claim 072, part 1: the profile (3)

* **Expansion.** Each normal density of (1) is `exp` of `f_j(z_j)` plus terms free of `z`, so the
  product is `exp ℓ_R(z)`, and the product law is Lebesgue measure with that density.
* **Borel.** `Z_V` has a countable dense subset; `ℓ_R(z)` is continuous in `z`, so the supremum is a
  countable supremum of continuous functions of `R`.
* **Existence.** For `R_k ≠ 0`, `f_k(s) ≤ −s/2 − κs²/2` with `κ = min(A_k, B_k) > 0`, every other
  `f_j(s) ≤ −s/2`, and feasibility gives `|z_j − z_1| ≤ V`. The upper level set of `ℓ_R` through
  `z = 0` is therefore bounded, hence compact, and the maximum is attained.
* **Uniqueness.** `f_j` lies strictly below its tangents (`tangent_lt`), so `ℓ_R` is strictly concave
  on the convex set `Z_V`.
* **`V = 0`.** `Z_0` is the constant vectors and (4) is the positive root of the summed scalar
  problem (`root_max`).
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D30VariationProfile

open Standalone.D30VariationProfile

variable {m : ℕ} {Δ : Fin (m + 1) → ℝ}

/-! ## Expansion -/

theorem gauss_eq (Δ' z r : ℝ) (hΔ : 0 < Δ') :
    gaussianPDFReal (-(Δ' * Real.exp z) / 2) (Δ' * Real.exp z).toNNReal r =
      Real.exp (-(1 / 2) * Real.log (2 * π) - (1 / 2) * Real.log Δ' - r / 2 +
        fj (r ^ 2 / (2 * Δ')) (Δ' / 8) z) := by
  have hv : 0 < Δ' * Real.exp z := mul_pos hΔ (Real.exp_pos z)
  rw [gaussianPDFReal_def, Real.coe_toNNReal _ hv.le]
  simp only
  have h2 : 0 < 2 * π * (Δ' * Real.exp z) := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h2.le, Real.rpow_def_of_pos h2, ← Real.exp_add]
  congr 1
  rw [Real.log_mul (by positivity) hv.ne', Real.log_mul hΔ.ne' (Real.exp_pos z).ne',
    Real.log_exp]
  unfold fj
  rw [Real.exp_neg]
  field_simp
  ring

theorem exp_ell (hΔ : ∀ j, 0 < Δ j) (R z : Fin (m + 1) → ℝ) :
    Real.exp (ell Δ R z) =
      ∏ j, gaussianPDFReal (-(Δ j * Real.exp (z j)) / 2) (Δ j * Real.exp (z j)).toNNReal (R j) := by
  simp_rw [fun j => gauss_eq (Δ j) (z j) (R j) (hΔ j), ← Real.exp_sum]
  congr 1
  unfold ell cR Aco Bco
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  push_cast
  rw [← Finset.sum_div]
  ring

theorem lintegral_pi_prod {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ) (hg0 : ∀ i x, 0 ≤ g i x)
    (hgi : ∀ i, Integrable (g i)) :
    ∫⁻ x, ∏ i, ENNReal.ofReal (g i (x i)) ∂(Measure.pi fun _ : ι => (volume : Measure ℝ)) =
      ∏ i, ∫⁻ y, ENNReal.ofReal (g i y) := by
  have hprod : ∀ x : ι → ℝ, ∏ i, ENNReal.ofReal (g i (x i)) = ENNReal.ofReal (∏ i, g i (x i)) :=
    fun x => (ENNReal.ofReal_prod_of_nonneg fun i _ => hg0 i _).symm
  simp_rw [hprod]
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod hgi)
    (Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => hg0 i _),
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg fun i _ =>
      integral_nonneg fun x => hg0 i x]
  exact Finset.prod_congr rfl fun i _ =>
    ofReal_integral_eq_lintegral_ofReal (hgi i) (Eventually.of_forall fun x => hg0 i x)

theorem nullLaw_eq (hΔ : ∀ j, 0 < Δ j) (z : Fin (m + 1) → ℝ) :
    nullLaw Δ z = volume.withDensity fun R => ENNReal.ofReal (Real.exp (ell Δ R z)) := by
  have hv : ∀ j, (Δ j * Real.exp (z j)).toNNReal ≠ 0 := fun j => by
    simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; exact mul_pos (hΔ j) (Real.exp_pos _)
  unfold nullLaw
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  simp_rw [gaussianReal_apply _ (hv _), exp_ell hΔ]
  have hind : ∀ R : Fin (m + 1) → ℝ, (Set.univ.pi s).indicator (fun R => ENNReal.ofReal
      (∏ j, gaussianPDFReal (-(Δ j * Real.exp (z j)) / 2) (Δ j * Real.exp (z j)).toNNReal (R j))) R =
      ∏ j, ENNReal.ofReal ((s j).indicator (gaussianPDFReal (-(Δ j * Real.exp (z j)) / 2)
        (Δ j * Real.exp (z j)).toNNReal) (R j)) := fun R => by
    by_cases hR : R ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hR, ENNReal.ofReal_prod_of_nonneg fun j _ =>
        gaussianPDFReal_nonneg _ _ _]
      exact Finset.prod_congr rfl fun j _ => by rw [Set.indicator_of_mem (hR j (mem_univ _))]
    · rw [Set.indicator_of_notMem hR]
      obtain ⟨j, hj⟩ : ∃ j, R j ∉ s j := by simpa [Set.mem_univ_pi] using hR
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by
        rw [Set.indicator_of_notMem hj, ENNReal.ofReal_zero])).symm
  simp_rw [hind]
  rw [lintegral_pi_prod (fun j => (s j).indicator (gaussianPDFReal (-(Δ j * Real.exp (z j)) / 2)
    (Δ j * Real.exp (z j)).toNNReal)) (fun j x => Set.indicator_nonneg (fun y _ =>
    gaussianPDFReal_nonneg _ _ y) x) fun j =>
      (integrable_gaussianPDFReal _ _).indicator (hs j)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← lintegral_indicator (hs j)]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ s j
  · simp [Set.indicator_of_mem hx, gaussianPDF]
  · simp [Set.indicator_of_notMem hx]

/-! ## Elementary facts about `Z_V` -/

theorem zero_mem (hV : 0 ≤ V) : (0 : Fin (m + 1) → ℝ) ∈ ZV (m := m) V := by
  simp [ZV, Dz, hV]

theorem const_mem (hV : 0 ≤ V) (t : ℝ) : (fun _ => t : Fin (m + 1) → ℝ) ∈ ZV (m := m) V := by
  simp [ZV, Dz, hV]

theorem ZV_mono {V V' : ℝ} (h : V ≤ V') : ZV (m := m) V ⊆ ZV V' := fun _ hz => le_trans hz h

/-- `z_j − z_0 = Σ_(i<j) (Dz)_i`. -/
theorem sub_zero_eq (z : Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
    z j - z 0 = ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), Dz z i := by
  induction j using Fin.induction with
  | zero => simp
  | succ i ih =>
    have hs : Finset.univ.filter (fun i' : Fin m => (i' : ℕ) < (i.succ : ℕ)) =
        insert i (Finset.univ.filter fun i' : Fin m => (i' : ℕ) < (i.castSucc : ℕ)) := by
      ext i'; simp only [Fin.val_succ, Fin.val_castSucc, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_insert]; omega
    rw [hs, Finset.sum_insert (by simp), ← ih]
    unfold Dz; ring

theorem abs_sub_zero_le {V : ℝ} {z : Fin (m + 1) → ℝ} (hz : z ∈ ZV V) (j : Fin (m + 1)) :
    |z j - z 0| ≤ V := by
  rw [sub_zero_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hz)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => abs_nonneg _

theorem ZV_convex {V : ℝ} {z z' : Fin (m + 1) → ℝ} (hz : z ∈ ZV V) (hz' : z' ∈ ZV V) :
    (fun j => (z j + z' j) / 2) ∈ ZV (m := m) V := by
  unfold ZV Dz at *
  simp only [mem_ofPred_eq] at *
  calc ∑ i : Fin m, |(z i.succ + z' i.succ) / 2 - (z i.castSucc + z' i.castSucc) / 2|
      ≤ ∑ i : Fin m, (|z i.succ - z i.castSucc| / 2 + |z' i.succ - z' i.castSucc| / 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [show (z i.succ + z' i.succ) / 2 - (z i.castSucc + z' i.castSucc) / 2 =
          (z i.succ - z i.castSucc) / 2 + (z' i.succ - z' i.castSucc) / 2 by ring]
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_div, abs_div, abs_two]
    _ ≤ V := by rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]; linarith

theorem isClosed_ZV (V : ℝ) : IsClosed (ZV (m := m) V) :=
  isClosed_le (continuous_finsetSum _ fun i _ => by unfold Dz; fun_prop) continuous_const

theorem continuous_ell_z (Δ R : Fin (m + 1) → ℝ) : Continuous (ell Δ R) := by
  unfold ell fj; fun_prop

theorem continuous_ell_R (Δ z : Fin (m + 1) → ℝ) : Continuous fun R => ell Δ R z := by
  unfold ell cR fj Aco; fun_prop

/-! ## Measurability, positivity, monotonicity -/

theorem measurable_PV (V : ℝ) : Measurable (PV Δ V) := by
  obtain ⟨D, hDs, hDc, hDd⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (ZV (m := m) V)).exists_countable_dense_subset
  have heq : PV Δ V = fun R => ⨆ z ∈ D, ENNReal.ofReal (Real.exp (ell Δ R z)) := by
    funext R
    refine le_antisymm (iSup₂_le fun z hz => ?_) (iSup₂_mono' fun z hz => ⟨z, hDs hz, le_rfl⟩)
    have hcl : IsClosed {z : Fin (m + 1) → ℝ | ENNReal.ofReal (Real.exp (ell Δ R z)) ≤
        ⨆ z ∈ D, ENNReal.ofReal (Real.exp (ell Δ R z))} :=
      isClosed_le (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_ell_z Δ R)))
        continuous_const
    exact closure_minimal (fun z hz => le_iSup₂ (f := fun z (_ : z ∈ D) =>
      ENNReal.ofReal (Real.exp (ell Δ R z))) z hz) hcl (hDd hz)
  rw [heq]
  exact Measurable.biSup _ hDc fun z _ => ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (continuous_ell_R Δ z).measurable)

theorem le_PV {V : ℝ} {z : Fin (m + 1) → ℝ} (hz : z ∈ ZV V) (R : Fin (m + 1) → ℝ) :
    ENNReal.ofReal (Real.exp (ell Δ R z)) ≤ PV Δ V R :=
  le_iSup₂ (f := fun z (_ : z ∈ ZV V) => ENNReal.ofReal (Real.exp (ell Δ R z))) z hz

theorem PV_pos {V : ℝ} (hV : 0 ≤ V) (R : Fin (m + 1) → ℝ) : 0 < PV Δ V R :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.exp_pos _)) (le_PV (zero_mem hV) R)

theorem PV_mono {V V' : ℝ} (h : V ≤ V') (R : Fin (m + 1) → ℝ) : PV Δ V R ≤ PV Δ V' R :=
  iSup₂_mono' fun z hz => ⟨z, ZV_mono h hz, le_rfl⟩

/-! ## Zero returns -/

theorem PV_zero (hΔ : ∀ j, 0 < Δ j) {V : ℝ} (hV : 0 ≤ V) : PV Δ V 0 = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  set Bs := ∑ j, Bco Δ j
  set c0 := cR Δ (0 : Fin (m + 1) → ℝ)
  have hn : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  set t := -(2 / ((m + 1 : ℕ) : ℝ)) * (|c0| + |Bs| + |Real.log (r + 1)|)
  have ht : t ≤ 0 := by
    have : 0 ≤ |c0| + |Bs| + |Real.log (r + 1)| := by positivity
    have : 0 ≤ 2 / ((m + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hB : ∀ j, 0 ≤ Bco Δ j := fun j => by unfold Bco; linarith [hΔ j]
  have hell : ell Δ 0 (fun _ => t) = c0 - ((m + 1 : ℕ) : ℝ) * t / 2 - Bs * Real.exp t := by
    unfold ell fj Aco
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      zero_mul, sub_zero, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, Bs, c0]
    push_cast; ring
  have hlin : -((m + 1 : ℕ) : ℝ) * t / 2 = |c0| + |Bs| + |Real.log (r + 1)| := by
    simp only [t]; field_simp
  have hBe : Bs * Real.exp t ≤ |Bs| := by
    have := Real.exp_le_one_iff.2 ht
    have hBs : 0 ≤ Bs := Finset.sum_nonneg fun j _ => hB j
    calc Bs * Real.exp t ≤ Bs * 1 := by gcongr
      _ ≤ |Bs| := by rw [mul_one]; exact le_abs_self _
  have hge : Real.log (r + 1) ≤ ell Δ 0 (fun _ => t) := by
    rw [hell]
    have := neg_abs_le c0
    have := le_abs_self (Real.log (r + 1))
    linarith
  have hr1 : ((r : ℝ) + 1) ≤ Real.exp (ell Δ 0 fun _ => t) := by
    calc ((r : ℝ) + 1) = Real.exp (Real.log (r + 1)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.2 hge
  calc (r : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (ell Δ 0 fun _ => t)) := by
        rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ PV Δ V 0 := le_PV (const_mem hV t) 0

/-! ## Existence and uniqueness for nonzero returns -/

theorem Aco_nonneg (hΔ : ∀ j, 0 < Δ j) (R : Fin (m + 1) → ℝ) (j : Fin (m + 1)) : 0 ≤ Aco Δ R j := by
  unfold Aco; have := hΔ j; positivity

theorem Bco_pos (hΔ : ∀ j, 0 < Δ j) (j : Fin (m + 1)) : 0 < Bco Δ j := by
  unfold Bco; linarith [hΔ j]

theorem fj_le_lin {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (s : ℝ) : fj A B s ≤ -s / 2 := by
  unfold fj; have := Real.exp_pos (-s); have := Real.exp_pos s; nlinarith

theorem fj_le_quad {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (s : ℝ) :
    fj A B s ≤ -s / 2 - min A B * s ^ 2 / 2 := by
  unfold fj
  have hk := min_le_left A B
  have hk' := min_le_right A B
  have hk0 : 0 ≤ min A B := le_min hA hB
  rcases le_total 0 s with hs | hs
  · have := Real.quadratic_le_exp_of_nonneg hs
    have : 0 ≤ A * Real.exp (-s) := mul_nonneg hA (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left (show s ^ 2 / 2 ≤ Real.exp s by nlinarith) hB,
      mul_le_mul_of_nonneg_right hk' (show 0 ≤ s ^ 2 / 2 by positivity)]
  · have := Real.quadratic_le_exp_of_nonneg (neg_nonneg.2 hs)
    have : 0 ≤ B * Real.exp s := mul_nonneg hB (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left (show s ^ 2 / 2 ≤ Real.exp (-s) by nlinarith) hA,
      mul_le_mul_of_nonneg_right hk (show 0 ≤ s ^ 2 / 2 by positivity)]

/-- Midpoint strict concavity of each `f_j`. -/
theorem fj_mid {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (a b : ℝ) :
    fj A B a + fj A B b ≤ 2 * fj A B ((a + b) / 2) ∧
      (a ≠ b → fj A B a + fj A B b < 2 * fj A B ((a + b) / 2)) := by
  have e : ∀ s, fj A B s = -(1 / 2) * s - A * Real.exp (-s) - B * Real.exp s := fun s => by
    unfold fj; ring
  have ta := tangent hA hB.le (1 / 2) ((a + b) / 2) a
  have tb := tangent hA hB.le (1 / 2) ((a + b) / 2) b
  refine ⟨by rw [e, e, e]; nlinarith, fun hab => ?_⟩
  have hne : a ≠ (a + b) / 2 := fun h => hab (by linarith)
  have ta' := tangent_lt hA hB (1 / 2) hne
  rw [e, e, e]; nlinarith

theorem ell_mid (hΔ : ∀ j, 0 < Δ j) (R z z' : Fin (m + 1) → ℝ) :
    ell Δ R z + ell Δ R z' ≤ 2 * ell Δ R (fun j => (z j + z' j) / 2) ∧
      (z ≠ z' → ell Δ R z + ell Δ R z' < 2 * ell Δ R (fun j => (z j + z' j) / 2)) := by
  have h := fun j => fj_mid (Aco_nonneg hΔ R j) (Bco_pos hΔ j) (z j) (z' j)
  unfold ell
  refine ⟨?_, fun hne => ?_⟩
  · have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => (h j).1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at this
    linarith
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    have := Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) => (h j).1) ⟨j, Finset.mem_univ j, (h j).2 hj⟩
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at this
    linarith

/-- The coercive bound along a nonzero coordinate. -/
theorem ell_le (hΔ : ∀ j, 0 < Δ j) {V : ℝ} {R z : Fin (m + 1) → ℝ} (hz : z ∈ ZV V) (k : Fin (m + 1)) :
    ell Δ R z ≤ cR Δ R + (m + 1 : ℝ) * V - (m + 1 : ℝ) * z k / 2 -
      min (Aco Δ R k) (Bco Δ k) * z k ^ 2 / 2 := by
  have hlin : ∀ j, fj (Aco Δ R j) (Bco Δ j) (z j) ≤ V - z k / 2 := fun j => by
    have h1 := fj_le_lin (Aco_nonneg hΔ R j) (Bco_pos hΔ j).le (z j)
    have h2 := abs_sub_zero_le hz j
    have h3 := abs_sub_zero_le hz k
    rw [abs_le] at h2 h3
    linarith
  have hk := fj_le_quad (Aco_nonneg hΔ R k) (Bco_pos hΔ k).le (z k)
  unfold ell
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have hs : ∑ j ∈ Finset.univ.erase k, fj (Aco Δ R j) (Bco Δ j) (z j) ≤
      ∑ j ∈ Finset.univ.erase k, (V - z k / 2) := Finset.sum_le_sum fun j _ => hlin j
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
    Fintype.card_fin, Nat.add_sub_cancel, nsmul_eq_mul] at hs
  have hV : 0 ≤ V := (abs_nonneg _).trans (abs_sub_zero_le hz 0)
  nlinarith [abs_sub_zero_le hz k, abs_nonneg (z k - z 0)]

theorem exists_max (hΔ : ∀ j, 0 < Δ j) {V : ℝ} (hV : 0 ≤ V) {R : Fin (m + 1) → ℝ} (hR : R ≠ 0) :
    ∃ z ∈ ZV V, ∀ z' ∈ ZV V, ell Δ R z' ≤ ell Δ R z := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hR
  have hk' : R k ≠ 0 := by simpa using hk
  have hAk : 0 < Aco Δ R k := by
    unfold Aco; exact div_pos (by positivity) (by linarith [hΔ k])
  set κ := min (Aco Δ R k) (Bco Δ k)
  have hκ : 0 < κ := lt_min hAk (Bco_pos hΔ k)
  set a := cR Δ R + (m + 1 : ℝ) * V - ell Δ R 0
  set K := 1 + 2 * (|a| + (m + 1 : ℝ)) / κ
  set L := {z ∈ ZV V | ell Δ R 0 ≤ ell Δ R z}
  have hbound : ∀ z ∈ L, ‖z‖ ≤ K + 2 * V := fun z hz => by
    have hzk : |z k| ≤ K := by
      by_contra hc
      rw [not_le] at hc
      have h1 : ell Δ R z ≤ cR Δ R + (m + 1 : ℝ) * V - (m + 1 : ℝ) * z k / 2 - κ * z k ^ 2 / 2 :=
        ell_le hΔ (R := R) hz.1 k
      have h2 := hz.2
      have hK1 : 1 ≤ K := by
        have : 0 ≤ 2 * (|a| + (m + 1 : ℝ)) / κ := by positivity
        linarith
      have h1' : 1 < |z k| := by linarith
      have hzk2 : κ * z k ^ 2 / 2 ≥ |z k| * (|a| + (m + 1 : ℝ)) := by
        have : κ * |z k| ≥ 2 * (|a| + (m + 1 : ℝ)) := by
          have := (div_lt_iff₀ hκ).1 (show 2 * (|a| + (m + 1 : ℝ)) / κ < |z k| by linarith)
          linarith
        have habs : z k ^ 2 = |z k| * |z k| := by rw [← sq_abs, sq]
        rw [habs]; nlinarith [abs_nonneg (z k)]
      have e1 : κ * z k ^ 2 / 2 ≥ |z k| * |a| + |z k| * (m + 1 : ℝ) := by rw [← mul_add]; exact hzk2
      have e2 : |z k| * |a| ≥ |a| := by nlinarith [abs_nonneg a]
      have e3 : (m + 1 : ℝ) * z k / 2 ≥ -(|z k| * (m + 1 : ℝ)) / 2 := by
        have := neg_abs_le (z k); nlinarith
      have e4 : 0 < |z k| * (m + 1 : ℝ) := by positivity
      have ha := le_abs_self a
      simp only [a] at ha
      linarith
    have hK0 : 0 ≤ K + 2 * V := by
      have h4 := abs_sub_zero_le hz.1 k
      have h5 := abs_nonneg (z k - z 0)
      have h6 := abs_nonneg (z k)
      linarith
    refine (pi_norm_le_iff_of_nonneg hK0).2 fun j => ?_
    rw [Real.norm_eq_abs]
    have h2 := abs_sub_zero_le hz.1 j
    have h3 := abs_sub_zero_le hz.1 k
    calc |z j| = |(z j - z 0) - (z k - z 0) + z k| := by ring_nf
      _ ≤ |z j - z 0| + |z k - z 0| + |z k| := by
          refine (abs_add_le _ _).trans ?_; gcongr; exact abs_sub _ _
      _ ≤ K + 2 * V := by linarith
  have hLc : IsCompact L := by
    refine (isCompact_closedBall (0 : Fin (m + 1) → ℝ) (K + 2 * V)).of_isClosed_subset ?_ ?_
    · exact (isClosed_ZV V).inter (isClosed_le continuous_const (continuous_ell_z Δ R))
    · intro z hz; rw [Metric.mem_closedBall, dist_zero_right]; exact hbound z hz
  have hL0 : (0 : Fin (m + 1) → ℝ) ∈ L := ⟨zero_mem hV, le_rfl⟩
  obtain ⟨z, hzL, hmax⟩ := hLc.exists_isMaxOn ⟨0, hL0⟩ (continuous_ell_z Δ R).continuousOn
  refine ⟨z, hzL.1, fun z' hz' => ?_⟩
  by_cases h : ell Δ R 0 ≤ ell Δ R z'
  · exact hmax ⟨hz', h⟩
  · exact (not_le.1 h).le.trans hzL.2

theorem unique_max (hΔ : ∀ j, 0 < Δ j) {V : ℝ} {R z z' : Fin (m + 1) → ℝ} (hz : z ∈ ZV V)
    (hz' : z' ∈ ZV V) (hmax : ∀ w ∈ ZV V, ell Δ R w ≤ ell Δ R z) (heq : ell Δ R z' = ell Δ R z) :
    z' = z := by
  by_contra hne
  have h1 := (ell_mid hΔ R z' z).2 hne
  have h2 := hmax _ (ZV_convex hz' hz)
  linarith

theorem PV_eq_of_max {V : ℝ} {R z : Fin (m + 1) → ℝ} (hz : z ∈ ZV V)
    (hmax : ∀ w ∈ ZV V, ell Δ R w ≤ ell Δ R z) :
    PV Δ V R = ENNReal.ofReal (Real.exp (ell Δ R z)) :=
  le_antisymm (iSup₂_le fun w hw => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hmax w hw)))
    (le_PV hz R)

theorem finite_unique (hΔ : ∀ j, 0 < Δ j) {V : ℝ} (hV : 0 ≤ V) {R : Fin (m + 1) → ℝ} (hR : R ≠ 0) :
    PV Δ V R < ⊤ ∧ ∃! z, z ∈ ZV V ∧ ENNReal.ofReal (Real.exp (ell Δ R z)) = PV Δ V R := by
  obtain ⟨z, hz, hmax⟩ := exists_max hΔ hV hR
  have hP := PV_eq_of_max hz hmax
  refine ⟨hP ▸ ENNReal.ofReal_lt_top, z, ⟨hz, hP.symm⟩, fun w ⟨hw, hweq⟩ => ?_⟩
  rw [hP, ENNReal.ofReal_eq_ofReal_iff (Real.exp_pos _).le (Real.exp_pos _).le,
    Real.exp_eq_exp] at hweq
  exact unique_max hΔ hz hw hmax hweq

/-! ## The common-scale endpoint (4) -/

theorem ZV0_const {z : Fin (m + 1) → ℝ} (hz : z ∈ ZV (m := m) 0) : z = fun _ => z 0 :=
  funext fun j => by
    have := abs_sub_zero_le hz j
    have := abs_nonneg (z j - z 0)
    have h : z j - z 0 = 0 := abs_eq_zero.1 (by linarith)
    linarith

theorem ell_const (R : Fin (m + 1) → ℝ) (s : ℝ) :
    ell Δ R (fun _ => s) = cR Δ R + (-(((m + 1 : ℕ) : ℝ) / 2) * s -
      (∑ j, Aco Δ R j) * Real.exp (-s) - (∑ j, Bco Δ j) * Real.exp s) := by
  unfold ell fj
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.sum_mul]
  push_cast; ring

theorem ystar_root (hΔ : ∀ j, 0 < Δ j) {R : Fin (m + 1) → ℝ} (hR : R ≠ 0) :
    0 < ystar Δ R ∧ (∑ j, Bco Δ j) * ystar Δ R ^ 2 + (((m + 1 : ℕ) : ℝ) / 2) * ystar Δ R -
      ∑ j, Aco Δ R j = 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hR
  have hk' : R k ≠ 0 := by simpa using hk
  have hAs : 0 < ∑ j, Aco Δ R j := Finset.sum_pos' (fun j _ => Aco_nonneg hΔ R j)
    ⟨k, Finset.mem_univ k, by unfold Aco; exact div_pos (by positivity) (by linarith [hΔ k])⟩
  have hBs : 0 < ∑ j, Bco Δ j := Finset.sum_pos (fun j _ => Bco_pos hΔ j) Finset.univ_nonempty
  have hd : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / 2 := by positivity
  unfold ystar
  generalize ∑ j, Aco Δ R j = A at hAs ⊢
  generalize ∑ j, Bco Δ j = B at hBs ⊢
  generalize ((m + 1 : ℕ) : ℝ) / 2 = d at hd ⊢
  have hr : Real.sqrt (d ^ 2 + 4 * B * A) ^ 2 = d ^ 2 + 4 * B * A := Real.sq_sqrt (by positivity)
  have hr0 := Real.sqrt_nonneg (d ^ 2 + 4 * B * A)
  generalize Real.sqrt (d ^ 2 + 4 * B * A) = r at hr hr0 ⊢
  have hdr : 0 < d + r := by linarith
  refine ⟨div_pos (by linarith : (0 : ℝ) < 2 * A) hdr, ?_⟩
  have hy' : 2 * A / (d + r) = (r - d) / (2 * B) := by
    rw [div_eq_div_iff hdr.ne' (by positivity)]; linear_combination (-1) * hr
  rw [hy']
  field_simp
  linear_combination hr

theorem PV_V0 (hΔ : ∀ j, 0 < Δ j) {R : Fin (m + 1) → ℝ} (hR : R ≠ 0) :
    0 < ystar Δ R ∧ PV Δ 0 R = ENNReal.ofReal (Real.exp (ell Δ R fun _ => Real.log (ystar Δ R))) := by
  obtain ⟨hy, hroot⟩ := ystar_root hΔ hR
  refine ⟨hy, PV_eq_of_max (const_mem le_rfl _) fun w hw => ?_⟩
  have hA : 0 ≤ ∑ j, Aco Δ R j := Finset.sum_nonneg fun j _ => Aco_nonneg hΔ R j
  have hB : 0 < ∑ j, Bco Δ j := Finset.sum_pos (fun j _ => Bco_pos hΔ j) Finset.univ_nonempty
  have h := (root_max hA hB hy hroot (w 0)).1
  have e : ell Δ R (fun _ => Real.log (ystar Δ R)) = cR Δ R + (-(((m + 1 : ℕ) : ℝ) / 2) *
      Real.log (ystar Δ R) - (∑ j, Aco Δ R j) / ystar Δ R - (∑ j, Bco Δ j) * ystar Δ R) := by
    rw [ell_const, Real.exp_neg, Real.exp_log hy]; ring
  rw [ZV0_const hw, ell_const, e]
  linarith

theorem profile_holds : Standalone.D30VariationProfile.profile := by
  intro m Δ V hΔ hV
  exact ⟨fun z R => exp_ell hΔ R z, nullLaw_eq hΔ, measurable_PV V, PV_pos hV,
    fun R hR => finite_unique hΔ hV hR, PV_zero hΔ hV, fun V' h R => PV_mono h R,
    fun R hR => PV_V0 hΔ hR⟩

end Novel.D30VariationProfile
