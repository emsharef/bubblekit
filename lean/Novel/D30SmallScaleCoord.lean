import Standalone.D30SmallScale
import Novel.PriceChainProof
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Claim 073: the coordinates carry `Γ_n` to the GBM price law

* One step: for `y = x exp(κ √Δ w − κ²Δ/2)`, Mathlib's one-dimensional change of variables turns the
  standard normal law of `w` into claim 052's lognormal kernel `f1(Δ, x, ·)` on `(0, ∞)`
  (`lognormal_change`).
* The coordinates (2) on `n + 1` steps are those on the first `n` steps, followed by the last price
  `x exp(r_last)` from the last earlier price `x` (`sk_cs`, `sk_last`).
* Induction on the last coordinate, as in claim 052's `chain_norm`: `∫ g(s_κ(z)) dΓ_n =
  ∫ g · chain f1 d posVol^n` for every measurable `g ≥ 0` (`coord_lintegral`).
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace Novel.D30SmallScale

open Standalone.D30SmallScale Standalone.PriceChain Novel.PriceChain

/-! ### One step -/

/-- The one-step map `w ↦ x exp(κ √Δ w − κ²Δ/2)`. -/
noncomputable def F1 (κ Δ x w : ℝ) : ℝ := x * Real.exp (κ * √Δ * w - κ ^ 2 * Δ / 2)

theorem F1_pos {κ Δ x : ℝ} (hx : 0 < x) (w : ℝ) : 0 < F1 κ Δ x w := mul_pos hx (Real.exp_pos _)

theorem F1_jac {κ Δ x : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ) (hx : 0 < x) (w : ℝ) :
    F1 κ Δ x w * (κ * √Δ) * f1 κ Δ x (F1 κ Δ x w) = gaussianPDFReal 0 1 w := by
  have hF := F1_pos (κ := κ) (Δ := Δ) hx w
  have hs : 0 < √Δ := Real.sqrt_pos.2 hΔ
  have hlog : Real.log (F1 κ Δ x w / x) = κ * √Δ * w - κ ^ 2 * Δ / 2 := by
    rw [F1, mul_div_cancel_left₀ _ hx.ne', Real.log_exp]
  have hsq : √(2 * π * (κ ^ 2 * Δ)) = √(2 * π) * (κ * √Δ) := by
    rw [Real.sqrt_mul (x := 2 * π) (by positivity) (κ ^ 2 * Δ),
      Real.sqrt_mul (x := κ ^ 2) (sq_nonneg κ) Δ, Real.sqrt_sq hκ.le]
  have hΔsq : √Δ ^ 2 = Δ := Real.sq_sqrt hΔ.le
  rw [f1, hlog, hsq, gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hexp : -(κ * √Δ * w - κ ^ 2 * Δ / 2 + κ ^ 2 * Δ / 2) ^ 2 / (2 * (κ ^ 2 * Δ)) = -w ^ 2 / 2 := by
    rw [show κ * √Δ * w - κ ^ 2 * Δ / 2 + κ ^ 2 * Δ / 2 = κ * √Δ * w by ring, mul_pow, mul_pow, hΔsq]
    field_simp
  rw [hexp]
  field_simp

theorem F1_hasDeriv (κ Δ x w : ℝ) :
    HasDerivAt (F1 κ Δ x) (F1 κ Δ x w * (κ * √Δ)) w := by
  have h := ((((hasDerivAt_id w).const_mul (κ * √Δ)).sub_const (κ ^ 2 * Δ / 2)).exp).const_mul x
  convert h using 1
  · funext w; simp [F1]
  · simp [F1]; ring

theorem F1_injective {κ Δ x : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ) (hx : 0 < x) :
    Function.Injective (F1 κ Δ x) := fun w w' h => by
  have hs : 0 < κ * √Δ := mul_pos hκ (Real.sqrt_pos.2 hΔ)
  simp only [F1] at h
  have := Real.exp_injective (mul_left_cancel₀ hx.ne' h)
  have : κ * √Δ * w = κ * √Δ * w' := by linarith
  exact mul_left_cancel₀ hs.ne' this

theorem F1_range {κ Δ x : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ) (hx : 0 < x) :
    F1 κ Δ x '' univ = Ioi 0 := by
  have hs : 0 < κ * √Δ := mul_pos hκ (Real.sqrt_pos.2 hΔ)
  ext y
  simp only [image_univ, mem_range, mem_Ioi]
  constructor
  · rintro ⟨w, rfl⟩; exact F1_pos hx w
  · intro hy
    refine ⟨(Real.log (y / x) + κ ^ 2 * Δ / 2) / (κ * √Δ), ?_⟩
    rw [F1, mul_div_cancel₀ _ hs.ne', add_sub_cancel_right, Real.exp_log (div_pos hy hx)]
    field_simp

/-- One step: the standard normal law carried to the lognormal kernel. -/
theorem lognormal_change {κ Δ x : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ) (hx : 0 < x)
    (h : PosReal → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ w, h ⟨F1 κ Δ x w, F1_pos hx w⟩ ∂(gaussianReal 0 1) =
      ∫⁻ y, h y * ENNReal.ofReal (f1 κ Δ x y) ∂posVol := by
  classical
  set h' : ℝ → ℝ≥0∞ := fun y => if hy : 0 < y then h ⟨y, hy⟩ * ENNReal.ofReal (f1 κ Δ x y) else 0
  have hR : ∫⁻ y, h y * ENNReal.ofReal (f1 κ Δ x y) ∂posVol = ∫⁻ y in Ioi 0, h' y := by
    rw [posVol, ← lintegral_subtype_comap measurableSet_Ioi]
    refine lintegral_congr fun y => ?_
    simp only [h', dif_pos y.2]
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun w _ => (F1_hasDeriv κ Δ x w).hasDerivWithinAt) (F1_injective hκ hΔ hx).injOn h'
  rw [F1_range hκ hΔ hx, Measure.restrict_univ] at hcv
  have hFm : Measurable (F1 κ Δ x) :=
    measurable_const.mul (Real.measurable_exp.comp ((measurable_id.const_mul _).sub_const _))
  have hmeas : Measurable fun w => h ⟨F1 κ Δ x w, F1_pos hx w⟩ :=
    hh.comp (Measurable.subtype_mk hFm)
  rw [hR, hcv, gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hmeas]
  · refine lintegral_congr fun w => ?_
    have hF := F1_pos (κ := κ) (Δ := Δ) hx w
    have hs : 0 < κ * √Δ := mul_pos hκ (Real.sqrt_pos.2 hΔ)
    simp only [h', dif_pos hF, Pi.mul_apply, gaussianPDF]
    rw [abs_of_pos (mul_pos hF hs), ← F1_jac hκ hΔ hx w, ENNReal.ofReal_mul (by positivity)]
    ring

/-! ### The coordinates split at the last step -/

variable {n : ℕ}

theorem sk_cs (κ : ℝ) (Δ z : Fin (n + 1) → ℝ) (j : Fin n) :
    sk κ Δ z j.castSucc = sk κ (fun i => Δ i.castSucc) (fun i => z i.castSucc) j := by
  apply Subtype.ext
  simp only [sk]
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc,
    if_neg (not_le.2 (Fin.castSucc_lt_last j)), add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.castSucc_le_castSucc_iff]
  rfl

theorem lastOr_sk (κ : ℝ) (Δ z : Fin n → ℝ) :
    lastOr 1 (sk κ Δ z) = Real.exp (∑ i, rk κ Δ z i) := by
  cases n with
  | zero => simp [lastOr]
  | succ m =>
    simp only [lastOr, Nat.add_one_ne_zero, ↓reduceDIte, sk]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact Fin.le_def.2 (by simp; omega)

theorem sk_last (κ : ℝ) (Δ z : Fin (n + 1) → ℝ) :
    (sk κ Δ z (Fin.last n) : ℝ) =
      F1 κ (Δ (Fin.last n)) (lastOr 1 (sk κ (fun i => Δ i.castSucc) (fun i => z i.castSucc)))
        (z (Fin.last n)) := by
  simp only [sk, F1, lastOr_sk, rk]
  rw [← Real.exp_add]
  congr 1
  rw [show (Finset.univ.filter fun i : Fin (n + 1) => i ≤ Fin.last n) = Finset.univ from
    Finset.filter_true_of_mem fun i _ => Fin.le_last i, Fin.sum_univ_castSucc]

theorem sk_snoc (κ : ℝ) (Δ z : Fin (n + 1) → ℝ) :
    sk κ Δ z = Fin.snoc (sk κ (fun i => Δ i.castSucc) (fun i => z i.castSucc))
      ⟨F1 κ (Δ (Fin.last n)) (lastOr 1 (sk κ (fun i => Δ i.castSucc) (fun i => z i.castSucc)))
        (z (Fin.last n)), (sk_last κ Δ z) ▸ (sk κ Δ z (Fin.last n)).2⟩ := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [Fin.snoc_last]; exact Subtype.ext (sk_last κ Δ z)
  · rw [Fin.snoc_castSucc]; exact sk_cs κ Δ z j

theorem measurable_rk (κ : ℝ) (Δ : Fin n → ℝ) (j : Fin n) : Measurable fun z => rk κ Δ z j :=
  ((measurable_pi_apply j).const_mul _).sub_const _

theorem measurable_sk (κ : ℝ) (Δ : Fin n → ℝ) : Measurable (sk κ Δ) :=
  measurable_pi_iff.2 fun j => Measurable.subtype_mk
    (Real.measurable_exp.comp (Finset.measurable_sum _ fun i _ => measurable_rk κ Δ i))

theorem meas_lastOr_fst {β : Type*} [MeasurableSpace β] :
    Measurable fun p : (Fin n → PosReal) × β => lastOr 1 p.1 := by
  unfold lastOr
  by_cases h : n = 0
  · simp only [h, dite_true]; exact measurable_const
  · simp only [h, dite_false]
    exact measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_fst)

theorem meas_chain1 (κ : ℝ) {m : ℕ} (Δ : Fin m → ℝ) :
    Measurable fun y : Fin m → PosReal => chain (f1 κ) Δ 1 y := by
  unfold chain
  refine Finset.measurable_prod _ fun j _ => ?_
  have hp : Measurable fun y : Fin m → PosReal => prev 1 y j := by
    unfold prev; split_ifs
    · exact measurable_const
    · exact measurable_subtype_coe.comp (measurable_pi_apply _)
  have := (f1_meas κ (Δ j)).comp (hp.prodMk (measurable_subtype_coe.comp (measurable_pi_apply j)))
  exact this

theorem measurable_snoc {α : Type*} [MeasurableSpace α] {m : ℕ} :
    Measurable fun p : (Fin m → α) × α => (Fin.snoc p.1 p.2 : Fin (m + 1) → α) := by
  refine measurable_pi_iff.2 fun j => ?_
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [Fin.snoc_last]; exact measurable_snd
  · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply j).comp measurable_fst

/-! ### The induction -/

instance (m : ℕ) : SFinite (Gam m) := by unfold Gam; infer_instance

set_option maxHeartbeats 1000000 in
/-- `∫ g(s_κ(z)) dΓ_n = ∫ g · chain f1 d posVol^n`. -/
theorem coord_lintegral {κ : ℝ} (hκ : 0 < κ) :
    ∀ (n : ℕ) (Δ : Fin n → ℝ), (∀ j, 0 < Δ j) → ∀ g : (Fin n → PosReal) → ℝ≥0∞, Measurable g →
      ∫⁻ z, g (sk κ Δ z) ∂Gam n =
        ∫⁻ y, g y * ENNReal.ofReal (chain (f1 κ) Δ 1 y) ∂(Measure.pi fun _ : Fin n => posVol)
  | 0, Δ, _, g, _ => by
    have hu : ∀ y : Fin 0 → PosReal, y = isEmptyElim := fun y => funext fun i => isEmptyElim i
    simp only [Gam, chain, Finset.univ_eq_empty, Finset.prod_empty, ENNReal.ofReal_one, mul_one]
    rw [show (fun z : Fin 0 → ℝ => g (sk κ Δ z)) = fun _ => g isEmptyElim from
      funext fun z => by rw [hu (sk κ Δ z)]]
    rw [show (fun y : Fin 0 → PosReal => g y) = fun _ => g isEmptyElim from
      funext fun y => by rw [hu y]]
    simp
  | n + 1, Δ, hΔ, g, hg => by
    set Δ' : Fin n → ℝ := fun i => Δ i.castSucc
    set d := Δ (Fin.last n)
    have hd : 0 < d := hΔ _
    have ih := coord_lintegral hκ n Δ' (fun j => hΔ _)
    -- The inner one-step integral, as a function of the earlier prices.
    set H : (Fin n → PosReal) → ℝ≥0∞ := fun y' =>
      ∫⁻ y, g (Fin.snoc y' y) * ENNReal.ofReal (f1 κ d (lastOr 1 y') y) ∂posVol
    have hl : Measurable fun p : (Fin n → PosReal) × PosReal => lastOr 1 p.1 := meas_lastOr_fst
    have hf : Measurable fun p : (Fin n → PosReal) × PosReal => f1 κ d (lastOr 1 p.1) (p.2 : ℝ) := by
      have := (f1_meas κ d).comp (hl.prodMk (measurable_subtype_coe.comp measurable_snd))
      exact this
    have hsn : Measurable fun p : (Fin n → PosReal) × PosReal =>
        (Fin.snoc p.1 p.2 : Fin (n + 1) → PosReal) := measurable_snoc
    have hK : Measurable fun p : (Fin n → PosReal) × PosReal =>
        g (Fin.snoc p.1 p.2) * ENNReal.ofReal (f1 κ d (lastOr 1 p.1) p.2) := by
      have := (hg.comp hsn).mul hf.ennreal_ofReal
      exact this
    have hH : Measurable H := hK.lintegral_prod_right'
    -- The Gaussian side.
    have eG := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) (Fin.last n)
    set G : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun p =>
      g (Fin.snoc (sk κ Δ' p.2) ⟨F1 κ d (lastOr 1 (sk κ Δ' p.2)) p.1,
        F1_pos (lastOr_pos one_pos _) p.1⟩) with hGdef
    have hGm : Measurable G := by
      have hs' : Measurable fun p : ℝ × (Fin n → ℝ) => sk κ Δ' p.2 :=
        (measurable_sk κ Δ').comp measurable_snd
      have hl' : Measurable fun p : ℝ × (Fin n → ℝ) => lastOr 1 (sk κ Δ' p.2) := by
        simp_rw [lastOr_sk]
        exact Real.measurable_exp.comp (Finset.measurable_sum _ fun i _ =>
          (measurable_rk κ Δ' i).comp measurable_snd)
      have hF' : Measurable fun p : ℝ × (Fin n → ℝ) => F1 κ d (lastOr 1 (sk κ Δ' p.2)) p.1 :=
        hl'.mul (Real.measurable_exp.comp ((measurable_fst.const_mul _).sub_const _))
      have hpair : Measurable fun p : ℝ × (Fin n → ℝ) =>
          (sk κ Δ' p.2, (⟨F1 κ d (lastOr 1 (sk κ Δ' p.2)) p.1,
            F1_pos (lastOr_pos one_pos _) p.1⟩ : PosReal)) :=
        hs'.prodMk (Measurable.subtype_mk hF')
      have := hg.comp (measurable_snoc.comp hpair)
      exact this
    have hzG : ∀ z, g (sk κ Δ z) =
        G (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n) z) := fun z => by
      show _ = G (z (Fin.last n), fun j => z ((Fin.last n).succAbove j))
      simp only [Fin.succAbove_last, hGdef]
      congr 1
      rw [sk_snoc]
    have hLHS : ∫⁻ z, g (sk κ Δ z) ∂Gam (n + 1) = ∫⁻ z', H (sk κ Δ' z') ∂Gam n := by
      simp_rw [hzG]
      rw [Gam, eG.lintegral_comp hGm, lintegral_prod_symm' G hGm]
      refine lintegral_congr fun z' => ?_
      simp only [hGdef, H]
      exact lognormal_change hκ hd (lastOr_pos one_pos _) (fun y => g (Fin.snoc (sk κ Δ' z') y))
        (hg.comp (show Measurable fun y : PosReal => (Fin.snoc (sk κ Δ' z') y : Fin (n + 1) → PosReal)
          from by
            have := (measurable_snoc (α := PosReal) (m := n)).comp
              ((measurable_const (a := sk κ Δ' z')).prodMk (measurable_id (α := PosReal)))
            exact this))
    -- The price side.
    have eP := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => posVol) (Fin.last n)
    set K : PosReal × (Fin n → PosReal) → ℝ≥0∞ := fun p =>
      g (Fin.snoc p.2 p.1) * (ENNReal.ofReal (chain (f1 κ) Δ' 1 p.2) *
        ENNReal.ofReal (f1 κ d (lastOr 1 p.2) p.1)) with hKdef
    have hKm : Measurable K := by
      have h1 : Measurable fun p : PosReal × (Fin n → PosReal) =>
          g (Fin.snoc p.2 p.1) * ENNReal.ofReal (f1 κ d (lastOr 1 p.2) p.1) := by
        have := hK.comp (measurable_snd.prodMk measurable_fst)
        exact this
      have h2' : Measurable fun p : PosReal × (Fin n → PosReal) => chain (f1 κ) Δ' 1 p.2 :=
        (meas_chain1 κ Δ').comp measurable_snd
      have h2 : Measurable fun p : PosReal × (Fin n → PosReal) =>
          ENNReal.ofReal (chain (f1 κ) Δ' 1 p.2) := h2'.ennreal_ofReal
      have : K = fun p => (g (Fin.snoc p.2 p.1) * ENNReal.ofReal (f1 κ d (lastOr 1 p.2) p.1)) *
          ENNReal.ofReal (chain (f1 κ) Δ' 1 p.2) := funext fun p => by simp only [hKdef]; ring
      rw [this]; exact h1.mul h2
    have hyK : ∀ v : Fin (n + 1) → PosReal, g v * ENNReal.ofReal (chain (f1 κ) Δ 1 v) =
        K (MeasurableEquiv.piFinSuccAbove (fun _ => PosReal) (Fin.last n) v) := fun v => by
      show _ = K (v (Fin.last n), fun j => v ((Fin.last n).succAbove j))
      simp only [Fin.succAbove_last, hKdef]
      rw [chain_succ, ENNReal.ofReal_mul (chain_pos (fun j x y hx hy =>
        f1_pos (Δ := Δ' j) hκ (hΔ _) hy) one_pos _).le]
      congr 1
      exact congrArg g (Fin.snoc_init_self v).symm
    have hRHS : ∫⁻ v, g v * ENNReal.ofReal (chain (f1 κ) Δ 1 v) ∂(Measure.pi fun _ => posVol) =
        ∫⁻ y', H y' * ENNReal.ofReal (chain (f1 κ) Δ' 1 y') ∂(Measure.pi fun _ : Fin n => posVol) := by
      simp_rw [hyK]
      rw [eP.lintegral_comp hKm, lintegral_prod_symm' K hKm]
      refine lintegral_congr fun y' => ?_
      simp only [hKdef, H]
      rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_congr fun y => by ring
    rw [hLHS, hRHS]
    exact ih H hH

/-- The coordinates carry `Γ_n` to the GBM price law. -/
theorem map_sk {κ : ℝ} (hκ : 0 < κ) (Δ : Fin n → ℝ) (hΔ : ∀ j, 0 < Δ j) :
    (Gam n).map (sk κ Δ) = Plaw f1 κ Δ := by
  ext B hB
  rw [Measure.map_apply (measurable_sk κ Δ) hB, Plaw, withDensity_apply _ hB,
    ← lintegral_indicator_one ((measurable_sk κ Δ) hB), ← lintegral_indicator hB]
  have := coord_lintegral hκ n Δ hΔ (B.indicator 1) (measurable_one.indicator hB)
  convert this using 1
  · rfl
  · refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ B <;> simp [indicator, hy]

end Novel.D30SmallScale
