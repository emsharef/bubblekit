import Standalone.D18ClockNoise
import Novel.D17ClockForecastLabels
import Novel.D16GaussianPoolForecastProof
import Novel.D18SignNoiseSign

/-!
# Claim 066, part 2: the clocked CEV numerator on noisy labels

* **Rows.** For a fixed next sign `t`, the sign intervals `I_(z',t)` partition `[0, ∞)`: a price
  `y ≥ 0` lies in `I_(z',t)` exactly when its observation with sign `t` has label `z'`. So the `Kc`
  masses of those intervals from a positive representative sum to one (AX-56), and with the sign
  weights `Σ_t A^forecast_(h,t) = 1` every row of (6) has mass one. Feasible targets have positive
  mass, empty ones mass zero.
* **The forecast.** A chain of rows of mass one is normalized over label/sign paths; summing out the
  signs normalizes it over label paths. The all-negative sign path is feasible for every label
  record, so every training likelihood and every forecast mass is positive. The final sign vector
  is a probability vector, zero on infeasible signs of the last training label.
* **Zero radius.** The sign intervals are the ordinary cells, the midpoints are claim 031's
  representatives, and summing the sign chain leaves claim 035's row product.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18ClockNoise

open Standalone.D18ClockNoise Standalone.D18SignNoise Standalone.CEVSupport
  Standalone.D13CEVCatalogue Standalone.D14FixedTick Standalone.D16GaussianPool
  Novel.D18SignNoise Novel.D13CEVCatalogue

variable {δ a : ℝ}

/-- A nonnegative price lies in `I_(z,t)` exactly when its observation with sign `t` is `z`. -/
theorem mem_icell_iff (hδ : 0 < δ) {y : ℝ} (hy : 0 ≤ y) (z : ℕ) (t : Bool) :
    y ∈ Ico (ilo δ a z t) (ihi δ a z t) ↔ obs δ a y t = z := by
  refine ⟨fun h => ?_, fun h => h ▸ obs_mem hδ hy t⟩
  unfold obs
  rw [Novel.D14FixedTick.mlabel_eq_iff hδ (le_max_left _ _)]
  obtain ⟨h1, h2⟩ := h
  unfold ihi at h2
  unfold ilo at h1
  refine ⟨?_, ?_⟩
  · split_ifs at h1 with hz
    · subst hz; rw [Novel.D14FixedTick.mlo_zero hδ]; exact le_max_left _ _
    · exact le_max_of_le_right (by linarith [le_max_right 0 (mlo δ z - sg t * a)])
  · refine max_lt ((Novel.D14FixedTick.mlo_nonneg δ z).trans_lt
      (Novel.D14FixedTick.mlo_lt_mhi hδ z)) (by linarith)

theorem rmid_pos {z : ℕ} {h : Bool} (hf : Feas δ a z h) : 0 < rmid δ a z h := by
  unfold rmid; have := ilo_nonneg (δ := δ) (a := a) z h; unfold Feas at hf; linarith

theorem measurableSet_icell (z : ℕ) (t : Bool) :
    MeasurableSet {y : NNR | (y : ℝ) ∈ Ico (ilo δ a z t) (ihi δ a z t)} :=
  measurable_subtype_coe measurableSet_Ico

/-- The interval masses for a fixed next sign sum to one. -/
theorem Pint_lsum (hC : Novel.D13CEVCatalogue.Cited) (hδ : 0 < δ) {p κ v : ℝ} (hp : 1 < p)
    (hκ : 0 < κ) (hv : 0 < v) {s : ℕ × Bool} (hs : Feas δ a s.1 s.2) (t : Bool) :
    ∑' z', ∫⁻ y in {y : NNR | (y : ℝ) ∈ Ico (ilo δ a z' t) (ihi δ a z' t)},
      ENNReal.ofReal (Kc p κ v (rmid δ a s.1 s.2) y) ∂muCEV = 1 := by
  have hdisj : Pairwise (Function.onFun Disjoint fun z' =>
      {y : NNR | (y : ℝ) ∈ Ico (ilo δ a z' t) (ihi δ a z' t)}) := fun b c hbc =>
    Set.disjoint_left.2 fun y h1 h2 => hbc (((mem_icell_iff hδ y.2 b t).1 h1).symm.trans
      ((mem_icell_iff hδ y.2 c t).1 h2))
  have hunion : (⋃ z', {y : NNR | (y : ℝ) ∈ Ico (ilo δ a z' t) (ihi δ a z' t)}) = univ := by
    ext y
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨_, (mem_icell_iff hδ y.2 _ t).2 rfl⟩
  rw [← lintegral_iUnion (fun z' => measurableSet_icell z' t) hdisj, hunion, Measure.restrict_univ]
  exact Kc_norm' hC (by linarith) hκ hv (rmid_pos hs).le

theorem Pint_lint_ne_top (hC : Novel.D13CEVCatalogue.Cited) (hδ : 0 < δ) {p κ v : ℝ} (hp : 1 < p)
    (hκ : 0 < κ) (hv : 0 < v) {s : ℕ × Bool} (hs : Feas δ a s.1 s.2) (z' : ℕ) (t : Bool) :
    ∫⁻ y in {y : NNR | (y : ℝ) ∈ Ico (ilo δ a z' t) (ihi δ a z' t)},
      ENNReal.ofReal (Kc p κ v (rmid δ a s.1 s.2) y) ∂muCEV ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top ((Pint_lsum hC hδ hp hκ hv hs t) ▸ ENNReal.le_tsum
    (f := fun z' => ∫⁻ y in {y : NNR | (y : ℝ) ∈ Ico (ilo δ a z' t) (ihi δ a z' t)},
      ENNReal.ofReal (Kc p κ v (rmid δ a s.1 s.2) y) ∂muCEV) z')

theorem Pint_hasSum (hC : Novel.D13CEVCatalogue.Cited) (hδ : 0 < δ) {p κ v : ℝ} (hp : 1 < p)
    (hκ : 0 < κ) (hv : 0 < v) {s : ℕ × Bool} (hs : Feas δ a s.1 s.2) (t : Bool) :
    HasSum (fun z' => Pint δ a p κ v s (z', t)) 1 := by
  have htsum := Pint_lsum hC hδ hp hκ hv hs t
  have := ENNReal.hasSum_toReal (htsum.symm ▸ ENNReal.one_ne_top)
  rwa [← ENNReal.tsum_toReal_eq (Pint_lint_ne_top hC hδ hp hκ hv hs · t), htsum,
    ENNReal.toReal_one] at this

theorem Pint_nonneg (p κ v : ℝ) (s s' : ℕ × Bool) : 0 ≤ Pint δ a p κ v s s' := ENNReal.toReal_nonneg

/-- An infeasible target has mass zero. -/
theorem Pint_infeas (p κ v : ℝ) (s : ℕ × Bool) {s' : ℕ × Bool} (h : ¬ Feas δ a s'.1 s'.2) :
    Pint δ a p κ v s s' = 0 := by
  unfold Pint
  have : {y : NNR | (y : ℝ) ∈ Ico (ilo δ a s'.1 s'.2) (ihi δ a s'.1 s'.2)} = ∅ := by
    ext y; simp only [mem_ofPred_eq, mem_Ico, mem_empty_iff_false, iff_false, not_and, not_lt]
    intro h1; unfold Feas at h; linarith
  rw [this, Measure.restrict_empty, lintegral_zero_measure, ENNReal.toReal_zero]

/-- A feasible target has positive mass from a feasible source. -/
theorem Pint_pos (hC : Novel.D13CEVCatalogue.Cited) (hδ : 0 < δ) {p κ v : ℝ} (hp : 1 < p)
    (hκ : 0 < κ) (hv : 0 < v) {s s' : ℕ × Bool} (hs : Feas δ a s.1 s.2)
    (hs' : Feas δ a s'.1 s'.2) : 0 < Pint δ a p κ v s s' := by
  refine ENNReal.toReal_pos ?_ (Pint_lint_ne_top hC hδ hp hκ hv hs _ _)
  set S' := {y : NNR | (y : ℝ) ∈ Ioo (ilo δ a s'.1 s'.2) (ihi δ a s'.1 s'.2)}
  have hsub : S' ⊆ {y : NNR | (y : ℝ) ∈ Ico (ilo δ a s'.1 s'.2) (ihi δ a s'.1 s'.2)} :=
    fun y hy => ⟨hy.1.le, hy.2⟩
  have hx := rmid_pos hs
  have hmeas : Measurable fun y : NNR => ENNReal.ofReal (Kc p κ v (rmid δ a s.1 s.2) y) :=
    ENNReal.measurable_ofReal.comp ((Kc_meas p κ v).comp
      (measurable_const.prodMk measurable_subtype_coe))
  refine (ne_of_gt (lt_of_lt_of_le ?_ (lintegral_mono_set (μ := muCEV) hsub)))
  refine (setLIntegral_pos_iff hmeas).2 ?_
  have hS : Function.support (fun y : NNR => ENNReal.ofReal (Kc p κ v (rmid δ a s.1 s.2) y)) ∩ S' =
      S' := by
    refine inter_eq_right.2 fun y hy => ?_
    have hy0 : 0 < (y : ℝ) := (ilo_nonneg _ _).trans_lt hy.1
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    rw [show Kc p κ v (rmid δ a s.1 s.2) (y : ℝ) = fcev p κ v (rmid δ a s.1 s.2) y by
      simp [Kc, K, hp.ne', hx.ne', hy0.ne']]
    exact hC.pos p κ v (by linarith) hp.ne' hκ hv _ _ hx hy0
  rw [hS]
  refine lt_of_lt_of_le (Novel.D17ClockForecast.lebNN_Ioo (ilo_nonneg _ _) hs') ?_
  unfold muCEV
  rw [Measure.add_apply]
  exact le_self_add

theorem Af_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ < 1) (h t : Bool) : 0 ≤ Af ρ h t := by
  unfold Af; have := hρ.2; split_ifs <;> nlinarith [hρ.1]

theorem Af_pos {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ < 1) (h t : Bool) : 0 < Af ρ h t := by
  unfold Af; have := hρ.2; split_ifs <;> nlinarith [hρ.1]

theorem Af_sum (ρ : ℝ) (h : Bool) : ∑ t : Bool, Af ρ h t = 1 := by
  cases h <;> simp [Af] <;> ring

/-- Fibers over a finite first coordinate. -/
theorem hasSum_of_fibers {α β : Type*} [Fintype α] {f : α × β → ℝ} (h0 : ∀ q, 0 ≤ f q)
    {g : α → ℝ} (hg : ∀ b, HasSum (fun y => f (b, y)) (g b)) : HasSum f (∑ b, g b) := by
  have hs : Summable f := (summable_prod_of_nonneg h0).2
    ⟨fun b => (hg b).summable, Summable.of_finite⟩
  have := hs.hasSum
  rwa [hs.tsum_prod' fun b => (hg b).summable, tsum_congr fun b => (hg b).tsum_eq,
    tsum_fintype] at this

theorem Kf_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ < 1) (p κ v : ℝ) (s s' : ℕ × Bool) :
    0 ≤ Kf δ a ρ p κ v s s' := mul_nonneg (Af_nonneg hρ _ _) (Pint_nonneg _ _ _ _ _)

/-- Every feasible row of (6) has mass one. -/
theorem Kf_hasSum (hC : Novel.D13CEVCatalogue.Cited) (hδ : 0 < δ) {ρ p κ v : ℝ}
    (hρ : 0 ≤ ρ ∧ ρ < 1) (hp : 1 < p) (hκ : 0 < κ) (hv : 0 < v) {s : ℕ × Bool}
    (hs : Feas δ a s.1 s.2) : HasSum (fun s' => Kf δ a ρ p κ v s s') 1 := by
  have h := hasSum_of_fibers (f := fun q : Bool × ℕ => Kf δ a ρ p κ v s (q.2, q.1))
    (fun q => Kf_nonneg hρ _ _ _ _ _) (g := fun t => Af ρ s.2 t * 1)
    fun t => (Pint_hasSum hC hδ hp hκ hv hs t).mul_left _
  simp only [mul_one, Af_sum] at h
  rw [← (Equiv.prodComm ℕ Bool).symm.hasSum_iff]
  exact h

/-- A chain of rows of mass one from good states, vanishing on bad targets, is normalized over
paths from a good start. -/
theorem chain_good {σ : Type*} (G : Set σ) : ∀ (n : ℕ) (F : Fin n → σ → σ → ℝ),
    (∀ j s, s ∈ G → HasSum (F j s) 1) → (∀ j s s', s' ∉ G → F j s s' = 0) →
    (∀ j s s', 0 ≤ F j s s') → ∀ s₀ ∈ G,
      HasSum (fun w : Fin n → σ => ∏ j, F j ((Fin.cons s₀ w : Fin (n + 1) → σ) j.castSucc) (w j)) 1
  | 0, F, _, _, _, s₀, _ => by simp
  | n + 1, F, hF, hbad, hF0, s₀, hs₀ => by
    set Gf : σ × (Fin n → σ) → ℝ := fun p => F 0 s₀ p.1 *
      ∏ j : Fin n, F j.succ ((Fin.cons p.1 p.2 : Fin (n + 1) → σ) j.castSucc) (p.2 j)
    have hG0 : ∀ p, 0 ≤ Gf p := fun p =>
      mul_nonneg (hF0 _ _ _) (Finset.prod_nonneg fun j _ => hF0 _ _ _)
    have hfib : ∀ b, HasSum (fun w => Gf (b, w)) (F 0 s₀ b * 1) := fun b => by
      by_cases hb : b ∈ G
      · exact (chain_good G n (fun j => F j.succ) (fun j => hF _) (fun j => hbad _)
          (fun j => hF0 _) b hb).mul_left _
      · simp only [Gf, hbad 0 s₀ b hb, zero_mul]; exact hasSum_zero
    have hout : HasSum (fun b => F 0 s₀ b * 1) 1 := by simp_rw [mul_one]; exact hF _ _ hs₀
    have hsum : Summable Gf := (summable_prod_of_nonneg hG0).2
      ⟨fun b => (hfib b).summable, by simp_rw [(hfib _).tsum_eq]; exact hout.summable⟩
    have htot : HasSum Gf 1 := by
      have := hsum.hasSum
      rwa [hsum.tsum_prod' fun b => (hfib b).summable, tsum_congr fun b => (hfib b).tsum_eq,
        hout.tsum_eq] at this
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => σ).hasSum_iff]
    convert htot using 1
    funext p
    simp only [Function.comp_apply, Fin.consEquiv, Equiv.coe_fn_mk, Gf]
    rw [Fin.prod_univ_succ]
    congr 1

/-- The good states: feasible label/sign pairs. -/
def Good (δ a : ℝ) : Set (ℕ × Bool) := {s | Feas δ a s.1 s.2}

theorem chainS_hasSum (hC : Novel.D13CEVCatalogue.Cited) (hδ : 0 < δ) {n : ℕ} {ρ p κ : ℝ}
    {v : Fin n → ℝ} (hρ : 0 ≤ ρ ∧ ρ < 1) (hp : 1 < p) (hκ : 0 < κ) (hv : ∀ j, 0 < v j)
    {s₀ : ℕ × Bool} (hs₀ : Feas δ a s₀.1 s₀.2) :
    HasSum (fun w => chainS (fun j => Kf δ a ρ p κ (v j)) s₀ w) 1 :=
  chain_good (Good δ a) n (fun j => Kf δ a ρ p κ (v j))
    (fun j s hs => Kf_hasSum hC hδ hρ hp hκ (hv j) hs)
    (fun j s s' hs' => by simp only [Kf, Pint_infeas p κ (v j) s hs', mul_zero])
    (fun j s s' => Kf_nonneg hρ _ _ _ _ _) s₀ hs₀

/-- Summing out the evaluation signs normalizes the chain over label paths. -/
theorem chainS_labels (hC : Novel.D13CEVCatalogue.Cited) (hδ : 0 < δ) {n : ℕ} {ρ p κ : ℝ}
    {v : Fin n → ℝ} (hρ : 0 ≤ ρ ∧ ρ < 1) (hp : 1 < p) (hκ : 0 < κ) (hv : ∀ j, 0 < v j)
    {s₀ : ℕ × Bool} (hs₀ : Feas δ a s₀.1 s₀.2) :
    HasSum (fun Z : Fin n → ℕ => ∑ Hz : Fin n → Bool,
      chainS (fun j => Kf δ a ρ p κ (v j)) s₀ (fun j => (Z j, Hz j))) 1 := by
  have h := chainS_hasSum hC hδ hρ hp hκ hv hs₀
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ℕ) (fun _ => Bool)).symm.hasSum_iff] at h
  exact h.prod_fiberwise fun Z => hasSum_fintype _

theorem chainS_nonneg {n : ℕ} {ρ p κ : ℝ} {v : Fin n → ℝ} (hρ : 0 ≤ ρ ∧ ρ < 1) (s₀ : ℕ × Bool)
    (w : Fin n → ℕ × Bool) : 0 ≤ chainS (fun j => Kf δ a ρ p κ (v j)) s₀ w :=
  Finset.prod_nonneg fun _ _ => Kf_nonneg hρ _ _ _ _ _

/-- The all-negative sign path has positive weight. -/
theorem chainS_false_pos (hC : Novel.D13CEVCatalogue.Cited) (hδ : 0 < δ) (ha : 0 ≤ a) {n : ℕ}
    {ρ p κ : ℝ} {v : Fin n → ℝ} (hρ : 0 ≤ ρ ∧ ρ < 1) (hp : 1 < p) (hκ : 0 < κ)
    (hv : ∀ j, 0 < v j) (z₀ : ℕ) (Z : Fin n → ℕ) :
    0 < chainS (fun j => Kf δ a ρ p κ (v j)) (z₀, false) (fun j => (Z j, false)) := by
  refine Finset.prod_pos fun j _ => mul_pos (Af_pos hρ _ _) (Pint_pos hC hδ hp hκ (hv j) ?_
    (feas_false hδ ha (Z j)))
  have : ((Fin.cons (z₀, false) (fun j => (Z j, false)) : Fin (n + 1) → ℕ × Bool) j.castSucc).2 =
      false := by
    refine Fin.cases rfl (fun i => rfl) j.castSucc
  rw [this]; exact feas_false hδ ha _

/-! ## The training likelihood and the final sign vector -/

theorem pi0_nonneg (z : ℕ) (h : Bool) : 0 ≤ pi0 δ a z h := by
  unfold pi0; split_ifs <;> positivity

open Classical in
theorem card_feas_pos (hδ : 0 < δ) (ha : 0 ≤ a) (z : ℕ) :
    0 < ((Finset.univ.filter fun t => Feas δ a z t).card : ℝ) := by
  exact_mod_cast Finset.card_pos.2 ⟨false, by simp [feas_false hδ ha z]⟩

open Classical in
theorem pi0_false_pos (hδ : 0 < δ) (ha : 0 ≤ a) (z : ℕ) : 0 < pi0 δ a z false := by
  classical
  unfold pi0; rw [ite_eq_left (feas_false hδ ha z)]
  exact div_pos one_pos (card_feas_pos hδ ha z)

open Classical in
theorem pi0_sum (hδ : 0 < δ) (ha : 0 ≤ a) (z : ℕ) : ∑ h : Bool, pi0 δ a z h = 1 := by
  classical
  have hc := card_feas_pos hδ ha z
  unfold pi0
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div, div_self hc.ne']

section Train

variable {r k n : ℕ} (C : Cat r k n)

theorem hρC (hρ : ∀ ξ, 0 ≤ C.ρf ξ ∧ C.ρf ξ < 1) (ξ : Fin r) : 0 ≤ C.ρf ξ ∧ C.ρf ξ < 1 := hρ ξ

theorem trainW_nonneg (hρ : ∀ ξ, 0 ≤ C.ρf ξ ∧ C.ρf ξ < 1) (ξ : Fin r) (u : Fin (k + 1) → ℕ)
    (h₀ : Bool) (H : Fin k → Bool) : 0 ≤ trainW δ a C ξ u h₀ H :=
  mul_nonneg (pi0_nonneg _ _) (chainS_nonneg (hρ ξ) _ _)

theorem trainW_false_pos (hC : Novel.D13CEVCatalogue.Cited) (hδ : 0 < δ) (ha : 0 ≤ a)
    (hp : ∀ ξ, 1 < C.pf ξ) (hκ : ∀ ξ, 0 < C.κf ξ) (hρ : ∀ ξ, 0 ≤ C.ρf ξ ∧ C.ρf ξ < 1)
    (hv : ∀ ξ j, 0 < C.vf ξ j) (ξ : Fin r) (u : Fin (k + 1) → ℕ) :
    0 < trainW δ a C ξ u false fun _ => false :=
  mul_pos (pi0_false_pos hδ ha _) (chainS_false_pos hC hδ ha (hρ ξ) (hp ξ) (hκ ξ)
    (fun _ => hv ξ _) (u 0) fun j => u j.succ)

theorem Lf_pos (hC : Novel.D13CEVCatalogue.Cited) (hδ : 0 < δ) (ha : 0 ≤ a)
    (hp : ∀ ξ, 1 < C.pf ξ) (hκ : ∀ ξ, 0 < C.κf ξ) (hρ : ∀ ξ, 0 ≤ C.ρf ξ ∧ C.ρf ξ < 1)
    (hv : ∀ ξ j, 0 < C.vf ξ j) (ξ : Fin r) (u : Fin (k + 1) → ℕ) : 0 < Lf δ a C ξ u := by
  unfold Lf
  refine lt_of_lt_of_le (trainW_false_pos C hC hδ ha hp hκ hρ hv ξ u) ?_
  refine le_trans ?_ (Finset.single_le_sum (fun h₀ _ => Finset.sum_nonneg fun H _ =>
    trainW_nonneg C hρ ξ u h₀ H) (Finset.mem_univ false))
  exact Finset.single_le_sum (fun H _ => trainW_nonneg C hρ ξ u false H)
    (Finset.mem_univ (fun _ => false))

open Classical in
/-- The training weight vanishes when the final sign is infeasible for the last training label. -/
theorem trainW_infeas (ξ : Fin r) (u : Fin (k + 1) → ℕ) (h₀ : Bool) (H : Fin k → Bool)
    (hf : ¬ Feas δ a (u (Fin.last k)) ((Fin.cons h₀ H : Fin (k + 1) → Bool) (Fin.last k))) :
    trainW δ a C ξ u h₀ H = 0 := by
  unfold trainW
  cases k with
  | zero =>
    rw [show (Fin.cons h₀ H : Fin 1 → Bool) (Fin.last 0) = h₀ from rfl] at hf
    unfold pi0; rw [ite_eq_right (by simpa using hf), zero_mul]
  | succ k =>
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ (Fin.last k)) ?_)
    simp only [Kf]
    refine mul_eq_zero_of_right _ (Pint_infeas _ _ _ _ ?_)
    rw [show (Fin.last (k + 1) : Fin (k + 2)) = (Fin.last k).succ from rfl, Fin.cons_succ] at hf
    exact hf

open Classical in
theorem piK_facts (hC : Novel.D13CEVCatalogue.Cited) (hδ : 0 < δ) (ha : 0 ≤ a)
    (hp : ∀ ξ, 1 < C.pf ξ) (hκ : ∀ ξ, 0 < C.κf ξ) (hρ : ∀ ξ, 0 ≤ C.ρf ξ ∧ C.ρf ξ < 1)
    (hv : ∀ ξ j, 0 < C.vf ξ j) (ξ : Fin r) (u : Fin (k + 1) → ℕ) :
    (∀ t, 0 ≤ piK δ a C ξ u t) ∧ ∑ t, piK δ a C ξ u t = 1 ∧
      (∀ t, ¬ Feas δ a (u (Fin.last k)) t → piK δ a C ξ u t = 0) ∧ 0 < piK δ a C ξ u false := by
  have hL := Lf_pos C hC hδ ha hp hκ hρ hv ξ u
  have hM0 : ∀ t, 0 ≤ ∑ h₀ : Bool, ∑ H : Fin k → Bool,
      (if (Fin.cons h₀ H : Fin (k + 1) → Bool) (Fin.last k) = t then trainW δ a C ξ u h₀ H
        else 0) := fun t => Finset.sum_nonneg fun h₀ _ => Finset.sum_nonneg fun H _ => by
    split_ifs
    · exact trainW_nonneg C hρ ξ u h₀ H
    · exact le_rfl
  refine ⟨fun t => div_nonneg (hM0 t) hL.le, ?_, fun t ht => ?_, ?_⟩
  · unfold piK
    rw [← Finset.sum_div, div_eq_one_iff_eq hL.ne', Finset.sum_comm]
    unfold Lf
    refine Finset.sum_congr rfl fun h₀ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [Finset.sum_ite_eq]; simp
  · unfold piK
    rw [div_eq_zero_iff]; left
    refine Finset.sum_eq_zero fun h₀ _ => Finset.sum_eq_zero fun H _ => ?_
    split_ifs with he
    · exact trainW_infeas C ξ u h₀ H (he ▸ ht)
    · rfl
  · unfold piK
    refine div_pos (lt_of_lt_of_le (trainW_false_pos C hC hδ ha hp hκ hρ hv ξ u) ?_) hL
    refine le_trans ?_ (Finset.single_le_sum (fun h₀ _ => Finset.sum_nonneg fun H _ => by
      split_ifs
      · exact trainW_nonneg C hρ ξ u h₀ H
      · exact le_rfl) (Finset.mem_univ false))
    refine le_trans ?_ (Finset.single_le_sum (fun H _ => by
      split_ifs
      · exact trainW_nonneg C hρ ξ u false H
      · exact le_rfl) (Finset.mem_univ (fun _ => false)))
    rw [ite_eq_left (by refine Fin.cases rfl (fun i => rfl) (Fin.last k))]

end Train

/-! ## The selected forecast -/

section Sel

variable {r k n : ℕ} [NeZero r] (C : Cat r k n)

omit [NeZero r] in
/-- The forecast of any catalogue member from its final sign vector. -/
theorem qgen_facts (hC : Novel.D13CEVCatalogue.Cited) (hδ : 0 < δ) (ha : 0 ≤ a)
    (hp : ∀ ξ, 1 < C.pf ξ) (hκ : ∀ ξ, 0 < C.κf ξ) (hρ : ∀ ξ, 0 ≤ C.ρf ξ ∧ C.ρf ξ < 1)
    (hv : ∀ ξ j, 0 < C.vf ξ j) (ξ : Fin r) (u : Fin (k + 1) → ℕ) :
    (∀ w : Fin n → ℕ, 0 < ∑ t : Bool, piK δ a C ξ u t * ∑ Hz : Fin n → Bool,
      chainS (fun j => Kf δ a (C.ρf ξ) (C.pf ξ) (C.κf ξ) (C.vf ξ (Fin.natAdd k j)))
        (u (Fin.last k), t) (fun j => (w j, Hz j))) ∧
    HasSum (fun w : Fin n → ℕ => ∑ t : Bool, piK δ a C ξ u t * ∑ Hz : Fin n → Bool,
      chainS (fun j => Kf δ a (C.ρf ξ) (C.pf ξ) (C.κf ξ) (C.vf ξ (Fin.natAdd k j)))
        (u (Fin.last k), t) (fun j => (w j, Hz j))) 1 := by
  obtain ⟨hπ0, hπ1, hπf, hπpos⟩ := piK_facts C hC hδ ha hp hκ hρ hv ξ u
  have hS0 : ∀ (t : Bool) (w : Fin n → ℕ), 0 ≤ ∑ Hz : Fin n → Bool,
      chainS (fun j => Kf δ a (C.ρf ξ) (C.pf ξ) (C.κf ξ) (C.vf ξ (Fin.natAdd k j)))
        (u (Fin.last k), t) (fun j => (w j, Hz j)) :=
    fun t w => Finset.sum_nonneg fun Hz _ => chainS_nonneg (hρ ξ) _ _
  refine ⟨fun w => ?_, ?_⟩
  · have h1 : 0 < chainS (fun j => Kf δ a (C.ρf ξ) (C.pf ξ) (C.κf ξ) (C.vf ξ (Fin.natAdd k j)))
        (u (Fin.last k), false) (fun j => (w j, false)) :=
      chainS_false_pos hC hδ ha (hρ ξ) (hp ξ) (hκ ξ) (fun j => hv ξ _) (u (Fin.last k)) w
    have h2 := Finset.single_le_sum (f := fun Hz : Fin n → Bool =>
      chainS (fun j => Kf δ a (C.ρf ξ) (C.pf ξ) (C.κf ξ) (C.vf ξ (Fin.natAdd k j)))
        (u (Fin.last k), false) (fun j => (w j, Hz j)))
      (fun Hz _ => chainS_nonneg (hρ ξ) _ _) (Finset.mem_univ fun _ => false)
    refine lt_of_lt_of_le (mul_pos hπpos (lt_of_lt_of_le h1 h2)) ?_
    exact Finset.single_le_sum (f := fun t => piK δ a C ξ u t * ∑ Hz : Fin n → Bool,
      chainS (fun j => Kf δ a (C.ρf ξ) (C.pf ξ) (C.κf ξ) (C.vf ξ (Fin.natAdd k j)))
        (u (Fin.last k), t) (fun j => (w j, Hz j)))
      (fun t _ => mul_nonneg (hπ0 t) (hS0 t w)) (Finset.mem_univ false)
  · have hterm : ∀ t ∈ (Finset.univ : Finset Bool), HasSum (fun w : Fin n → ℕ => piK δ a C ξ u t *
        ∑ Hz : Fin n → Bool, chainS (fun j => Kf δ a (C.ρf ξ) (C.pf ξ) (C.κf ξ)
          (C.vf ξ (Fin.natAdd k j))) (u (Fin.last k), t) (fun j => (w j, Hz j)))
        (piK δ a C ξ u t) := fun t _ => by
      by_cases hf : Feas δ a (u (Fin.last k)) t
      · have := (chainS_labels hC hδ (hρ ξ) (hp ξ) (hκ ξ) (v := fun j => C.vf ξ (Fin.natAdd k j))
          (fun j => hv ξ _) (s₀ := (u (Fin.last k), t)) hf).mul_left (piK δ a C ξ u t)
        rwa [mul_one] at this
      · simp only [hπf t hf, zero_mul]; exact hasSum_zero
    have := hasSum_sum hterm
    rwa [hπ1] at this

theorem qCN_facts (hC : Novel.D13CEVCatalogue.Cited) (hδ : 0 < δ) (ha : 0 ≤ a)
    (hp : ∀ ξ, 1 < C.pf ξ) (hκ : ∀ ξ, 0 < C.κf ξ) (hρ : ∀ ξ, 0 ≤ C.ρf ξ ∧ C.ρf ξ < 1)
    (hv : ∀ ξ j, 0 < C.vf ξ j) (u : Fin (k + 1) → ℕ) :
    (∀ w, 0 < qCN δ a C u w) ∧ HasSum (qCN δ a C u) 1 :=
  qgen_facts C hC hδ ha hp hκ hρ hv (selF δ a C u) u

/-! ## Zero radius -/

theorem ilo_zero (hδ : 0 < δ) (z : ℕ) (t : Bool) : ilo δ 0 z t = Standalone.D14FixedTick.mlo δ z := by
  unfold ilo; split_ifs with hz
  · subst hz; exact (Novel.D14FixedTick.mlo_zero hδ).symm
  · simp only [mul_zero, sub_zero]; exact max_eq_right (Novel.D14FixedTick.mlo_nonneg δ z)

theorem ihi_zero (z : ℕ) (t : Bool) : ihi δ 0 z t = Standalone.D14FixedTick.mhi δ z := by
  unfold ihi; simp

theorem rmid_zero (hδ : 0 < δ) (z : ℕ) (h : Bool) : rmid δ 0 z h = mrep δ z := by
  unfold rmid mrep
  rw [ilo_zero hδ, ihi_zero]
  split_ifs with hz
  · subst hz; rw [Novel.D14FixedTick.mlo_zero hδ]; unfold mhi; push_cast; ring
  · unfold mlo mhi
    have : (1 : ℝ) ≤ z := Nat.one_le_cast.2 (Nat.pos_of_ne_zero hz)
    rw [max_eq_right (by nlinarith)]; ring

theorem Pint_zero (hδ : 0 < δ) (p κ v : ℝ) (s s' : ℕ × Bool) :
    Pint δ 0 p κ v s s' = Standalone.D17ClockForecast.Pcell δ p κ v s.1 s'.1 := by
  unfold Pint Standalone.D17ClockForecast.Pcell
  rw [ilo_zero hδ, ihi_zero, rmid_zero hδ]
  rfl

theorem cons_pair {m : ℕ} (z₀ : ℕ) (h₀ : Bool) (Z : Fin m → ℕ) (H : Fin m → Bool)
    (i : Fin (m + 1)) : (Fin.cons (z₀, h₀) (fun j => (Z j, H j)) : Fin (m + 1) → ℕ × Bool) i =
      ((Fin.cons z₀ Z : Fin (m + 1) → ℕ) i, (Fin.cons h₀ H : Fin (m + 1) → Bool) i) :=
  Fin.cases rfl (fun _ => rfl) i

/-- The sign chain of the forecast sums to one. -/
theorem Af_chain (ρ : ℝ) : ∀ (m : ℕ) (h₀ : Bool),
    ∑ H : Fin m → Bool, ∏ j : Fin m, Af ρ ((Fin.cons h₀ H : Fin (m + 1) → Bool) j.castSucc) (H j) = 1
  | 0, h₀ => by simp
  | m + 1, h₀ => by
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Bool).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    have e : ∀ (t : Bool) (H' : Fin m → Bool), ∏ j : Fin (m + 1),
        Af ρ ((Fin.cons h₀ (Fin.cons t H' : Fin (m + 1) → Bool) : Fin (m + 2) → Bool) j.castSucc)
          ((Fin.cons t H' : Fin (m + 1) → Bool) j) =
        Af ρ h₀ t * ∏ j : Fin m, Af ρ ((Fin.cons t H' : Fin (m + 1) → Bool) j.castSucc) (H' j) := by
      intro t H'
      rw [Fin.prod_univ_succ]
      congr 1
    simp_rw [e, ← Finset.mul_sum, Af_chain ρ m, mul_one, Af_sum]

theorem chainS_zero (hδ : 0 < δ) {m : ℕ} (ρ p κ : ℝ) (v : Fin m → ℝ) (z₀ : ℕ) (h₀ : Bool)
    (Z : Fin m → ℕ) :
    ∑ H : Fin m → Bool, chainS (fun j => Kf δ 0 ρ p κ (v j)) (z₀, h₀) (fun j => (Z j, H j)) =
      Standalone.D17ClockForecast.chainCell δ p κ v z₀ Z := by
  unfold chainS Standalone.D17ClockForecast.chainCell
  simp only [cons_pair, Kf, Pint_zero hδ, Finset.prod_mul_distrib]
  rw [← Finset.sum_mul, Af_chain ρ m h₀, one_mul]

omit [NeZero r] in
theorem Lf_zero (hδ : 0 < δ) (ξ : Fin r) (u : Fin (k + 1) → ℕ) :
    Lf δ 0 C ξ u = Standalone.D17ClockForecast.chainCell δ (C.pf ξ) (C.κf ξ)
      (fun j => C.vf ξ (Fin.castAdd n j)) (u 0) (Fin.tail u) := by
  unfold Lf trainW
  simp_rw [← Finset.mul_sum]
  simp_rw [chainS_zero hδ (Z := fun j => u j.succ)]
  rw [← Finset.sum_mul, pi0_sum hδ le_rfl, one_mul]
  rfl

theorem qCN_zero (hδ : 0 < δ) (hρ : ∀ ξ, 0 ≤ C.ρf ξ ∧ C.ρf ξ < 1)
    (hC : Novel.D13CEVCatalogue.Cited) (hp : ∀ ξ, 1 < C.pf ξ) (hκ : ∀ ξ, 0 < C.κf ξ)
    (hv : ∀ ξ j, 0 < C.vf ξ j) (u : Fin (k + 1) → ℕ) (w : Fin n → ℕ) :
    qCN δ 0 C u w = Standalone.D17ClockForecast.qCell δ C.pf C.κf
      (fun ξ j => C.vf ξ (Fin.castAdd n j)) (fun ξ j => C.vf ξ (Fin.natAdd k j)) u w := by
  have hsel : selF δ 0 C u = Standalone.D17ClockForecast.selCell δ C.pf C.κf
      (fun ξ j => C.vf ξ (Fin.castAdd n j)) u := by
    unfold selF Standalone.D17ClockForecast.selCell
    congr 1; funext ξ; exact Lf_zero C hδ ξ u
  unfold qCN Standalone.D17ClockForecast.qCell
  simp only [hsel]
  simp_rw [chainS_zero hδ, ← Finset.sum_mul]
  rw [(piK_facts C hC hδ le_rfl hp hκ hρ hv _ u).2.1, one_mul]

end Sel

/-- Part 2. -/
theorem forecast_holds : Standalone.D18ClockNoise.forecast := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW r k n _ δ a C hδ ha hp hκ hρ hv
  have hC := cited_of h55 h56 hW
  refine ⟨fun ξ u => Lf_pos C hC hδ ha hp hκ hρ hv ξ u,
    fun ξ u => let h := piK_facts C hC hδ ha hp hκ hρ hv ξ u; ⟨h.1, h.2.1, h.2.2.1⟩,
    fun u w => (qCN_facts C hC hδ ha hp hκ hρ hv u).1 w,
    fun u => (qCN_facts C hC hδ ha hp hκ hρ hv u).2, fun qb lam hqb0 hqb hlam u => ?_,
    fun h0 u w => ?_⟩
  · have := ((hqb u).mul_left (lam u)).add ((qCN_facts C hC hδ ha hp hκ hρ hv u).2.mul_left
      (1 - lam u))
    rwa [mul_one, mul_one, add_sub_cancel] at this
  · subst h0; exact qCN_zero C hδ hρ hC hp hκ hv u w

end Novel.D18ClockNoise
