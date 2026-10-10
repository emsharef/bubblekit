import Standalone.D16CopulaForecast
import Novel.D16GaussianPoolForecastProof
import Novel.D16CopulaAlgebraProof
import Novel.PiTranspose
import Novel.ParamCDF
import Upstream.GaussianCopula

/-!
# Claim 063: the copula forecast's steps, chain, normalization and factorization

* The CEV marginal CDF `Fcev` and its normal score `zsc = Φ⁻¹ ∘ Fcev`, measurable in the parameters
  and the prices (`Novel.ParamCDF`).
* The definitions are `Standalone.D16CopulaForecast`'s; `qcopc_chain` rewrites `q_cop` as a
  time-major chain.
* The step kernel `kstep` on price vectors.
  - From a positive state it is the copula transition `c_R(z) ∏ f_i` on positive next prices, and
    `0` if any next price is zero (the CEV marginals have no atom for `p > 1`).
  - From a state with a zero price it is the independent product of claim 054's kernels. Such
    states carry no forecast mass; the choice only makes every step normalized.
* `qCop` is the time-major chain of steps (`Novel.PiTranspose.chainT`) started at the last training
  prices. `R` is fitted from the training normal scores by (2).
* The normalization of a positive step is AX-61's content: `hstep_of` derives it from
  `Upstream.AX61` (with the CEV marginals' cited normalization), and `qcopc_norm'` assembles the chain.
-/

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal

namespace Novel.D16CopulaSteps

open Standalone.D16GaussianPool Standalone.D16CopulaAlgebra Standalone.CEVSupport
  Standalone.D16CopulaForecast Novel.D13CEVCatalogue Novel.PiTranspose

/-! ## The chain form -/

theorem prevV_eq {m n k : ℕ} (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR) (j : Fin n) :
    (Fin.cons (fun i => u i (Fin.last k)) (transp v) : Fin (n + 1) → Fin m → NNR) j.castSucc =
      prevV u v j := by
  funext i
  cases n with
  | zero => exact j.elim0
  | succ n =>
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
  · rfl
  · simp only [prevV, ← Fin.succ_castSucc, Fin.cons_succ]; rfl

theorem qcopc_chain {m n k cp cs : ℕ} (γ : ℝ) (Pw : Fin cp → ℝ) (Ksc : Fin m → Fin cs → ℝ)
    (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ) (c : Cand cp m cs)
    (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR) :
    qcopc γ Pw Ksc ΔT ΔE s c u v =
      chainT (fun j => kstep (Rcop γ (ztr ΔT s (pc Pw c) (κc Ksc c) u)) (pc Pw c) (κc Ksc c) (ΔE j))
        (fun i => u i (Fin.last k)) (transp v) := by
  unfold qcopc chainT
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [prevV_eq]; rfl

/-- The evaluation normal scores for a fixed power and scales. -/
noncomputable def zevc {m n k : ℕ} (ΔE : Fin n → ℝ) (p : ℝ) (κ : Fin m → ℝ)
    (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR) : Fin n → Fin m → ℝ :=
  fun j i => zsc p (κ i) (ΔE j) (prevN (u i (Fin.last k) : ℝ) (v i) j) (v i j)

/-! ## Measurability -/

theorem measurable_Fcev (p κ Δ : ℝ) : Measurable fun q : ℝ × ℝ => Fcev p κ Δ q.1 q.2 :=
  Novel.ParamCDF.measurable_cdf (g := fcev p κ Δ) (fcev_meas p κ Δ)

theorem measurable_zsc (p κ Δ : ℝ) : Measurable fun q : ℝ × ℝ => zsc p κ Δ q.1 q.2 :=
  Novel.D16CopulaAlgebra.measurable_PhiInv.comp (measurable_Fcev p κ Δ)

theorem measurable_matrix_inv {m : ℕ} :
    Measurable fun A : Matrix (Fin m) (Fin m) ℝ => A⁻¹ := by
  have e : (fun A : Matrix (Fin m) (Fin m) ℝ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  exact ((continuous_id.matrix_det).measurable.inv).smul
    (continuous_id.matrix_adjugate).measurable

theorem measurable_cR {m : ℕ} {X : Type*} [MeasurableSpace X] {R : X → Matrix (Fin m) (Fin m) ℝ}
    {z : X → Fin m → ℝ} (hR : Measurable R) (hz : Measurable z) :
    Measurable fun q => cR (R q) (z q) := by
  unfold cR
  have hdet : Measurable fun q => (R q).det := (continuous_id.matrix_det).measurable.comp hR
  have hinv : Measurable fun q => (R q)⁻¹ := measurable_matrix_inv.comp hR
  refine (hdet.pow_const _).mul (Real.measurable_exp.comp ?_)
  refine ((Continuous.measurable (by fun_prop :
    Continuous fun p : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ => -(p.1 ⬝ᵥ ((p.2 - 1) *ᵥ p.1)) / 2))).comp
    (hz.prodMk hinv)

theorem measurableSet_allpos {m : ℕ} {X : Type*} [MeasurableSpace X] {x : X → Fin m → NNR}
    (hx : Measurable x) : MeasurableSet {q | ∀ i, 0 < ((x q) i : ℝ)} := by
  have : {q | ∀ i, 0 < ((x q) i : ℝ)} = ⋂ i, {q | 0 < ((x q) i : ℝ)} := by ext; simp
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const
    (measurable_subtype_coe.comp ((measurable_pi_apply i).comp hx))

/-- The step kernel is measurable jointly in a parameter `q` (through `R`) and both price vectors. -/
theorem measurable_kstep {m : ℕ} {X : Type*} [MeasurableSpace X] {R : X → Matrix (Fin m) (Fin m) ℝ}
    (hR : Measurable R) (p : ℝ) (κ : Fin m → ℝ) (Δ : ℝ) :
    Measurable fun q : X × (Fin m → NNR) × (Fin m → NNR) => kstep (R q.1) p κ Δ q.2.1 q.2.2 := by
  classical
  have hx : Measurable fun q : X × (Fin m → NNR) × (Fin m → NNR) => q.2.1 :=
    measurable_fst.comp measurable_snd
  have hy : Measurable fun q : X × (Fin m → NNR) × (Fin m → NNR) => q.2.2 :=
    measurable_snd.comp measurable_snd
  have hxi : ∀ i, Measurable fun q : X × (Fin m → NNR) × (Fin m → NNR) => ((q.2.1 i : NNR) : ℝ) :=
    fun i => measurable_subtype_coe.comp ((measurable_pi_apply i).comp hx)
  have hyi : ∀ i, Measurable fun q : X × (Fin m → NNR) × (Fin m → NNR) => ((q.2.2 i : NNR) : ℝ) :=
    fun i => measurable_subtype_coe.comp ((measurable_pi_apply i).comp hy)
  unfold kstep
  refine Measurable.ite (measurableSet_allpos hx) (Measurable.ite (measurableSet_allpos hy) ?_
    measurable_const) (Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
      ((Kc_meas _ _ _).comp ((hxi i).prodMk (hyi i))))
  refine ENNReal.measurable_ofReal.comp ((measurable_cR (hR.comp measurable_fst)
    (measurable_pi_iff.2 fun i => (measurable_zsc _ _ _).comp ((hxi i).prodMk (hyi i)))).mul
    (Finset.measurable_prod _ fun i _ => (fcev_meas _ _ _).comp ((hxi i).prodMk (hyi i))))

/-- A chain whose kernels depend measurably on a parameter. -/
theorem measurable_chainT_param {β X : Type*} [MeasurableSpace β] [MeasurableSpace X] {n : ℕ}
    {k : X → Fin n → β → β → ℝ≥0∞}
    (hk : ∀ j, Measurable fun q : X × β × β => k q.1 j q.2.1 q.2.2) :
    Measurable fun q : X × β × (Fin n → β) => chainT (k q.1) q.2.1 q.2.2 := by
  unfold chainT
  have hc : Measurable fun q : X × β × (Fin n → β) => (Fin.cons q.2.1 q.2.2 : Fin (n + 1) → β) := by
    refine measurable_pi_iff.2 fun l => ?_
    refine Fin.cases ?_ (fun i => ?_) l
    · simp only [Fin.cons_zero]; exact measurable_fst.comp measurable_snd
    · simp only [Fin.cons_succ]
      exact (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  exact Finset.measurable_prod _ fun j _ => (hk j).comp (measurable_fst.prodMk
    (((measurable_pi_apply j.castSucc).comp hc).prodMk
      ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))))

theorem measurable_prevN' {k : ℕ} (j : Fin (k + 1)) {X : Type*} [MeasurableSpace X] {x : X → ℝ}
    {u : X → Fin (k + 1) → NNR} (hx : Measurable x) (hu : Measurable u) :
    Measurable fun q => prevN (x q) (u q) j :=
  (prevN_meas j).comp (hx.prodMk hu)

theorem measurable_ztr {m k : ℕ} (ΔT : Fin (k + 1) → ℝ) (s : Fin m → ℝ) (p : ℝ) (κ : Fin m → ℝ) :
    Measurable fun u : Fin m → Fin (k + 1) → NNR => ztr ΔT s p κ u := by
  refine measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun i => ?_
  show Measurable fun u : Fin m → Fin (k + 1) → NNR =>
    zsc p (κ i) (ΔT j) (prevN (s i) (u i) j) (u i j : ℝ)
  have h1 : Measurable fun u : Fin m → Fin (k + 1) → NNR => prevN (s i) (u i) j :=
    measurable_prevN' j measurable_const (measurable_pi_apply i)
  have h2 : Measurable fun u : Fin m → Fin (k + 1) → NNR => ((u i j : NNR) : ℝ) :=
    measurable_subtype_coe.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))
  exact Measurable.comp (g := fun q : ℝ × ℝ => zsc p (κ i) (ΔT j) q.1 q.2)
    (f := fun u : Fin m → Fin (k + 1) → NNR => (prevN (s i) (u i) j, ((u i j : NNR) : ℝ)))
    (measurable_zsc _ _ _) (h1.prodMk h2)

variable {m n k cp cs : ℕ}

theorem measurable_qcopc (γ : ℝ) (Pw : Fin cp → ℝ) (Ksc : Fin m → Fin cs → ℝ)
    (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ) (c : Cand cp m cs) :
    Measurable fun q : (Fin m → Fin (k + 1) → NNR) × (Fin m → Fin n → NNR) =>
      qcopc γ Pw Ksc ΔT ΔE s c q.1 q.2 := by
  have hR : Measurable fun u : Fin m → Fin (k + 1) → NNR => Rcop γ (ztr ΔT s (pc Pw c) (κc Ksc c) u) :=
    (Novel.D16CopulaAlgebra.measurable_Rcop γ).comp (measurable_ztr _ _ _ _)
  have hch := measurable_chainT_param (X := Fin m → Fin (k + 1) → NNR) (β := Fin m → NNR)
    (k := fun u j => kstep (Rcop γ (ztr ΔT s (pc Pw c) (κc Ksc c) u)) (pc Pw c) (κc Ksc c) (ΔE j))
    fun j => measurable_kstep hR _ _ _
  have hlast : Measurable fun u : Fin m → Fin (k + 1) → NNR => fun i => u i (Fin.last k) :=
    measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp (measurable_pi_apply i)
  have e : (fun q : (Fin m → Fin (k + 1) → NNR) × (Fin m → Fin n → NNR) =>
      qcopc γ Pw Ksc ΔT ΔE s c q.1 q.2) = fun q => chainT (fun j => kstep (Rcop γ
        (ztr ΔT s (pc Pw c) (κc Ksc c) q.1)) (pc Pw c) (κc Ksc c) (ΔE j))
          (fun i => q.1 i (Fin.last k)) (transp q.2) :=
    funext fun q => qcopc_chain γ Pw Ksc ΔT ΔE s c q.1 q.2
  rw [e]
  exact Measurable.comp (g := fun r : (Fin m → Fin (k + 1) → NNR) × (Fin m → NNR) ×
      (Fin n → Fin m → NNR) => chainT (fun j => kstep (Rcop γ (ztr ΔT s (pc Pw c) (κc Ksc c) r.1))
        (pc Pw c) (κc Ksc c) (ΔE j)) r.2.1 r.2.2)
    (f := fun q : (Fin m → Fin (k + 1) → NNR) × (Fin m → Fin n → NNR) =>
      (q.1, (fun i => q.1 i (Fin.last k)), transp q.2)) hch
    (measurable_fst.prodMk ((hlast.comp measurable_fst).prodMk
      (measurable_transp.comp measurable_snd)))

/-- `q_cop` with the selected candidate, as an extended density. -/
theorem measurable_qCopE [NeZero cp] [NeZero cs] (γ : ℝ) (Pw : Fin cp → ℝ)
    (Ksc : Fin m → Fin cs → ℝ) (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ) :
    Measurable fun q : (Fin m → Fin (k + 1) → NNR) × (Fin m → Fin n → NNR) =>
      qcopc γ Pw Ksc ΔT ΔE s (selPool Pw Ksc ΔT s q.1) q.1 q.2 := by
  classical
  have e : (fun q : (Fin m → Fin (k + 1) → NNR) × (Fin m → Fin n → NNR) =>
      qcopc γ Pw Ksc ΔT ΔE s (selPool Pw Ksc ΔT s q.1) q.1 q.2) = fun q =>
      ∑ c : Cand cp m cs, {u | selPool Pw Ksc ΔT s u = c}.indicator (fun _ => (1 : ℝ≥0∞)) q.1 *
        qcopc γ Pw Ksc ΔT ΔE s c q.1 q.2 := by
    funext q
    rw [Finset.sum_eq_single (selPool Pw Ksc ΔT s q.1)]
    · rw [indicator_of_mem (show q.1 ∈ {u | selPool Pw Ksc ΔT s u = selPool Pw Ksc ΔT s q.1} from rfl),
        one_mul]
    · intro c _ hc
      rw [indicator_of_notMem (show q.1 ∉ {u | selPool Pw Ksc ΔT s u = c} from fun h => hc h.symm),
        zero_mul]
    · simp
  rw [e]
  exact Finset.measurable_sum _ fun c _ =>
    ((measurable_const.indicator (Novel.D16GaussianPoolForecast.measurableSet_sel c)).comp
      measurable_fst).mul (measurable_qcopc γ Pw Ksc ΔT ΔE s c)

theorem measurable_qCop [NeZero cp] [NeZero cs] (γ : ℝ) (Pw : Fin cp → ℝ)
    (Ksc : Fin m → Fin cs → ℝ) (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ) :
    Measurable (Function.uncurry (qCop γ Pw Ksc ΔT ΔE s)) :=
  ENNReal.measurable_toReal.comp (measurable_qCopE γ Pw Ksc ΔT ΔE s)

/-! ## Normalization -/

theorem measurable_kstep' {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (p : ℝ) (κ : Fin m → ℝ) (Δ : ℝ) :
    Measurable (Function.uncurry (kstep R p κ Δ)) :=
  Measurable.comp (g := fun q : Unit × (Fin m → NNR) × (Fin m → NNR) => kstep R p κ Δ q.2.1 q.2.2)
    (f := fun q : (Fin m → NNR) × (Fin m → NNR) => ((), q.1, q.2))
    (measurable_kstep (R := fun _ : Unit => R) measurable_const p κ Δ)
    (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))

/-- From a state with a zero price the step is the independent product of claim 054's kernels,
which has mass one (`Cited`). -/
theorem kstep_norm_off (hC : Cited) {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) {p : ℝ} (hp : 0 < p)
    {κ : Fin m → ℝ} (hκ : ∀ i, 0 < κ i) {Δ : ℝ} (hΔ : 0 < Δ) {x : Fin m → NNR}
    (hx : ¬ ∀ i, 0 < (x i : ℝ)) :
    ∫⁻ y, kstep R p κ Δ x y ∂(Measure.pi fun _ : Fin m => muCEV) = 1 := by
  classical
  simp only [kstep, hx, ↓reduceIte]
  rw [Novel.D16GaussianPoolForecast.lintegral_pi_prod muCEV m
    (fun i y => ENNReal.ofReal (Kc p (κ i) Δ (x i) (y : ℝ)))
    fun i => ENNReal.measurable_ofReal.comp ((Kc_meas _ _ _).comp
      (measurable_const.prodMk measurable_subtype_coe))]
  exact Finset.prod_eq_one fun i _ => Kc_norm' hC hp (hκ i) hΔ (x i).2

/-- `q_cop` has mass one, given that every positive-state copula step with a positive-definite
unit-diagonal matrix has mass one (AX-61's normalization, applied to the CEV marginals). -/
theorem qcopc_norm (hC : Cited) {m n k cp cs : ℕ} {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {Pw : Fin cp → ℝ} {Ksc : Fin m → Fin cs → ℝ} (hP : ∀ a, 1 < Pw a) (hK : ∀ i b, 0 < Ksc i b)
    (ΔT : Fin (k + 1) → ℝ) {ΔE : Fin n → ℝ} (hΔ : ∀ j, 0 < ΔE j) (s : Fin m → ℝ)
    (hstep : ∀ (R : Matrix (Fin m) (Fin m) ℝ) (p : ℝ) (κ : Fin m → ℝ) (Δ : ℝ) (x : Fin m → NNR),
      R.PosDef → (∀ i, R i i = 1) → 1 < p → (∀ i, 0 < κ i) → 0 < Δ → (∀ i, 0 < (x i : ℝ)) →
      ∫⁻ y, kstep R p κ Δ x y ∂(Measure.pi fun _ : Fin m => muCEV) = 1)
    (c : Cand cp m cs) (u : Fin m → Fin (k + 1) → NNR) :
    ∫⁻ v, qcopc γ Pw Ksc ΔT ΔE s c u v
      ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV) = 1 := by
  set R := Rcop γ (ztr ΔT s (pc Pw c) (κc Ksc c) u)
  have hR := Novel.D16CopulaAlgebra.Rcop_posDef hγ hγ1 (ztr ΔT s (pc Pw c) (κc Ksc c) u)
  have hdiag := Novel.D16CopulaAlgebra.Rcop_diag γ (ztr ΔT s (pc Pw c) (κc Ksc c) u)
  have hp : 1 < pc Pw c := hP _
  have hκ : ∀ i, 0 < κc Ksc c i := fun i => hK _ _
  have hmeas : ∀ j, Measurable (Function.uncurry (fun x y =>
      kstep R (pc Pw c) (κc Ksc c) (ΔE j) x y)) := fun j => measurable_kstep' _ _ _ _
  simp_rw [qcopc_chain γ Pw Ksc ΔT ΔE s c u]
  rw [lintegral_transp muCEV (F := chainT (fun j => kstep R (pc Pw c) (κc Ksc c) (ΔE j))
    (fun i => u i (Fin.last k))) ((measurable_chainT hmeas).comp
      (measurable_const.prodMk measurable_id))]
  refine lintegral_chainT _ _ hmeas (fun j x => ?_) _
  by_cases hx : ∀ i, 0 < (x i : ℝ)
  · exact hstep R _ _ _ x hR hdiag hp hκ (hΔ j) hx
  · exact kstep_norm_off hC R (by linarith) hκ (hΔ j) hx

/-! ## The positive-record factorization -/

theorem cons_transp_eq {m n k : ℕ} (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR)
    (j : Fin n) (i : Fin m) :
    (((Fin.cons (fun i => u i (Fin.last k)) (transp v) : Fin (n + 1) → Fin m → NNR)
      j.castSucc i : NNR) : ℝ) = prevN (u i (Fin.last k) : ℝ) (v i) j := by
  cases n with
  | zero => exact j.elim0
  | succ n =>
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
  · simp [prevN]
  · rw [← Fin.succ_castSucc, Fin.cons_succ]
    simp only [transp, prevN, Fin.val_succ, Nat.add_one_ne_zero, dite_false]
    rfl

theorem prevN_pos {n : ℕ} {x₀ : ℝ} (hx : 0 < x₀) {y : Fin n → NNR} (hy : ∀ j, 0 < (y j : ℝ))
    (j : Fin n) : 0 < prevN x₀ y j := by
  unfold prevN; split_ifs
  · exact hx
  · exact hy _

theorem Kc_eq_fcev {p κ Δ x y : ℝ} (hp : p ≠ 1) (hx : 0 < x) (hy : 0 < y) :
    Kc p κ Δ x y = fcev p κ Δ x y := by
  simp [Kc, K, hp, hx.ne', hy.ne']

theorem qcopc_pos (hC : Cited) {m n k cp cs : ℕ} {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {Pw : Fin cp → ℝ} {Ksc : Fin m → Fin cs → ℝ} (hP : ∀ a, 1 < Pw a) (hK : ∀ i b, 0 < Ksc i b)
    (ΔT : Fin (k + 1) → ℝ) {ΔE : Fin n → ℝ} (hΔ : ∀ j, 0 < ΔE j) (s : Fin m → ℝ)
    (c : Cand cp m cs) (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR)
    (hu : ∀ i, 0 < (u i (Fin.last k) : ℝ)) (hv : ∀ i j, 0 < (v i j : ℝ)) :
    qcopc γ Pw Ksc ΔT ΔE s c u v = ENNReal.ofReal
      ((∏ j, cR (Rcop γ (ztr ΔT s (pc Pw c) (κc Ksc c) u)) (zevc ΔE (pc Pw c) (κc Ksc c) u v j)) *
        Novel.D16GaussianPoolForecast.qc Pw Ksc ΔE c u v) := by
  classical
  set R := Rcop γ (ztr ΔT s (pc Pw c) (κc Ksc c) u)
  have hR : R.PosDef := Novel.D16CopulaAlgebra.Rcop_posDef hγ hγ1 _
  have hp1 : pc Pw c ≠ 1 := (hP _).ne'
  have hp0 : 0 < pc Pw c := by have := hP (ofLex c).1; simp only [pc]; linarith
  set f : Fin n → Fin m → ℝ := fun j i =>
    fcev (pc Pw c) (κc Ksc c i) (ΔE j) (prevN (u i (Fin.last k) : ℝ) (v i) j) (v i j)
  have hf : ∀ j i, 0 < f j i := fun j i =>
    hC.pos _ _ _ hp0 hp1 (hK _ _) (hΔ j) _ _ (prevN_pos (hu i) (hv i) j) (hv i j)
  have hstep : ∀ j, kstep R (pc Pw c) (κc Ksc c) (ΔE j)
      ((Fin.cons (fun i => u i (Fin.last k)) (transp v) : Fin (n + 1) → Fin m → NNR) j.castSucc)
      (transp v j) = ENNReal.ofReal (cR R (zevc ΔE (pc Pw c) (κc Ksc c) u v j) * ∏ i, f j i) := by
    intro j
    have hx : ∀ i, 0 < (((Fin.cons (fun i => u i (Fin.last k)) (transp v) :
        Fin (n + 1) → Fin m → NNR) j.castSucc i : NNR) : ℝ) := fun i => by
      rw [cons_transp_eq]; exact prevN_pos (hu i) (hv i) j
    have hy : ∀ i, 0 < ((transp v j i : NNR) : ℝ) := fun i => hv i j
    have hz : (fun i => zsc (pc Pw c) (κc Ksc c i) (ΔE j)
        (((Fin.cons (fun i => u i (Fin.last k)) (transp v) : Fin (n + 1) → Fin m → NNR)
          j.castSucc i : NNR) : ℝ) ((transp v j i : NNR) : ℝ)) = zevc ΔE (pc Pw c) (κc Ksc c) u v j := by
      funext i; rw [cons_transp_eq]; rfl
    have hpr : (∏ i, fcev (pc Pw c) (κc Ksc c i) (ΔE j)
        (((Fin.cons (fun i => u i (Fin.last k)) (transp v) : Fin (n + 1) → Fin m → NNR)
          j.castSucc i : NNR) : ℝ) ((transp v j i : NNR) : ℝ)) = ∏ i, f j i := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [cons_transp_eq]; rfl
    simp only [kstep, hx, hy, implies_true, ↓reduceIte]
    rw [hz, hpr]
  have hqc : Novel.D16GaussianPoolForecast.qc Pw Ksc ΔE c u v = ∏ j, ∏ i, f j i := by
    unfold Novel.D16GaussianPoolForecast.qc chainN
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i _ => ?_
    exact Kc_eq_fcev hp1 (prevN_pos (hu i) (hv i) j) (hv i j)
  rw [qcopc_chain]
  show (∏ j, kstep R (pc Pw c) (κc Ksc c) (ΔE j)
      ((Fin.cons (fun i => u i (Fin.last k)) (transp v) : Fin (n + 1) → Fin m → NNR) j.castSucc)
      (transp v j)) = _
  rw [Finset.prod_congr rfl fun j _ => hstep j,← ENNReal.ofReal_prod_of_nonneg fun j _ => mul_nonneg
    (Novel.D16CopulaAlgebra.cR_pos hR _).le (Finset.prod_nonneg fun i _ => (hf j i).le),
    Finset.prod_mul_distrib, hqc]

/-! ## AX-61: the positive-state step -/

theorem muCEV_eq : Upstream.CEVKernel.muCEV = Standalone.CEVSupport.muCEV := rfl

theorem cR_bridge {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (z : Fin m → ℝ) :
    Standalone.D16CopulaAlgebra.cR R z = Upstream.GaussianCopula.cR R z := by
  unfold Standalone.D16CopulaAlgebra.cR Upstream.GaussianCopula.cR
  congr 2; ring

theorem PhiInv_bridge : Standalone.D16CopulaAlgebra.PhiInv = Upstream.GaussianCopula.phiInv := rfl

theorem Fm_bridge {f : ℝ → ℝ} (hf : Measurable f) (hpos : ∀ v, 0 < v → 0 ≤ f v) {y : ℝ}
    (hy : 0 ≤ y) : Fm f y = Upstream.GaussianCopula.Fcdf f y := by
  unfold Fm Upstream.GaussianCopula.Fcdf
  rw [intervalIntegral.integral_of_le hy, integral_eq_lintegral_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun v hv => hpos v hv.1))
    hf.aestronglyMeasurable]

theorem zsc_bridge {p κ Δ x y : ℝ} (hf : ∀ v, 0 < v → 0 ≤ fcev p κ Δ x v) (hy : 0 ≤ y) :
    zsc p κ Δ x y = Upstream.GaussianCopula.zScore (fcev p κ Δ x) y := by
  unfold zsc Upstream.GaussianCopula.zScore Fcev
  rw [Fm_bridge (f := fcev p κ Δ x) ((fcev_meas p κ Δ).comp (measurable_const.prodMk measurable_id))
    hf hy,
    PhiInv_bridge]

/-- The statement's restated AX-61 is `Upstream.AX61`: the definitions agree. -/
theorem ax61_up (h : Standalone.D16CopulaForecast.AX61) : Upstream.AX61 :=
  fun m R f hp => ⟨(h m R f hp).1, (h m R f hp).2⟩

/-- From a positive state, the step is AX-61's copula density with the CEV marginals. -/
theorem kstep_eq_kCop (hC : Cited) {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) {p : ℝ} (hp : 1 < p)
    {κ : Fin m → ℝ} (hκ : ∀ i, 0 < κ i) {Δ : ℝ} (hΔ : 0 < Δ) {x : Fin m → NNR}
    (hx : ∀ i, 0 < (x i : ℝ)) (y : Fin m → NNR) :
    kstep R p κ Δ x y =
      ENNReal.ofReal (Upstream.GaussianCopula.kCop R (fun i => fcev p (κ i) Δ (x i)) y) := by
  classical
  have hf : ∀ i v, 0 < v → 0 ≤ fcev p (κ i) Δ (x i) v := fun i v hv =>
    (hC.pos p (κ i) Δ (by linarith) hp.ne' (hκ i) hΔ (x i) v (hx i) hv).le
  unfold kstep Upstream.GaussianCopula.kCop
  simp only [hx, implies_true, ↓reduceIte]
  by_cases hy : ∀ i, 0 < (y i : ℝ)
  · simp only [hy, implies_true, ↓reduceIte]
    rw [cR_bridge]
    congr 3
    funext i
    exact zsc_bridge (hf i) (y i).2
  · simp only [hy, ↓reduceIte, ENNReal.ofReal_zero]

/-- AX-61 discharges the positive-state normalization premise of `qcopc_norm`. -/
theorem hstep_of (hC : Cited) (h61 : Upstream.AX61) {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (p : ℝ) (κ : Fin m → ℝ) (Δ : ℝ) (x : Fin m → NNR) (hR : R.PosDef) (hdiag : ∀ i, R i i = 1)
    (hp : 1 < p) (hκ : ∀ i, 0 < κ i) (hΔ : 0 < Δ) (hx : ∀ i, 0 < (x i : ℝ)) :
    ∫⁻ y, kstep R p κ Δ x y ∂(Measure.pi fun _ : Fin m => muCEV) = 1 := by
  have hprem : Upstream.GaussianCopula.CopPremises R (fun i => fcev p (κ i) Δ (x i)) := by
    refine ⟨hR, hdiag, fun i => ⟨(fcev_meas p (κ i) Δ).comp (measurable_const.prodMk measurable_id),
      fun v hv => hC.pos p (κ i) Δ (by linarith) hp.ne' (hκ i) hΔ (x i) v (hx i) hv, ?_⟩⟩
    have h := hC.norm p (κ i) Δ (by linarith) hp.ne' (hκ i) hΔ (x i) (hx i)
    rwa [show acev p (κ i) Δ (x i) = 0 by simp [acev, not_lt.2 hp.le], ENNReal.ofReal_zero,
      add_zero] at h
  have hnorm := (h61 m R _ hprem).norm
  simp_rw [kstep_eq_kCop hC R hp hκ hΔ hx]
  exact hnorm

/-- `q_cop` has mass one under AX-61 and the cited CEV kernel facts. -/
theorem qcopc_norm' (hC : Cited) (h61 : Upstream.AX61) {m n k cp cs : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) {Pw : Fin cp → ℝ} {Ksc : Fin m → Fin cs → ℝ} (hP : ∀ a, 1 < Pw a)
    (hK : ∀ i b, 0 < Ksc i b) (ΔT : Fin (k + 1) → ℝ) {ΔE : Fin n → ℝ} (hΔ : ∀ j, 0 < ΔE j)
    (s : Fin m → ℝ) (c : Cand cp m cs) (u : Fin m → Fin (k + 1) → NNR) :
    ∫⁻ v, qcopc γ Pw Ksc ΔT ΔE s c u v
      ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV) = 1 :=
  qcopc_norm hC hγ hγ1 hP hK ΔT hΔ s
    (fun R p κ Δ x hR hd hp hκ hΔ' hx => hstep_of hC h61 R p κ Δ x hR hd hp hκ hΔ' hx) c u

end Novel.D16CopulaSteps
