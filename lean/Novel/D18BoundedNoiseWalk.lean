import Novel.D18BoundedNoiseEmit

/-!
# Claim 064: the suffix bound

For an emission `h z y ∈ [0, 1]` that vanishes outside the expanded interval `I_z^a`,
`Qh h v x = E[∏_j h(v_j, X_j)]` is the expected emission product along the Gaussian latent path
from the exact state `x`. Support mode is `h = 1_{I^a}`; uniform mode is `h = gnoise`.

* `Qh_succ`: the first-step decomposition through `MeasurableEquiv.piFinSuccAbove`.
* `Qh_le_Ue` (claim 030's finite-partition argument): from every state of subcell `c` of `I_z^a`,
  `Qh ≤ U`, when `h ≤ M` on every subcell. Partition the next expanded interval into its subcells;
  on each, the emission is at most `M`, the suffix at most the next `U`, and the transition at most
  claim 031's `W`, uniformly over the current subcell (exact zero state included). `1` and the
  parent's bound are also valid.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18BoundedNoise

open Standalone.D18BoundedNoise Standalone.D14FixedTick Novel.D14FixedTick

variable {δ a : ℝ}

theorem measurable_lpath : ∀ n : ℕ, Measurable fun q : ℝ × (Fin n → ℝ) => lpath n q.1 q.2
  | 0 => measurable_of_subsingleton_codomain _
  | n + 1 => by
    have hfirst : Measurable fun q : ℝ × (Fin (n + 1) → ℝ) => q.1 * Real.exp (q.2 0) :=
      measurable_fst.mul (Real.measurable_exp.comp ((measurable_pi_apply 0).comp measurable_snd))
    have htail : Measurable fun q : ℝ × (Fin (n + 1) → ℝ) => Fin.tail q.2 :=
      measurable_pi_iff.2 fun j => (measurable_pi_apply j.succ).comp measurable_snd
    refine measurable_pi_iff.2 fun j => ?_
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [lpath, Fin.cons_zero]
      exact hfirst
    · simp only [lpath, Fin.cons_succ]
      exact (measurable_pi_apply i).comp ((measurable_lpath n).comp (hfirst.prodMk htail))

theorem lpath_succ {n : ℕ} (x : ℝ) (ξ : Fin (n + 1) → ℝ) :
    lpath (n + 1) x ξ = Fin.cons (x * Real.exp (ξ 0)) (lpath n (x * Real.exp (ξ 0)) (Fin.tail ξ)) :=
  rfl

theorem lpath_zero : ∀ (n : ℕ) (ξ : Fin n → ℝ), lpath n 0 ξ = fun _ => 0
  | 0, _ => funext fun j => j.elim0
  | n + 1, ξ => by
    rw [lpath_succ, zero_mul, lpath_zero n]
    funext j
    refine Fin.cases rfl (fun i => rfl) j

theorem lpath_nonneg : ∀ (n : ℕ) {x : ℝ} (ξ : Fin n → ℝ), 0 ≤ x → ∀ j, 0 ≤ lpath n x ξ j
  | 0, _, _, _, j => j.elim0
  | n + 1, x, ξ, hx, j => by
    rw [lpath_succ]
    have h0 : 0 ≤ x * Real.exp (ξ 0) := mul_nonneg hx (Real.exp_pos _).le
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [Fin.cons_zero]; exact h0
    · rw [Fin.cons_succ]; exact lpath_nonneg n _ h0 i

/-- The Gaussian law of the log returns. -/
noncomputable def gpi {n : ℕ} (μ s : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi fun j => gaussianReal (μ j) (s j ^ 2).toNNReal

instance {n : ℕ} (μ s : Fin n → ℝ) : IsProbabilityMeasure (gpi μ s) := by unfold gpi; infer_instance

/-- The expected emission product along the latent path from `x`. -/
noncomputable def Qh (h : ℕ → ℝ → ℝ) {n : ℕ} (μ s : Fin n → ℝ) (v : Fin n → ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, ∏ j, ENNReal.ofReal (h (v j) (lpath n x ξ j)) ∂(gpi μ s)

section Qh

variable {h : ℕ → ℝ → ℝ} (hhm : ∀ z, Measurable (h z))
include hhm

theorem measurable_prod_h {n : ℕ} (v : Fin n → ℕ) :
    Measurable fun q : ℝ × (Fin n → ℝ) => ∏ j, ENNReal.ofReal (h (v j) (lpath n q.1 q.2 j)) :=
  Finset.measurable_prod _ fun j _ => ENNReal.measurable_ofReal.comp
    ((hhm (v j)).comp ((measurable_pi_apply j).comp (measurable_lpath n)))

theorem Qh_succ {n : ℕ} (μ s : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℕ) (x : ℝ) :
    Qh h μ s v x = ∫⁻ t, ENNReal.ofReal (h (v 0) (x * Real.exp t)) *
      Qh h (Fin.tail μ) (Fin.tail s) (Fin.tail v) (x * Real.exp t)
        ∂(gaussianReal (μ 0) (s 0 ^ 2).toNNReal) := by
  set g : Fin (n + 1) → Measure ℝ := fun j => gaussianReal (μ j) (s j ^ 2).toNNReal
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp := measurePreserving_piFinSuccAbove g 0
  simp only [Fin.succAbove_zero] at hmp
  have hfirst : Measurable fun t : ℝ => x * Real.exp t := measurable_const.mul Real.measurable_exp
  set G : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal (h (v 0) (x * Real.exp p.1)) *
    ∏ j, ENNReal.ofReal (h (Fin.tail v j) (lpath n (x * Real.exp p.1) p.2 j)) with hGdef
  have hG : Measurable G :=
    (ENNReal.measurable_ofReal.comp ((hhm (v 0)).comp (hfirst.comp measurable_fst))).mul
      ((measurable_prod_h hhm (Fin.tail v)).comp ((hfirst.comp measurable_fst).prodMk measurable_snd))
  have he : ∀ ξ, e ξ = (ξ 0, Fin.tail ξ) := fun ξ => by
    refine Prod.ext rfl ?_
    funext j
    simp [e, Fin.tail]
  have hF : (fun ξ : Fin (n + 1) → ℝ => ∏ j, ENNReal.ofReal (h (v j) (lpath (n + 1) x ξ j))) =
      G ∘ e := by
    funext ξ
    rw [Function.comp_apply, he, Fin.prod_univ_succ, lpath_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, hGdef]
    rfl
  unfold Qh gpi
  rw [hF]
  change ∫⁻ ξ, G (e ξ) ∂(Measure.pi g) = _
  rw [hmp.lintegral_comp hG, lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr fun t => ?_
  have hm : Measurable fun r : Fin n → ℝ =>
      ∏ j, ENNReal.ofReal (h (Fin.tail v j) (lpath n (x * Real.exp t) r j)) :=
    (measurable_prod_h hhm (Fin.tail v)).comp (measurable_const.prodMk measurable_id)
  simp only [hGdef]
  rw [lintegral_const_mul _ hm]
  rfl

variable (hh1 : ∀ z y, h z y ≤ 1)
include hh1

omit hhm in
theorem Qh_le_one {n : ℕ} (μ s : Fin n → ℝ) (v : Fin n → ℕ) (x : ℝ) : Qh h μ s v x ≤ 1 := by
  unfold Qh
  calc ∫⁻ ξ, ∏ j, ENNReal.ofReal (h (v j) (lpath n x ξ j)) ∂(gpi μ s) ≤ ∫⁻ _, 1 ∂(gpi μ s) :=
        lintegral_mono fun ξ => Finset.prod_le_one fun j _ => ENNReal.ofReal_le_one.2 (hh1 _ _)
    _ = 1 := by simp

variable (hδ : 0 < δ) (ha : 0 ≤ a) (hout : ∀ z y, 0 ≤ y → y ∉ ecell δ a z → h z y = 0)
include hδ ha hout

omit hh1 hδ ha in
/-- The first-step decomposition with a cover of the next expanded interval. -/
theorem Qh_le_sum {n : ℕ} (μ s : Fin (n + 1) → ℝ) {x : ℝ} (hx : 0 ≤ x) (v : Fin (n + 1) → ℕ)
    {ι : Type*} (F : Finset ι) (S : ι → Set ℝ) (c : ι → ℝ≥0∞) (hS : ∀ i, MeasurableSet (S i))
    (hcov : ecell δ a (v 0) ⊆ ⋃ i ∈ F, S i)
    (hc : ∀ i ∈ F, ∀ y ∈ S i, 0 ≤ y → ENNReal.ofReal (h (v 0) y) *
      Qh h (Fin.tail μ) (Fin.tail s) (Fin.tail v) y ≤ c i) :
    Qh h μ s v x ≤ ∑ i ∈ F, stepP (μ 0) (s 0) x (S i) * c i := by
  rw [Qh_succ hhm]
  have hfirst : Measurable fun t : ℝ => x * Real.exp t := measurable_const.mul Real.measurable_exp
  have hstep : ∀ t : ℝ, ENNReal.ofReal (h (v 0) (x * Real.exp t)) *
      Qh h (Fin.tail μ) (Fin.tail s) (Fin.tail v) (x * Real.exp t) ≤
        ∑ i ∈ F, (S i).indicator (fun _ => c i) (x * Real.exp t) := fun t => by
    have hy : 0 ≤ x * Real.exp t := mul_nonneg hx (Real.exp_pos t).le
    by_cases hin : x * Real.exp t ∈ ecell δ a (v 0)
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (hcov hin)
      calc _ ≤ c i := hc i hi _ hyi hy
        _ = (S i).indicator (fun _ => c i) (x * Real.exp t) := (indicator_of_mem hyi (fun _ => c i)).symm
        _ ≤ _ := Finset.single_le_sum (f := fun i => (S i).indicator (fun _ => c i)
              (x * Real.exp t)) (fun _ _ => by simp) hi
    · rw [hout _ _ hy hin, ENNReal.ofReal_zero, zero_mul]; exact bot_le
  calc _ ≤ ∫⁻ t, ∑ i ∈ F, (S i).indicator (fun _ => c i) (x * Real.exp t)
        ∂(gaussianReal (μ 0) (s 0 ^ 2).toNNReal) := lintegral_mono hstep
    _ = ∑ i ∈ F, ∫⁻ t, (S i).indicator (fun _ => c i) (x * Real.exp t)
        ∂(gaussianReal (μ 0) (s 0 ^ 2).toNNReal) :=
        lintegral_finsetSum _ fun i _ => (measurable_const.indicator (hS i)).comp hfirst
    _ = ∑ i ∈ F, stepP (μ 0) (s 0) x (S i) * c i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h2 : ∫⁻ t, (S i).indicator (fun _ => c i) (x * Real.exp t)
            ∂(gaussianReal (μ 0) (s 0 ^ 2).toNNReal) =
            ∫⁻ t, {t : ℝ | x * Real.exp t ∈ S i}.indicator (fun _ => c i) t
              ∂(gaussianReal (μ 0) (s 0 ^ 2).toNNReal) :=
          lintegral_congr fun t => by
            by_cases hm : x * Real.exp t ∈ S i
            · rw [indicator_of_mem hm,
                indicator_of_mem (show t ∈ {t : ℝ | x * Real.exp t ∈ S i} from hm)]
            · rw [indicator_of_notMem hm,
                indicator_of_notMem (show t ∉ {t : ℝ | x * Real.exp t ∈ S i} from hm)]
        have hm : MeasurableSet {t : ℝ | x * Real.exp t ∈ S i} := hfirst (hS i)
        rw [h2, lintegral_indicator_const hm, mul_comm]
        rfl

variable {M : ℕ → ℕ → ℕ → ℝ} (hM : ∀ ℓ z d, d < 2 ^ ℓ → 0 < M ℓ z d)
  (hhM : ∀ ℓ z d, d < 2 ^ ℓ → ∀ y ∈ esub δ a ℓ z d, h z y ≤ M ℓ z d)
include hM hhM

omit hh1 in
/-- The `T` step of (5). -/
theorem Qh_le_T {n : ℕ} (μ s : Fin (n + 1) → ℝ) (hs : ∀ j, 0 < s j) (ℓ z : ℕ)
    (v : Fin (n + 1) → ℕ) (c : ℕ) (Un : ℕ → ℝ) (hUn : ∀ d < 2 ^ ℓ, 0 ≤ Un d)
    (hnext : ∀ d < 2 ^ ℓ, ∀ y ∈ esub δ a ℓ (v 0) d,
      Qh h (Fin.tail μ) (Fin.tail s) (Fin.tail v) y ≤ ENNReal.ofReal (Un d))
    {x : ℝ} (hx : x ∈ esub δ a ℓ z c) :
    Qh h μ s v x ≤ ENNReal.ofReal (∑ d ∈ Finset.range (2 ^ ℓ),
      Wesub δ a (μ 0) (s 0) ℓ z c (v 0) d * M ℓ (v 0) d * Un d) := by
  refine (Qh_le_sum hhm hout μ s (esub_nonneg hδ ha hx) v (Finset.range (2 ^ ℓ))
    (esub δ a ℓ (v 0)) (fun d => ENNReal.ofReal (M ℓ (v 0) d * Un d)) (fun _ => measurableSet_Ico)
    (esub_cover hδ ha ℓ (v 0)) (fun d hd y hy _ => ?_)).trans ?_
  · have hd' := Finset.mem_range.1 hd
    rw [ENNReal.ofReal_mul (hM _ _ _ hd').le]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hhM _ _ _ hd' y hy)) (hnext d hd' y hy)
  · have hW := fun d => (Wesub_bounds hδ ha (μ := μ 0) (hs 0) ℓ z c (v 0) d).1.le
    rw [ENNReal.ofReal_sum_of_nonneg fun d hd =>
      mul_nonneg (mul_nonneg (hW d) (hM _ _ _ (Finset.mem_range.1 hd)).le)
        (hUn d (Finset.mem_range.1 hd))]
    refine Finset.sum_le_sum fun d hd => ?_
    rw [mul_assoc, ENNReal.ofReal_mul (hW d)]
    gcongr
    exact step_le_Wesub hδ ha (hs 0) _ _ hx

/-- The suffix bound: `Qh ≤ U` from every state of the subcell. -/
theorem Qh_le_Ue : ∀ (n ℓ : ℕ) (μ s : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (c : ℕ),
    (∀ j, 0 < s j) → c < 2 ^ ℓ →
    ∀ x ∈ esub δ a ℓ z c, Qh h μ s v x ≤ ENNReal.ofReal (Ue δ a M ℓ n μ s z v c)
  | 0, ℓ, μ, s, z, v, c, _, _ => fun x _ => by
    rw [Ue_nil, ENNReal.ofReal_one]; exact Qh_le_one hh1 μ s v x
  | n + 1, ℓ, μ, s, z, v, c, hs, hc => by
    have IH := Qh_le_Ue n
    have hb := Ue_bounds hδ ha hM n
    have hTq : ∀ ℓ' c', ∀ x ∈ esub δ a ℓ' z c', Qh h μ s v x ≤ ENNReal.ofReal
        (∑ d ∈ Finset.range (2 ^ ℓ'), Wesub δ a (μ 0) (s 0) ℓ' z c' (v 0) d * M ℓ' (v 0) d *
          Ue δ a M ℓ' n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d) := fun ℓ' c' x hx =>
      Qh_le_T hhm hδ ha hout hM hhM μ s hs ℓ' z v c' _
        (fun d hd => (hb ℓ' _ _ _ _ d (fun j => hs _) hd).1.le)
        (fun d hd y hy => IH ℓ' _ _ _ _ d (fun j => hs _) hd y hy) hx
    have h1 : ∀ x, Qh h μ s v x ≤ ENNReal.ofReal 1 := fun x => by
      rw [ENNReal.ofReal_one]; exact Qh_le_one hh1 μ s v x
    induction ℓ generalizing c with
    | zero =>
      rw [Ue_zero_succ]
      exact fun x hx => le_ofReal_min (h1 x) (hTq 0 c x hx)
    | succ ℓ ih =>
      have hc2 : c / 2 < 2 ^ ℓ := by rw [pow_succ] at hc; omega
      rw [Ue_succ_succ]
      exact fun x hx => le_ofReal_min (le_ofReal_min (h1 x) (hTq _ c x hx))
        (ih (c / 2) hc2 x (esub_nest hδ ha ℓ z c hx))

theorem Qh_le_Bn (ℓ : ℕ) {n : ℕ} {μ s : Fin n → ℝ} (hs : ∀ j, 0 < s j) {z₀ : ℕ} (v : Fin n → ℕ)
    {x : ℝ} (hx : x ∈ ecell δ a z₀) :
    Qh h μ s v x ≤ ENNReal.ofReal (Bn δ a M ℓ μ s z₀ v) := by
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (esub_cover hδ ha ℓ z₀ hx)
  exact (Qh_le_Ue hhm hh1 hδ ha hout hM hhM n ℓ μ s z₀ v c hs (Finset.mem_range.1 hc) x hxc).trans
    (ENNReal.ofReal_le_ofReal (Finset.le_sup' (Ue δ a M ℓ n μ s z₀ v) hc))

end Qh

end Novel.D18BoundedNoise
