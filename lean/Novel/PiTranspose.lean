import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Transposing a product of products

`Measure.pi` over `Fin m → Fin n → α` of a σ-finite `μ` is carried to the product over
`Fin n → Fin m → α` by transposition. Mathlib states the currying of products only for infinite
products of probability measures (`infinitePi_map_piCurry`). The finite σ-finite case follows from
`Measure.pi_eq_generateFrom` with boxes as generators. Used by claim 063 to integrate a panel
forecast time step by time step.
-/

open MeasureTheory Set

namespace Novel.PiTranspose

variable {α : Type*} [MeasurableSpace α]

/-- The transpose `v ↦ (j ↦ i ↦ v i j)`. -/
def transp {m n : ℕ} (v : Fin m → Fin n → α) : Fin n → Fin m → α := fun j i => v i j

theorem measurable_transp {m n : ℕ} : Measurable (transp (α := α) (m := m) (n := n)) :=
  measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun i =>
    (measurable_pi_apply j).comp (measurable_pi_apply i)

theorem map_transp (μ : Measure α) [SigmaFinite μ] (m n : ℕ) :
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => μ).map transp =
      Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin m => μ := by
  symm
  refine Measure.pi_eq_generateFrom (C := fun _ => pi univ '' pi univ fun _ => {s : Set α | MeasurableSet s})
    (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => μ.toFiniteSpanningSetsIn) ?_
  intro s hs
  choose t ht hst using hs
  have hmeas : ∀ j i, MeasurableSet (t j i) := fun j i => ht j i (mem_univ _)
  have hpre : transp ⁻¹' pi univ s = pi univ fun i : Fin m => pi univ fun j : Fin n => t j i := by
    ext v
    simp only [mem_preimage, mem_pi, mem_univ, true_implies, transp, ← hst]
    exact forall_comm
  rw [Measure.map_apply measurable_transp (MeasurableSet.univ_pi fun j => hst j ▸
    MeasurableSet.univ_pi fun i => hmeas j i), hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi, ← hst, Measure.pi_pi]
  exact Finset.prod_comm

theorem lintegral_transp (μ : Measure α) [SigmaFinite μ] {m n : ℕ}
    (F : (Fin n → Fin m → α) → ENNReal) (hF : Measurable F) :
    ∫⁻ v, F (transp v) ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => μ) =
      ∫⁻ w, F w ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin m => μ) := by
  rw [← map_transp μ m n, lintegral_map hF measurable_transp]

end Novel.PiTranspose

/-! ## Chains of normalized kernels -/

namespace Novel.PiTranspose

variable {β : Type*} [MeasurableSpace β]

/-- The chain `∏_j k_j(w_{j−1}, w_j)` started at `x₀`. -/
noncomputable def chainT {n : ℕ} (k : Fin n → β → β → ENNReal) (x₀ : β) (w : Fin n → β) : ENNReal :=
  ∏ j, k j ((Fin.cons x₀ w : Fin (n + 1) → β) j.castSucc) (w j)

omit [MeasurableSpace β] in
theorem chainT_succ {n : ℕ} (k : Fin (n + 1) → β → β → ENNReal) (x₀ : β) (w : Fin (n + 1) → β) :
    chainT k x₀ w = k 0 x₀ (w 0) * chainT (fun j => k j.succ) (w 0) (Fin.tail w) := by
  unfold chainT
  rw [Fin.prod_univ_succ]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have e1 : (Fin.cons x₀ w : Fin (n + 2) → β) j.succ.castSucc = w j.castSucc := by
    rw [← Fin.succ_castSucc, Fin.cons_succ]
  have e2 : (Fin.cons (w 0) (Fin.tail w) : Fin (n + 1) → β) j.castSucc = w j.castSucc := by
    rw [Fin.cons_self_tail]
  rw [e1, e2]
  rfl

theorem measurable_chainT {n : ℕ} {k : Fin n → β → β → ENNReal}
    (hk : ∀ j, Measurable (Function.uncurry (k j))) :
    Measurable fun q : β × (Fin n → β) => chainT k q.1 q.2 := by
  unfold chainT
  have hc : Measurable fun q : β × (Fin n → β) => (Fin.cons q.1 q.2 : Fin (n + 1) → β) := by
    refine measurable_pi_iff.2 fun l => ?_
    refine Fin.cases ?_ (fun i => ?_) l
    · simp only [Fin.cons_zero]; exact measurable_fst
    · simp only [Fin.cons_succ]; exact (measurable_pi_apply i).comp measurable_snd
  exact Finset.measurable_prod _ fun j _ => (hk j).comp (((measurable_pi_apply j.castSucc).comp hc).prodMk
    ((measurable_pi_apply j).comp measurable_snd))

/-- A chain of kernels each of mass one integrates to one. -/
theorem lintegral_chainT (μ : Measure β) [SigmaFinite μ] : ∀ {n : ℕ} (k : Fin n → β → β → ENNReal),
    (∀ j, Measurable (Function.uncurry (k j))) → (∀ j x, ∫⁻ y, k j x y ∂μ = 1) →
    ∀ x₀, ∫⁻ w, chainT k x₀ w ∂(Measure.pi fun _ : Fin n => μ) = 1
  | 0, k, _, _, x₀ => by simp [chainT]
  | n + 1, k, hk, hnorm, x₀ => by
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    have hF : Measurable fun p : β × (Fin n → β) =>
        k 0 x₀ p.1 * chainT (fun j => k j.succ) p.1 p.2 :=
      ((hk 0).comp (measurable_const.prodMk measurable_fst)).mul
        (measurable_chainT fun j => hk j.succ)
    have e : (fun w : Fin (n + 1) → β => chainT k x₀ w) =
        (fun p : β × (Fin n → β) => k 0 x₀ p.1 * chainT (fun j => k j.succ) p.1 p.2) ∘
          MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => β) 0 := by
      funext w; rw [chainT_succ]; rfl
    have h1 : ∫⁻ w, chainT k x₀ w ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
        ∫⁻ p, k 0 x₀ p.1 * chainT (fun j => k j.succ) p.1 p.2
          ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
      rw [e]; exact hmp.lintegral_comp hF
    rw [h1, lintegral_prod _ hF.aemeasurable]
    have hinner : ∀ y, ∫⁻ w, k 0 x₀ y * chainT (fun j => k j.succ) y w
        ∂(Measure.pi fun _ : Fin n => μ) = k 0 x₀ y := fun y => by
      rw [lintegral_const_mul (f := fun w => chainT (fun j => k j.succ) y w) _
        ((measurable_chainT fun j => hk j.succ).comp
        (measurable_const.prodMk measurable_id)),
        lintegral_chainT μ (fun j => k j.succ) (fun j => hk j.succ) (fun j => hnorm j.succ) y,
        mul_one]
    simp_rw [hinner]
    exact hnorm 0 x₀

end Novel.PiTranspose
