import Standalone.D14RoundedModel
import Novel.D14FixedTickProof
import Novel.D14VolPathsProof
import Novel.GaussianCell

/-!
# Claim 032: component laws as kernels, and the first-minimizer reference

* **Walk laws as a kernel.** `walkM δ μ s x` is the image of the standard Gaussian vector `r` under
  `r ↦ labels of x · exp(cumulative (s_j r_j + μ_j))` (`walk_eq`, from `gauss_affine`). So the walk
  laws form claim 028's kernel `Lk` in the parameters `(μ, s, x)`, which is measurable.
* **The first minimizer** of (1) over a fixed enumeration of `Γ` (`ksel`) is measurable in the
  component parameters, and attains the minimum (`epsC_eq`).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14RoundedModel

open Standalone.D14RoundedModel Standalone.D14FixedTick Standalone.D14Cell Standalone.D14VolPaths
  Novel.D14RoundedStart

variable {n : ℕ}

/-- The standard Gaussian vector law. -/
noncomputable def L01 (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1

instance (n : ℕ) : IsProbabilityMeasure (L01 n) := by unfold L01; infer_instance

/-- The labels as a function of the parameters `(μ, s, x)` and the standard Gaussian vector. -/
noncomputable def Fw (δ : ℝ) (n : ℕ) (q : ((Fin n → ℝ) × (Fin n → ℝ) × ℝ) × (Fin n → ℝ)) :
    Fin n → ℕ :=
  mlabels δ n q.1.2.2 fun j => q.1.2.1 j * q.2 j + q.1.1 j

theorem measurable_Fw (δ : ℝ) (n : ℕ) : Measurable (Fw δ n) :=
  (Novel.D14FixedTick.measurable_mlabels δ n).comp
    ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
      (measurable_pi_iff.2 fun j =>
        (((measurable_pi_apply j).comp (measurable_fst.comp (measurable_snd.comp measurable_fst))).mul
          ((measurable_pi_apply j).comp measurable_snd)).add
        ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))))

/-- The walk-law kernel in the parameters. -/
noncomputable def Kw (δ : ℝ) (n : ℕ) : Kernel ((Fin n → ℝ) × (Fin n → ℝ) × ℝ) (Fin n → ℕ) :=
  Lk (measurable_Fw δ n) (L01 n)

instance (δ : ℝ) (n : ℕ) : IsMarkovKernel (Kw δ n) := by unfold Kw; infer_instance

theorem walk_eq (δ : ℝ) (μ s : Fin n → ℝ) (x : ℝ) : Kw δ n (μ, s, x) = walkM δ μ s x := by
  rw [Kw, Lk_apply, walkM]
  have hpi : (Measure.pi fun j => gaussianReal (μ j) (s j ^ 2).toNNReal) =
      (L01 n).map fun r j => s j * r j + μ j := by
    unfold L01
    rw [Measure.pi_map_pi (f := fun j t => s j * t + μ j) fun j => (by fun_prop : Measurable
      fun t : ℝ => s j * t + μ j).aemeasurable]
    congr 1; funext j
    exact Novel.GaussianCell.gauss_affine (μ j) (s j)
  rw [hpi, Measure.map_map (Novel.D14FixedTick.measurable_mlabels' δ n x)
    (measurable_pi_iff.2 fun j => by fun_prop)]
  rfl

/-! ## The first minimizer -/

section Sel

variable (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ))

/-- The `k`-th catalogue member in a fixed enumeration. -/
noncomputable def θk (k : Fin Γ.card) : ℝ × ℝ := (Γ.equivFin.symm k).1

theorem θk_mem (k : Fin Γ.card) : θk Γ k ∈ Γ := (Γ.equivFin.symm k).2

theorem card_pos (hΓ : Γ.Nonempty) : 0 < Γ.card := Finset.card_pos.2 hΓ

theorem sel_nonempty (hΓ : Γ.Nonempty) (b σ : Fin n → ℝ) :
    (Finset.univ.filter fun k => ∀ k', εcomp Δ b σ (θk Γ k).1 (θk Γ k).2 ≤
      εcomp Δ b σ (θk Γ k').1 (θk Γ k').2).Nonempty := by
  have : Nonempty (Fin Γ.card) := ⟨⟨0, card_pos Γ hΓ⟩⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_min_image Finset.univ
    (fun k => εcomp Δ b σ (θk Γ k).1 (θk Γ k).2) Finset.univ_nonempty
  exact ⟨k, by simpa using hk⟩

/-- The first index minimizing the component budget. -/
noncomputable def ksel (hΓ : Γ.Nonempty) (b σ : Fin n → ℝ) : Fin Γ.card :=
  (Finset.univ.filter fun k => ∀ k', εcomp Δ b σ (θk Γ k).1 (θk Γ k).2 ≤
    εcomp Δ b σ (θk Γ k').1 (θk Γ k').2).min' (sel_nonempty Δ Γ hΓ b σ)

theorem ksel_min (hΓ : Γ.Nonempty) (b σ : Fin n → ℝ) (k' : Fin Γ.card) :
    εcomp Δ b σ (θk Γ (ksel Δ Γ hΓ b σ)).1 (θk Γ (ksel Δ Γ hΓ b σ)).2 ≤
      εcomp Δ b σ (θk Γ k').1 (θk Γ k').2 := by
  have := Finset.min'_mem _ (sel_nonempty Δ Γ hΓ b σ)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this k'

theorem ksel_iff (hΓ : Γ.Nonempty) (b σ : Fin n → ℝ) (k : Fin Γ.card) :
    ksel Δ Γ hΓ b σ = k ↔ (∀ k', εcomp Δ b σ (θk Γ k).1 (θk Γ k).2 ≤
      εcomp Δ b σ (θk Γ k').1 (θk Γ k').2) ∧ ∀ k', (∀ k'', εcomp Δ b σ (θk Γ k').1 (θk Γ k').2 ≤
        εcomp Δ b σ (θk Γ k'').1 (θk Γ k'').2) → k ≤ k' := by
  constructor
  · rintro rfl
    exact ⟨ksel_min Δ Γ hΓ b σ, fun k' hk' => Finset.min'_le _ _ (by simpa using hk')⟩
  · rintro ⟨h1, h2⟩
    exact le_antisymm (Finset.min'_le _ _ (by simpa using h1))
      (h2 _ (ksel_min Δ Γ hΓ b σ))

theorem epsC_eq (hΓ : Γ.Nonempty) (b σ : Fin n → ℝ) {x : ℝ} (hx : 0 < x) :
    epsC Δ Γ hΓ b σ x = εcomp Δ b σ (θk Γ (ksel Δ Γ hΓ b σ)).1 (θk Γ (ksel Δ Γ hΓ b σ)).2 := by
  classical
  unfold epsC
  rw [ite_eq_left hx]
  refine le_antisymm (Finset.inf'_le _ (θk_mem Γ _)) (Finset.le_inf' _ _ fun θ hθ => ?_)
  obtain ⟨k', hk'⟩ : ∃ k', θk Γ k' = θ := ⟨Γ.equivFin ⟨θ, hθ⟩, by simp [θk]⟩
  rw [← hk']
  exact ksel_min Δ Γ hΓ b σ k'

theorem measurable_ksel (hΓ : Γ.Nonempty) :
    Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => ksel Δ Γ hΓ p.1 p.2 := by
  have hε : ∀ k, Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      εcomp Δ p.1 p.2 (θk Γ k).1 (θk Γ k).2 := fun k =>
    Measurable.comp (g := fun p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ =>
        εcomp Δ p.1 p.2.1 p.2.2.1 p.2.2.2)
      (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, p.2, (θk Γ k).1, (θk Γ k).2))
      (Novel.D14VolPaths.component_holds.2.1 n Δ)
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  refine measurable_to_countable' fun k => ?_
  have e : (fun p : (Fin n → ℝ) × (Fin n → ℝ) => ksel Δ Γ hΓ p.1 p.2) ⁻¹' {k} =
      (⋂ k', {p | εcomp Δ p.1 p.2 (θk Γ k).1 (θk Γ k).2 ≤ εcomp Δ p.1 p.2 (θk Γ k').1 (θk Γ k').2}) ∩
        ⋂ k', ((⋂ k'', {p | εcomp Δ p.1 p.2 (θk Γ k').1 (θk Γ k').2 ≤
          εcomp Δ p.1 p.2 (θk Γ k'').1 (θk Γ k'').2})ᶜ ∪ {_p | k ≤ k'}) := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff,
      mem_ofPred_eq, ksel_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun k' => (em _).elim (fun h => Or.inr (h2 k' h)) Or.inl⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun k' hk' => (h2 k').resolve_left (not_not.2 hk')⟩
  rw [e]
  exact (MeasurableSet.iInter fun k' => measurableSet_le (hε k) (hε k')).inter
    (MeasurableSet.iInter fun k' => (MeasurableSet.iInter fun k'' =>
      measurableSet_le (hε k') (hε k'')).compl.union (MeasurableSet.const _))

end Sel

end Novel.D14RoundedModel
