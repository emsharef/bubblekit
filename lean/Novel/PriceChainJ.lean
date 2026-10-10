import Novel.D13CEVCatalogueProof

/-!
# Price chains with increment-dependent kernels

Claim 054's `chainN f Δ x₀ v = ∏ⱼ f(Δⱼ, v_{j−1}, vⱼ)` lets a kernel depend on the step only through
`Δⱼ`. Claim 027 needs the drift and scale to vary with the increment, so `chainJ F x₀ v` takes one
kernel `F j` per step.

`chainJ_lint` generalizes claim 054's `chainN_norm`. Suppose every step from a positive state
integrates to `K_j` against `μ_CEV`, and kills the zero state (`F j x 0 = 0` for `x ≠ 0`). Then, from
a positive start, the chain integrates to `∏ K_j`. Normalization is `K_j = 1`. Claim 027 applies the
lemma to the square root of a product of two chains, where `K_j` is a one-step affinity.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Novel.PriceChainJ

open Standalone.CEVSupport Novel.D13CEVCatalogue

variable {m : ℕ}

/-- The chain with one kernel per step. -/
noncomputable def chainJ (F : Fin m → ℝ → ℝ → ℝ) (x₀ : ℝ) (v : Fin m → NNR) : ℝ :=
  ∏ j, F j (prevN x₀ v j) (v j)

theorem chainJ_meas {F : Fin m → ℝ → ℝ → ℝ} (hF : ∀ j, Measurable (Function.uncurry (F j))) :
    Measurable fun q : ℝ × (Fin m → NNR) => chainJ F q.1 q.2 :=
  Finset.measurable_prod _ fun j _ => (hF j).comp ((prevN_meas j).prodMk
    (measurable_subtype_coe.comp ((measurable_pi_apply j).comp measurable_snd)))

theorem chainJ_nonneg {F : Fin m → ℝ → ℝ → ℝ} (hF : ∀ j x y, 0 ≤ x → 0 ≤ y → 0 ≤ F j x y)
    {x₀ : ℝ} (hx₀ : 0 ≤ x₀) (v : Fin m → NNR) : 0 ≤ chainJ F x₀ v :=
  Finset.prod_nonneg fun j _ => hF j _ _ (Novel.D13CEVCatalogue.prevN_nonneg hx₀ v j) (v j).2

theorem chainJ_succ (F : Fin (m + 1) → ℝ → ℝ → ℝ) (x₀ : ℝ) (v : Fin (m + 1) → NNR) :
    chainJ F x₀ v = chainJ (fun j => F j.castSucc) x₀ (fun j => v j.castSucc) *
      F (Fin.last m) (lastOrN x₀ fun j => v j.castSucc) (v (Fin.last m)) := by
  unfold chainJ
  rw [Fin.prod_univ_castSucc]
  congr 1

/-- A zero coordinate after a positive start kills the chain. -/
theorem chainJ_first_zero {F : Fin m → ℝ → ℝ → ℝ} (hF : ∀ j x, x ≠ 0 → F j x 0 = 0) {x₀ : ℝ}
    (hx₀ : x₀ ≠ 0) {v : Fin m → NNR} (hz : ∃ l, (v l : ℝ) = 0) : chainJ F x₀ v = 0 := by
  classical
  have hex : ∃ n', ∃ h : n' < m, (v ⟨n', h⟩ : ℝ) = 0 := by
    obtain ⟨l, hl⟩ := hz; exact ⟨l, l.2, hl⟩
  set n' := Nat.find hex
  obtain ⟨hn, hvn⟩ := Nat.find_spec hex
  refine Finset.prod_eq_zero (Finset.mem_univ ⟨n', hn⟩) ?_
  have hprev : prevN x₀ v ⟨n', hn⟩ ≠ 0 := by
    rcases Nat.eq_zero_or_pos n' with h0 | h0
    · rw [Novel.CEVSupport.prevN_zero x₀ v ⟨n', hn⟩ h0]; exact hx₀
    · rw [Novel.CEVSupport.prevN_succ x₀ v ⟨n', hn⟩ h0.ne']
      intro h
      exact Nat.find_min hex (show n' - 1 < n' by omega) ⟨by omega, h⟩
  show F ⟨n', hn⟩ (prevN x₀ v ⟨n', hn⟩) (v ⟨n', hn⟩) = 0
  rw [hvn]; exact hF _ _ hprev

/-- From a zero start, the chain is `1` on the all-zero array and `0` otherwise. -/
theorem chainJ_zero_start {F : Fin m → ℝ → ℝ → ℝ} (hf0 : ∀ j, F j 0 0 = 1)
    (hf1 : ∀ j y, y ≠ 0 → F j 0 y = 0) (v : Fin m → NNR) :
    chainJ F 0 v = if ∀ l, (v l : ℝ) = 0 then 1 else 0 := by
  classical
  split_ifs with hz
  · refine Finset.prod_eq_one fun j _ => ?_
    have hp : prevN 0 v j = 0 := by
      unfold prevN; split_ifs
      · rfl
      · exact hz _
    rw [hp, hz j]; exact hf0 _
  · push Not at hz
    have hex : ∃ n', ∃ h : n' < m, (v ⟨n', h⟩ : ℝ) ≠ 0 := by
      obtain ⟨l, hl⟩ := hz; exact ⟨l, l.2, hl⟩
    set n' := Nat.find hex
    obtain ⟨hn, hvn⟩ := Nat.find_spec hex
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨n', hn⟩) ?_
    have hprev : prevN 0 v ⟨n', hn⟩ = 0 := by
      rcases Nat.eq_zero_or_pos n' with h0 | h0
      · exact Novel.CEVSupport.prevN_zero 0 v ⟨n', hn⟩ h0
      · rw [Novel.CEVSupport.prevN_succ 0 v ⟨n', hn⟩ h0.ne']
        by_contra h
        exact Nat.find_min hex (show n' - 1 < n' by omega) ⟨by omega, h⟩
    show F ⟨n', hn⟩ (prevN 0 v ⟨n', hn⟩) (v ⟨n', hn⟩) = 0
    rw [hprev]; exact hf1 _ _ hvn

/-- From a positive start, the chain integrates to the product of the one-step integrals. -/
theorem chainJ_lint : ∀ (m : ℕ) (F : Fin m → ℝ → ℝ → ℝ) (K : Fin m → ℝ),
    (∀ j, Measurable (Function.uncurry (F j))) → (∀ j x y, 0 ≤ x → 0 ≤ y → 0 ≤ F j x y) →
    (∀ j x, x ≠ 0 → F j x 0 = 0) → (∀ j, 0 ≤ K j) →
    (∀ j x, 0 < x → ∫⁻ y, ENNReal.ofReal (F j x (y : ℝ)) ∂muCEV = ENNReal.ofReal (K j)) →
    ∀ x₀ : ℝ, 0 < x₀ →
      ∫⁻ y, ENNReal.ofReal (chainJ F x₀ y) ∂(Measure.pi fun _ : Fin m => muCEV) =
        ENNReal.ofReal (∏ j, K j)
  | 0, F, K, _, _, _, _, _, x₀, _ => by
    simp [chainJ]
  | m + 1, F, K, hm, hp, hz, hK, hn, x₀, hx₀ => by
    have ih := chainJ_lint m (fun j => F j.castSucc) (fun j => K j.castSucc) (fun j => hm _)
      (fun j => hp _) (fun j => hz _) (fun j => hK _) (fun j => hn _) x₀ hx₀
    have e := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => muCEV) (Fin.last m)
    set G : NNR × (Fin m → NNR) → ℝ≥0∞ := fun q =>
      ENNReal.ofReal (chainJ (fun j => F j.castSucc) x₀ q.2) *
        ENNReal.ofReal (F (Fin.last m) (lastOrN x₀ q.2) q.1) with hGdef
    have hc := chainJ_meas (F := fun j => F j.castSucc) (fun j => hm _)
    have h1 : Measurable fun q : NNR × (Fin m → NNR) =>
        chainJ (fun j => F j.castSucc) x₀ q.2 := hc.comp (measurable_const.prodMk measurable_snd)
    have h2 : Measurable fun q : NNR × (Fin m → NNR) =>
        F (Fin.last m) (lastOrN x₀ q.2) (q.1 : ℝ) :=
      (hm (Fin.last m)).comp ((lastOrN_meas.comp (measurable_const.prodMk measurable_snd)).prodMk
        (measurable_subtype_coe.comp measurable_fst))
    have hG : Measurable G :=
      (ENNReal.measurable_ofReal.comp h1).mul (ENNReal.measurable_ofReal.comp h2)
    have hFG : ∀ v, ENNReal.ofReal (chainJ F x₀ v) =
        G (MeasurableEquiv.piFinSuccAbove (fun _ => NNR) (Fin.last m) v) := fun v => by
      rw [chainJ_succ, ENNReal.ofReal_mul (chainJ_nonneg (fun j => hp _) hx₀.le _)]
      show _ = G ((v (Fin.last m)), fun j => v ((Fin.last m).succAbove j))
      simp only [Fin.succAbove_last, hGdef]
    simp_rw [hFG]
    rw [e.lintegral_comp hG, lintegral_prod_symm' G hG]
    have hinner : ∀ w : Fin m → NNR, ∫⁻ y, G (y, w) ∂muCEV =
        ENNReal.ofReal (chainJ (fun j => F j.castSucc) x₀ w) * ENNReal.ofReal (K (Fin.last m)) :=
      fun w => by
        simp only [hGdef]
        have h3 : Measurable fun y : NNR =>
            ENNReal.ofReal (F (Fin.last m) (lastOrN x₀ w) (y : ℝ)) :=
          ENNReal.measurable_ofReal.comp ((hm (Fin.last m)).comp
            (measurable_const.prodMk measurable_subtype_coe))
        rw [lintegral_const_mul _ h3]
        rcases (lastOrN_nonneg hx₀.le w).lt_or_eq with hl | hl
        · rw [hn _ _ hl]
        · -- The last earlier price is zero, so an earlier coordinate kills the chain.
          have hm0 : m ≠ 0 := by
            intro h; unfold lastOrN at hl; simp only [h, dite_true] at hl; exact hx₀.ne' hl.symm
          have hz' : ∃ l, (w l : ℝ) = 0 := by
            refine ⟨⟨m - 1, by omega⟩, ?_⟩
            unfold lastOrN at hl; simp only [hm0, dite_false] at hl; exact hl.symm
          rw [chainJ_first_zero (fun j => hz _) hx₀.ne' hz', ENNReal.ofReal_zero, zero_mul,
            zero_mul]
    simp_rw [hinner]
    have h1' : Measurable fun w : Fin m → NNR =>
        ENNReal.ofReal (chainJ (fun j => F j.castSucc) x₀ w) :=
      ENNReal.measurable_ofReal.comp (hc.comp (measurable_const.prodMk measurable_id))
    rw [lintegral_mul_const _ h1', ih, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => hK _),
      Fin.prod_univ_castSucc]

end Novel.PriceChainJ
