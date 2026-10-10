import Novel.D14RoundedModelComp
import Novel.D14VolPathsAvgProof

/-!
# Claim 032: parts 1–3 (`comparison`)

Claim 027's latent-mixture averaging (`averaging_holds`) is applied with:
* latent space `ℝ × 𝒵`;
* the actual component kernel `H(u, (x, z)) = walkM` with the component parameters;
* the reference kernel `G(u, (x, z)) = walkM` from the same `x` with the first minimizer of (1);
* the budget `ε = epsC`.

Averaging needs its two component hypotheses at *every* latent point, while the contract only
places `x` in the last cell almost surely. So off the cell the reference starts at the cell's left
end, where its moment still holds, and the budget there is `1`. Since `ν(u, ·)` puts no mass off the
cell, this changes neither the mixtures nor `ε̄` almost surely.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14RoundedModel

open Standalone.D14RoundedModel Standalone.D14FixedTick Standalone.D14Cell Standalone.D14VolPaths
  Standalone.D14Misspecification

variable {n : ℕ}

theorem measurable_muV (Δ : Fin n → ℝ) :
    Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => muV Δ p.1 p.2 := by
  unfold muV
  exact measurable_pi_iff.2 fun j =>
    (((measurable_pi_apply j).comp measurable_fst).sub
      ((((measurable_pi_apply j).comp measurable_snd).pow_const 2).div_const 2)).mul_const _

theorem measurable_sV (Δ : Fin n → ℝ) : Measurable fun σ : Fin n → ℝ => sV Δ σ := by
  unfold sV
  exact measurable_pi_iff.2 fun j => (measurable_pi_apply j).mul_const _

theorem measurable_muθ (Δ : Fin n → ℝ) : Measurable fun θ : ℝ × ℝ => muθ Δ θ := by
  unfold muθ
  exact measurable_pi_iff.2 fun j => (measurable_fst.sub ((measurable_snd.pow_const 2).div_const 2)).mul_const _

theorem measurable_sθ (Δ : Fin n → ℝ) : Measurable fun θ : ℝ × ℝ => sθ Δ θ := by
  unfold sθ
  exact measurable_pi_iff.2 fun j => measurable_snd.mul_const _

theorem measurable_epsC (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty) :
    Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ => epsC Δ Γ hΓ p.1 p.2.1 p.2.2 := by
  classical
  unfold epsC
  refine Measurable.ite (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd)) ?_
    measurable_const
  have hm := Finset.inf'_induction hΓ (fun θ : ℝ × ℝ =>
    fun p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ => εcomp Δ p.1 p.2.1 θ.1 θ.2) (p := Measurable)
    (fun f hf g hg => hf.inf hg) fun θ _ =>
      Measurable.comp (g := fun r : (Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ =>
        εcomp Δ r.1 r.2.1 r.2.2.1 r.2.2.2)
        (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ => (p.1, p.2.1, θ.1, θ.2))
        (Novel.D14VolPaths.component_holds.2.1 n Δ)
        (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk measurable_const))
  convert hm using 1
  funext p; simp [Finset.inf'_apply]

theorem εcomp_bounds {Δ b σ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (hσ : ∀ j, 0 < σ j) {bref κ : ℝ}
    (hκ : 0 < κ) : 0 ≤ εcomp Δ b σ bref κ ∧ εcomp Δ b σ bref κ ≤ 1 :=
  let h := Novel.D14VolPaths.component_holds.1 n Δ b σ bref κ hΔ hσ hκ
  ⟨h.2.2.1, h.2.2.2.1⟩

theorem epsC_bounds {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {Γ : Finset (ℝ × ℝ)} (hΓ : Γ.Nonempty)
    (hΓκ : ∀ θ ∈ Γ, 0 < θ.2) {b σ : Fin n → ℝ} (hσ : ∀ j, 0 < σ j) (x : ℝ) :
    0 ≤ epsC Δ Γ hΓ b σ x ∧ epsC Δ Γ hΓ b σ x ≤ 1 := by
  classical
  unfold epsC
  split_ifs
  · exact ⟨Finset.le_inf' _ _ fun θ hθ => (εcomp_bounds hΔ hσ (hΓκ θ hθ)).1,
      (Finset.inf'_le _ hΓ.choose_spec).trans (εcomp_bounds hΔ hσ (hΓκ _ hΓ.choose_spec)).2⟩
  · exact ⟨le_rfl, zero_le_one⟩


theorem muV_const (Δ : Fin n → ℝ) (θ : ℝ × ℝ) :
    muV Δ (fun _ => θ.1) (fun _ => θ.2) = muθ Δ θ := rfl

theorem sV_const (Δ : Fin n → ℝ) (θ : ℝ × ℝ) : sV Δ (fun _ => θ.2) = sθ Δ θ := rfl

/-- (6) for one component: (1) is a minimum over `Γ`, so claim 027's uniform envelope at the
member within the radii bounds it. -/
theorem epsC_env {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {Γ : Finset (ℝ × ℝ)} (hΓ : Γ.Nonempty)
    {b σ : Fin n → ℝ} (x : ℝ) {smin smax hvol Bphys : ℝ} (hsmin : 0 < smin)
    (h : ∃ θ ∈ Γ, (∀ j, σ j ∈ Icc smin smax) ∧ θ.2 ∈ Icc smin smax ∧
      (∀ j, |Real.log (σ j / θ.2)| ≤ hvol) ∧ ∀ j, |b j - θ.1| ≤ Bphys) :
    epsC Δ Γ hΓ b σ x ≤ Real.sqrt (1 - Real.exp (-(n * Real.log (Real.cosh hvol) +
      (∑ j, Δ j) * (Bphys / (2 * smin) + smax * Real.sinh hvol / 2) ^ 2))) := by
  classical
  obtain ⟨θ, hθ, hσI, hκI, hlog, hb⟩ := h
  unfold epsC
  split_ifs
  · exact (Finset.inf'_le _ hθ).trans (Novel.D14VolPaths.component_holds.2.2.2 n Δ b σ θ.1 θ.2
      smin smax hvol Bphys hΔ hsmin hσI hκI hlog hb)
  · exact Real.sqrt_nonneg _

theorem bind_real {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {m : Measure α}
    {f : α → Measure β} (hf : AEMeasurable f m) (hprob : ∀ a, IsProbabilityMeasure (f a))
    {A : Set β} (hA : MeasurableSet A) : (m.bind f).real A = ∫ a, (f a).real A ∂m := by
  rw [measureReal_def, Measure.bind_apply hA hf, ← integral_toReal (f := fun a => f a A)
    ((Measure.measurable_coe hA).comp_aemeasurable hf)
    (ae_of_all _ fun a => (prob_le_one (μ := f a)).trans_lt ENNReal.one_lt_top)]
  rfl

theorem comparison_holds : comparison := by
  intro Ω 𝒵 _ _ P _ k n δ Δ Γ hΓ ν _ b σ U V q Lv e hδ hΔ hΓκ hb hσm hσ hU hV hq0 hq1 he01 hcell
    hmix εbar hbud E
  classical
  have hl : Measurable fun up : (Fin (k + 1) → ℕ) × (ℝ × 𝒵) => up.1 (Fin.last k) :=
    (measurable_pi_apply _).comp measurable_fst
  have hx1 : Measurable fun up : (Fin (k + 1) → ℕ) × (ℝ × 𝒵) => up.2.1 :=
    measurable_fst.comp measurable_snd
  have hCm : MeasurableSet {up : (Fin (k + 1) → ℕ) × (ℝ × 𝒵) | up.2.1 ∈ mcell δ (up.1 (Fin.last k))} :=
    (measurableSet_le ((Novel.D14FixedTick.measurable_mlo δ).comp hl) hx1).inter
      (measurableSet_lt hx1 ((Novel.D14FixedTick.measurable_mhi δ).comp hl))
  let θs := fun up : (Fin (k + 1) → ℕ) × (ℝ × 𝒵) => θk Γ (ksel Δ Γ hΓ (b up) (σ up))
  have hθs : Measurable θs := (measurable_from_top (f := θk Γ)).comp
    (Measurable.comp (g := fun p : (Fin n → ℝ) × (Fin n → ℝ) => ksel Δ Γ hΓ p.1 p.2)
      (f := fun up => (b up, σ up)) (measurable_ksel Δ Γ hΓ) (hb.prodMk hσm))
  let xt := fun up : (Fin (k + 1) → ℕ) × (ℝ × 𝒵) =>
    if up.2.1 ∈ mcell δ (up.1 (Fin.last k)) then up.2.1 else mlo δ (up.1 (Fin.last k))
  have hxt : Measurable xt := Measurable.ite hCm hx1
    ((Novel.D14FixedTick.measurable_mlo δ).comp hl)
  have hxt_mem : ∀ up, xt up ∈ mcell δ (up.1 (Fin.last k)) := fun up => by
    simp only [xt]; split_ifs with h
    · exact h
    · exact ⟨le_rfl, Novel.D14FixedTick.mlo_lt_mhi hδ _⟩
  have hparH : Measurable fun up : (Fin (k + 1) → ℕ) × (ℝ × 𝒵) =>
      (muV Δ (b up) (σ up), sV Δ (σ up), up.2.1) :=
    ((measurable_muV Δ).comp (hb.prodMk hσm)).prodMk (((measurable_sV Δ).comp hσm).prodMk hx1)
  have hparG : Measurable fun up : (Fin (k + 1) → ℕ) × (ℝ × 𝒵) =>
      (muθ Δ (θs up), sθ Δ (θs up), xt up) :=
    ((measurable_muθ Δ).comp hθs).prodMk (((measurable_sθ Δ).comp hθs).prodMk hxt)
  let Hk := (Kw δ n).comap _ hparH
  let Gk := (Kw δ n).comap _ hparG
  have hHk : ∀ up, Hk up = walkM δ (muV Δ (b up) (σ up)) (sV Δ (σ up)) up.2.1 := fun up => by
    show Kw δ n _ = _; exact walk_eq δ _ _ _
  have hGk : ∀ up, Gk up = walkM δ (muθ Δ (θs up)) (sθ Δ (θs up)) (xt up) := fun up => by
    show Kw δ n _ = _; exact walk_eq δ _ _ _
  let ε' := fun up : (Fin (k + 1) → ℕ) × (ℝ × 𝒵) =>
    if up.2.1 ∈ mcell δ (up.1 (Fin.last k)) then epsC Δ Γ hΓ (b up) (σ up) up.2.1 else 1
  have hε' : Measurable ε' := Measurable.ite hCm
    (Measurable.comp (g := fun p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ => epsC Δ Γ hΓ p.1 p.2.1 p.2.2)
      (f := fun up : (Fin (k + 1) → ℕ) × (ℝ × 𝒵) => (b up, σ up, up.2.1))
      (measurable_epsC Δ Γ hΓ) (hb.prodMk (hσm.prodMk hx1))) measurable_const
  have hε'01 : ∀ up, 0 ≤ ε' up ∧ ε' up ≤ 1 := fun up => by
    simp only [ε']; split_ifs
    · exact epsC_bounds hΔ hΓ hΓκ (hσ up) _
    · exact ⟨zero_le_one, le_rfl⟩
  have hEfin : ∀ u v, E u v < ⊤ := fun u v =>
    ENNReal.div_lt_top ENNReal.ofReal_ne_top
      (Dm_bounds hδ hΔ hΓκ hΓ (Lv u v) (u (Fin.last k)) v).1.ne'
  let Er := fun u v => (E u v).toReal
  have hErm : Measurable (Function.uncurry Er) := measurable_of_countable _
  have hEm : Measurable (Function.uncurry E) := measurable_of_countable _
  have hofr : ∀ u v, ENNReal.ofReal (Er u v) = E u v := fun u v =>
    ENNReal.ofReal_toReal (hEfin u v).ne
  have hmom : ∀ u p, ∫⁻ v, ENNReal.ofReal (Er u v) ∂(Gk (u, p)) ≤ 1 := fun u p => by
    simp_rw [hofr, hGk]
    exact ref_moment hδ hΔ hΓκ hq1 Lv u (θk_mem Γ _) (hxt_mem (u, p))
  have hx0 : ∀ up : (Fin (k + 1) → ℕ) × (ℝ × 𝒵), up.2.1 ∈ mcell δ (up.1 (Fin.last k)) →
      0 ≤ up.2.1 := fun up h => (Novel.D14FixedTick.mlo_nonneg δ _).trans h.1
  have htv : ∀ u p (A : Set (Fin n → ℕ)), MeasurableSet A →
      |(Hk (u, p)).real A - (Gk (u, p)).real A| ≤ ε' (u, p) := fun u p A _ => by
    rw [hHk, hGk]
    simp only [ε', xt]
    split_ifs with hc
    · exact walk_tv hΔ hΓ hΓκ (hσ _) (hx0 (u, p) hc) A
    · exact Novel.RoundedCells.abs_sub_le_one _ _ A
  have hmix' : ∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun p => Hk (u, p) := by
    filter_upwards [hmix] with u hu
    rw [hu]; congr 1; funext p; rw [hHk]
  obtain ⟨h5c, h5u, -, h6, -⟩ := Novel.D14VolPathsAvg.averaging_holds.1 P U V ν Hk Gk Er ε' hU hV
    hErm (fun u v => ENNReal.toReal_nonneg) hε' hε'01 hmom htv hmix'
  -- `ε̄` agrees with the averaged budget almost surely.
  set εb' := fun u => ∫ p, ε' (u, p) ∂(ν u) with hεb'
  have hbar : ∀ᵐ u ∂(P.map U), εb' u = εbar u := by
    filter_upwards [hcell] with u hu
    exact integral_congr_ae (by filter_upwards [hu] with p hp; simp [ε', hp])
  have hεb'm : Measurable εb' := Novel.D14VolPathsAvg.epsbar_meas hε' hε'01
  have hεb'01 : ∀ u, 0 ≤ εb' u ∧ εb' u ≤ 1 := Novel.D14VolPathsAvg.epsbar_bounds hε' hε'01
  have hle : ∀ᵐ u ∂(P.map U), εb' u ≤ e u := by
    filter_upwards [hbar, hbud] with u h1 h2; rw [h1]; exact h2
  have hleP : ∀ᵐ ω ∂P, εb' (U ω) ≤ e (U ω) := ae_of_ae_map hU.aemeasurable hle
  have hev : ∀ (t : ℝ), 0 ≤ t → ∀ u, {v | t < Er u v} = {v | ENNReal.ofReal t < E u v} :=
    fun t ht u => by
      ext v
      simp only [mem_ofPred_eq, Er]
      exact (ENNReal.ofReal_lt_iff_lt_toReal ht (hEfin u v).ne).symm
  have hem : Measurable e := measurable_of_countable _
  have heint : Integrable (fun ω => e (U ω)) P :=
    Integrable.of_bound (C := 1) (hem.comp hU).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (he01 _).1]; exact (he01 _).2)
  have hεint : Integrable (fun ω => εb' (U ω)) P :=
    Integrable.of_bound (C := 1) (hεb'm.comp hU).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hεb'01 _).1]; exact (hεb'01 _).2)
  have hint_le : ∫ ω, εb' (U ω) ∂P ≤ ∫ ω, e (U ω) ∂P := integral_mono_ae hεint heint hleP
  -- (4), unconditional.
  have h4u : ∀ α : ℝ, 0 < α → P.real {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤
      min 1 (α + ∫ ω, e (U ω) ∂P) := fun α hα => by
    have h := h5u α hα
    have hs : {ω | 1 / α < Er (U ω) (V ω)} = {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} := by
      ext ω
      simp only [mem_ofPred_eq, Er]
      exact (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (hEfin _ _).ne).symm
    rw [hs] at h
    exact h.trans (min_le_min le_rfl (by linarith))
  have hepsint : ∀ u, Integrable (fun p => epsC Δ Γ hΓ (b (u, p)) (σ (u, p)) p.1) (ν u) :=
    fun u => Integrable.of_bound (C := 1) (Measurable.comp
        (g := fun r : (Fin n → ℝ) × (Fin n → ℝ) × ℝ => epsC Δ Γ hΓ r.1 r.2.1 r.2.2)
        (f := fun p : ℝ × 𝒵 => (b (u, p), σ (u, p), p.1)) (measurable_epsC Δ Γ hΓ)
        ((hb.comp measurable_prodMk_left).prodMk ((hσm.comp measurable_prodMk_left).prodMk
          measurable_fst))).aestronglyMeasurable
        (Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs, abs_of_nonneg (epsC_bounds hΔ hΓ hΓκ (hσ _) _).1]
          exact (epsC_bounds hΔ hΓ hΓκ (hσ _) _).2)
  have hsub : ∀ (t : ℝ≥0∞) (F : Ω → ℝ≥0∞), (∀ ω, F ω ≤ E (U ω) (V ω)) →
      {ω | t < F ω} ⊆ {ω | t < E (U ω) (V ω)} := fun t F hF ω (hω : t < F ω) =>
    lt_of_lt_of_le hω (hF ω)
  refine ⟨⟨θs, hθs, fun up => θk_mem Γ _, ?_⟩, fun α hα g hg => ?_,
    fun α hα F hF => (measureReal_mono (hsub _ F hF)).trans (h4u α hα),
    fun α es hes hα F hF => ?_, fun c hc => ?_, fun hz => ?_,
    fun smin smax hvol Bphys hsmin hrad => ?_⟩
  · -- Part 1.
    filter_upwards [hmix', hcell] with u hu hcu
    intro G
    have hfG : AEMeasurable (fun p => walkM δ (muθ Δ (θs (u, p))) (sθ Δ (θs (u, p))) p.1) (ν u) := by
      refine (Gk.measurable.comp (measurable_prodMk_left (x := u))).aemeasurable.congr ?_
      filter_upwards [hcu] with p hp
      show Gk (u, p) = _
      rw [hGk]; simp [xt, hp]
    have hfH : Measurable fun p => Hk (u, p) := Hk.measurable.comp (measurable_prodMk_left (x := u))
    have hwalk_prob : ∀ (μ s : Fin n → ℝ) (x : ℝ), IsProbabilityMeasure (walkM δ μ s x) := fun μ s x =>
      (Measure.isProbabilityMeasure_map_iff
        (Novel.D14FixedTick.measurable_mlabels' δ n x).aemeasurable).2 (by infer_instance)
    refine ⟨fun A => ?_, ?_⟩
    · have hA : MeasurableSet A := MeasurableSet.of_discrete
      show |(condDistrib V U P u).real A - ((ν u).bind fun p =>
        walkM δ (muθ Δ (θs (u, p))) (sθ Δ (θs (u, p))) p.1).real A| ≤ εbar u
      rw [hu, bind_real hfH.aemeasurable (fun p => by rw [hHk]; exact hwalk_prob _ _ _) hA,
        bind_real hfG (fun p => hwalk_prob _ _ _) hA]
      have hi1 : Integrable (fun p => (Hk (u, p)).real A) (ν u) :=
        Integrable.of_bound (C := 1) ((Measure.measurable_coe hA).comp hfH).ennreal_toReal.aestronglyMeasurable
          (Eventually.of_forall fun p => by
            rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
            rw [hHk]; exact Novel.RoundedCells.real_le_one _ _)
      have hi2 : Integrable (fun p => (walkM δ (muθ Δ (θs (u, p))) (sθ Δ (θs (u, p))) p.1).real A)
          (ν u) :=
        Integrable.of_bound (C := 1)
          ((Measure.measurable_coe hA).comp_aemeasurable hfG).ennreal_toReal.aestronglyMeasurable
          (Eventually.of_forall fun p => by
            rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
            exact Novel.RoundedCells.real_le_one _ _)
      rw [← integral_sub hi1 hi2]
      refine (abs_integral_le_integral_abs).trans (integral_mono_ae (hi1.sub hi2).abs (hepsint u) ?_)
      filter_upwards [hcu] with p hp
      rw [hHk]
      exact walk_tv hΔ hΓ hΓκ (hσ _) (hx0 (u, p) hp) A
    · show ∫⁻ v, E u v ∂((ν u).bind fun p => walkM δ (muθ Δ (θs (u, p))) (sθ Δ (θs (u, p))) p.1) ≤ 1
      rw [Measure.lintegral_bind (f := fun v => E u v) hfG
        (measurable_of_countable (fun v => E u v)).aemeasurable]
      calc ∫⁻ p, ∫⁻ v, E u v ∂(walkM δ (muθ Δ (θs (u, p))) (sθ Δ (θs (u, p))) p.1) ∂(ν u)
          ≤ ∫⁻ _, 1 ∂(ν u) := lintegral_mono_ae (by
            filter_upwards [hcu] with p hp
            exact ref_moment hδ hΔ hΓκ hq1 Lv u (θk_mem Γ _) hp)
        _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
  · -- (4), conditional.
    filter_upwards [h5c α hα, hle] with u hu hue
    rw [hev (1 / α) (by positivity) u] at hu
    exact (measure_mono fun v (hv : _ < g u v) => lt_of_lt_of_le hv (hg u v)).trans
      (hu.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  · -- The strict threshold for a constant budget.
    have h := h4u (α - es) (by linarith)
    have hie : ∫ ω, e (U ω) ∂P ≤ es := by
      calc ∫ ω, e (U ω) ∂P ≤ ∫ _ω, es ∂P := integral_mono heint (integrable_const _) fun ω => hes _
        _ = es := by simp
    exact (measureReal_mono (hsub _ F hF)).trans (h.trans ((min_le_right _ _).trans (by linarith)))
  · -- (5).
    set eb := fun u => if εb' u ≤ e u then e u else 1
    have hebm : Measurable eb := Measurable.ite (measurableSet_le hεb'm hem) hem measurable_const
    have heb : ∀ u, εb' u ≤ eb u := fun u => by
      simp only [eb]; split_ifs with h
      · exact h
      · exact (hεb'01 u).2
    have hebe : ∀ᵐ u ∂(P.map U), eb u = e u := by
      filter_upwards [hle] with u hu; simp [eb, hu]
    obtain ⟨hcc, hcu⟩ := h6 c eb hc hebm heb
    have hcu' : ∫⁻ ω, ENNReal.ofReal (min (E (U ω) (V ω)).toReal c / (1 + c * e (U ω))) ∂P ≤ 1 := by
      refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hcu
      filter_upwards [ae_of_ae_map hU.aemeasurable hebe] with ω hω
      rw [hω]
    refine ⟨?_, hcu', fun F _ hF => (lintegral_mono fun ω =>
      ENNReal.ofReal_le_ofReal (hF ω).2).trans hcu', fun α hα u v h =>
        Novel.D14RoundedStart.cap_cond hc (he01 u).1 hα h⟩
    filter_upwards [hcc, hebe] with u hu hue
    rw [hue] at hu
    exact hu
  · -- Part 3.
    have hzero : ∀ u p, ((0 < p.1 → ∃ θ ∈ Γ, b (u, p) = (fun _ => θ.1) ∧
        σ (u, p) = (fun _ => θ.2))) → epsC Δ Γ hΓ (b (u, p)) (σ (u, p)) p.1 = 0 := fun u p h => by
      by_cases hp : 0 < p.1
      · obtain ⟨θ, hθ, hbθ, hσθ⟩ := h hp
        refine le_antisymm ?_ (epsC_bounds hΔ hΓ hΓκ (hσ _) _).1
        unfold epsC
        rw [ite_eq_left hp]
        refine (Finset.inf'_le _ hθ).trans (le_of_eq ?_)
        rw [hbθ, hσθ]
        exact (Novel.D14VolPaths.component_holds.2.2.1 n Δ θ.1 θ.2 (hΓκ θ hθ)).2
      · unfold epsC; rw [ite_eq_right hp]
    have hc : ∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1 := by
      filter_upwards [hmix', hz, hcell] with u hu hzu hcu
      rw [hu, Measure.lintegral_bind (f := fun v => E u v)
        (μ := fun p => Hk (u, p))
        (Hk.measurable.comp (measurable_prodMk_left (x := u))).aemeasurable
        (measurable_of_countable (fun v => E u v)).aemeasurable]
      calc ∫⁻ p, ∫⁻ v, E u v ∂(Hk (u, p)) ∂(ν u) ≤ ∫⁻ _, 1 ∂(ν u) := lintegral_mono_ae (by
            filter_upwards [hzu, hcu] with p h1 hp
            rw [hHk]
            rcases (hx0 (u, p) hp).lt_or_eq with hpos | hpos
            · obtain ⟨θ, hθ, hbθ, hσθ⟩ := h1 hpos
              rw [hbθ, hσθ, muV_const, sV_const]
              exact ref_moment hδ hΔ hΓκ hq1 Lv u hθ hp
            · obtain ⟨θ0, hθ0⟩ := hΓ
              have e1 : walkM δ (muV Δ (b (u, p)) (σ (u, p))) (sV Δ (σ (u, p))) p.1 =
                  walkM δ (muθ Δ θ0) (sθ Δ θ0) p.1 := by
                show walkM δ _ _ (u, p).2.1 = walkM δ _ _ (u, p).2.1
                rw [← hpos, walk_zero, walk_zero]
              rw [e1]
              exact ref_moment hδ hΔ hΓκ hq1 Lv u hθ0 hp)
        _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
    refine ⟨?_, fun g hg => by filter_upwards [hc] with u hu using (lintegral_mono (hg u)).trans hu,
      fun F hF => (lintegral_mono hF).trans ?_⟩
    · filter_upwards [hz, hcell] with u hzu hcu
      exact integral_eq_zero_of_ae (by filter_upwards [hzu] with p h1 using hzero u p h1)
    · have : IsProbabilityMeasure (P.map U) :=
        (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
      refine (le_of_eq (Novel.D14SupportRobustness.disint (P := P) hU hV hEm)).trans ?_
      calc ∫⁻ u, ∫⁻ v, E u v ∂(condDistrib V U P u) ∂(P.map U) ≤ ∫⁻ _, 1 ∂(P.map U) :=
            lintegral_mono_ae hc
        _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
  · -- Part 3, (6), averaged.
    filter_upwards [hrad] with u hu
    calc εbar u ≤ ∫ _p, Real.sqrt (1 - Real.exp (-(n * Real.log (Real.cosh hvol) +
          (∑ j, Δ j) * (Bphys / (2 * smin) + smax * Real.sinh hvol / 2) ^ 2))) ∂(ν u) :=
          integral_mono_ae (hepsint u) (integrable_const _) (by
            filter_upwards [hu] with p hp
            by_cases hpos : 0 < p.1
            · exact epsC_env hΔ hΓ p.1 hsmin (hp hpos)
            · show epsC _ _ _ _ _ _ ≤ _
              unfold epsC; rw [ite_eq_right hpos]; exact Real.sqrt_nonneg _)
      _ = _ := by simp

end Novel.D14RoundedModel
