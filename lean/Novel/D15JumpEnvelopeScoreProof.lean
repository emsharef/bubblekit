import Novel.D15JumpEnvelopeMeasProof
import Novel.D15SwitchScoreProof

/-!
# Claim 060 (D15): proof of the score, parts 1–3 on claim 054's design

Proves `Standalone.D15JumpEnvelope.score` (`score_holds`).

Parts 1–2 are proved for any envelope `Ũ` (`score_gen`). `Ũ` must be measurable and finite,
dominate every jump law in `Θ_J`, and take `D_G`'s zero/trapped values off the positive stratum.
Claim 060 is the case `Ũ = U_J`; tighter envelopes, as in claim 061, can reuse it.
* **Domination.** `D = max(G₀, D_G, U_J)` dominates the catalogue nulls through `G₀`, every
  constant Gaussian through claim 055's supremum `D_G`, and every jump law in `Θ_J` through `U_J`
  (`gJ_le`).
* **The null set.** `G₀` and `U_J` are finite, so `D = ∞` forces `D_G = ∞`: a positive path with
  `Q_G = 0`. Its first two rates are then equal, which is claim 059's null pair set
  (`Novel.D15SwitchNull.pair_null`).
* **Part 2.** Each component has the score's reference moment, by AX-58's pointwise step (claim
  027's `ref_moment_of_dom`). The mixture (3) is integrated directly (`Measure.lintegral_bind`), so
  the component laws need not be shown normalized; in particular the jump law's normalization
  (AX-59) is never used. Disintegration, Markov and claim 054's `zval_valid` give the rest.
* **Part 3.** Monotonicity of `Edrift` in its denominator (`Edrift_anti`) and the envelope facts.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal NNReal

namespace Novel.D15JumpEnvelopeScore

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated
  Standalone.D13DriftNull Standalone.D13DriftRect Standalone.D15JumpEnvelope
  Novel.D13DriftScore Novel.D13DriftRectScore Novel.D15JumpEnvelopeBound

/-- Measurability of a density on `(A ⊕ B) × X` from its two parts. -/
theorem measurable_sum_prod {A B X : Type} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace X] {fA : A → X → ℝ≥0∞} {fB : B → X → ℝ≥0∞}
    (hA : Measurable fun q : A × X => fA q.1 q.2) (hB : Measurable fun q : B × X => fB q.1 q.2) :
    Measurable fun q : (A ⊕ B) × X => Sum.elim fA fB q.1 q.2 := by
  have e : (fun q : (A ⊕ B) × X => Sum.elim fA fB q.1 q.2) =
      (Sum.elim (fun q : A × X => fA q.1 q.2) (fun q : B × X => fB q.1 q.2)) ∘
        (MeasurableEquiv.sumProdDistrib A B X) := by
    funext q; rcases q with ⟨z, x⟩; cases z <;> rfl
  rw [e]
  exact (hA.sumElim hB).comp (MeasurableEquiv.sumProdDistrib A B X).measurable

/-- The zero-residual arrays are `μ_CEV^m`-null when `m ≥ 2`. -/
theorem DG_top_null {m : ℕ} {Δ : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) (hm : 2 ≤ m) (y0 : ℝ) :
    (Measure.pi fun _ : Fin m => muCEV) {v | DG Δ y0 (fun l => (v l : ℝ)) = ⊤} = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hil : ((0 : Fin (n + 1)) : ℕ) < ((⟨1, by omega⟩ : Fin (n + 1)) : ℕ) := by simp
  refine measure_mono_null (fun v hv => ?_) (Novel.D15SwitchNull.pair_null hΔ y0 hil)
  simp only [mem_ofPred_eq] at hv ⊢
  unfold DG at hv
  split_ifs at hv with hp hQ
  · exact absurd hv ENNReal.ofReal_ne_top
  · have hQ0 : QG Δ y0 (fun l => (v l : ℝ)) = 0 :=
      le_antisymm (not_lt.1 hQ) (Novel.D15Switch.QH_nonneg hΔ Finset.univ)
    exact ⟨hp.2, Novel.D15SwitchNull.pair_of_QH hΔ (H := Finset.univ) hQ0 (Finset.mem_univ _)
      (Finset.mem_univ _)⟩
  · exact absurd hv ENNReal.one_ne_top
  · exact absurd hv ENNReal.zero_ne_top


open Classical in
/-- **Claim 060's parts 1–2 for any envelope `Ũ`.** Suppose `Ũ` is measurable and finite,
dominates every jump law in `Θ_J`, and takes `D_G`'s zero/trapped values off the positive stratum.
Then the score with denominator `max(D, Ũ)` has:
* part 1's domination, measurability and finiteness;
* an infinite denominator only where `D_G = ∞`, a `μ_CEV^m`-null set;
* part 2's conclusions under the mixture premise (3);
* the ordering against claims 055 and 054;
* a positive value on the nonzero example;
* claim 055's score off the positive stratum.
Claim 060 is the case `Ũ = U_J` (`score_holds`). -/
theorem score_gen {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop)
    (h55 : Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb) (h56 : AX56 P' 𝓕 Wb Solves)
    (hW : Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P')
    (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ) (σmin : ℝ) (Λ : ℝ≥0∞) (hm2 : 2 ≤ m)
    (Ũ : ℝ → (Fin m → ℝ) → ℝ≥0∞)
    (hUm : Measurable fun x : ℝ × (Fin m → ℝ) => Ũ x.1 x.2) (hUfin : ∀ y0 y, Ũ y0 y < ⊤)
    (hUdom : ∀ θ, ThetaJ σmin Λ θ → ∀ y0 y,
      ENNReal.ofReal (gJ (fun l : Fin m => incr t (Fin.natAdd (k + 1) l)) θ y0 y) ≤ Ũ y0 y)
    (hUoff : ∀ y0 y, ¬ PosPath y0 y →
      Ũ y0 y = DG (fun l : Fin m => incr t (Fin.natAdd (k + 1) l)) y0 y) :
    let g := gC t pw κ
    let sel := selC hN.size t s pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    let μm : Measure (Fin m → NNR) := Measure.pi fun _ : Fin m => muCEV
    let gJN := fun (θ : ℝ × ℝ × ℝ × ℝ × ℝ) (u : Fin (k + 1) → NNR) (v : Fin m → NNR) =>
      gJ Δe θ (u (Fin.last k) : ℝ) fun l => (v l : ℝ)
    let D := fun (u : Fin (k + 1) → NNR) (v : Fin m → NNR) =>
      max (Dmax Δe pw g u v) (Ũ (u (Fin.last k) : ℝ) fun l => (v l : ℝ))
    let E := fun u v => Edrift (g (sel u) u v) (D u v)
    let ED := fun u v => Edrift (g (sel u) u v) (Dmax Δe pw g u v)
    (∀ θ, ThetaJ σmin Λ θ → ∀ u v, ENNReal.ofReal (gJN θ u v) ≤ D u v) ∧
    Measurable (Function.uncurry E) ∧ (∀ u v, E u v < ⊤) ∧
    (∀ u v, D u v = ⊤ → DG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) = ⊤) ∧
    (∀ u, μm {v | D u v = ⊤} = 0) ∧
    (∀ (ν : ProbabilityTheory.Kernel (Fin (k + 1) → NNR)
        ({ϑ : Fin c // pw ϑ ≤ 1} ⊕ (GPar ⊕ JPar σmin Λ))) [ProbabilityTheory.IsMarkovKernel ν]
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z =>
        μm.withDensity fun v => ENNReal.ofReal
          (Sum.elim (fun ϑ => g ϑ.1 u v)
            (Sum.elim (fun p : GPar => gGN Δe p.1.1 p.1.2 u v)
              (fun θ : JPar σmin Λ => gJN θ.1 u v)) z)) →
      P {ω | D (U ω) (V ω) = ⊤} = 0 ∧
      (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a) ∧
    (∀ u v, E u v ≤ ED u v ∧ ED u v ≤ Ecomp pw (fun ϑ => g ϑ u v) (sel u)) ∧
    (∀ u v, PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) →
      0 < QG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) → 0 < g (sel u) u v → 0 < E u v) ∧
    (∀ u v, ¬ PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) → E u v = ED u v) := by
  intro g sel Δe μm gJN D E ED
  have hC := Novel.D13CEVCatalogue.cited_of h55 h56 hW
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  have hΔ : ∀ j, 0 < Δe j := fun j => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  have hm : 0 < m := by omega
  -- Measurability.
  have hu_meas : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      ((p.1 (Fin.last k) : NNR) : ℝ) :=
    measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_fst)
  have hv_meas : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      fun l => ((p.2 l : NNR) : ℝ) :=
    measurable_pi_iff.2 fun l => measurable_subtype_coe.comp ((measurable_pi_apply l).comp
      measurable_snd)
  have hGnm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => Gnull pw g p.1 p.2 :=
    Measurable.iSup fun ϑ => Measurable.iSup fun _ => ENNReal.measurable_ofReal.comp (hSM.measg ϑ)
  have hDm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => Dmax Δe pw g p.1 p.2 :=
    hGnm.max ((Novel.D13DriftNull.measurable_DG (Δ := Δe)).comp (hu_meas.prodMk hv_meas))
  have hDJm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => D p.1 p.2 :=
    hDm.max (hUm.comp (hu_meas.prodMk hv_meas))
  have hGm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => g (sel p.1) p.1 p.2 :=
    Novel.SplitLikelihood.measurable_selected hSM.measg hSM.measSel
  have hEJm : Measurable (Function.uncurry E) :=
    Novel.SplitLikelihoodDominated.Edrift_meas.comp (hGm.prodMk hDJm)
  -- Facts about the denominator.
  have hUJ_lt : ∀ (u : Fin (k + 1) → NNR) (v : Fin m → NNR), Ũ (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) < ⊤ := fun u v =>
    hUfin _ _
  have hGD : ∀ u v, Gnull pw g u v ≤ D u v := fun u v =>
    (le_max_left _ _).trans (le_max_left _ _)
  have hfin : ∀ u v, E u v < ⊤ := fun u v => by
    show Edrift _ _ < ⊤
    unfold Edrift
    split_ifs with h1 h2
    · exact ENNReal.zero_lt_top
    · exfalso
      push Not at h1
      have hpos := Gnull_pos hN hC u v (lt_of_le_of_ne (hSM.nonneg _ _ _) (Ne.symm h1.1))
      exact (hpos.trans_le (hGD u v)).ne' h2
    · push Not at h1
      exact ENNReal.div_lt_top ENNReal.ofReal_ne_top h2
  have hdomJ : ∀ θ, ThetaJ σmin Λ θ → ∀ u v, ENNReal.ofReal (gJN θ u v) ≤ D u v :=
    fun θ hθ u v => (hUdom θ hθ _ _).trans (le_max_right _ _)
  have hdomG : ∀ (b κg : ℝ) u v, 0 < κg → ENNReal.ofReal (gGN Δe b κg u v) ≤ D u v :=
    fun b κg u v hκ => (le_max_of_le_right (by
      rw [← Novel.D13DriftNull.sup_eq hm hΔ]
      exact le_iSup_of_le b (le_iSup_of_le κg (le_iSup_of_le hκ le_rfl)))).trans (le_max_left _ _)
  have hdomC : ∀ u v (ϑ : Fin c), pw ϑ ≤ 1 → ENNReal.ofReal (g ϑ u v) ≤ D u v :=
    fun u v ϑ hϑ => (le_iSup₂_of_le ϑ hϑ le_rfl : ENNReal.ofReal (g ϑ u v) ≤ Gnull pw g u v).trans
      (hGD u v)
  have htop : ∀ (u : Fin (k + 1) → NNR) (v : Fin m → NNR), D u v = ⊤ → DG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) = ⊤ :=
    fun u v h => by
      rcases max_eq_top.1 h with h1 | h1
      · rcases max_eq_top.1 h1 with h2 | h2
        · exact absurd h2 (Gnull_lt_top hN hC u v).ne
        · exact h2
      · exact absurd h1 (hUJ_lt u v).ne
  have hnullset : ∀ u, μm {v | D u v = ⊤} = 0 := fun u =>
    measure_mono_null (fun v hv => htop u v hv)
      (DG_top_null hΔ hm2 ((u (Fin.last k) : NNR) : ℝ))
  -- The mixture components.
  let Z := {ϑ : Fin c // pw ϑ ≤ 1} ⊕ (GPar ⊕ JPar σmin Λ)
  let dens := fun (u : Fin (k + 1) → NNR) (z : Z) (v : Fin m → NNR) =>
    Sum.elim (fun ϑ : {ϑ : Fin c // pw ϑ ≤ 1} => g ϑ.1 u v)
      (Sum.elim (fun p : GPar => gGN Δe p.1.1 p.1.2 u v)
        (fun θ : JPar σmin Λ => gJN θ.1 u v)) z
  have hdA : Measurable fun q : {ϑ : Fin c // pw ϑ ≤ 1} × ((Fin (k + 1) → NNR) × (Fin m → NNR)) =>
      ENNReal.ofReal (g q.1.1 q.2.1 q.2.2) :=
    measurable_from_prod_countable_right fun ϑ => ENNReal.measurable_ofReal.comp (hSM.measg ϑ.1)
  have hdB : Measurable fun q : GPar × ((Fin (k + 1) → NNR) × (Fin m → NNR)) =>
      ENNReal.ofReal (gGN Δe q.1.1.1 q.1.1.2 q.2.1 q.2.2) :=
    ENNReal.measurable_ofReal.comp ((Novel.D15JumpEnvelopeMeas.measurable_gG2 (Δ := Δe)).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk
        ((hu_meas.comp measurable_snd).prodMk (hv_meas.comp measurable_snd))))
  have hdC : Measurable fun q : JPar σmin Λ × ((Fin (k + 1) → NNR) × (Fin m → NNR)) =>
      ENNReal.ofReal (gJN q.1.1 q.2.1 q.2.2) :=
    ENNReal.measurable_ofReal.comp ((Novel.D15JumpEnvelopeMeas.measurable_gJ hΔ).comp
      (measurable_fst.prodMk ((hu_meas.comp measurable_snd).prodMk (hv_meas.comp measurable_snd))))
  have hdZ : Measurable fun q : Z × ((Fin (k + 1) → NNR) × (Fin m → NNR)) =>
      ENNReal.ofReal (dens q.2.1 q.1 q.2.2) := by
    have hBC := measurable_sum_prod (fA := fun (p : GPar) (x : (Fin (k + 1) → NNR) × (Fin m → NNR)) =>
      ENNReal.ofReal (gGN Δe p.1.1 p.1.2 x.1 x.2))
      (fB := fun (θ : JPar σmin Λ) (x : (Fin (k + 1) → NNR) × (Fin m → NNR)) =>
        ENNReal.ofReal (gJN θ.1 x.1 x.2)) hdB hdC
    have h := measurable_sum_prod (fA := fun (ϑ : {ϑ : Fin c // pw ϑ ≤ 1})
      (x : (Fin (k + 1) → NNR) × (Fin m → NNR)) => ENNReal.ofReal (g ϑ.1 x.1 x.2))
      (fB := Sum.elim (fun (p : GPar) (x : (Fin (k + 1) → NNR) × (Fin m → NNR)) =>
        ENNReal.ofReal (gGN Δe p.1.1 p.1.2 x.1 x.2))
        (fun (θ : JPar σmin Λ) (x : (Fin (k + 1) → NNR) × (Fin m → NNR)) =>
          ENNReal.ofReal (gJN θ.1 x.1 x.2))) hdA hBC
    convert h using 1
    funext q; rcases q with ⟨z, x⟩; rcases z with ϑ | p | θ <;> rfl
  have hdens : Measurable (Function.uncurry fun (p : (Fin (k + 1) → NNR) × Z) (v : Fin m → NNR) =>
      ENNReal.ofReal (dens p.1 p.2 v)) := by
    show Measurable fun p : ((Fin (k + 1) → NNR) × Z) × (Fin m → NNR) =>
      ENNReal.ofReal (dens p.1.1 p.1.2 p.2)
    exact Measurable.comp (g := fun q : Z × ((Fin (k + 1) → NNR) × (Fin m → NNR)) =>
        ENNReal.ofReal (dens q.2.1 q.1 q.2.2))
      (f := fun p : ((Fin (k + 1) → NNR) × Z) × (Fin m → NNR) => (p.1.2, (p.1.1, p.2))) hdZ
      ((measurable_snd.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  let HK : Kernel ((Fin (k + 1) → NNR) × Z) (Fin m → NNR) :=
    Kernel.withDensity (Kernel.const _ μm) fun p v => ENNReal.ofReal (dens p.1 p.2 v)
  have hHK : ∀ p, HK p = μm.withDensity fun v => ENNReal.ofReal (dens p.1 p.2 v) := fun p => by
    simp only [HK]; rw [Kernel.withDensity_apply _ hdens, Kernel.const_apply]
  have hgr : ∀ u z, Measurable fun v => dens u z v := fun u z => by
    rcases z with ϑ | p | θ
    · exact (hSM.measg ϑ.1).comp ((measurable_const (a := u)).prodMk measurable_id)
    · exact (Novel.D15JumpEnvelopeMeas.measurable_gG2 (Δ := Δe)).comp
        (measurable_const.prodMk (measurable_const.prodMk (measurable_pi_iff.2 fun l =>
          measurable_subtype_coe.comp (measurable_pi_apply l))))
    · exact (Novel.D15JumpEnvelopeMeas.measurable_gJ hΔ).comp
        (measurable_const.prodMk (measurable_const.prodMk (measurable_pi_iff.2 fun l =>
          measurable_subtype_coe.comp (measurable_pi_apply l))))
  have hEu : ∀ u, Measurable fun v => E u v := fun u => (hEJm).of_uncurry_left
  -- Each component's reference moment.
  have hmom : ∀ u z, ∫⁻ v, E u v ∂(HK (u, z)) ≤ 1 := fun u z => by
    have h := Novel.D14VolPathsCev.ref_moment_of_dom (hgr u z) (hEu u) (fun v => hfin u v)
      (fun v => by
        rcases z with ϑ | p | θ
        · exact hdomC u v ϑ.1 ϑ.2
        · exact hdomG p.1.1 p.1.2 u v p.2
        · exact hdomJ θ.1 θ.2 u v)
      (hSM.norm _ u)
    rw [hHK]
    exact le_trans (le_of_eq (lintegral_congr fun v => (ENNReal.ofReal_toReal (hfin u v).ne).symm)) h
  -- Part 2.
  have hpart2 : ∀ (ν : Kernel (Fin (k + 1) → NNR) Z) [IsMarkovKernel ν] {Ω : Type}
      [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → Fin (k + 1) → NNR)
      (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z =>
        μm.withDensity fun v => ENNReal.ofReal (dens u z v)) →
      P {ω | D (U ω) (V ω) = ⊤} = 0 ∧
      (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a := by
    intro ν _ Ω _ P _ U V hU hV hmix
    have hmix' : ∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z => HK (u, z) := by
      filter_upwards [hmix] with u hu
      rw [hu]; congr 1; funext z; rw [hHK]
    have hHz : ∀ u, Measurable fun z => HK (u, z) := fun u => HK.measurable.comp measurable_prodMk_left
    have hc : ∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1 := by
      filter_upwards [hmix'] with u hu
      rw [hu, Measure.lintegral_bind (hHz u).aemeasurable (hEu u).aemeasurable]
      calc ∫⁻ z, ∫⁻ v, E u v ∂(HK (u, z)) ∂(ν u) ≤ ∫⁻ _, 1 ∂(ν u) := lintegral_mono fun z => hmom u z
        _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
    have hEK : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => E p.1 p.2 := hEJm
    have hu : ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 := by
      have : IsProbabilityMeasure (P.map U) :=
        (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
      refine (le_of_eq (Novel.D14SupportRobustness.disint (P := P) hU hV hEK)).trans ?_
      calc ∫⁻ u, ∫⁻ v, E u v ∂(condDistrib V U P u) ∂(P.map U) ≤ ∫⁻ _, 1 ∂(P.map U) :=
            lintegral_mono_ae hc
        _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
    have hT : Measurable fun ω => E (U ω) (V ω) :=
      Measurable.comp (g := fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => E p.1 p.2)
        (f := fun ω => (U ω, V ω)) hEK (hU.prodMk hV)
    have hnull : P {ω | D (U ω) (V ω) = ⊤} = 0 := by
      have hSm : MeasurableSet {p : (Fin (k + 1) → NNR) × (Fin m → NNR) | D p.1 p.2 = ⊤} :=
        measurableSet_eq_fun (hDJm) measurable_const
      have hF : Measurable ({p : (Fin (k + 1) → NNR) × (Fin m → NNR) | D p.1 p.2 = ⊤}.indicator
          (1 : (Fin (k + 1) → NNR) × (Fin m → NNR) → ℝ≥0∞)) := measurable_const.indicator hSm
      have hmeasω : MeasurableSet {ω | D (U ω) (V ω) = ⊤} := (hU.prodMk hV) hSm
      rw [← lintegral_indicator_one hmeasω]
      refine (Eq.trans (by rfl) (Novel.D14SupportRobustness.disint (P := P) hU hV hF)).trans ?_
      refine lintegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [hmix'] with u hu
      show ∫⁻ v, (Prod.mk u ⁻¹' {p | D p.1 p.2 = ⊤}).indicator 1 v ∂_ = 0
      have hSu : MeasurableSet (Prod.mk u ⁻¹' {p : (Fin (k + 1) → NNR) × (Fin m → NNR) |
          D p.1 p.2 = ⊤}) := measurable_prodMk_left hSm
      rw [lintegral_indicator_one hSu, hu, Measure.bind_apply hSu (hHz u).aemeasurable]
      refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun z => ?_)
      show HK (u, z) _ = 0
      rw [hHK]
      exact withDensity_absolutelyContinuous _ _ (hnullset u)
    refine ⟨hnull, hc, hu, fun α hα hα1 => ?_, fun a ha0 ha1 => Novel.D13CEVCatalogue.zval_valid
      hT (fun ω => hfin _ _) hu a ha0 ha1⟩
    have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hT.aemeasurable (ENNReal.ofReal (1 / α))
    have hsub : {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ⊆
        {ω | ENNReal.ofReal (1 / α) ≤ E (U ω) (V ω)} := fun ω (h : _ < E (U ω) (V ω)) =>
      show _ ≤ E (U ω) (V ω) from le_of_lt h
    have hle : ENNReal.ofReal (1 / α) * P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ 1 :=
      (mul_le_mul_right (measure_mono hsub) _).trans (hmk.trans hu)
    have hinv : (ENNReal.ofReal (1 / α))⁻¹ = ENNReal.ofReal α := by
      rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
    rw [← hinv, ENNReal.le_inv_iff_mul_le, mul_comm]
    exact hle
  -- Part 3.
  have hord : ∀ u v, E u v ≤ ED u v ∧ ED u v ≤ Ecomp pw (fun ϑ => g ϑ u v) (sel u) :=
    fun u v => ⟨Edrift_anti (le_max_left _ _),
      (Edrift_anti (le_max_left _ _)).trans_eq (Edrift_Gsup hN hC u v)⟩
  have hoff : ∀ (u : Fin (k + 1) → NNR) (v : Fin m → NNR), ¬ PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) → E u v = ED u v :=
    fun u v hp => by
      have hle : Ũ (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) ≤ Dmax Δe pw g u v :=
        (le_of_eq (hUoff _ _ hp)).trans (le_max_right (Gnull pw g u v) _)
      show Edrift _ (max _ _) = Edrift _ _
      rw [max_eq_left hle]
  refine ⟨hdomJ, hEJm, hfin, htop, hnullset,
    fun ν _ Ω _ P _ U V hU hV hmix => hpart2 ν P U V hU hV hmix, hord,
    fun u v hp hQ ha => ?_, hoff⟩
  · have hDG : DG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) < ⊤ := by
      unfold DG; simp only [hp, hQ, ↓reduceIte]; exact ENNReal.ofReal_lt_top
    have hD : D u v < ⊤ :=
      max_lt (max_lt (Gnull_lt_top hN hC u v) hDG) (hUJ_lt u v)
    have hD0 : D u v ≠ 0 := ((Gnull_pos hN hC u v ha).trans_le (hGD u v)).ne'
    show 0 < Edrift _ _
    rw [Edrift_pos_eq ha.ne' hD0]
    exact ENNReal.div_pos (ENNReal.ofReal_pos.2 ha).ne' hD.ne


theorem score_holds : Standalone.D15JumpEnvelope.score := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN σmin Λ hm2 hs g sel Δe μm gJN DJ EJ
    ED E
  have hΔ : ∀ j, 0 < Δe j := fun j => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  have hm : 0 < m := by omega
  have henv := envelope_holds m Δe σmin Λ hm hΔ hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := score_gen P' 𝓕 Wb Solves h55 h56 hW s R k m c t
    pw κ hN σmin Λ hm2 (fun y0 y => UJ σmin Λ Δe y0 y) (measurable_UJ σmin Λ Δe)
    (UJ_lt_top σmin Λ hΔ hs) (fun θ hθ y0 y => (gJ_le hs hm hΔ hθ y0 y).2)
    (fun y0 y hp => UJ_off hp)
  refine ⟨h1, h2, h3, h4, h5, h6, h7,
    fun Λ' hΛ u v => Edrift_anti (max_le_max le_rfl (UJ_mono hΔ hs le_rfl hΛ _ _)),
    fun σ' hs' hσ u v => Edrift_anti (max_le_max le_rfl (UJ_mono hΔ hs' hσ le_rfl _ _)),
    fun h0 u v => ?_, fun htop' u v hp => ?_, h8, h9⟩
  · by_cases hp : PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ))
    · have hle : UJ σmin Λ Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) ≤ Dmax Δe pw g u v :=
        (henv.2.2.2.2.2.2.1 h0 _ _).trans (le_max_right _ _)
      show Edrift _ (max _ _) = Edrift _ _
      rw [max_eq_left hle]
    · exact h9 u v hp
  · show Edrift _ (max _ _) = Edrift _ _
    rw [henv.2.2.2.2.2.2.2.1 htop' _ _ hp]

end Novel.D15JumpEnvelopeScore
