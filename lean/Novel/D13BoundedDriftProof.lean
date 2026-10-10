import Standalone.D13BoundedDrift
import Novel.D13BoundedDriftProfileProof
import Novel.D13DriftRectProof

/-!
# Claim 056 (D13): proof

Proves `Standalone.D13BoundedDrift.statement` (`statement_holds`): part 1 is
`Novel/D13BoundedDriftProfileProof.lean` (`profile_holds`), and the score is `score_holds` here,
following claim 057's score proof (`Novel.D13DriftRectScore`).
* **The denominator.** `D_B = max(G₀, D_{G,B})` with `D_{G,B}` part 1's closed form, so it is
  measurable. It can be infinite (zero residual with `a_G ∈ B`), where the score is `0`. Otherwise
  the score is `Ĝ/D_B`, and `D_B ≥ G₀ > 0` when `Ĝ > 0` (claim 054's support).
* **Part 2.** AX-58 (`ax58_holds`). The null family is the catalogue nulls together with every
  `(b, κ)`, `b ∈ B`, `κ > 0`, which `D_{G,B}` dominates as a supremum. The Gaussian
  normalization is claim 055's `gGN_norm`.
* **Part 3.**
  - `Edrift(Ĝ, ·)` is antitone (claim 057), and the Gaussian suprema are nested,
    `D_{G,B} ≤ D_{G,B'} ≤ D_G`. That gives (7) and the interval ordering.
  - For intervals increasing to `ℝ`, the suprema increase to `D_G`, and `Ĝ/·` is continuous along
    them (`ENNReal.Tendsto.const_div`).
* **Absorption.** It is as in claims 055 and 057.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D13BoundedDrift

open Standalone.D13DriftNull Standalone.D13DriftRect Standalone.D13BoundedDrift Standalone.CEVSupport
  Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated Standalone.D3CatalogueCalibration
  Novel.D13DriftScore Novel.D13DriftRectScore

theorem score_holds : Standalone.D13BoundedDrift.score := by
  refine ⟨?_, Novel.D14SupportRobustness.general_holds.2⟩
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN blo bhi hb g sel Δe G0 D E
  have hC := Novel.D13CEVCatalogue.cited_of h55 h56 hW
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  have hm : 0 < m := hN.evals
  have hΔ : ∀ j, 0 < Δe j := fun j => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  have hcl : ∀ {bl bh : ℝ}, bl ≤ bh → ∀ (u : Fin (k + 1) → NNR) (v : Fin m → NNR),
      DGB Δe bl bh u v = DGBc Δe bl bh (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) :=
    fun hb' u v => sup_eq_B hm hΔ hb' _ _
  have hBG : ∀ bl bh u v, DGB Δe bl bh u v ≤ DG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) :=
    fun bl bh u v => by
      rw [← Novel.D13DriftNull.sup_eq hm hΔ]
      exact iSup₂_le fun b _ => iSup₂_le fun κg hκ =>
        le_iSup_of_le b (le_iSup_of_le κg (le_iSup_of_le hκ le_rfl))
  have hDpos : ∀ u v, 0 < g (sel u) u v → 0 < D u v :=
    fun u v h => (Gnull_pos hN hC u v h).trans_le (le_max_left _ _)
  have hform : ∀ u v, E u v = if g (sel u) u v = 0 ∨ D u v = ⊤ then 0 else
      ENNReal.ofReal (g (sel u) u v) / D u v := fun u v => by
    split_ifs with h
    · rcases h with ha | hd
      · show Edrift _ _ = 0; rw [ha, Edrift_zero]
      · show Edrift _ _ = 0; rw [hd, Edrift_top]
    · push Not at h
      exact Edrift_eq h.1 (hDpos u v (lt_of_le_of_ne (hSM.nonneg _ _ _) (Ne.symm h.1))).ne' h.2
  -- Measurability.
  have hu_meas : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      ((p.1 (Fin.last k) : NNR) : ℝ) :=
    measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_fst)
  have hv_meas : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      fun l => ((p.2 l : NNR) : ℝ) :=
    measurable_pi_iff.2 fun l => measurable_subtype_coe.comp ((measurable_pi_apply l).comp
      measurable_snd)
  have hDm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => D p.1 p.2 := by
    have : (fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => D p.1 p.2) = fun p =>
        max (G0 p.1 p.2) (DGBc Δe blo bhi (p.1 (Fin.last k) : ℝ) (fun l => (p.2 l : ℝ))) :=
      funext fun p => by show max _ _ = max _ _; rw [hcl hb]
    rw [this]
    exact (Measurable.iSup fun ϑ => Measurable.iSup fun _ =>
      ENNReal.measurable_ofReal.comp (hSM.measg ϑ)).max
      ((measurable_DGBc (Δ := Δe) blo bhi).comp (hu_meas.prodMk hv_meas))
  have hGm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => g (sel p.1) p.1 p.2 :=
    Novel.SplitLikelihood.measurable_selected hSM.measg hSM.measSel
  have hEm : Measurable (Function.uncurry E) :=
    Novel.SplitLikelihoodDominated.Edrift_meas.comp (hGm.prodMk hDm)
  have hfin : ∀ u v, E u v < ⊤ := fun u v => by
    rw [hform]
    split_ifs with h
    · exact ENNReal.zero_lt_top
    · push Not at h
      exact ENNReal.div_lt_top ENNReal.ofReal_ne_top
        (hDpos u v (lt_of_le_of_ne (hSM.nonneg _ _ _) (Ne.symm h.1))).ne'
  -- Part 2, by AX-58.
  have hpart2 : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      ((∃ ϑ, pw ϑ ≤ 1 ∧ IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (g ϑ)) ∨
        ∃ b ∈ Icc blo bhi, ∃ κg : ℝ, 0 < κg ∧
          IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (gGN Δe b κg)) →
      (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a := by
    intro Ω _ P _ U V hU hV hnull
    let gl : ({ϑ : Fin c // pw ϑ ≤ 1} ⊕ {p : ℝ × ℝ // p.1 ∈ Icc blo bhi ∧ 0 < p.2}) →
        (Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ :=
      Sum.elim (fun ϑ => g ϑ.1) (fun p => gGN Δe p.1.1 p.1.2)
    have hDM : DomModel U V (Measure.pi fun _ : Fin m => muCEV) (fun u v => g (sel u) u v) gl
        (fun u v => D u v) := by
      refine ⟨hU, hV, hSM.sfinite, hGm, fun u v => hSM.nonneg _ _ _, fun u => hSM.norm _ u,
        ?_, ?_, ?_, hDm, ?_⟩
      · rintro (ϑ | p)
        · exact hSM.measg ϑ.1
        · exact (Novel.D13DriftNull.measurable_gG (Δ := Δe) p.1.1 p.1.2).comp
            (hu_meas.prodMk hv_meas)
      · rintro (ϑ | p) u v
        · exact hSM.nonneg _ _ _
        · exact Novel.D13DriftNull.gG_nonneg _ _ _ _
      · rintro (ϑ | p) u
        · exact hSM.norm _ u
        · exact gGN_norm hΔ p.1.1 p.2.2 u
      · rintro (ϑ | p) u v
        · exact le_max_of_le_left (le_iSup₂_of_le ϑ.1 ϑ.2 le_rfl)
        · exact le_max_of_le_right (le_iSup₂_of_le p.1.1 p.2.1
            (le_iSup₂_of_le p.1.2 (show p.1.2 ∈ Ioi 0 from p.2.2) le_rfl))
    have hl : ∃ l, IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (gl l) := by
      rcases hnull with ⟨ϑ, hϑ, h⟩ | ⟨b, hb', κg, hκ, h⟩
      · exact ⟨Sum.inl ⟨ϑ, hϑ⟩, h⟩
      · exact ⟨Sum.inr ⟨(b, κg), hb', hκ⟩, h⟩
    obtain ⟨l, hlc⟩ := hl
    obtain ⟨h1, h2, h3⟩ := Novel.SplitLikelihoodDominated.ax58_holds P U V _ _ gl _ l hDM hlc
    exact ⟨h1, h2, h3, fun a ha0 ha1 => Novel.D13CEVCatalogue.zval_valid
      (hEm.comp (hU.prodMk hV)) (fun ω => hfin _ _) h2 a ha0 ha1⟩
  -- Part 3: ordering.
  have hord : ∀ u v, Edrift (g (sel u) u v) (Dmax Δe pw g u v) ≤ E u v ∧
      E u v ≤ Ecomp pw (fun ϑ => g ϑ u v) (sel u) := fun u v =>
    ⟨Edrift_anti (max_le_max le_rfl (hBG blo bhi u v)),
      (Edrift_anti (le_max_left _ _)).trans_eq (Edrift_Gsup hN hC u v)⟩
  have hsub : ∀ bl bh bl' bh' : ℝ, bl' ≤ bl → bh ≤ bh' →
      ∀ (u : Fin (k + 1) → NNR) (v : Fin m → NNR),
      DGB Δe bl bh u v ≤ DGB Δe bl' bh' u v := by
    intro bl bh bl' bh' h1 h2 u v
    unfold DGB
    refine iSup₂_le fun b hb' => ?_
    have hb'' : b ∈ Icc bl' bh' := ⟨h1.trans hb'.1, hb'.2.trans h2⟩
    exact le_iSup₂_of_le (f := fun b (_ : b ∈ Icc bl' bh') =>
      ⨆ κ ∈ Ioi (0 : ℝ), ENNReal.ofReal (gGN Δe b κ u v)) b hb'' le_rfl
  have hnest : ∀ blo' bhi' : ℝ, blo' ≤ blo → bhi ≤ bhi' → ∀ u v,
      Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe blo' bhi' u v)) ≤ E u v :=
    fun blo' bhi' h1 h2 u v => Edrift_anti (max_le_max le_rfl (hsub _ _ _ _ h1 h2 u v))
  -- Part 3: the limit to claim 055's score.
  have hlim : ∀ bl bh : ℕ → ℝ, Antitone bl → Monotone bh → (∀ i, bl i ≤ bh i) →
      Tendsto bl atTop atBot → Tendsto bh atTop atTop → ∀ u v,
      Antitone (fun i => Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe (bl i) (bh i) u v))) ∧
      Tendsto (fun i => Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe (bl i) (bh i) u v)))
        atTop (𝓝 (Edrift (g (sel u) u v) (Dmax Δe pw g u v))) := by
    intro bl bh hbl hbh hblh hbl_lim hbh_lim u v
    set Di : ℕ → ℝ≥0∞ := fun i => max (G0 u v) (DGB Δe (bl i) (bh i) u v)
    have hmono : Monotone Di := fun i j hij => max_le_max le_rfl (hsub _ _ _ _ (hbl hij) (hbh hij) u v)
    have hsup : ⨆ i, Di i = Dmax Δe pw g u v := by
      apply le_antisymm
      · exact iSup_le fun i => max_le_max le_rfl (hBG _ _ u v)
      · refine max_le (le_iSup_of_le 0 (le_max_left _ _)) ?_
        rw [← Novel.D13DriftNull.sup_eq hm hΔ]
        refine iSup_le fun b => iSup_le fun κg => iSup_le fun hκ => ?_
        obtain ⟨i, hi1, hi2⟩ := ((tendsto_atBot.1 hbl_lim b).and (tendsto_atTop.1 hbh_lim b)).exists
        refine le_iSup_of_le i (le_max_of_le_right ?_)
        exact le_iSup₂_of_le b ⟨hi1, hi2⟩ (le_iSup₂_of_le κg (show κg ∈ Ioi 0 from hκ) le_rfl)
    refine ⟨fun i j hij => Edrift_anti (hmono hij), ?_⟩
    by_cases ha : g (sel u) u v = 0
    · simp only [ha, Edrift_zero]; exact tendsto_const_nhds
    have ha' : 0 < g (sel u) u v := lt_of_le_of_ne (hSM.nonneg _ _ _) (Ne.symm ha)
    have hG0 := Gnull_pos hN hC u v ha'
    have hD0 : ∀ i, Di i ≠ 0 := fun i => (hG0.trans_le (le_max_left _ _)).ne'
    have hlimD : Tendsto Di atTop (𝓝 (Dmax Δe pw g u v)) := hsup ▸ tendsto_atTop_iSup hmono
    have := ENNReal.Tendsto.const_div hlimD (Or.inr (ENNReal.ofReal_ne_top
      (r := g (sel u) u v)))
    have hDm0 : Dmax Δe pw g u v ≠ 0 :=
      (hG0.trans_le (le_max_left (Gnull pw g u v) _ : Gnull pw g u v ≤ Dmax Δe pw g u v)).ne'
    rw [Edrift_pos_eq ha hDm0]
    exact this.congr fun i => (Edrift_pos_eq ha (hD0 i)).symm
  -- Part 3: absorbed arrays.
  have htrain : ∀ u v, (u (Fin.last k) : ℝ) = 0 → (∀ l, (v l : ℝ) = 0) → E u v = 1 :=
    fun u v hu0 hv0 => by
      have hvz : v = fun _ => zero := funext fun l => Subtype.ext (hv0 l)
      have hg1 : ∀ ϑ, g ϑ u v = 1 := fun ϑ => by
        show chainN _ _ (u (Fin.last k) : ℝ) v = 1
        rw [hu0, hvz]; exact Novel.CEVSupport.chain_absorbed _ _ _
      have hDG : DGB Δe blo bhi u v = 1 := by
        rw [hcl hb]; unfold DGBc PosPath; simp [hu0, hv0]
      have hsup : G0 u v = 1 := by
        show (⨆ ϑ ∈ {ϑ | pw ϑ ≤ 1}, ENNReal.ofReal (g ϑ u v)) = 1
        simp only [hg1, ENNReal.ofReal_one]
        obtain ⟨ϑ0, h0⟩ := hN.hasNull
        exact le_antisymm (iSup₂_le fun _ _ => le_rfl) (le_iSup₂_of_le ϑ0 h0 le_rfl)
      show Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe blo bhi u v)) = 1
      rw [hsup, hDG, max_self, hg1, Edrift_eq one_ne_zero one_ne_zero ENNReal.one_ne_top,
        ENNReal.ofReal_one, ENNReal.div_self one_ne_zero ENNReal.one_ne_top]
  have hfirst : ∀ u v, 0 < (u (Fin.last k) : ℝ) → (∃ l, (v l : ℝ) = 0) →
      E u v = Ecomp pw (fun ϑ => g ϑ u v) (sel u) ∧ E u v ≤ 1 := fun u v hpos hz => by
    have hDG0 : DGB Δe blo bhi u v = 0 := by
      have hnp : ¬ PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) := fun h => by
        obtain ⟨l, hl⟩ := hz; exact (h.2 l).ne' hl
      rw [hcl hb]; unfold DGBc; simp only [hnp, ↓reduceIte, hpos.ne', false_and]
    have hE1 : E u v = Ecomp pw (fun ϑ => g ϑ u v) (sel u) := by
      show Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe blo bhi u v)) = _
      rw [hDG0, max_eq_left (show (0 : ℝ≥0∞) ≤ G0 u v from bot_le)]
      exact Edrift_Gsup hN hC u v
    exact ⟨hE1, hE1 ▸ Novel.D14SupportRobustness.Ecomp_absorbed hN hC u v (Or.inr hz)⟩
  exact ⟨fun u v => hcl hb u v, hform, hDpos, hfin, hEm, hpart2, hord, hnest, hlim, htrain, hfirst⟩

/-- Claim 056. -/
theorem statement_holds : Standalone.D13BoundedDrift.statement := ⟨profile_holds, score_holds⟩

end Novel.D13BoundedDrift
