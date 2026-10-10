import Standalone.D13DriftRect
import Novel.D13DriftRectProfileProof
import Novel.D13DriftScoreProof

/-!
# Claim 057 (D13): proof of the score and parts 1–4 on claim 054's design

Proves `Standalone.D13DriftRect.score` (`score_holds`).

* **The denominator.** `D_{B,C} = max(G₀, D_{G,B,C})` is finite: `G₀` is a finite maximum, and
  `D_{G,B,C}` is part 1's closed form. Hence (2) is `0` exactly when `Ĝ = 0`, and positive and finite
  otherwise (claim 054's support gives `G₀ > 0`).
* **Part 2.** AX-58 (`ax58_holds`) with the null family made of the catalogue nulls and every
  `(b, κ)` in the rectangle, which part 1's supremum dominates (`sup_eq`). The Gaussian
  normalization is claim 055's `gGN_norm`.
* **Part 3.**
  - `Edrift(Ĝ, ·)` is antitone, and the Gaussian denominators are nested suprema:
    `D_{G,B,C} ≤ D_{G,B} ≤ D_G`. `Edrift(Ĝ, G₀) = E` (`Edrift_Gsup`), which gives (7).
  - Larger rectangles have larger suprema.
  - For scale intervals increasing to `(0, ∞)`, the rectangle suprema increase to `D_{G,B}`, and
    `Ĝ/·` is continuous from the left along them (`ENNReal.continuous_inv`).
* **Absorption.** It is as in claim 055: training absorption makes every density one, and evaluation
  absorption from a positive endpoint makes the Gaussian term zero.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D13DriftRectScore

open Standalone.D13DriftNull Standalone.D13DriftRect Standalone.CEVSupport
  Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated Standalone.D3CatalogueCalibration
  Novel.D13DriftScore

/-- `Edrift(a, ·)` is antitone. -/
theorem Edrift_anti {a : ℝ} {d d' : ℝ≥0∞} (h : d ≤ d') : Edrift a d' ≤ Edrift a d := by
  by_cases ha : a = 0
  · rw [ha, Edrift_zero]; exact bot_le
  by_cases hd' : d' = ⊤
  · rw [hd', Edrift_top]; exact bot_le
  by_cases hd0 : d = 0
  · have : Edrift a d = ⊤ := by unfold Edrift; simp [ha, hd0]
    rw [this]; exact le_top
  have hdt : d ≠ ⊤ := ne_top_of_le_ne_top hd' h
  have hd0' : d' ≠ 0 := fun h0 => hd0 (le_antisymm (h0 ▸ h) bot_le)
  rw [Edrift_eq ha hd0 hdt, Edrift_eq ha hd0' hd']
  exact ENNReal.div_le_div_left h _

theorem Edrift_pos_eq {a : ℝ} (ha : a ≠ 0) {d : ℝ≥0∞} (hd : d ≠ 0) :
    Edrift a d = ENNReal.ofReal a / d := by
  by_cases ht : d = ⊤
  · rw [ht, Edrift_top, ENNReal.div_top]
  · exact Edrift_eq ha hd ht

section Name

variable {s R : ℝ} {k m c : ℕ} {t : Fin (k + 1 + m + 1) → ℝ≥0} {pw κ : Fin c → ℝ}

/-- At `D = G₀`, the score is claim 054's. -/
theorem Edrift_Gsup (hN : NameC s R t pw κ) (hC : Novel.D13CEVCatalogue.Cited)
    (u : Fin (k + 1) → NNR) (v : Fin m → NNR) :
    Edrift (gC t pw κ (selC hN.size t s pw κ u) u v) (Gnull pw (gC t pw κ) u v) =
      Ecomp pw (fun ϑ => gC t pw κ ϑ u v) (selC hN.size t s pw κ u) := by
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  have hsc := Novel.CEVSupport.score pw (fun ϑ => gC t pw κ ϑ u v) (selC hN.size t s pw κ u)
    (fun ϑ => hSM.nonneg _ _ _) hN.hasNull (Novel.D13CEVCatalogue.support hN hC u v)
  rcases (hSM.nonneg (selC hN.size t s pw κ u) u v).lt_or_eq with ha | ha
  · obtain ⟨G0, hG0, hle, ⟨ϑs, hϑs, hGs⟩, hE⟩ := hsc.2.2.1 ha
    have hS : Gnull pw (gC t pw κ) u v = ENNReal.ofReal G0 :=
      le_antisymm (iSup₂_le fun ϑ hϑ => ENNReal.ofReal_le_ofReal (hle ϑ hϑ))
        (le_iSup₂_of_le ϑs hϑs (by rw [hGs]))
    rw [hS, hE, Edrift_eq ha.ne' (ENNReal.ofReal_pos.2 hG0).ne' ENNReal.ofReal_ne_top,
      ENNReal.ofReal_div_of_pos hG0]
  · rw [hsc.2.1 ha.symm, ← ha, Edrift_zero]

theorem Gnull_lt_top (hN : NameC s R t pw κ) (hC : Novel.D13CEVCatalogue.Cited)
    (u : Fin (k + 1) → NNR) (v : Fin m → NNR) : Gnull pw (gC t pw κ) u v < ⊤ := by
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  refine lt_of_le_of_lt (iSup₂_le fun ϑ _ => ENNReal.ofReal_le_ofReal
    (Finset.single_le_sum (f := fun ϑ => gC t pw κ ϑ u v) (fun ϑ _ => hSM.nonneg _ _ _)
      (Finset.mem_univ ϑ))) ENNReal.ofReal_lt_top

theorem Gnull_pos (hN : NameC s R t pw κ) (hC : Novel.D13CEVCatalogue.Cited)
    (u : Fin (k + 1) → NNR) (v : Fin m → NNR) (h : 0 < gC t pw κ (selC hN.size t s pw κ u) u v) :
    0 < Gnull pw (gC t pw κ) u v := by
  obtain ⟨ϑ, hϑ, hpos⟩ := Novel.D13CEVCatalogue.support hN hC u v h
  exact (ENNReal.ofReal_pos.2 hpos).trans_le (le_iSup₂_of_le ϑ hϑ le_rfl)

theorem DGR_lt_top {n : ℕ} (Δ : Fin n → ℝ) (blo bhi slo shi y0 : ℝ) (y : Fin n → ℝ) :
    DGR Δ blo bhi slo shi y0 y < ⊤ := by
  unfold DGR; split_ifs
  · exact ENNReal.ofReal_lt_top
  · exact ENNReal.one_lt_top
  · exact ENNReal.zero_lt_top

end Name

theorem score_holds : Standalone.D13DriftRect.score := by
  refine ⟨?_, Novel.D14SupportRobustness.general_holds.2⟩
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN blo bhi slo shi hb hs hss g sel Δe
    G0 E
  have hC := Novel.D13CEVCatalogue.cited_of h55 h56 hW
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  have hm : 0 < m := hN.evals
  have hΔ : ∀ j, 0 < Δe j := fun j => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  -- The rectangle supremum, for any rectangle.
  have hrect : ∀ {bl bh sl sh : ℝ}, bl ≤ bh → 0 < sl → sl ≤ sh →
      ∀ (u : Fin (k + 1) → NNR) (v : Fin m → NNR),
      DGRN Δe bl bh sl sh u v = ⨆ b ∈ Icc bl bh, ⨆ κg ∈ Icc sl sh, ENNReal.ofReal (gGN Δe b κg u v) :=
    fun hb' hs' hss' u v => (Novel.D13DriftRect.sup_eq hm hΔ hb' hs' hss' _ _).symm
  have hrectB : ∀ {bl bh sl sh : ℝ}, bl ≤ bh → 0 < sl → sl ≤ sh →
      ∀ (u : Fin (k + 1) → NNR) (v : Fin m → NNR),
      DGRN Δe bl bh sl sh u v ≤ DGB Δe bl bh u v := fun hb' hs' hss' u v => by
    rw [hrect hb' hs' hss']
    exact iSup₂_le fun b hb'' => iSup₂_le fun κg hκ =>
      le_iSup₂_of_le b hb'' (le_iSup₂_of_le κg (show κg ∈ Ioi 0 from hs'.trans_le hκ.1) le_rfl)
  have hBG : ∀ u v, DGB Δe blo bhi u v ≤ DG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) :=
    fun u v => by
      rw [← Novel.D13DriftNull.sup_eq hm hΔ]
      exact iSup₂_le fun b _ => iSup₂_le fun κg hκ =>
        le_iSup_of_le b (le_iSup_of_le κg (le_iSup_of_le hκ le_rfl))
  have hDfin : ∀ u v, max (G0 u v) (DGRN Δe blo bhi slo shi u v) < ⊤ := fun u v =>
    max_lt (Novel.D13DriftRectScore.Gnull_lt_top hN hC u v) (DGR_lt_top _ _ _ _ _ _ _)
  have hDpos : ∀ u v, 0 < g (sel u) u v → 0 < max (G0 u v) (DGRN Δe blo bhi slo shi u v) :=
    fun u v h => (Gnull_pos hN hC u v h).trans_le (le_max_left _ _)
  have hform : ∀ u v, E u v = if g (sel u) u v = 0 then 0 else
      ENNReal.ofReal (g (sel u) u v) / max (G0 u v) (DGRN Δe blo bhi slo shi u v) := fun u v => by
    split_ifs with ha
    · show Edrift _ _ = 0
      rw [ha, Edrift_zero]
    · exact Edrift_pos_eq ha (hDpos u v (lt_of_le_of_ne (hSM.nonneg _ _ _) (Ne.symm ha))).ne'
  -- Measurability.
  have hu_meas : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      ((p.1 (Fin.last k) : NNR) : ℝ) :=
    measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_fst)
  have hv_meas : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      fun l => ((p.2 l : NNR) : ℝ) :=
    measurable_pi_iff.2 fun l => measurable_subtype_coe.comp ((measurable_pi_apply l).comp
      measurable_snd)
  have hDm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      max (G0 p.1 p.2) (DGRN Δe blo bhi slo shi p.1 p.2) :=
    (Measurable.iSup fun ϑ => Measurable.iSup fun _ =>
      ENNReal.measurable_ofReal.comp (hSM.measg ϑ)).max
      ((Novel.D13DriftRect.measurable_DGR (Δ := Δe) blo bhi slo shi).comp
        (hu_meas.prodMk hv_meas))
  have hGm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => g (sel p.1) p.1 p.2 :=
    Novel.SplitLikelihood.measurable_selected hSM.measg hSM.measSel
  have hEm : Measurable (Function.uncurry E) :=
    Novel.SplitLikelihoodDominated.Edrift_meas.comp (hGm.prodMk hDm)
  have hfin : ∀ u v, E u v < ⊤ := fun u v => by
    rw [hform]
    split_ifs with ha
    · exact ENNReal.zero_lt_top
    · exact ENNReal.div_lt_top ENNReal.ofReal_ne_top
        (hDpos u v (lt_of_le_of_ne (hSM.nonneg _ _ _) (Ne.symm ha))).ne'
  -- Part 2, by AX-58.
  have hpart2 : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      ((∃ ϑ, pw ϑ ≤ 1 ∧ IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (g ϑ)) ∨
        ∃ b ∈ Icc blo bhi, ∃ κg ∈ Icc slo shi,
          IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (gGN Δe b κg)) →
      (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a := by
    intro Ω _ P _ U V hU hV hnull
    let gl : ({ϑ : Fin c // pw ϑ ≤ 1} ⊕ {p : ℝ × ℝ // p.1 ∈ Icc blo bhi ∧ p.2 ∈ Icc slo shi}) →
        (Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ :=
      Sum.elim (fun ϑ => g ϑ.1) (fun p => gGN Δe p.1.1 p.1.2)
    have hDM : DomModel U V (Measure.pi fun _ : Fin m => muCEV) (fun u v => g (sel u) u v) gl
        (fun u v => max (G0 u v) (DGRN Δe blo bhi slo shi u v)) := by
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
        · exact gGN_norm hΔ p.1.1 (hs.trans_le p.2.2.1) u
      · rintro (ϑ | p) u v
        · exact le_max_of_le_left (le_iSup₂_of_le ϑ.1 ϑ.2 le_rfl)
        · refine le_max_of_le_right ?_
          rw [hrect hb hs hss]
          exact le_iSup₂_of_le p.1.1 p.2.1 (le_iSup₂_of_le p.1.2 p.2.2 le_rfl)
    have hl : ∃ l, IsCondDensity P U V (Measure.pi fun _ : Fin m => muCEV) (gl l) := by
      rcases hnull with ⟨ϑ, hϑ, h⟩ | ⟨b, hb', κg, hκ, h⟩
      · exact ⟨Sum.inl ⟨ϑ, hϑ⟩, h⟩
      · exact ⟨Sum.inr ⟨(b, κg), hb', hκ⟩, h⟩
    obtain ⟨l, hlc⟩ := hl
    obtain ⟨h1, h2, h3⟩ := Novel.SplitLikelihoodDominated.ax58_holds P U V _ _ gl _ l hDM hlc
    exact ⟨h1, h2, h3, fun a ha0 ha1 => Novel.D13CEVCatalogue.zval_valid
      (hEm.comp (hU.prodMk hV)) (fun ω => hfin _ _) h2 a ha0 ha1⟩
  -- Part 3: ordering.
  have hord : ∀ u v, Edrift (g (sel u) u v) (Dmax Δe pw g u v) ≤
        Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe blo bhi u v)) ∧
      Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe blo bhi u v)) ≤ E u v ∧
      E u v ≤ Ecomp pw (fun ϑ => g ϑ u v) (sel u) := fun u v =>
    ⟨Edrift_anti (max_le_max le_rfl (hBG u v)),
      Edrift_anti (max_le_max le_rfl (hrectB hb hs hss u v)),
      (Edrift_anti (le_max_left _ _)).trans_eq (Edrift_Gsup hN hC u v)⟩
  have hnest : ∀ blo' bhi' slo' shi' : ℝ, blo' ≤ blo → bhi ≤ bhi' → 0 < slo' → slo' ≤ slo →
      shi ≤ shi' → ∀ u v,
      Edrift (g (sel u) u v) (max (G0 u v) (DGRN Δe blo' bhi' slo' shi' u v)) ≤ E u v :=
    fun blo' bhi' slo' shi' h1 h2 h3 h4 h5 u v => by
      refine Edrift_anti (max_le_max le_rfl ?_)
      rw [hrect hb hs hss, hrect (h1.trans (hb.trans h2)) h3 (h4.trans (hss.trans h5))]
      exact iSup₂_le fun b hb' => iSup₂_le fun κg hκ =>
        le_iSup₂_of_le b ⟨h1.trans hb'.1, hb'.2.trans h2⟩
          (le_iSup₂_of_le κg ⟨h4.trans hκ.1, hκ.2.trans h5⟩ le_rfl)
  -- Part 3: the limit to claim 056's score.
  have hlim : ∀ sl sh : ℕ → ℝ, Antitone sl → Monotone sh → (∀ i, 0 < sl i) →
      (∀ i, sl i ≤ sh i) → Tendsto sl atTop (𝓝 0) → Tendsto sh atTop atTop → ∀ u v,
      Antitone (fun i => Edrift (g (sel u) u v)
        (max (G0 u v) (DGRN Δe blo bhi (sl i) (sh i) u v))) ∧
      Tendsto (fun i => Edrift (g (sel u) u v)
        (max (G0 u v) (DGRN Δe blo bhi (sl i) (sh i) u v)))
        atTop (𝓝 (Edrift (g (sel u) u v) (max (G0 u v) (DGB Δe blo bhi u v)))) := by
    intro sl sh hsl hsh hsl0 hslh hsl_lim hsh_lim u v
    set D : ℕ → ℝ≥0∞ := fun i => max (G0 u v) (DGRN Δe blo bhi (sl i) (sh i) u v)
    have hmono : Monotone D := fun i j hij => max_le_max le_rfl (by
      rw [hrect hb (hsl0 i) (hslh i), hrect hb (hsl0 j) (hslh j)]
      exact iSup₂_le fun b hb' => iSup₂_le fun κg hκ =>
        le_iSup₂_of_le b hb' (le_iSup₂_of_le κg ⟨(hsl hij).trans hκ.1, hκ.2.trans (hsh hij)⟩
          le_rfl))
    have hsup : ⨆ i, D i = max (G0 u v) (DGB Δe blo bhi u v) := by
      apply le_antisymm
      · exact iSup_le fun i => max_le_max le_rfl (hrectB hb (hsl0 i) (hslh i) u v)
      · refine max_le (le_iSup_of_le 0 (le_max_left _ _)) ?_
        refine iSup₂_le fun b hb' => iSup₂_le fun κg hκ => ?_
        have hκ0 : 0 < κg := hκ
        obtain ⟨i, hi1, hi2⟩ := (((tendsto_order.1 hsl_lim).2 κg hκ0).and
          (tendsto_atTop.1 hsh_lim κg)).exists
        refine le_iSup_of_le i (le_max_of_le_right ?_)
        rw [hrect hb (hsl0 i) (hslh i)]
        exact le_iSup₂_of_le b hb' (le_iSup₂_of_le κg ⟨hi1.le, hi2⟩ le_rfl)
    refine ⟨fun i j hij => Edrift_anti (hmono hij), ?_⟩
    by_cases ha : g (sel u) u v = 0
    · simp only [ha, Edrift_zero]; exact tendsto_const_nhds
    have ha' : 0 < g (sel u) u v := lt_of_le_of_ne (hSM.nonneg _ _ _) (Ne.symm ha)
    have hG0 := Gnull_pos hN hC u v ha'
    have hD0 : ∀ i, D i ≠ 0 := fun i => (hG0.trans_le (le_max_left _ _)).ne'
    have hlimD : Tendsto D atTop (𝓝 (max (G0 u v) (DGB Δe blo bhi u v))) :=
      hsup ▸ tendsto_atTop_iSup hmono
    have := ENNReal.Tendsto.const_div hlimD (Or.inr (ENNReal.ofReal_ne_top
      (r := g (sel u) u v)))
    rw [Edrift_pos_eq ha (hG0.trans_le (le_max_left _ _)).ne']
    exact this.congr fun i => (Edrift_pos_eq ha (hD0 i)).symm
  -- Part 3: absorbed arrays.
  have htrain : ∀ u v, (u (Fin.last k) : ℝ) = 0 → (∀ l, (v l : ℝ) = 0) → E u v = 1 :=
    fun u v hu0 hv0 => by
      have hvz : v = fun _ => zero := funext fun l => Subtype.ext (hv0 l)
      have hg1 : ∀ ϑ, g ϑ u v = 1 := fun ϑ => by
        show chainN _ _ (u (Fin.last k) : ℝ) v = 1
        rw [hu0, hvz]; exact Novel.CEVSupport.chain_absorbed _ _ _
      have hDG : DGRN Δe blo bhi slo shi u v = 1 := by
        unfold DGRN DGR PosPath; simp [hu0, hv0]
      have hsup : G0 u v = 1 := by
        show (⨆ ϑ ∈ {ϑ | pw ϑ ≤ 1}, ENNReal.ofReal (g ϑ u v)) = 1
        simp only [hg1, ENNReal.ofReal_one]
        obtain ⟨ϑ0, h0⟩ := hN.hasNull
        exact le_antisymm (iSup₂_le fun _ _ => le_rfl) (le_iSup₂_of_le ϑ0 h0 le_rfl)
      show Edrift (g (sel u) u v) (max (G0 u v) (DGRN Δe blo bhi slo shi u v)) = 1
      rw [hsup, hDG, max_self, hg1, Edrift_eq one_ne_zero one_ne_zero ENNReal.one_ne_top,
        ENNReal.ofReal_one, ENNReal.div_self one_ne_zero ENNReal.one_ne_top]
  have hfirst : ∀ u v, 0 < (u (Fin.last k) : ℝ) → (∃ l, (v l : ℝ) = 0) →
      E u v = Ecomp pw (fun ϑ => g ϑ u v) (sel u) ∧ E u v ≤ 1 := fun u v hpos hz => by
    have hDG0 : DGRN Δe blo bhi slo shi u v = 0 := by
      have hnp : ¬ PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) := fun h => by
        obtain ⟨l, hl⟩ := hz; exact (h.2 l).ne' hl
      unfold DGRN DGR; simp only [hnp, ↓reduceIte, hpos.ne', false_and]
    have hE1 : E u v = Ecomp pw (fun ϑ => g ϑ u v) (sel u) := by
      show Edrift (g (sel u) u v) (max (G0 u v) (DGRN Δe blo bhi slo shi u v)) = _
      rw [hDG0, max_eq_left (show (0 : ℝ≥0∞) ≤ G0 u v from bot_le)]
      exact Edrift_Gsup hN hC u v
    exact ⟨hE1, hE1 ▸ Novel.D14SupportRobustness.Ecomp_absorbed hN hC u v (Or.inr hz)⟩
  exact ⟨hDfin, hform, hfin, hEm, fun u v ha => by
      rw [hform]
      simp only [ha.ne', ↓reduceIte]
      exact ENNReal.div_pos (ENNReal.ofReal_pos.2 ha).ne' (hDfin u v).ne,
    hpart2, hord, hnest, hlim, htrain, hfirst⟩

end Novel.D13DriftRectScore
