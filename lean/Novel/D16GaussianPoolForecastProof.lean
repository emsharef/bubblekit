import Standalone.D16GaussianPool
import Novel.D13CEVCatalogueProof

/-!
# Claim 062: the shared-power forecast

Proves `Standalone.D16GaussianPool.forecast` (`forecast_holds`).
* **First maximizers** (`firstMax_spec`). `firstMax f` maximizes `f` and is below every maximizer.
* **Measurability.** The forecast is the sum over the finitely many candidates of the candidate's
  evaluation density on the measurable set where it is selected.
* **Normalization.** For a fixed training record the selected candidate is fixed. Its density is a
  product over names of claim 054's chains, each normalized by claim 054's `chainN_norm` (cited
  AX-55/AX-56 normalization), and a product density integrates to the product of the integrals
  (`lintegral_pi_prod`).
* **Positivity.** For `p > 1` the kernel on positive prices is AX-56's density, which is positive.
* **Separation.** On a positive training record every factor is positive. So the product's maximizers
  are the products of the name-wise maximizers, and the lexicographically first one is the vector
  of name-wise first maximizers (`Pi.toLex_monotone`). Over powers, it is the first maximizer of
  the separately maximized likelihoods.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D16GaussianPoolForecast

open Standalone.D16GaussianPool Standalone.CEVSupport Novel.D13CEVCatalogue

theorem lintegral_pi_prod {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    ∀ (m : ℕ) (f : Fin m → X → ℝ≥0∞), (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi fun _ : Fin m => μ) = ∏ i, ∫⁻ y, f i y ∂μ
  | 0, f, _ => by simp
  | m + 1, f, hf => by
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
    rw [← hmp.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have e : ∀ p : X × (Fin m → X), ∏ i, f i ((MeasurableEquiv.piFinSuccAbove (fun _ => X) 0).symm p i)
        = f 0 p.1 * ∏ i : Fin m, f i.succ (p.2 i) := fun p => by
      rw [Fin.prod_univ_succ]; simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp_rw [e]
    rw [lintegral_prod_mul (f := f 0) (g := fun w : Fin m → X => ∏ i : Fin m, f i.succ (w i))
      (hf 0).aemeasurable (Finset.measurable_prod _ fun i _ =>
        (hf i.succ).comp (measurable_pi_apply i)).aemeasurable, Fin.prod_univ_succ]
    congr 1
    exact lintegral_pi_prod μ m (fun i => f i.succ) fun i => hf _

/-! ## First maximizers -/

section FirstMax

variable {α : Type*} [Fintype α] [LinearOrder α] [Nonempty α] (f : α → ℝ)

theorem firstMax_max : ∀ b, f b ≤ f (firstMax f) := by
  unfold firstMax
  have := Finset.min'_mem (Finset.univ.filter fun a => ∀ b, f b ≤ f a) (by
    obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
    exact ⟨a, by simpa using ha⟩)
  simpa using this

theorem firstMax_le {a : α} (ha : ∀ b, f b ≤ f a) : firstMax f ≤ a :=
  Finset.min'_le _ _ (by simpa using ha)

theorem firstMax_eq {c : α} (hc : ∀ b, f b ≤ f c) (hmin : ∀ a, (∀ b, f b ≤ f a) → c ≤ a) :
    firstMax f = c :=
  le_antisymm (firstMax_le f hc) (hmin _ (firstMax_max f))

theorem firstMax_iff (c : α) :
    firstMax f = c ↔ (∀ b, f b ≤ f c) ∧ ∀ a, (∀ b, f b ≤ f a) → c ≤ a :=
  ⟨fun h => h ▸ ⟨firstMax_max f, fun _ ha => firstMax_le f ha⟩, fun h => firstMax_eq f h.1 h.2⟩

end FirstMax


/-! ## Chains -/

theorem chain_meas {n : ℕ} (p κ : ℝ) (Δ : Fin n → ℝ) :
    Measurable fun q : ℝ × (Fin n → NNR) => chainN (Kc p κ) Δ q.1 q.2 :=
  chainN_meas fun _ => Kc_meas _ _ _

theorem chain_nonneg {n : ℕ} {p κ : ℝ} (hp : 0 < p) (hκ : 0 < κ) {Δ : Fin n → ℝ}
    (hΔ : ∀ j, 0 < Δ j) {x : ℝ} (hx : 0 ≤ x) (y : Fin n → NNR) : 0 ≤ chainN (Kc p κ) Δ x y :=
  chainN_nonneg (fun j _ _ hx hy => Kc_nonneg hp hκ (hΔ j) hx hy) hx y

theorem chain_pos (hC : Cited) {n : ℕ} {p κ : ℝ} (hp : 1 < p) (hκ : 0 < κ) {Δ : Fin n → ℝ}
    (hΔ : ∀ j, 0 < Δ j) {x : ℝ} (hx : 0 < x) {y : Fin n → NNR} (hy : ∀ j, 0 < (y j : ℝ)) :
    0 < chainN (Kc p κ) Δ x y := by
  unfold chainN
  refine Finset.prod_pos fun j _ => ?_
  have hprev : 0 < prevN x y j := by
    unfold prevN; split_ifs
    · exact hx
    · exact hy _
  rw [Novel.CEVSupport.Kc_pos_pos hprev.ne' (hy j).ne', ite_eq_right hp.ne']
  exact hC.pos p κ (Δ j) (by linarith) hp.ne' hκ (hΔ j) _ _ hprev (hy j)

/-! ## The forecast -/

section Forecast

variable {m n k cp cs : ℕ} [NeZero cp] [NeZero cs] {Pw : Fin cp → ℝ} {Ksc : Fin m → Fin cs → ℝ}
  {ΔT : Fin (k + 1) → ℝ} {ΔE : Fin n → ℝ} {s : Fin m → ℝ}

/-- A fixed candidate's evaluation density. -/
noncomputable def qc (Pw : Fin cp → ℝ) (Ksc : Fin m → Fin cs → ℝ) (ΔE : Fin n → ℝ)
    (c : Cand cp m cs) (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR) : ℝ :=
  ∏ i, chainN (Kc (Pw (ofLex c).1) (Ksc i (ofLex (ofLex c).2 i))) ΔE (u i (Fin.last k) : ℝ) (v i)

theorem q_eq (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR) :
    qPool Pw Ksc ΔT ΔE s u v = qc Pw Ksc ΔE (selPool Pw Ksc ΔT s u) u v := rfl

omit [NeZero cp] [NeZero cs] in
theorem measurable_L (c : Cand cp m cs) :
    Measurable fun u : Fin m → Fin (k + 1) → NNR => LtrC Pw Ksc ΔT s c u :=
  Finset.measurable_prod _ fun i _ => Measurable.comp
    (g := fun q : ℝ × (Fin (k + 1) → NNR) => chainN (Kc (Pw (ofLex c).1) (Ksc i (ofLex (ofLex c).2 i)))
      ΔT q.1 q.2) (f := fun u : Fin m → Fin (k + 1) → NNR => (s i, u i))
    (chain_meas _ _ _) (measurable_const.prodMk (measurable_pi_apply i))

omit [NeZero cp] [NeZero cs] in
theorem measurable_qc (c : Cand cp m cs) :
    Measurable fun p : (Fin m → Fin (k + 1) → NNR) × (Fin m → Fin n → NNR) =>
      qc Pw Ksc ΔE c p.1 p.2 :=
  Finset.measurable_prod _ fun i _ => Measurable.comp
    (g := fun q : ℝ × (Fin n → NNR) => chainN (Kc (Pw (ofLex c).1) (Ksc i (ofLex (ofLex c).2 i)))
      ΔE q.1 q.2)
    (f := fun p : (Fin m → Fin (k + 1) → NNR) × (Fin m → Fin n → NNR) =>
      ((p.1 i (Fin.last k) : ℝ), p.2 i))
    (chain_meas _ _ _) ((measurable_subtype_coe.comp ((measurable_pi_apply _).comp
      ((measurable_pi_apply i).comp measurable_fst))).prodMk ((measurable_pi_apply i).comp measurable_snd))

theorem measurableSet_sel (c : Cand cp m cs) :
    MeasurableSet {u : Fin m → Fin (k + 1) → NNR | selPool Pw Ksc ΔT s u = c} := by
  classical
  have e : {u : Fin m → Fin (k + 1) → NNR | selPool Pw Ksc ΔT s u = c} =
      (⋂ b, {u | LtrC Pw Ksc ΔT s b u ≤ LtrC Pw Ksc ΔT s c u}) ∩
        ⋂ a, ({u | ∀ b, LtrC Pw Ksc ΔT s b u ≤ LtrC Pw Ksc ΔT s a u}ᶜ ∪
          {_u | c ≤ a}) := by
    ext u
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff]
    rw [selPool, firstMax_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun a => (em _).elim (fun h => Or.inr (h2 a h)) Or.inl⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun a ha => (h2 a).resolve_left (not_not.2 ha)⟩
  rw [e]
  refine (MeasurableSet.iInter fun b => measurableSet_le (measurable_L b) (measurable_L c)).inter
    (MeasurableSet.iInter fun a => (?_ : MeasurableSet _).compl.union (MeasurableSet.const _))
  have : {u : Fin m → Fin (k + 1) → NNR | ∀ b, LtrC Pw Ksc ΔT s b u ≤ LtrC Pw Ksc ΔT s a u} =
      ⋂ b, {u | LtrC Pw Ksc ΔT s b u ≤ LtrC Pw Ksc ΔT s a u} := by ext; simp
  rw [this]
  exact MeasurableSet.iInter fun b => measurableSet_le (measurable_L b) (measurable_L a)

theorem measurable_q :
    Measurable (Function.uncurry (qPool (k := k) Pw Ksc ΔT ΔE s)) := by
  classical
  have e : Function.uncurry (qPool (k := k) Pw Ksc ΔT ΔE s) = fun p =>
      ∑ c : Cand cp m cs, {u | selPool Pw Ksc ΔT s u = c}.indicator (fun _ => (1 : ℝ)) p.1 *
        qc Pw Ksc ΔE c p.1 p.2 := by
    funext p
    rw [Finset.sum_eq_single (selPool Pw Ksc ΔT s p.1)]
    · rw [indicator_of_mem (show p.1 ∈ {u | selPool Pw Ksc ΔT s u = selPool Pw Ksc ΔT s p.1} from rfl),
        one_mul]; rfl
    · intro c _ hc
      rw [indicator_of_notMem (show p.1 ∉ {u | selPool Pw Ksc ΔT s u = c} from fun h => hc h.symm),
        zero_mul]
    · simp
  rw [e]
  exact Finset.measurable_sum _ fun c _ =>
    ((measurable_const.indicator (measurableSet_sel c)).comp measurable_fst).mul (measurable_qc c)

end Forecast


section Forecast2

variable {m n k cp cs : ℕ} [NeZero cp] [NeZero cs] {Pw : Fin cp → ℝ} {Ksc : Fin m → Fin cs → ℝ}
  {ΔT : Fin (k + 1) → ℝ} {ΔE : Fin n → ℝ} {s : Fin m → ℝ}

omit [NeZero cp] [NeZero cs] in
theorem qc_norm (hC : Cited) (hP : ∀ a, 1 < Pw a) (hK : ∀ i b, 0 < Ksc i b) (hΔ : ∀ j, 0 < ΔE j)
    (c : Cand cp m cs) (u : Fin m → Fin (k + 1) → NNR) :
    ∫⁻ v, ENNReal.ofReal (qc Pw Ksc ΔE c u v)
      ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV) = 1 := by
  have hp : 0 < Pw (ofLex c).1 := by linarith [hP (ofLex c).1]
  unfold qc
  simp_rw [ENNReal.ofReal_prod_of_nonneg fun i _ => chain_nonneg hp (hK _ _) hΔ
    (u i (Fin.last k)).2 _]
  rw [lintegral_pi_prod _ m (fun i w => ENNReal.ofReal
    (chainN (Kc (Pw (ofLex c).1) (Ksc i (ofLex (ofLex c).2 i))) ΔE (u i (Fin.last k) : ℝ) w))
    fun i => ENNReal.measurable_ofReal.comp ((chain_meas _ _ _).comp
      (measurable_const.prodMk measurable_id))]
  refine Finset.prod_eq_one fun i _ => ?_
  exact chainN_norm n ΔE (fun _ => Kc_meas _ _ _)
    (fun j _ _ hx hy => Kc_nonneg hp (hK _ _) (hΔ j) hx hy)
    (fun j x hx => Kc_norm' hC hp (hK _ _) (hΔ j) hx) _ (u i (Fin.last k)).2

/-- On a positive training record, the separated maximizer is the first maximizer. -/
theorem sel_sep (hC : Cited) (hP : ∀ a, 1 < Pw a) (hK : ∀ i b, 0 < Ksc i b) (hΔT : ∀ j, 0 < ΔT j)
    (hs : ∀ i, 0 < s i) (u : Fin m → Fin (k + 1) → NNR) (hu : ∀ i j, 0 < (u i j : ℝ)) :
    selPool Pw Ksc ΔT s u = toLex (aFirst Pw Ksc ΔT s u,
      toLex fun i => kFirst Pw Ksc ΔT s (aFirst Pw Ksc ΔT s u) i u) := by
  set f : Fin cp → Fin m → Fin cs → ℝ := fun a i b => Ltr1 ΔT (s i) (Pw a) (Ksc i b) (u i)
  have hf : ∀ a i b, 0 < f a i b := fun a i b =>
    chain_pos hC (hP a) (hK i b) hΔT (hs i) (hu i)
  have hL : ∀ a (kk : Fin m → Fin cs), LtrC Pw Ksc ΔT s (toLex (a, toLex kk)) u = ∏ i, f a i (kk i) :=
    fun a kk => rfl
  set kst : Fin cp → Fin m → Fin cs := fun a i => kFirst Pw Ksc ΔT s a i u
  have hkst : ∀ a i b, f a i b ≤ f a i (kst a i) := fun a i => firstMax_max (fun b => f a i b)
  have hkmin : ∀ a i b, (∀ b', f a i b' ≤ f a i b) → kst a i ≤ b :=
    fun a i b h => firstMax_le (fun b => f a i b) h
  set ast := aFirst Pw Ksc ΔT s u
  have hast : ∀ a, ∏ i, f a i (kst a i) ≤ ∏ i, f ast i (kst ast i) := fun a =>
    firstMax_max (fun a => LtrC Pw Ksc ΔT s (toLex (a, toLex fun i => kst a i)) u) a
  have hamin : ∀ a, (∀ a', ∏ i, f a' i (kst a' i) ≤ ∏ i, f a i (kst a i)) → ast ≤ a := fun a h =>
    firstMax_le (fun a => LtrC Pw Ksc ΔT s (toLex (a, toLex fun i => kst a i)) u) h
  -- Every candidate is at most the separated maximum.
  have hle : ∀ c : Cand cp m cs, LtrC Pw Ksc ΔT s c u ≤ ∏ i, f ast i (kst ast i) := fun c => by
    show ∏ i, f (ofLex c).1 i (ofLex (ofLex c).2 i) ≤ _
    exact (Finset.prod_le_prod₀ (fun i _ => (hf _ _ _).le) fun i _ => hkst _ _ _).trans (hast _)
  refine firstMax_eq _ (fun c => (hle c).trans_eq (hL _ _).symm) fun c hc => ?_
  -- `c` is a maximizer.
  set a := (ofLex c).1
  set kk := ofLex (ofLex c).2
  have hcmax : ∏ i, f ast i (kst ast i) ≤ ∏ i, f a i (kk i) :=
    (hL _ _).symm.trans_le (hc (toLex (ast, toLex fun i => kst ast i)))
  have ha : ∀ a', ∏ i, f a' i (kst a' i) ≤ ∏ i, f a i (kst a i) := fun a' =>
    (hast a').trans (hcmax.trans (Finset.prod_le_prod₀ (fun i _ => (hf _ _ _).le)
      fun i _ => hkst _ _ _))
  have hle_a : ast ≤ a := hamin a ha
  rw [Prod.Lex.le_iff]
  simp only [ofLex_toLex]
  rcases hle_a.lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    rw [← heq] at hcmax
    -- Each coordinate of `kk` maximizes its factor.
    have hk : ∀ i, ∀ b, f ast i b ≤ f ast i (kk i) := by
      intro i b
      by_contra hlt
      push Not at hlt
      have hstrict : ∏ j, f ast j (kk j) < ∏ j, f ast j (kst ast j) :=
        Finset.prod_lt_prod₀ (fun j _ => hf _ _ _) (fun j _ => hkst _ _ _)
          ⟨i, Finset.mem_univ _, lt_of_lt_of_le hlt (hkst _ _ _)⟩
      linarith
    have := Pi.toLex_monotone (fun i => hkmin _ _ _ (hk i) : (fun i => kst ast i) ≤ kk)
    simpa [kk] using this

theorem forecast_holds : forecast := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW m n k cp cs _ _ Pw Ksc ΔT ΔE s hP hK hΔT hΔE hs q
  have hC := cited_of h55 h56 hW
  refine ⟨measurable_q, fun u v => ?_, fun u => qc_norm hC hP hK hΔE _ u, fun u v hu hv => ?_,
    fun u hu => sel_sep hC hP hK hΔT hs u hu⟩
  · exact Finset.prod_nonneg fun i _ => chain_nonneg (lt_trans zero_lt_one (hP _)) (hK _ _) hΔE
      (u i (Fin.last k)).2 _
  · exact Finset.prod_pos fun i _ => chain_pos hC (hP _) (hK _ _) hΔE (hu i) (hv i)

end Forecast2

end Novel.D16GaussianPoolForecast
