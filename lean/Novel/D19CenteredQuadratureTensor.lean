import Novel.D19CenteredQuadratureCoef

/-!
# Claim 038: the tensor subcells

* Each observed log cell `[a_j, d_j)` is the disjoint union of its `M` subcells, so the cell product
  is the disjoint union over index tuples `L : Fin J → Fin M` of the subcell products; each of those
  is almost everywhere the closed box `t_L ± r` around its midpoint path (`lintegral_cellBox`).
* Distributing claim 036's forward sums in time order gives `Q_J = Σ_L W_L`, where `W_L` is the
  product of `h_j φ_j(t_(j,L_j) − t_(j−1,L_(j−1)))` (`Qs_eq`, from `msg_sum` by induction on the
  string). For (1)'s parameters `W_L = P(t_L) vol(box_L)` (`Wt_eq`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D19CenteredQuadrature

open Standalone.D19CenteredQuadrature Standalone.D19FilteredLikelihood Standalone.D19CondSensitivity
  Standalone.D17ClockCells Novel.D19FilteredLikelihood Novel.D19CondSensitivity

variable {δ s : ℝ} {M : ℕ}

/-! ## The cell partition -/

/-- Subcell `l` of the log cell of `z`. -/
def piece (δ : ℝ) (M z : ℕ) (l : ℕ) : Set ℝ :=
  Ico (lA δ z + l * wd δ M z) (lA δ z + (l + 1) * wd δ M z)

theorem Ico_partition (hδ : 0 < δ) (hM : 0 < M) {z : ℕ} (hz : 1 ≤ z) :
    Ico (lA δ z) (lD δ z) = ⋃ l : Fin M, piece δ M z l := by
  have hw := wd_pos hδ hM hz
  have hMw : (M : ℝ) * wd δ M z = lD δ z - lA δ z := by
    unfold wd; field_simp
  ext x
  simp only [mem_Ico, mem_iUnion, piece]
  constructor
  · rintro ⟨h1, h2⟩
    set q := (x - lA δ z) / wd δ M z
    have hq0 : 0 ≤ q := div_nonneg (by linarith) hw.le
    have hqM : q < M := by rw [div_lt_iff₀ hw]; linarith
    refine ⟨⟨⌊q⌋₊, (Nat.floor_lt hq0).2 hqM⟩, ?_, ?_⟩
    · have := Nat.floor_le hq0
      have : (⌊q⌋₊ : ℝ) * wd δ M z ≤ x - lA δ z := by
        rwa [le_div_iff₀ hw] at this
      simp only; linarith
    · have := Nat.lt_floor_add_one q
      have : x - lA δ z < ((⌊q⌋₊ : ℝ) + 1) * wd δ M z := by
        rwa [div_lt_iff₀ hw] at this
      simp only; linarith
  · rintro ⟨l, h1, h2⟩
    have hl : ((l : ℕ) : ℝ) + 1 ≤ M := by exact_mod_cast l.isLt
    have h0 : (0 : ℝ) ≤ (l : ℕ) := Nat.cast_nonneg _
    constructor
    · nlinarith
    · nlinarith

theorem piece_disj {z : ℕ} (hw : 0 < wd δ M z) {l l' : ℕ} (hll : l ≠ l') :
    Disjoint (piece δ M z l) (piece δ M z l') := by
  rcases Nat.lt_or_gt_of_ne hll with h | h <;> refine Set.disjoint_left.2 fun x hx hx' => ?_ <;>
    simp only [piece, mem_Ico] at hx hx'
  · have : ((l : ℝ) + 1) ≤ l' := by exact_mod_cast h
    nlinarith [hx.2, hx'.1]
  · have : ((l' : ℝ) + 1) ≤ l := by exact_mod_cast h
    nlinarith [hx.1, hx'.2]

variable {m : ℕ}

/-- The midpoint path `t_L`. -/
noncomputable def tv (δ : ℝ) (M : ℕ) (z : Fin m → ℕ) (L : Fin m → Fin M) : Fin m → ℝ :=
  fun j => tMid δ M (z j) (L j)

/-- The radii `r_j = h_j/2`. -/
noncomputable def rv (δ : ℝ) (M : ℕ) (z : Fin m → ℕ) : Fin m → ℝ := fun j => wd δ M (z j) / 2

theorem rv_eq (z : Fin m → ℕ) (j : Fin m) : rv δ M z j = hP δ M z j.succ / 2 := by
  unfold rv hP wd; rw [Fin.cons_succ]

/-- The subcell product of the index tuple `L`. -/
def subB (δ : ℝ) (M : ℕ) (z : Fin m → ℕ) (L : Fin m → Fin M) : Set (Fin m → ℝ) :=
  Set.pi univ fun j => piece δ M (z j) (L j)

theorem subB_eq (z : Fin m → ℕ) (L : Fin m → Fin M) :
    subB δ M z L = Set.pi univ fun j => Ico ((tv δ M z L - rv δ M z) j) ((tv δ M z L + rv δ M z) j) := by
  unfold subB piece
  congr 1; funext j
  simp only [tv, rv, tMid, wd, Pi.sub_apply, Pi.add_apply]
  congr 1 <;> ring

theorem lintegral_cellBox (hδ : 0 < δ) (hM : 0 < M) {z : Fin m → ℕ} (hz : ∀ j, 1 ≤ z j)
    {f : (Fin m → ℝ) → ℝ≥0∞} :
    ∫⁻ y in cellBox δ z, f y =
      ∑ L : Fin m → Fin M, ∫⁻ y in Icc (tv δ M z L - rv δ M z) (tv δ M z L + rv δ M z), f y := by
  have hcb : cellBox δ z = ⋃ L : Fin m → Fin M, subB δ M z L := by
    unfold cellBox subB
    rw [Set.iUnion_univ_pi (t := fun j (l : Fin M) => piece δ M (z j) l)]
    congr 1; funext j
    exact Ico_partition hδ hM (hz j)
  have hmeas : ∀ L : Fin m → Fin M, MeasurableSet (subB δ M z L) := fun L =>
    MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hdisj : Pairwise (Function.onFun Disjoint (subB δ M z)) := fun L L' hLL => by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hLL
    refine Set.disjoint_univ_pi.2 ⟨j, piece_disj (wd_pos hδ hM (hz j)) fun h => hj (Fin.ext h)⟩
  rw [hcb, lintegral_iUnion hmeas hdisj, tsum_fintype]
  refine Finset.sum_congr rfl fun L _ => setLIntegral_congr ?_
  rw [subB_eq, volume_pi]
  exact Measure.univ_pi_Ico_ae_eq_Icc

/-! ## The forward sums as a sum over index tuples -/

/-- `W_L = Π_j h_j φ_j(t_(j,L_j) − t_(j−1,L_(j−1)))`, with `t_0 = log s`. -/
noncomputable def Wt (δ s : ℝ) (M : ℕ) {m : ℕ} (μ σ : Fin m → ℝ) (z : Fin m → ℕ)
    (L : Fin m → Fin M) : ℝ :=
  ∏ j, wd δ M (z j) *
    gaussianPDFReal (μ j) (σ j ^ 2).toNNReal (inc (Fin.cons (Real.log s) (tv δ M z L)) j)

/-- The last index of a tuple (`0` for the empty one). -/
def lastIdx : {m : ℕ} → (Fin m → Fin M) → ℕ
  | 0, _ => 0
  | m + 1, L => L (Fin.last m)

theorem cons_castSucc_init (c : ℝ) (f : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    (Fin.cons c f : Fin (m + 2) → ℝ) k.castSucc = (Fin.cons c (Fin.init f) : Fin (m + 1) → ℝ) k := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]; rfl

theorem inc_cons_castSucc (c : ℝ) (f : Fin (m + 1) → ℝ) (j : Fin m) :
    inc (Fin.cons c f) j.castSucc = inc (Fin.cons c (Fin.init f)) j := by
  unfold inc
  rw [Fin.succ_castSucc, cons_castSucc_init, cons_castSucc_init]

theorem inc_cons_last (c : ℝ) (f : Fin (m + 1) → ℝ) :
    inc (Fin.cons c f) (Fin.last m) = f (Fin.last m) - (Fin.cons c (Fin.init f) : Fin (m + 1) → ℝ) (Fin.last m) := by
  unfold inc
  rw [Fin.cons_succ, cons_castSucc_init]

theorem init_tv (z : Fin (m + 1) → ℕ) (L' : Fin m → Fin M) (l : Fin M) :
    Fin.init (tv δ M z (Fin.snoc L' l)) = tv δ M (Fin.init z) L' := by
  funext i; simp [tv, Fin.init]

theorem cons_tv_last (z : Fin m → ℕ) (L : Fin m → Fin M) :
    (Fin.cons (Real.log s) (tv δ M z L) : Fin (m + 1) → ℝ) (Fin.last m) = lastMid δ s M m z (lastIdx L) := by
  cases m with
  | zero => rfl
  | succ m => rw [← Fin.succ_last, Fin.cons_succ]; rfl

theorem Wt_snoc (μ σ : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℕ) (L' : Fin m → Fin M) (l : Fin M) :
    Wt δ s M μ σ z (Fin.snoc L' l) = Wt δ s M (Fin.init μ) (Fin.init σ) (Fin.init z) L' *
      (wd δ M (z (Fin.last m)) * gaussianPDFReal (μ (Fin.last m)) (σ (Fin.last m) ^ 2).toNNReal
        (tMid δ M (z (Fin.last m)) l - lastMid δ s M m (Fin.init z) (lastIdx L'))) := by
  unfold Wt
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [inc_cons_castSucc, init_tv]; rfl
  · rw [inc_cons_last, init_tv, cons_tv_last]
    simp [tv]

theorem lastIdx_snoc (L' : Fin m → Fin M) (l : Fin M) : lastIdx (Fin.snoc L' l : Fin (m + 1) → Fin M) = l := by
  simp [lastIdx]

theorem sum_snoc {α : Type*} [AddCommMonoid α] (F : (Fin (m + 1) → Fin M) → α) :
    ∑ L, F L = ∑ L' : Fin m → Fin M, ∑ l : Fin M, F (Fin.snoc L' l) := by
  rw [← (Fin.snocEquiv fun _ => Fin M).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The forward sums against any test function of the last index. -/
theorem msg_sum (hM : 0 < M) : ∀ (m : ℕ) (μ σ : Fin m → ℝ) (z : Fin m → ℕ) (φ : ℕ → ℝ),
    ∑ l ∈ Finset.range M, msg δ s M m μ σ z l * φ l = ∑ L : Fin m → Fin M, Wt δ s M μ σ z L * φ (lastIdx L)
  | 0, μ, σ, z, φ => by
    have h0 : (0 : ℕ) ∈ Finset.range M := Finset.mem_range.2 hM
    show ∑ l ∈ Finset.range M, (if l = 0 then (1 : ℝ) else 0) * φ l = _
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', h0]
    simp [Wt, lastIdx]
  | m + 1, μ, σ, z, φ => by
    set φ' : ℕ → ℝ := fun l' => ∑ l ∈ Finset.range M, wd δ M (z (Fin.last m)) *
      gaussianPDFReal (μ (Fin.last m)) (σ (Fin.last m) ^ 2).toNNReal
        (tMid δ M (z (Fin.last m)) l - lastMid δ s M m (Fin.init z) l') * φ l
    have IH := msg_sum hM m (Fin.init μ) (Fin.init σ) (Fin.init z) φ'
    have hL : ∑ l ∈ Finset.range M, msg δ s M (m + 1) μ σ z l * φ l =
        ∑ l' ∈ Finset.range M, msg δ s M m (Fin.init μ) (Fin.init σ) (Fin.init z) l' * φ' l' := by
      show ∑ l ∈ Finset.range M, ((lD δ (z (Fin.last m)) - lA δ (z (Fin.last m))) / M *
        ∑ l' ∈ Finset.range M, msg δ s M m (Fin.init μ) (Fin.init σ) (Fin.init z) l' *
          gaussianPDFReal (μ (Fin.last m)) (σ (Fin.last m) ^ 2).toNNReal
            (tMid δ M (z (Fin.last m)) l - lastMid δ s M m (Fin.init z) l')) * φ l = _
      simp only [φ', Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun l _ => ?_
      unfold wd; ring
    rw [hL, IH, sum_snoc]
    refine Finset.sum_congr rfl fun L' _ => ?_
    simp only [φ', Finset.mul_sum]
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Wt_snoc, lastIdx_snoc]; ring

theorem Qs_eq (hM : 0 < M) (μ σ : Fin m → ℝ) (z : Fin m → ℕ) :
    Qs δ s M μ σ z = ∑ L : Fin m → Fin M, Wt δ s M μ σ z L := by
  have := msg_sum (δ := δ) (s := s) hM m μ σ z (fun _ => 1)
  simp only [mul_one] at this
  exact this

/-- For (1)'s parameters, `W_L = P(t_L) vol(box_L)`. -/
theorem Wt_eq (Δ : Fin m → ℝ) {v : Fin m → ℝ} (hv : ∀ j, 0 < v j) (b : ℝ) {w : ℝ} (hw : 0 < w)
    (z : Fin m → ℕ) (hz : ∀ j, 1 ≤ z j) (hδ : 0 < δ) (L : Fin m → Fin M) :
    ENNReal.ofReal (Wt δ s M (muF Δ v b w) (sdF v w) z L) =
      ENNReal.ofReal (pdens Δ v b w (Real.log s) (tv δ M z L)) *
        volume (Icc (tv δ M z L - rv δ M z) (tv δ M z L + rv δ M z)) := by
  have hwd : ∀ j, 0 ≤ wd δ M (z j) := fun j => by
    unfold wd; exact div_nonneg (sub_nonneg.2 (lA_lt_lD hδ (hz j)).le) (Nat.cast_nonneg _)
  rw [Real.volume_Icc_pi]
  unfold Wt pdens
  rw [Finset.prod_mul_distrib, ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => hwd j),
    ENNReal.ofReal_prod_of_nonneg fun j _ => hwd j,
    ENNReal.ofReal_prod_of_nonneg fun j _ => gaussianPDFReal_nonneg _ _ _, dens_eq hv hw, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  simp only [rv, Pi.add_apply, Pi.sub_apply]; ring

end Novel.D19CenteredQuadrature
