import Standalone.CEVSupport
import Novel.PriceChainProof
import Novel.D3PowerTailProof
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Claim 054, deterministic part: proof

Proves `Standalone.CEVSupport.statement` (`proof`).
* `pattern`: if a `p > 1` chain is positive, then each coordinate is zero exactly when the start
  is. A positive state cannot jump to `0` (no atom for `p > 1`), and the trapped `0` cannot leave.
* `null_pos`: on such a pattern every `p ≤ 1` factor is positive: `f1`, the cited positive `fcev`,
  or the trapped `1`.
* `first_zero`: from a positive start, the first zero coordinate is reached from a positive state,
  where a `p ≥ 1` kernel has no atom.
* `score`: the composite minimum of extended ratios, by cases on `Ĝ`.
* Blocks: claim 013's `B1_eq`/`B2_eq` with `integral_rpow` or `integral_inv_of_pos`.
* The tail: `integrableOn_Ioi_rpow_iff`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Novel.CEVSupport

open Standalone.PriceChain Standalone.SplitLikelihoodSupport Standalone.CEVSupport

/-! ## Kernel values -/

theorem Kc_zero_zero (p κ Δ : ℝ) : Kc p κ Δ 0 0 = 1 := by
  unfold Kc K; split_ifs <;> simp_all

theorem Kc_zero_pos {p κ Δ y : ℝ} (hy : y ≠ 0) : Kc p κ Δ 0 y = 0 := by
  unfold Kc K; split_ifs <;> simp_all

theorem Kc_pos_zero {p κ Δ x : ℝ} (hp : 1 ≤ p) (hx : x ≠ 0) : Kc p κ Δ x 0 = 0 := by
  unfold Kc K acev
  split_ifs <;> first | rfl | (exfalso; linarith) | simp_all

theorem Kc_pos_pos {p κ Δ x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Kc p κ Δ x y = if p = 1 then f1 κ Δ x y else fcev p κ Δ x y := by
  unfold Kc K; split_ifs <;> simp_all

/-! ## Chains -/

variable {m : ℕ}

theorem prevN_zero (x₀ : ℝ) (v : Fin m → NNR) (j : Fin m) (hj : (j : ℕ) = 0) :
    prevN x₀ v j = x₀ := by simp [prevN, hj]

theorem prevN_succ (x₀ : ℝ) (v : Fin m → NNR) (j : Fin m) (hj : (j : ℕ) ≠ 0) :
    prevN x₀ v j = (v ⟨j - 1, by omega⟩ : ℝ) := by simp [prevN, hj]

theorem prevN_nonneg {x₀ : ℝ} (hx₀ : 0 ≤ x₀) (v : Fin m → NNR) (j : Fin m) : 0 ≤ prevN x₀ v j := by
  unfold prevN; split_ifs
  · exact hx₀
  · exact (v _).2

/-- A positive `p > 1` chain: each coordinate is zero exactly when the start is. -/
theorem pattern {Δ : Fin m → ℝ} {p κ x₀ : ℝ} {v : Fin m → NNR} (hp : 1 < p) (_hx₀ : 0 ≤ x₀)
    (h : 0 < chainN (Kc p κ) Δ x₀ v) : ∀ j : Fin m, ((v j : ℝ) = 0 ↔ x₀ = 0) := by
  have hfac : ∀ j, Kc p κ (Δ j) (prevN x₀ v j) (v j) ≠ 0 := fun j hj => by
    have : chainN (Kc p κ) Δ x₀ v = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
    linarith
  -- Each factor forces `v j = 0 ↔ prev j = 0`.
  have hstep : ∀ j, ((v j : ℝ) = 0 ↔ prevN x₀ v j = 0) := fun j => by
    constructor
    · intro hv
      by_contra hpr
      exact hfac j (by rw [hv]; exact Kc_pos_zero hp.le hpr)
    · intro hpr
      by_contra hv
      exact hfac j (by rw [hpr]; exact Kc_zero_pos hv)
  have key : ∀ n (hn : n < m), ((v ⟨n, hn⟩ : ℝ) = 0 ↔ x₀ = 0) := by
    intro n
    induction n with
    | zero => intro hn; rw [hstep, prevN_zero x₀ v _ rfl]
    | succ n ih =>
      intro hn
      rw [hstep, prevN_succ x₀ v _ (by simp)]
      exact ih (by omega)
  intro j
  exact key j j.2

/-- On a positive `p > 1` pattern, every `p ≤ 1` chain is positive. -/
theorem null_pos {Δ : Fin m → ℝ} {p p' κ κ' x₀ : ℝ} {v : Fin m → NNR} (hΔ : ∀ j, 0 < Δ j)
    (hx₀ : 0 ≤ x₀) (hp : 1 < p) (_hp'0 : 0 < p') (_hp' : p' ≤ 1) (hκ' : 0 < κ')
    (hf : p' ≠ 1 → ∀ Δ' x y : ℝ, 0 < Δ' → 0 < x → 0 < y → 0 < fcev p' κ' Δ' x y)
    (h : 0 < chainN (Kc p κ) Δ x₀ v) : 0 < chainN (Kc p' κ') Δ x₀ v := by
  have hpat := pattern hp hx₀ h
  refine Finset.prod_pos fun j _ => ?_
  have hprev : prevN x₀ v j = 0 ↔ x₀ = 0 := by
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
    · rw [prevN_zero x₀ v j hj]
    · rw [prevN_succ x₀ v j hj.ne']; exact hpat _
  by_cases hz : x₀ = 0
  · rw [hprev.2 hz, (hpat j).2 hz, Kc_zero_zero]; exact one_pos
  · have h1 : prevN x₀ v j ≠ 0 := fun h' => hz (hprev.1 h')
    have h2 : (v j : ℝ) ≠ 0 := fun h' => hz ((hpat j).1 h')
    have hpx : 0 < prevN x₀ v j := lt_of_le_of_ne (prevN_nonneg hx₀ v j) (Ne.symm h1)
    have hpy : 0 < (v j : ℝ) := lt_of_le_of_ne (v j).2 (Ne.symm h2)
    rw [Kc_pos_pos h1 h2]
    split_ifs with h1'
    · exact Novel.PriceChain.f1_pos hκ' (hΔ j) hpy
    · exact hf h1' _ _ _ (hΔ j) hpx hpy

/-- The all-zero array from a zero start has chain `1`. -/
theorem chain_absorbed (Δ : Fin m → ℝ) (p κ : ℝ) : chainN (Kc p κ) Δ 0 (fun _ => zero) = 1 := by
  refine Finset.prod_eq_one fun j _ => ?_
  have : prevN 0 (fun _ : Fin m => zero) j = 0 := by unfold prevN; split_ifs <;> rfl
  rw [this]
  exact Kc_zero_zero p κ (Δ j)

/-- From a positive start, a zero coordinate kills every `p ≥ 1` chain. -/
theorem first_zero {Δ : Fin m → ℝ} {p κ x₀ : ℝ} {v : Fin m → NNR} (hp : 1 ≤ p) (hx₀ : 0 < x₀)
    (hz : ∃ l, (v l : ℝ) = 0) : chainN (Kc p κ) Δ x₀ v = 0 := by
  classical
  have hex : ∃ n, ∃ h : n < m, (v ⟨n, h⟩ : ℝ) = 0 := by
    obtain ⟨l, hl⟩ := hz; exact ⟨l, l.2, hl⟩
  set n := Nat.find hex
  obtain ⟨hn, hvn⟩ := Nat.find_spec hex
  refine Finset.prod_eq_zero (Finset.mem_univ ⟨n, hn⟩) ?_
  have hprev : prevN x₀ v ⟨n, hn⟩ ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [prevN_zero x₀ v ⟨n, hn⟩ h0]; exact hx₀.ne'
    · rw [prevN_succ x₀ v ⟨n, hn⟩ h0.ne']
      intro h
      exact Nat.find_min hex (show n - 1 < n by omega) ⟨by omega, h⟩
  show Kc p κ (Δ ⟨n, hn⟩) (prevN x₀ v ⟨n, hn⟩) (v ⟨n, hn⟩) = 0
  rw [hvn]
  exact Kc_pos_zero hp hprev

/-! ## The composite score -/

theorem Rplus_zero_left (b : ℝ) : Rplus 0 b = 0 := by
  unfold Rplus; split_ifs <;> simp_all

theorem Rplus_pos {a b : ℝ} (hb : 0 < b) : Rplus a b = ENNReal.ofReal (a / b) := by
  unfold Rplus; rw [ite_eq_left hb]

theorem score {c : ℕ} (pw : Fin c → ℝ) (g : Fin c → ℝ) (sel : Fin c) (hg : ∀ ϑ, 0 ≤ g ϑ)
    (hnull : ∃ ϑ, pw ϑ ≤ 1) (hsupp : 0 < g sel → ∃ ϑ, pw ϑ ≤ 1 ∧ 0 < g ϑ) :
    Ecomp pw g sel < ⊤ ∧ (g sel = 0 → Ecomp pw g sel = 0) ∧
    (0 < g sel → ∃ G₀ : ℝ, 0 < G₀ ∧ (∀ ϑ, pw ϑ ≤ 1 → g ϑ ≤ G₀) ∧ (∃ ϑ, pw ϑ ≤ 1 ∧ g ϑ = G₀) ∧
      Ecomp pw g sel = ENNReal.ofReal (g sel / G₀)) ∧
    (pw sel ≤ 1 → Ecomp pw g sel ≤ 1) := by
  classical
  obtain ⟨ϑ₀, hϑ₀⟩ := hnull
  have hzero : g sel = 0 → Ecomp pw g sel = 0 := fun h => by
    refine le_antisymm ((biInf_le _ (show ϑ₀ ∈ {ϑ | pw ϑ ≤ 1} from hϑ₀)).trans ?_) bot_le
    rw [h, Rplus_zero_left]
  have hposf : 0 < g sel → ∃ G₀ : ℝ, 0 < G₀ ∧ (∀ ϑ, pw ϑ ≤ 1 → g ϑ ≤ G₀) ∧
      (∃ ϑ, pw ϑ ≤ 1 ∧ g ϑ = G₀) ∧ Ecomp pw g sel = ENNReal.ofReal (g sel / G₀) := fun h => by
    set s := Finset.univ.filter fun ϑ => pw ϑ ≤ 1
    have hs : s.Nonempty := ⟨ϑ₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hϑ₀⟩⟩
    obtain ⟨ϑm, hϑm, hmax⟩ := s.exists_max_image g hs
    have hϑm' : pw ϑm ≤ 1 := (Finset.mem_filter.1 hϑm).2
    have hle : ∀ ϑ, pw ϑ ≤ 1 → g ϑ ≤ g ϑm := fun ϑ hϑ =>
      hmax ϑ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hϑ⟩)
    have hG : 0 < g ϑm := by
      obtain ⟨ϑ', hϑ', hg'⟩ := hsupp h
      exact hg'.trans_le (hle ϑ' hϑ')
    refine ⟨g ϑm, hG, hle, ⟨ϑm, hϑm', rfl⟩, le_antisymm ?_ ?_⟩
    · refine (biInf_le _ (show ϑm ∈ {ϑ | pw ϑ ≤ 1} from hϑm')).trans ?_
      rw [Rplus_pos hG]
    · refine le_iInf₂ fun ϑ hϑ => ?_
      rcases (hg ϑ).lt_or_eq with hϑp | hϑ0
      · rw [Rplus_pos hϑp]
        exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (hg sel) hϑp (hle ϑ hϑ))
      · have : Rplus (g sel) (g ϑ) = ⊤ := by
          unfold Rplus; rw [← hϑ0]; simp [h.ne']
        rw [this]; exact le_top
  refine ⟨?_, hzero, hposf, fun hsel => ?_⟩
  · rcases (hg sel).lt_or_eq with h | h
    · obtain ⟨G₀, -, -, -, hE⟩ := hposf h
      rw [hE]; exact ENNReal.ofReal_lt_top
    · rw [hzero h.symm]; exact ENNReal.zero_lt_top
  · refine (biInf_le _ (show sel ∈ {ϑ | pw ϑ ≤ 1} from hsel)).trans ?_
    rcases (hg sel).lt_or_eq with h | h
    · rw [Rplus_pos h, div_self h.ne', ENNReal.ofReal_one]
    · rw [← h, Rplus_zero_left]; exact bot_le

/-! ## Blocks and the tail -/

theorem blocks {R r p κ : ℝ} (hR : 0 < R) (hr : 1 < r) (hκ : 0 < κ) :
    Standalone.D3PowerTail.B1 R r (fun x => κ * x ^ p) = blk1 R r p κ ∧
    Standalone.D3PowerTail.B2 R r (fun x => κ * x ^ p) = r ^ (2 - 2 * p) * blk1 R r p κ ∧
    0 < blk1 R r p κ := by
  have hσ : ∀ x, R ≤ x → (fun x => κ * x ^ p) x = κ * x ^ p := fun _ _ => rfl
  have h1 := Novel.D3PowerTail.B1_eq hκ hσ hR hr
  have h2 := Novel.D3PowerTail.B2_eq hκ hσ hR hr
  have hpos := Novel.D3PowerTail.B1_pos hκ hσ hR hr
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hRr : 0 < R * r := mul_pos hR hr0
  have hB : Standalone.D3PowerTail.B1 R r (fun x => κ * x ^ p) = blk1 R r p κ := by
    rw [h1, blk1]
    split_ifs with hp
    · subst hp
      have : ∀ x : ℝ, x ^ (1 - 2 * (1 : ℝ)) = x⁻¹ := fun x => by norm_num [Real.rpow_neg_one]
      simp_rw [this]
      rw [integral_inv_of_pos hR hRr, mul_div_cancel_left₀ _ hR.ne']
      ring
    · have hne : (1 - 2 * p) ≠ -1 := fun h => hp (by linarith)
      have h0 : (0 : ℝ) ∉ Set.uIcc R (R * r) := by
        rw [uIcc_of_le (by nlinarith)]; exact fun h => absurd h.1 (not_le.2 hR)
      rw [integral_rpow (Or.inr ⟨hne, h0⟩), show 1 - 2 * p + 1 = 2 - 2 * p by ring,
        Real.mul_rpow hR.le hr0.le]
      have hη : (2 - 2 * p) ≠ 0 := fun h => hp (by linarith)
      field_simp
  exact ⟨hB, by rw [h2, hB], hB ▸ hpos⟩

theorem tail {p κ : ℝ} (hκ : 0 < κ) :
    Standalone.D1TwoEndpoint.IInftyFinite (fun x => κ * x ^ p) ↔ 1 < p := by
  have heq : ∀ y : ℝ, 0 < y → y / (κ * y ^ p) ^ 2 = (κ ^ 2)⁻¹ * y ^ (1 - 2 * p) := fun y hy => by
    rw [Real.rpow_sub hy, Real.rpow_one, mul_pow, ← Real.rpow_natCast (y ^ p) 2,
      ← Real.rpow_mul hy.le]
    push_cast
    rw [show 2 * p = p * 2 by ring]
    field_simp
  have hiff : ∀ x : ℝ, 0 < x → (IntegrableOn (fun y => y / (κ * y ^ p) ^ 2) (Ioi x) ↔
      1 - 2 * p < -1) := fun x hx => by
    rw [integrableOn_congr_fun (s := Ioi x) (fun y hy => heq y (hx.trans hy)) measurableSet_Ioi,
      ← integrableOn_Ioi_rpow_iff hx]
    constructor
    · intro h
      have hc : κ ^ 2 ≠ 0 := by positivity
      have h' : IntegrableOn (fun y => κ ^ 2 * ((κ ^ 2)⁻¹ * y ^ (1 - 2 * p))) (Ioi x) :=
        Integrable.const_mul h (κ ^ 2)
      refine (integrableOn_congr_fun (s := Ioi x) (fun y _ => ?_) measurableSet_Ioi).1 h'
      field_simp
    · intro h; exact h.const_mul _
  constructor
  · rintro ⟨x, hx, h⟩; have := (hiff x hx).1 h; linarith
  · intro hp; exact ⟨1, one_pos, (hiff 1 one_pos).2 (by linarith)⟩

theorem proof : Standalone.CEVSupport.statement :=
  ⟨fun _ _ _ _ _ _ _ _ hΔ hx₀ hp hp'0 hp' hκ' hf h => null_pos hΔ hx₀ hp hp'0 hp' hκ' hf h,
    fun _ Δ p κ => chain_absorbed Δ p κ,
    fun _ _ _ _ _ _ hp hx₀ hz => first_zero hp hx₀ hz,
    fun _ pw g sel hg hnull hsupp => score pw g sel hg hnull hsupp,
    fun _ _ _ _ hR hr hκ => blocks hR hr hκ,
    fun _ _ hκ => tail hκ⟩

end Novel.CEVSupport
