import Standalone.D9Refinement
import Novel.D9FiniteGridProof
import Upstream.EmeryStability
import Upstream.ContinuousHittingTimes

/-!
# Claim 007 (D9): proof

Proves `Standalone.D9Refinement.statement` (`statement_holds`), conditional on the restated AX-06,
AX-10, AX-11 and AX-14. The restated AX-10, AX-11 and AX-14 are derived from
`Upstream.EmeryStability`, `Upstream.ContinuousHittingTimes` and
`Upstream.StochasticIntegration.IntegralCalculus` (`ax10_of_upstream`, `ax11_of_upstream`,
`ax14_of_upstream`). The project work is the check of AX-10's hypotheses for the sampled recursion,
together with the deterministic and probabilistic steps around it.

* **The stop (2).** `stopping_rho` (AX-11, then the minimum with `T`). `mem_Icc_before`: before and at
  the open entry, the price is in `[1/m, m]`, by continuity and `X₀ = 1`; hence `Xm_mem`.
* **The operators (9).** `kappa` is the latest grid point at or before `t`. `Fop` and `Fnop` map
  `D` to `D` (`isCadlag_comp_kappa` for the step), are nonanticipating (`κ(t) ≤ t`), and are
  `Lip(1 + |π| m)` (`lip_bound`, using `Xᵐ ≥ 1/m`).
* **The limiting equation (8).** `V_solves`: AX-14's exponential and associativity, with
  `Fop(V) = πV · (1/Xᵐ)` and continuous left limits.
* **The approximating equations.** `W_solves`: the left limits of `Fₙ(W)` are the step integrand
  with holdings `πW_{tᵢ}/Xᵐ_{tᵢ}` (`kap_eventually_left`). AX-14's elementary integral gives the
  finite gain, which is `W − 1` by claim 005's `gridP_sum`; the last term vanishes because `Xᵐ` is
  constant after `T`.
* **Convergence at the limit (10).** `LA_stop`: `Lᵐ` and its bracket are a.s. frozen after `ρ_m`,
  by stopping, uniqueness and bracket invariance. `ucp_FnV`: uniform continuity on `[0, T]` and the
  mesh give a.s. uniform convergence; `ucp_of_ae` turns it into ucp, deciding `∃ t ≤ T` on
  countably many times for right-continuous paths.
* **(4).** `part4_ucp` is AX-10's stability. `gridWealth_stop` is the pathwise identity
  `W_{t∧ρ} = W(Xᵐ)_t` (`minmax_eq`).
* **(5).** `LA_relate`: `Lᵐ = L_{·∧ρ}` a.s. (`stop_local`). `part5_ucp` is the exhaustion over
  `m`, with the entry events decided on countably many times (`measurableSet_enter`).
  `part5_breach` uses the positive minimum of the limit on `[0, T]`.
* **(6), (7).** `pathConv_of_ucp`: the bounded-Lipschitz comparison, with a measurable hull of the
  ucp event. `uiConv_of_ucp`: Mathlib's Vitali theorem (`tendsto_Lp_finite_of_tendstoInMeasure`),
  with the limit's terminal integrability from AX-06 (`expo_integrable`).
* **D1.** `d1_identification`, by AX-14's associativity three times (in `d(X − 1)`, in `dW`, and
  with the constant `π`), constant elementary integrals, and `bracket_density` with `⟨W⟩_t = t`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace Novel.D9Refinement

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9Refinement

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {m : ℕ}

/-! ## The band stop `ρ_m` and the stopped price -/

theorem band_eq (m : ℕ) : band m = Iio (1 / (m : ℝ)) ∪ Ioi (m : ℝ) := rfl

theorem isOpen_band (m : ℕ) : IsOpen (band m) := by
  rw [band_eq]; exact isOpen_Iio.union isOpen_Ioi

theorem untopA_coe (r : ℝ≥0) : (r : WithTop ℝ≥0).untopA = r := by
  simp only [WithTop.untopA, WithTop.untopD_coe]

theorem rho_le (ω : Ω) : rho X T m ω ≤ T := min_le_right _ _

theorem rho_eq (ω : Ω) : rho X T m ω = ((rho X T m ω).untopA : WithTop ℝ≥0) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top
    (rho_le (X := X) (T := T) (m := m) ω))
  rw [← hr, untopA_coe]

/-- The stop time as a real time. -/
noncomputable def rr (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ≥0 := (rho X T m ω).untopA

theorem rr_le (ω : Ω) : rr X T m ω ≤ T := by
  have h := rho_le (X := X) (T := T) (m := m) ω
  rw [rho_eq] at h
  exact WithTop.coe_le_coe.1 h

theorem min_untopA (t : ℝ≥0) (ω : Ω) :
    (min (t : WithTop ℝ≥0) (rho X T m ω)).untopA = min t (rr X T m ω) := by
  rw [rho_eq, ← WithTop.coe_min, untopA_coe]; rfl

theorem Xm_apply (t : ℝ≥0) (ω : Ω) : Xm X T m t ω = X (min t (rr X T m ω)) ω := by
  simp only [Xm, stoppedProcess, min_untopA]

theorem stopping_rho (h11 : AX11 𝓕) (hX : Setting Q 𝓕 X T) : IsStoppingTime 𝓕 (rho X T m) :=
  (h11 X hX.usual.1 hX.adapted hX.cont (band m) (isOpen_band m)).min_const T

/-- Before (and at) the entry time the price is in `[1/m, m]`. -/
theorem mem_Icc_before (hX : Setting Q 𝓕 X T) (hm : 1 < m) {ω : Ω} {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) ≤ openHitTime X (band m) ω) :
    X s ω ∈ Icc (1 / (m : ℝ)) m := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hnot : ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < openHitTime X (band m) ω → X r ω ∉ band m := by
    intro r hr hb
    exact absurd (sInf_le ⟨r, hb, rfl⟩ : openHitTime X (band m) ω ≤ r) (not_le.2 hr)
  have hband : ∀ x : ℝ, x ∉ band m ↔ x ∈ Icc (1 / (m : ℝ)) m := fun x => by
    simp only [band, mem_ofPred_eq, not_or, not_lt, mem_Icc]
  by_cases hlt : (s : WithTop ℝ≥0) < openHitTime X (band m) ω
  · exact (hband _).1 (hnot s hlt)
  · have heq : (s : WithTop ℝ≥0) = openHitTime X (band m) ω := le_antisymm hs (not_lt.1 hlt)
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [hX.start]
      refine ⟨?_, hm1.le⟩
      rw [div_le_one hmpos]; exact hm1.le
    · have : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.2 hs0⟩
      have hev : ∀ᶠ r in 𝓝[<] s, X r ω ∈ Icc (1 / (m : ℝ)) m :=
        eventually_nhdsWithin_of_forall fun r (hr : r < s) =>
          (hband _).1 (hnot r (heq ▸ WithTop.coe_lt_coe.2 hr))
      exact isClosed_Icc.mem_of_tendsto
        ((hX.cont ω).continuousAt.continuousWithinAt (s := Iio s)) hev

theorem Xm_mem (hX : Setting Q 𝓕 X T) (hm : 1 < m) (t : ℝ≥0) (ω : Ω) :
    Xm X T m t ω ∈ Icc (1 / (m : ℝ)) m := by
  rw [Xm_apply]
  refine mem_Icc_before hX hm ?_
  have h1 : ((min t (rr X T m ω) : ℝ≥0) : WithTop ℝ≥0) ≤ rho X T m ω := by
    rw [rho_eq]; exact WithTop.coe_le_coe.2 (min_le_right _ _)
  exact h1.trans (min_le_left _ _)

theorem Xm_pos (hX : Setting Q 𝓕 X T) (hm : 1 < m) (t : ℝ≥0) (ω : Ω) : 0 < Xm X T m t ω := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  exact lt_of_lt_of_le (by positivity) (Xm_mem hX hm t ω).1

theorem Xm_cont (hX : Setting Q 𝓕 X T) (ω : Ω) : Continuous fun t => Xm X T m t ω := by
  simp only [Xm_apply]
  exact (hX.cont ω).comp (continuous_id.min continuous_const)

theorem Xm_const (t : ℝ≥0) (ht : T ≤ t) (ω : Ω) : Xm X T m t ω = Xm X T m T ω := by
  simp only [Xm_apply, min_eq_right ((rr_le ω).trans ht), min_eq_right (rr_le ω)]

theorem Xm_adapted (h11 : AX11 𝓕) (hX : Setting Q 𝓕 X T) : Adapted 𝓕 (Xm X T m) := fun t =>
  (((StronglyAdapted.isStronglyProgressive_of_continuous (f := 𝓕) (u := X)
    (fun s => (hX.adapted s).stronglyMeasurable) hX.cont).stronglyAdapted_stoppedProcess
    (stopping_rho h11 hX)) t).measurable

/-! ## The grid index `κₙ` -/

/-- The index of the latest grid point at or before `t` (capped at `N`). -/
noncomputable def kap (g : ℕ → ℝ≥0) (N : ℕ) (t : ℝ≥0) : ℕ :=
  open Classical in Nat.findGreatest (fun i => g i ≤ t) N

/-- `κ(t)`, the latest grid point at or before `t`, capped at `g N`. -/
noncomputable def kappa (g : ℕ → ℝ≥0) (N : ℕ) (t : ℝ≥0) : ℝ≥0 := g (kap g N t)

section Grid

variable {g : ℕ → ℝ≥0} {N : ℕ}

theorem kap_spec (hg0 : g 0 = 0) (t : ℝ≥0) : g (kap g N t) ≤ t := by
  classical
  exact Nat.findGreatest_spec (P := fun i => g i ≤ t) (Nat.zero_le N) (by rw [hg0]; exact bot_le)

theorem kappa_le (hg0 : g 0 = 0) (t : ℝ≥0) : kappa g N t ≤ t := kap_spec hg0 t

theorem kap_le (t : ℝ≥0) : kap g N t ≤ N := Nat.findGreatest_le N

theorem lt_next {t : ℝ≥0} (h : kap g N t < N) : t < g (kap g N t + 1) := by
  classical
  by_contra hle
  push Not at hle
  exact Nat.findGreatest_is_greatest (P := fun i => g i ≤ t) (Nat.lt_succ_self _)
    (Nat.succ_le_of_lt h) hle

theorem kap_eq_of (hg : StrictMono g) {t : ℝ≥0} {i : ℕ} (hi : i ≤ N) (h1 : g i ≤ t)
    (h2 : i < N → t < g (i + 1)) : kap g N t = i := by
  classical
  refine le_antisymm ?_ (Nat.le_findGreatest (P := fun i => g i ≤ t) hi h1)
  by_contra hlt
  push Not at hlt
  have hs : g (kap g N t) ≤ t := Nat.findGreatest_spec (P := fun i => g i ≤ t) hi h1
  have := hg.monotone (Nat.succ_le_of_lt hlt)
  exact absurd ((h2 (hlt.trans_le (kap_le t))).trans_le (this.trans hs)) (lt_irrefl t)

theorem kappa_of_ge (hg : StrictMono g) {t : ℝ≥0} (ht : g N ≤ t) : kappa g N t = g N := by
  unfold kappa; rw [kap_eq_of hg le_rfl ht fun h => absurd h (lt_irrefl N)]

/-- To the right of `t`, `κ` is constant. -/
theorem kappa_eventually_right (hg : StrictMono g) (hg0 : g 0 = 0) (t : ℝ≥0) :
    ∀ᶠ s in 𝓝[>] t, kap g N s = kap g N t := by
  set i := kap g N t
  by_cases hiN : i < N
  · filter_upwards [Ioo_mem_nhdsGT (lt_next hiN)] with s hs
    exact kap_eq_of hg (kap_le t) ((kap_spec hg0 t).trans hs.1.le) fun _ => hs.2
  · filter_upwards [self_mem_nhdsWithin] with s (hs : t < s)
    exact kap_eq_of hg (kap_le t) ((kap_spec hg0 t).trans hs.le) fun h => absurd h hiN

/-- To the left of `t > 0`, `κ` is constant. -/
theorem kap_eventually_left (hg : StrictMono g) (hg0 : g 0 = 0) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᶠ s in 𝓝[<] t, kap g N s = (open Classical in Nat.findGreatest (fun i => g i < t) N) := by
  classical
  set j := Nat.findGreatest (fun i => g i < t) N
  have hj : g j < t := Nat.findGreatest_spec (P := fun i => g i < t) (Nat.zero_le N)
    (by rw [hg0]; exact ht)
  filter_upwards [Ioo_mem_nhdsLT hj] with s hs
  refine kap_eq_of hg (Nat.findGreatest_le N) hs.1.le fun hjN => ?_
  have := Nat.findGreatest_is_greatest (P := fun i => g i < t) (Nat.lt_succ_self _)
    (Nat.succ_le_of_lt hjN)
  exact hs.2.trans_le (not_lt.1 this)

theorem kappa_eventually_left (hg : StrictMono g) (hg0 : g 0 = 0) {t : ℝ≥0} (ht : 0 < t) :
    ∃ j, ∀ᶠ s in 𝓝[<] t, kap g N s = j :=
  ⟨_, kap_eventually_left hg hg0 ht⟩

/-- Any function of `κ(t)` is càdlàg in `t`. -/
theorem isCadlag_comp_kappa (hg : StrictMono g) (hg0 : g 0 = 0) (c : ℝ≥0 → ℝ) :
    IsCadlag fun t => c (kappa g N t) := by
  refine ⟨fun a => ?_, fun x => ?_⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [kappa_eventually_right (N := N) hg hg0 a] with s hs
    simp only [kappa, hs]
  · rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨0, by simp⟩
    · obtain ⟨j, hj⟩ := kappa_eventually_left (N := N) hg hg0 (pos_iff_ne_zero.2 hx)
      refine ⟨c (g j), tendsto_const_nhds.congr' ?_⟩
      filter_upwards [hj] with s hs
      simp only [kappa, hs]

end Grid

/-! ## The two operators -/

/-- `F(Z) = πZ / Y`, (9). -/
noncomputable def Fop (π : ℝ) (Y Z : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := π * Z t ω / Y t ω

/-- `Fₙ(Z) = π Z_{κ(t)} / Y_{κ(t)}`, (9). -/
noncomputable def Fnop (π : ℝ) (Y : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) (N : ℕ) (Z : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  π * Z (kappa g N t) ω / Y (kappa g N t) ω

section Ops

variable {π : ℝ} {Y : ℝ≥0 → Ω → ℝ} {g : ℕ → ℝ≥0} {N : ℕ}

theorem mapsD_Fnop (hg : StrictMono g) (hg0 : g 0 = 0) (hY : Adapted 𝓕 Y) :
    MapsD 𝓕 (Fnop π Y g N) := by
  intro Z hZ
  refine ⟨fun t => ?_, fun ω => isCadlag_comp_kappa hg hg0 fun s => π * Z s ω / Y s ω⟩
  have hk := 𝓕.mono (kappa_le (N := N) hg0 t)
  exact (measurable_const.mul ((hZ.adapted _).mono hk le_rfl)).div ((hY _).mono hk le_rfl)

theorem mapsD_Fop (hY : Adapted 𝓕 Y) (hYc : ∀ ω, Continuous fun t => Y t ω)
    (hY0 : ∀ t ω, Y t ω ≠ 0) : MapsD 𝓕 (Fop π Y) := by
  intro Z hZ
  refine ⟨fun t => (measurable_const.mul (hZ.adapted t)).div (hY t), fun ω => ⟨fun a => ?_, fun x => ?_⟩⟩
  · exact (tendsto_const_nhds.mul ((hZ.cadlag ω).isRightContinuous a)).div
      ((hYc ω).continuousAt.continuousWithinAt) (hY0 a ω)
  · obtain ⟨l, hl⟩ := (hZ.cadlag ω).tendsto_nhdsLT x
    exact ⟨π * l / Y x ω, (tendsto_const_nhds.mul hl).div
      ((hYc ω).continuousAt.continuousWithinAt) (hY0 x ω)⟩

theorem nonanticipating_Fnop (hg0 : g 0 = 0) : Nonanticipating Q 𝓕 (Fnop π Y g N) := by
  intro U V τ _ _ _ h
  filter_upwards [h] with ω hω t ht
  simp only [Fnop]
  rw [hω _ (lt_of_le_of_lt (WithTop.coe_le_coe.2 (kappa_le hg0 t)) ht)]

theorem nonanticipating_Fop : Nonanticipating Q 𝓕 (Fop π Y) := by
  intro U V τ _ _ _ h
  filter_upwards [h] with ω hω t ht
  simp only [Fop]
  rw [hω t ht]

theorem lip_bound {a b y c : ℝ} (hy : 1 / (m : ℝ) ≤ y) (hm : 0 < (m : ℝ)) (hab : |a - b| ≤ c) :
    |π * a / y - π * b / y| ≤ (1 + |π| * m) * c := by
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hc : 0 ≤ c := (abs_nonneg _).trans hab
  have hinv : 1 / y ≤ m := by
    rw [div_le_iff₀ hy0]; rw [div_le_iff₀ hm] at hy; linarith
  rw [show π * a / y - π * b / y = π * (a - b) * (1 / y) by ring, abs_mul, abs_mul,
    abs_of_pos (one_div_pos.2 hy0)]
  calc |π| * |a - b| * (1 / y) ≤ |π| * c * m :=
        mul_le_mul (mul_le_mul_of_nonneg_left hab (abs_nonneg _)) hinv (by positivity)
          (by positivity)
    _ ≤ (1 + |π| * m) * c := by nlinarith [abs_nonneg π]

theorem lip_Fnop (hm : 0 < (m : ℝ)) (hY : ∀ t ω, 1 / (m : ℝ) ≤ Y t ω) :
    LipOp Q 𝓕 (1 + |π| * m) (Fnop π Y g N) := by
  intro U V _ _
  exact Eventually.of_forall fun ω C hC t => lip_bound (hY _ ω) hm (hC _)

theorem lip_Fop (hm : 0 < (m : ℝ)) (hY : ∀ t ω, 1 / (m : ℝ) ≤ Y t ω) :
    LipOp Q 𝓕 (1 + |π| * m) (Fop π Y) := by
  intro U V _ _
  exact Eventually.of_forall fun ω C hC t => lip_bound (hY _ ω) hm (hC _)

end Ops

/-! ## Admissible integrands and the stopped setting -/

/-- A continuous adapted process with every path continuous is an admissible integrand. -/
theorem integrand_of_cont {K : ℝ≥0 → Ω → ℝ} (hK : Adapted 𝓕 K) (hc : ∀ ω, Continuous fun t => K t ω) :
    Integrand Q 𝓕 K := by
  refine ⟨StronglyAdapted.isStronglyProgressive_of_continuous (fun t => (hK t).stronglyMeasurable) hc,
    Eventually.of_forall fun ω T => ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    (hc ω).continuousOn
  exact ⟨C, fun t ht => by simpa [Real.norm_eq_abs] using hC t ⟨bot_le, ht⟩⟩

theorem contLocMart_X (hX : Setting Q 𝓕 X T) (hconst : ∀ t ω, X t ω = X (min t T) ω) :
    ContLocMart Q 𝓕 X := by
  refine ⟨hX.adapted, hX.cont, ?_⟩
  have : stopAt T X = X := funext fun t => funext fun ω => (hconst t ω).symm
  have h := hX.localMart
  rwa [this] at h

theorem stopAt_Xm : stopAt T (Xm X T m) = Xm X T m :=
  funext fun t => funext fun ω => by
    simp only [stopAt]
    rcases le_total t T with ht | ht
    · rw [min_eq_left ht]
    · rw [min_eq_right ht, Xm_const t ht]

section Stopped

theorem contLocMart_Xm {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
    {Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop} (h14 : AX14 Q 𝓕 Integral Bracket)
    (h11 : AX11 𝓕) (hX : Setting Q 𝓕 X T) (hconst : ∀ t ω, X t ω = X (min t T) ω) :
    ContLocMart Q 𝓕 (Xm X T m) :=
  h14.stop_contLocMart X _ hX.prob hX.usual (contLocMart_X hX hconst) (stopping_rho h11 hX)

theorem setting_Xm {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
    {Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop} (h14 : AX14 Q 𝓕 Integral Bracket)
    (h11 : AX11 𝓕) (hX : Setting Q 𝓕 X T) (hconst : ∀ t ω, X t ω = X (min t T) ω)
    (hm : 1 < m) : Setting Q 𝓕 (Xm X T m) T := by
  have hc := contLocMart_Xm (m := m) h14 h11 hX hconst
  refine ⟨hX.prob, hX.usual, hc.adapted, hc.cont, fun t ω => (Xm_pos hX hm t ω).le,
    fun ω => ?_, ?_⟩
  · rw [Xm_apply, min_eq_left (zero_le : (0 : ℝ≥0) ≤ rr X T m ω), hX.start]
  · rw [stopAt_Xm]; exact hc.localMart

end Stopped

/-! ## The limiting equation (8) and the approximating equations -/

theorem leftLim_cont {Z : ℝ≥0 → Ω → ℝ} {ω : Ω} (hZ : Continuous fun t => Z t ω) (t : ℝ≥0) :
    leftLimProc Z t ω = Z t ω := by
  rcases eq_or_ne t 0 with rfl | ht
  · exact leftLim_eq_of_eq_bot _ (by simp)
  · have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.2 ht⟩
    exact leftLim_eq_of_tendsto (hZ.continuousAt.continuousWithinAt)

theorem elemIntegrand_zero' {g : ℕ → ℝ≥0} (N : ℕ) (h : ℕ → Ω → ℝ) (ω : Ω) :
    elemIntegrand g N h 0 ω = h 0 ω := by
  classical
  unfold elemIntegrand
  congr 1
  exact Nat.findGreatest_eq_zero_iff.2 fun n _ _ hn => absurd hn (not_lt.2 bot_le)

section Equations

variable {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop} (h14 : AX14 Q 𝓕 Integral Bracket)
  (h11 : AX11 𝓕) (hX : Setting Q 𝓕 X T) (hconst : ∀ t ω, X t ω = X (min t T) ω) (hm : 1 < m)
include h14 h11 hX hconst hm

theorem integrand_invXm : Integrand Q 𝓕 (fun t ω => 1 / Xm X T m t ω) :=
  integrand_of_cont (fun t => measurable_const.div ((contLocMart_Xm h14 h11 hX hconst).adapted t))
    fun ω => continuous_const.div (Xm_cont hX ω) fun t => (Xm_pos hX hm t ω).ne'

/-- (8): `V = exp(πLᵐ − π²⟨Lᵐ⟩/2)` solves `V = 1 + ∫ F(V)_{s−} dXᵐ`. -/
theorem V_solves {L A : ℝ≥0 → Ω → ℝ} (hL : Integral (fun t ω => 1 / Xm X T m t ω) (Xm X T m) L)
    (hA : Bracket L A) (π : ℝ) :
    IsD 𝓕 (expo π L A) ∧ ContLocMart Q 𝓕 (expo π L A) ∧
      Integral (leftLimProc (Fop π (Xm X T m) (expo π L A))) (Xm X T m)
        (fun t ω => expo π L A t ω - 1) := by
  have := hX.prob
  have hXm := contLocMart_Xm (m := m) h14 h11 hX hconst
  have hK := integrand_invXm h14 h11 hX hconst hm
  have hLc := h14.integral_contLocMart _ _ _ hX.prob hX.usual hXm hK hL
  obtain ⟨hVc, hVI⟩ := h14.exponential L A π hX.prob hX.usual hLc (h14.integral_zero hL) hA
  have hH : Integrand Q 𝓕 (fun t ω => π * expo π L A t ω) :=
    integrand_of_cont (fun t => measurable_const.mul (hVc.adapted t))
      fun ω => continuous_const.mul (hVc.cont ω)
  have hI := h14.assoc _ _ _ _ _ hX.prob hX.usual hXm hK hH hL hVI
  refine ⟨⟨hVc.adapted, fun ω => (hVc.cont ω).isCadlag⟩, hVc, ?_⟩
  have heq : leftLimProc (Fop π (Xm X T m) (expo π L A)) =
      fun t ω => π * expo π L A t ω * (1 / Xm X T m t ω) := by
    funext t ω
    rw [leftLim_cont (Z := Fop π (Xm X T m) (expo π L A))
      ((continuous_const.mul (hVc.cont ω)).div (Xm_cont hX ω)
        fun t => (Xm_pos hX hm t ω).ne') t]
    simp only [Fop]; ring
  rw [heq]; exact hI

/-- The stopped recursion solves its approximating equation (AX-08's elementary integral). -/
theorem W_solves {g : ℕ → ℝ≥0} {N : ℕ} (hg : StrictMono g) (hg0 : g 0 = 0) (hgN : g N = T)
    (π : ℝ) :
    IsD 𝓕 (gridWealth π (Xm X T m) N g) ∧
      Integral (leftLimProc (Fnop π (Xm X T m) g N (gridWealth π (Xm X T m) N g))) (Xm X T m)
        (fun t ω => gridWealth π (Xm X T m) N g t ω - 1) := by
  have hS := setting_Xm h14 h11 hX hconst hm
  have hXm := contLocMart_Xm (m := m) h14 h11 hX hconst
  set W := gridWealth π (Xm X T m) N g
  set h : ℕ → Ω → ℝ := fun i ω => π * W (g i) ω / Xm X T m (g i) ω
  have hWad := Novel.D9FiniteGrid.gridWealth_adapted hS hg (π := π) (N := N)
  refine ⟨⟨hWad, fun ω => (Novel.D9FiniteGrid.gridWealth_cont hS ω).isCadlag⟩, ?_⟩
  have hmeas : ∀ i ≤ N, Measurable[𝓕 (g i)] (h i) := fun i _ =>
    (measurable_const.mul (hWad (g i))).div (hXm.adapted (g i))
  have hel := h14.elementary (Xm X T m) g N h hX.prob hX.usual hXm hg hg0 hmeas
  have hleft : leftLimProc (Fnop π (Xm X T m) g N W) = elemIntegrand g N h := by
    funext t ω
    rcases eq_or_ne t 0 with rfl | ht
    · rw [elemIntegrand_zero', leftLimProc, leftLim_eq_of_eq_bot _ (by simp)]
      have hk : kap g N 0 = 0 := by
        rcases Nat.eq_zero_or_pos N with hN | hN
        · subst hN; exact Nat.le_zero.1 (kap_le 0)
        · exact kap_eq_of hg (Nat.zero_le N) (by rw [hg0]) fun _ => by
            rw [← hg0]; exact hg (Nat.lt_succ_self 0)
      simp only [Fnop, kappa, hk, h]
    · have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.2 ht⟩
      rw [leftLimProc]
      refine leftLim_eq_of_tendsto (tendsto_const_nhds.congr' ?_)
      filter_upwards [kap_eventually_left (N := N) hg hg0 (pos_iff_ne_zero.2 ht)] with s hs
      simp only [Fnop, kappa, hs, elemIntegrand, h]
  have hgain : elemGain (Xm X T m) g N h = fun t ω => W t ω - 1 := by
    funext t ω
    have hlast : Xm X T m t ω - Xm X T m (min t (g N)) ω = 0 := by
      rw [hgN, ← congrFun (congrFun (stopAt_Xm (X := X) (T := T) (m := m)) t) ω]
      simp [stopAt]
    have hW := Novel.D9FiniteGrid.gridP_sum (π := π) (X := Xm X T m) hg N t ω
    rw [← Novel.D9FiniteGrid.gridWealth_eq_gridP] at hW
    simp only [elemGain, hlast, mul_zero, add_zero]
    rw [show W t ω = _ from hW]
    simp only [add_sub_cancel_left]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Novel.D9FiniteGrid.holding_eq hg (Finset.mem_range.1 hi).le]
    simp only [Standalone.D9FiniteGrid.holding, Xm_pos hX hm _ ω, ite_true, h]
    rfl
  rw [hleft, ← hgain]; exact hel

end Equations

/-! ## The stopped recursion is the recursion on the stopped price -/

theorem minmax_eq {t r a b : ℝ≥0} (har : a ≤ r) :
    min (max (min t r) a) b = min (min (max t a) b) r := by
  rcases le_total t r with h | h
  · have h1 : max t a ≤ r := max_le h har
    rw [min_eq_left h]
    rcases le_total (max t a) b with h2 | h2
    · rw [min_eq_left h2, min_eq_left h1]
    · rw [min_eq_right h2, min_eq_left (h2.trans h1)]
  · rw [min_eq_right h, max_eq_left har]
    have h1 : r ≤ max t a := h.trans (le_max_left t a)
    rcases le_total r b with h2 | h2
    · rw [min_eq_left h2, min_eq_right (le_min h1 h2)]
    · rw [min_eq_right h2, min_eq_right (h2.trans h1), min_eq_left h2]

theorem gridWealth_stop (hX : Setting Q 𝓕 X T) (hm : 1 < m) {π : ℝ} {g : ℕ → ℝ≥0} {N : ℕ}
    (hg : StrictMono g) (t : ℝ≥0) (ω : Ω) :
    gridWealth π X N g (min t (rr X T m ω)) ω = gridWealth π (Xm X T m) N g t ω := by
  unfold gridWealth
  refine Finset.prod_congr rfl fun i _ => ?_
  set r := rr X T m ω with hr
  have hab : g i ≤ g (i + 1) := hg.monotone (Nat.le_succ i)
  have hpos : 0 < X r ω := by
    have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < m := by linarith
    refine lt_of_lt_of_le (by positivity) (mem_Icc_before hX hm ?_).1
    rw [show (r : WithTop ℝ≥0) = rho X T m ω from (rho_eq ω).symm]
    exact min_le_left _ _
  rcases le_or_gt (g i) r with har | hlt
  · simp only [gridFactor, Xm_apply, ← hr, min_eq_left har, minmax_eq har]
  · rw [Novel.D9HoldingPeriod.gridFactor_of_le hab ((min_le_right t r).trans hlt.le)]
    have h1 : min (g i) r = r := min_eq_right hlt.le
    have h2 : min (min (max t (g i)) (g (i + 1))) r = r :=
      min_eq_right (hlt.le.trans (le_min (le_max_right _ _) hab))
    simp only [gridFactor, Xm_apply, ← hr, h1, h2, hpos, ite_true]
    rw [mul_div_assoc, div_self hpos.ne', mul_one]
    ring

/-! ## From almost-sure uniform convergence to ucp -/

/-- For a right-continuous path, `∃ t ≤ T, ε < |D t|` is decided on countably many times. -/
theorem exists_le_iff_rat {D : ℝ≥0 → ℝ} (hD : IsRightContinuous D) (T : ℝ≥0) (ε : ℝ) :
    (∃ t ≤ T, ε < |D t|) ↔
      (ε < |D T|) ∨ ∃ q : ℚ, ((q : ℝ).toNNReal ≤ T ∧ ε < |D (q : ℝ).toNNReal|) := by
  constructor
  · rintro ⟨t, htT, ht⟩
    rcases htT.lt_or_eq with hlt | rfl
    · right
      have hev : ∀ᶠ s in 𝓝[>] t, ε < |D s| ∧ s < T :=
        (((continuous_abs.tendsto _).comp (hD t)).eventually (lt_mem_nhds ht)).and
          (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hlt))
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) < u from hu)
      have hq0 : 0 ≤ (q : ℝ) := t.2.trans hq1.le
      have hmem : (q : ℝ).toNNReal ∈ Ioo t u := by
        constructor
        · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq1
        · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq2
      obtain ⟨h1, h2⟩ := hsub hmem
      exact ⟨q, h2.le, h1⟩
    · left; exact ht
  · rintro (h | ⟨q, hq, h⟩)
    · exact ⟨T, le_rfl, h⟩
    · exact ⟨_, hq, h⟩

theorem measurableSet_exceed {D : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (D t))
    (hrc : ∀ ω, IsRightContinuous fun t => D t ω) (T : ℝ≥0) (ε : ℝ) :
    MeasurableSet {ω | ∃ t ≤ T, ε < |D t ω|} := by
  have : {ω | ∃ t ≤ T, ε < |D t ω|} = {ω | ε < |D T ω|} ∪
      ⋃ q : ℚ, {ω | (q : ℝ).toNNReal ≤ T ∧ ε < |D (q : ℝ).toNNReal ω|} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion]
    exact exists_le_iff_rat (hrc ω) T ε
  rw [this]
  refine (measurableSet_lt measurable_const (continuous_abs.measurable.comp (hm T))).union
    (MeasurableSet.iUnion fun q => ?_)
  by_cases hq : (q : ℝ).toNNReal ≤ T
  · simp only [hq, true_and]
    exact measurableSet_lt measurable_const (continuous_abs.measurable.comp (hm _))
  · simp only [hq, false_and, ofPred_false, MeasurableSet.empty]

/-- Almost-sure uniform convergence on compacts gives ucp convergence. -/
theorem ucp_of_ae [IsFiniteMeasure Q] {D : ℕ → ℝ≥0 → Ω → ℝ} (hm : ∀ n t, Measurable (D n t))
    (hrc : ∀ n ω, IsRightContinuous fun t => D n t ω)
    (h : ∀ᵐ ω ∂Q, ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t ≤ T, |D n t ω| ≤ ε)
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => Q {ω | ∃ t ≤ T, ε < |D n t ω|}) atTop (𝓝 0) := by
  set S : ℕ → Set Ω := fun n => {ω | ∃ t ≤ T, ε < |D n t ω|}
  have hS : ∀ n, MeasurableSet (S n) := fun n => measurableSet_exceed (hm n) (hrc n) T ε
  set B : ℕ → Set Ω := fun n => ⋃ k ≥ n, S k
  have hB : ∀ n, MeasurableSet (B n) := fun n => MeasurableSet.biUnion (to_countable _) fun k _ => hS k
  have hanti : Antitone B := fun a b hab ω hω => by
    simp only [B, mem_iUnion] at hω ⊢
    obtain ⟨k, hk, hω⟩ := hω
    exact ⟨k, hab.trans hk, hω⟩
  have hlim := tendsto_measure_iInter_atTop (μ := Q) (fun n => (hB n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have hnull : Q (⋂ n, B n) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 h)
    simp only [mem_iInter, B, mem_iUnion] at hω
    simp only [mem_ofPred_eq]
    intro hall
    obtain ⟨N, hN⟩ := (hall T ε hε).exists_forall_of_atTop
    obtain ⟨k, hk, t, ht, hlt⟩ := hω N
    exact absurd (hN k hk t ht) (not_le.2 hlt)
  rw [hnull] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => bot_le)
    fun n => measure_mono (subset_biUnion_of_mem (u := S) (le_refl n))

/-! ## Part (4) -/

theorem stoppedProcess_Xm : stoppedProcess (Xm X T m) (rho X T m) = Xm X T m :=
  funext fun t => funext fun ω => by
    simp only [stoppedProcess, min_untopA, Xm_apply, min_assoc, min_self]

theorem stoppedProcess_apply (Z : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess Z (rho X T m) t ω = Z (min t (rr X T m ω)) ω := by
  simp only [stoppedProcess, min_untopA]

section Four

variable {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop} (h14 : AX14 Q 𝓕 Integral Bracket)
  (h11 : AX11 𝓕) (hX : Setting Q 𝓕 X T) (hconst : ∀ t ω, X t ω = X (min t T) ω) (hm : 1 < m)
include h14 h11 hX hconst hm

/-- `Lᵐ` and its bracket are frozen after `ρ_m`, almost surely. -/
theorem LA_stop {L A : ℝ≥0 → Ω → ℝ} (hL : Integral (fun t ω => 1 / Xm X T m t ω) (Xm X T m) L)
    (hA : Bracket L A) :
    ∀ᵐ ω ∂Q, ∀ t, L t ω = L (min t (rr X T m ω)) ω ∧ A t ω = A (min t (rr X T m ω)) ω := by
  have hXm := contLocMart_Xm (m := m) h14 h11 hX hconst
  have hK := integrand_invXm h14 h11 hX hconst hm
  have hLc := h14.integral_contLocMart _ _ _ hX.prob hX.usual hXm hK hL
  have hρ := stopping_rho (m := m) h11 hX
  have h1 := h14.stop_integral _ _ _ _ hX.prob hX.usual hXm hK hρ hL
  rw [stoppedProcess_Xm] at h1
  have hu := h14.integral_unique _ _ _ _ hX.prob hX.usual hXm hK hL h1
  have hb := h14.bracket_congr (h14.stop_bracket L A _ hX.prob hX.usual hLc hρ hA)
    (hu.mono fun ω h t => (h t).symm)
  have hAu := h14.bracket_unique _ _ _ hX.prob hX.usual hLc hA hb
  filter_upwards [hu, hAu] with ω h1 h2 t
  exact ⟨(h1 t).trans (stoppedProcess_apply L t ω), (h2 t).trans (stoppedProcess_apply A t ω)⟩

theorem V_stop {L A : ℝ≥0 → Ω → ℝ} (hL : Integral (fun t ω => 1 / Xm X T m t ω) (Xm X T m) L)
    (hA : Bracket L A) (π : ℝ) :
    ∀ᵐ ω ∂Q, ∀ t, expo π L A t ω = expo π L A (min t (rr X T m ω)) ω := by
  filter_upwards [LA_stop h14 h11 hX hconst hm hL hA] with ω h t
  simp only [expo, (h t).1, (h t).2]

/-- `Fₙ(V) → F(V)` ucp, (10). -/
theorem ucp_FnV {g : ℕ → ℕ → ℝ≥0} {N : ℕ → ℕ} (hgr : Grids T g N) {L A : ℝ≥0 → Ω → ℝ}
    (hL : Integral (fun t ω => 1 / Xm X T m t ω) (Xm X T m) L) (hA : Bracket L A) (π : ℝ) :
    TendstoUCP Q (fun n => Fnop π (Xm X T m) (g n) (N n) (expo π L A))
      (Fop π (Xm X T m) (expo π L A)) := by
  have := hX.prob
  obtain ⟨hVD, hVc, -⟩ := V_solves h14 h11 hX hconst hm hL hA π
  have hXm := contLocMart_Xm (m := m) h14 h11 hX hconst
  have hY0 : ∀ t ω, Xm X T m t ω ≠ 0 := fun t ω => (Xm_pos hX hm t ω).ne'
  intro T' ε hε
  refine ucp_of_ae (D := fun n t ω => Fnop π (Xm X T m) (g n) (N n) (expo π L A) t ω -
      Fop π (Xm X T m) (expo π L A) t ω) (fun n t => ?_) (fun n ω => ?_) ?_ T' hε
  · exact (((mapsD_Fnop (hgr.1 n).2.1 (hgr.1 n).1 hXm.adapted _ hVD).adapted t).mono (𝓕.le t)
      le_rfl).sub (((mapsD_Fop hXm.adapted hXm.cont hY0 _ hVD).adapted t).mono (𝓕.le t) le_rfl)
  · exact ((mapsD_Fnop (hgr.1 n).2.1 (hgr.1 n).1 hXm.adapted _ hVD).cadlag ω).isRightContinuous.sub
      ((mapsD_Fop hXm.adapted hXm.cont hY0 _ hVD).cadlag ω).isRightContinuous
  · filter_upwards [V_stop h14 h11 hX hconst hm hL hA π] with ω hω T'' ε' hε'
    set c : ℝ≥0 → ℝ := fun s => π * expo π L A s ω / Xm X T m s ω
    have hc : Continuous c := (continuous_const.mul (hVc.cont ω)).div (Xm_cont hX ω)
      fun t => hY0 t ω
    obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).uniformContinuousOn_of_continuous
        hc.continuousOn) ε' hε'
    have hcT : ∀ t, T ≤ t → c t = c T := fun t ht => by
      simp only [c, Xm_const t ht]
      rw [hω t, hω T, min_eq_right ((rr_le ω).trans ht), min_eq_right (rr_le ω)]
    filter_upwards [hgr.2 δ hδ] with n hn t _
    obtain ⟨hg0, hg, hgN⟩ := hgr.1 n
    show |c (kappa (g n) (N n) t) - c t| ≤ ε'
    rcases le_total T t with hTt | htT
    · rw [kappa_of_ge hg (hgN.symm ▸ hTt), hgN, hcT t hTt, sub_self, abs_zero]
      exact hε'.le
    · have hk := kappa_le (N := N n) hg0 t
      have hdist : dist (kappa (g n) (N n) t) t < δ := by
        rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hk))]
        by_cases hiN : kap (g n) (N n) t < N n
        · have h1 := lt_next hiN
          have h2 := hn _ hiN
          have : (t : ℝ) < g n (kap (g n) (N n) t + 1) := by exact_mod_cast h1
          simp only [kappa]; linarith
        · have hi : kap (g n) (N n) t = N n := le_antisymm (kap_le t) (not_lt.1 hiN)
          have : kappa (g n) (N n) t = T := by simp only [kappa, hi, hgN]
          rw [this, le_antisymm htT (this ▸ hk)]; simpa using hδ
      have := hunif _ ⟨bot_le, hk.trans htT⟩ t ⟨bot_le, htT⟩ hdist
      rw [Real.dist_eq] at this
      exact this.le

/-- **(4)** in ucp form on every horizon. -/
theorem part4_ucp (h10 : AX10 Q 𝓕 Integral) {g : ℕ → ℕ → ℝ≥0} {N : ℕ → ℕ}
    (hgr : Grids T g N) {L A : ℝ≥0 → Ω → ℝ}
    (hL : Integral (fun t ω => 1 / Xm X T m t ω) (Xm X T m) L) (hA : Bracket L A) (π : ℝ) :
    TendstoUCP Q (fun n => gridWealth π (Xm X T m) (N n) (g n)) (expo π L A) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hXm := contLocMart_Xm (m := m) h14 h11 hX hconst
  have hY0 : ∀ t ω, Xm X T m t ω ≠ 0 := fun t ω => (Xm_pos hX hm t ω).ne'
  have hY1 : ∀ t ω, 1 / (m : ℝ) ≤ Xm X T m t ω := fun t ω => (Xm_mem hX hm t ω).1
  obtain ⟨hVD, -, hVI⟩ := V_solves h14 h11 hX hconst hm hL hA π
  exact h10.stable (Fop π (Xm X T m)) (fun n => Fnop π (Xm X T m) (g n) (N n)) (1 + |π| * m)
    (fun _ _ => 1) (Xm X T m) (expo π L A) (fun n => gridWealth π (Xm X T m) (N n) (g n))
    hX.prob hX.usual (by positivity)
    ⟨mapsD_Fop hXm.adapted hXm.cont hY0, nonanticipating_Fop, lip_Fop hm0 hY1⟩
    (fun n => ⟨mapsD_Fnop (hgr.1 n).2.1 (hgr.1 n).1 hXm.adapted,
      nonanticipating_Fnop (hgr.1 n).1, lip_Fnop hm0 hY1⟩)
    ⟨fun _ => measurable_const, fun _ => IsCadlag.const⟩ hXm hVD hVI
    (fun n => W_solves h14 h11 hX hconst hm (hgr.1 n).2.1 (hgr.1 n).1 (hgr.1 n).2.2 π)
    (ucp_FnV h14 h11 hX hconst hm hgr hL hA π)

omit h14 h11 hconst in
theorem stoppedW_eq {π : ℝ} {g : ℕ → ℕ → ℝ≥0} {N : ℕ → ℕ} (hg : ∀ n, StrictMono (g n)) (n : ℕ)
    (t : ℝ≥0) (ω : Ω) :
    stoppedW π X T m g N n t ω = gridWealth π (Xm X T m) (N n) (g n) t ω := by
  simp only [stoppedW, min_untopA]
  exact gridWealth_stop hX hm (hg n) t ω

end Four

/-! ## (6) and (7) from ucp convergence on `[0, T]` -/

section Consequences

variable [IsProbabilityMeasure Q] {U : ℕ → ℝ≥0 → Ω → ℝ} {V : ℝ≥0 → Ω → ℝ}

theorem measurable_path {Z : ℝ≥0 → Ω → ℝ} (hZ : ∀ t, Measurable (Z t)) :
    Measurable fun ω => fun t : Icc (0 : ℝ≥0) T => Z t.1 ω :=
  measurable_pi_iff.2 fun t => hZ t.1

/-- (6) from ucp convergence on `[0, T]`. -/
theorem pathConv_of_ucp (hUm : ∀ n t, Measurable (U n t)) (hVm : ∀ t, Measurable (V t))
    (hUc : ∀ n ω, Continuous fun t => U n t ω) (hVc : ∀ ω, Continuous fun t => V t ω)
    (hucp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => Q {ω | ∃ t ≤ T, ε < |U n t ω - V t ω|}) atTop
      (𝓝 0)) : PathConv Q T U V := by
  intro G B C hGm hB hL
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB fun _ => 0)
  set φ : ℕ → Ω → ℝ := fun n ω => G fun t => U n t.1 ω
  set ψ : Ω → ℝ := fun ω => G fun t => V t.1 ω
  have hφm : ∀ n, Measurable (φ n) := fun n => hGm.comp (measurable_path (hUm n))
  have hψm : Measurable ψ := hGm.comp (measurable_path hVm)
  have hint : ∀ f : Ω → ℝ, Measurable f → (∀ ω, |f ω| ≤ B) → Integrable f Q := fun f hf hfB =>
    Integrable.of_bound (C := B) hf.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfB ω)
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set η : ℝ := δ / (2 * (|C| + 1))
  have hη : 0 < η := by positivity
  have hCη : (|C| + 1) * η = δ / 2 := by
    simp only [η]; field_simp
  have hS := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hucp η hη)
  simp only [ENNReal.toReal_zero] at hS
  have hev := (Metric.tendsto_atTop.1 hS) (δ / (4 * (B + 1))) (by positivity)
  obtain ⟨n₀, hn₀⟩ := hev
  refine ⟨n₀, fun n hn => ?_⟩
  set Sn := {ω | ∃ t ≤ T, η < |U n t ω - V t ω|}
  have hSn := hn₀ n hn
  simp only [Function.comp_apply, Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
    at hSn
  set M := toMeasurable Q Sn
  have hMm : MeasurableSet M := measurableSet_toMeasurable Q Sn
  have hpt : ∀ ω, |φ n ω - ψ ω| ≤ δ / 2 + 2 * B * M.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ M
    · rw [indicator_of_mem hω]
      have := abs_sub (φ n ω) (ψ ω)
      linarith [hB (fun t => U n t.1 ω), hB (fun t => V t.1 ω)]
    · rw [indicator_of_notMem hω, mul_zero, add_zero]
      have hnot : ω ∉ Sn := fun h => hω (subset_toMeasurable Q Sn h)
      simp only [Sn, mem_ofPred_eq, not_exists, not_and, not_lt] at hnot
      have h1 := hL _ _ ((hUc n ω).comp continuous_subtype_val)
        ((hVc ω).comp continuous_subtype_val) η fun t => hnot t.1 t.2.2
      calc |φ n ω - ψ ω| ≤ C * η := h1
        _ ≤ (|C| + 1) * η := by nlinarith [le_abs_self C]
        _ = δ / 2 := hCη
  have hφi := hint _ (hφm n) fun ω => hB _
  have hψi := hint _ hψm fun ω => hB _
  have hbound : |∫ ω, φ n ω ∂Q - ∫ ω, ψ ω ∂Q| ≤ δ / 2 + 2 * B * (Q Sn).toReal := by
    rw [← integral_sub hφi hψi]
    refine (abs_integral_le_integral_abs).trans ?_
    have hrhs : Integrable (fun ω => δ / 2 + 2 * B * M.indicator (fun _ => (1 : ℝ)) ω) Q :=
      (integrable_const _).add ((integrable_const 1).indicator hMm |>.const_mul _)
    refine (integral_mono ((hφi.sub hψi).abs) hrhs hpt).trans (le_of_eq ?_)
    rw [integral_add (integrable_const _) ((integrable_const 1).indicator hMm |>.const_mul _),
      integral_const_mul, integral_indicator hMm, setIntegral_const, smul_eq_mul, mul_one,
      integral_const, smul_eq_mul]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_mul, M, measure_toMeasurable]
  rw [Real.dist_eq]
  calc |∫ ω, φ n ω ∂Q - ∫ ω, ψ ω ∂Q| ≤ δ / 2 + 2 * B * (Q Sn).toReal := hbound
    _ ≤ δ / 2 + 2 * B * (δ / (4 * (B + 1))) := by gcongr
    _ < δ := by
      have : 2 * B * (δ / (4 * (B + 1))) < δ / 2 := by
        rw [show 2 * B * (δ / (4 * (B + 1))) = δ / 2 * (B / (B + 1)) by field_simp; ring]
        exact mul_lt_of_lt_one_right (by positivity) ((div_lt_one (by positivity)).2 (by linarith))
      linarith

/-- (7) from ucp convergence on `[0, T]`, under uniform integrability. -/
theorem uiConv_of_ucp (hVi : Integrable (V T) Q)
    (hucp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => Q {ω | ∃ t ≤ T, ε < |U n t ω - V t ω|}) atTop
      (𝓝 0)) : UIConv Q T U V := by
  intro hUI
  have hUint : ∀ n, Integrable (U n T) Q := fun n => memLp_one_iff_integrable.1 (hUI.memLp n)
  have hmeas : TendstoInMeasure Q (fun n ω => U n T ω) atTop (V T) := by
    refine tendstoInMeasure_of_ne_top fun ε hε hεt => ?_
    have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hucp _ (half_pos hε'))
      (fun n => bot_le) fun n => measure_mono fun ω (hω : ε ≤ edist _ _) => ?_
    rw [edist_dist, Real.dist_eq] at hω
    exact ⟨T, le_rfl, (half_lt_self hε').trans_le
      (ENNReal.toReal_le_of_le_ofReal (abs_nonneg _) hω)⟩
  have hL1 := tendsto_Lp_finite_of_tendstoInMeasure (le_refl (1 : ℝ≥0∞)) ENNReal.one_ne_top
    (fun n => (hUint n).aestronglyMeasurable) (memLp_one_iff_integrable.2 hVi) hUI.unifIntegrable hmeas
  have heq : ∀ n, ∫ ω, |U n T ω - V T ω| ∂Q = (eLpNorm (U n T - V T) 1 Q).toReal :=
    fun n => by
      have h := ofReal_integral_norm_eq_lintegral_enorm ((hUint n).sub hVi)
      rw [eLpNorm_one_eq_lintegral_enorm, ← h,
        ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]
      · rfl
      · exact ((hUint n).sub hVi).aestronglyMeasurable
  have h1 : Tendsto (fun n => ∫ ω, |U n T ω - V T ω| ∂Q) atTop (𝓝 0) := by
    simp only [heq]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1
    simpa [Function.comp_def] using this
  refine ⟨h1, ?_⟩
  have h2 : Tendsto (fun n => ∫ ω, U n T ω ∂Q) atTop (𝓝 (∫ ω, V T ω ∂Q)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h1
    rw [Real.norm_eq_abs, ← integral_sub (hUint n) hVi]
    exact abs_integral_le_integral_abs
  exact tendsto_const_nhds.sub h2

end Consequences

/-! ## Entering an open set before `T` -/

theorem exists_le_iff_rat_open {D : ℝ≥0 → ℝ} (hD : IsRightContinuous D) {U : Set ℝ}
    (hU : IsOpen U) (T : ℝ≥0) :
    (∃ t ≤ T, D t ∈ U) ↔ D T ∈ U ∨ ∃ q : ℚ, ((q : ℝ).toNNReal ≤ T ∧ D (q : ℝ).toNNReal ∈ U) := by
  constructor
  · rintro ⟨t, htT, ht⟩
    rcases htT.lt_or_eq with hlt | rfl
    · right
      have hev : ∀ᶠ s in 𝓝[>] t, D s ∈ U ∧ s < T :=
        ((hD t).eventually (hU.mem_nhds ht)).and
          (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hlt))
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) < u from hu)
      have hq0 : 0 ≤ (q : ℝ) := t.2.trans hq1.le
      have hmem : (q : ℝ).toNNReal ∈ Ioo t u := by
        constructor
        · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq1
        · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq2
      obtain ⟨h1, h2⟩ := hsub hmem
      exact ⟨q, h2.le, h1⟩
    · left; exact ht
  · rintro (h | ⟨q, hq, h⟩)
    · exact ⟨T, le_rfl, h⟩
    · exact ⟨_, hq, h⟩

theorem measurableSet_enter {D : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (D t))
    (hrc : ∀ ω, IsRightContinuous fun t => D t ω) {U : Set ℝ} (hU : IsOpen U) (T : ℝ≥0) :
    MeasurableSet {ω | ∃ t ≤ T, D t ω ∈ U} := by
  have : {ω | ∃ t ≤ T, D t ω ∈ U} = {ω | D T ω ∈ U} ∪
      ⋃ q : ℚ, {ω | (q : ℝ).toNNReal ≤ T ∧ D (q : ℝ).toNNReal ω ∈ U} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion]
    exact exists_le_iff_rat_open (hrc ω) hU T
  rw [this]
  refine (hm T hU.measurableSet).union (MeasurableSet.iUnion fun q => ?_)
  by_cases hq : (q : ℝ).toNNReal ≤ T
  · simp only [hq, true_and]; exact hm _ hU.measurableSet
  · simp only [hq, false_and, ofPred_false, MeasurableSet.empty]

/-! ## Part (5): removing the price stop under strict positivity -/

theorem progressive_comp {u : ℝ≥0 → Ω → ℝ} (hu : IsStronglyProgressive 𝓕 u) {f : ℝ → ℝ}
    (hf : Measurable f) : IsStronglyProgressive 𝓕 (fun t ω => f (u t ω)) := fun i =>
  (hf.comp (hu i).measurable).stronglyMeasurable

theorem progressive_X (hX : Setting Q 𝓕 X T) : IsStronglyProgressive 𝓕 X :=
  StronglyAdapted.isStronglyProgressive_of_continuous (fun t => (hX.adapted t).stronglyMeasurable)
    hX.cont

/-- A positive continuous path on `[0, T]` has a positive minimum there. -/
theorem exists_min_pos {f : ℝ≥0 → ℝ} (hf : Continuous f) (hpos : ∀ t ≤ T, 0 < f t) :
    ∃ a, 0 < a ∧ ∀ t ≤ T, a ≤ f t := by
  obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_isMinOn
    ⟨0, bot_le, bot_le⟩ hf.continuousOn
  exact ⟨f t₀, hpos t₀ ht₀.2, fun t ht => hmin ⟨bot_le, ht⟩⟩

theorem integrand_invX (hX : Setting Q 𝓕 X T) (hconst : ∀ t ω, X t ω = X (min t T) ω)
    (hpos : ∀ᵐ ω ∂Q, ∀ t ≤ T, 0 < X t ω) : Integrand Q 𝓕 (fun t ω => 1 / X t ω) := by
  refine ⟨progressive_comp (progressive_X hX) (measurable_const.div measurable_id), ?_⟩
  filter_upwards [hpos] with ω hω T'
  obtain ⟨a, ha, hmin⟩ := exists_min_pos (hX.cont ω) hω
  refine ⟨1 / a, fun t _ => ?_⟩
  have h1 : a ≤ X t ω := by rw [hconst]; exact hmin _ (min_le_right _ _)
  rw [abs_of_pos (one_div_pos.2 (ha.trans_le h1))]
  exact one_div_le_one_div_of_le ha h1

section Five

variable {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop} (h14 : AX14 Q 𝓕 Integral Bracket)
  (h11 : AX11 𝓕) (hX : Setting Q 𝓕 X T) (hconst : ∀ t ω, X t ω = X (min t T) ω)
  (hpos : ∀ᵐ ω ∂Q, ∀ t ≤ T, 0 < X t ω)
include h14 h11 hX hconst hpos

/-- The stopped exponent is the global one stopped at `ρ_m`. -/
theorem LA_relate (hm : 1 < m) {L A Lm Am : ℝ≥0 → Ω → ℝ}
    (hL : Integral (fun t ω => 1 / X t ω) X L) (hA : Bracket L A)
    (hLm : Integral (fun t ω => 1 / Xm X T m t ω) (Xm X T m) Lm) (hAm : Bracket Lm Am) :
    ∀ᵐ ω ∂Q, ∀ t, Lm t ω = L (min t (rr X T m ω)) ω ∧ Am t ω = A (min t (rr X T m ω)) ω := by
  have hXc := contLocMart_X hX hconst
  have hXm := contLocMart_Xm (m := m) h14 h11 hX hconst
  have hK := integrand_invX hX hconst hpos
  have hKm := integrand_invXm h14 h11 hX hconst hm
  have hρ := stopping_rho (m := m) h11 hX
  have hLc := h14.integral_contLocMart _ _ _ hX.prob hX.usual hXc hK hL
  have hLmc := h14.integral_contLocMart _ _ _ hX.prob hX.usual hXm hKm hLm
  have h1 := h14.stop_integral _ _ _ _ hX.prob hX.usual hXc hK hρ hL
  have hagree : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ rho X T m ω →
      1 / X t ω = 1 / Xm X T m t ω := fun ω t ht => by
    rw [Xm_apply, min_eq_left]
    rw [rho_eq] at ht; exact WithTop.coe_le_coe.1 ht
  have hloc := h14.stop_local _ _ _ _ _ _ hX.prob hX.usual hXm hK hKm hρ hagree h1 hLm
  have hfr := LA_stop h14 h11 hX hconst hm hLm hAm
  have hLL : ∀ᵐ ω ∂Q, ∀ t, Lm t ω = L (min t (rr X T m ω)) ω := by
    filter_upwards [hloc, hfr] with ω h1 h2 t
    have hr : ((rr X T m ω : ℝ≥0) : WithTop ℝ≥0) ≤ rho X T m ω := (rho_eq ω).symm ▸ le_rfl
    have key : ∀ s ≤ rr X T m ω, Lm s ω = L s ω := fun s hs => by
      have := h1 s ((WithTop.coe_le_coe.2 hs).trans hr)
      rw [stoppedProcess_apply, min_eq_left hs] at this
      exact this.symm
    rw [(h2 t).1, key _ (min_le_right _ _)]
  have hb := h14.bracket_congr (h14.stop_bracket L A _ hX.prob hX.usual hLc hρ hA)
    (hLL.mono fun ω h t => ((stoppedProcess_apply L t ω).trans (h t).symm))
  have hAu := h14.bracket_unique _ _ _ hX.prob hX.usual hLmc hAm hb
  filter_upwards [hLL, hAu] with ω h1 h2 t
  exact ⟨h1 t, (h2 t).trans (stoppedProcess_apply A t ω)⟩

end Five

theorem band_anti {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : band b ⊆ band a := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  rintro x (h | h)
  · exact Or.inl (h.trans_le (one_div_le_one_div_of_le ha' hab'))
  · exact Or.inr (hab'.trans_lt h)

theorem rr_eq_T_of {ω : Ω} (h : ¬ ∃ s ≤ T, X s ω ∈ band m) : rr X T m ω = T := by
  have hhit : (T : WithTop ℝ≥0) ≤ openHitTime X (band m) ω := by
    refine le_sInf ?_
    rintro _ ⟨s, hs, rfl⟩
    by_contra hlt
    exact h ⟨s, (WithTop.coe_lt_coe.1 (not_le.1 hlt)).le, hs⟩
  simp only [rr, rho, min_eq_right hhit, untopA_coe]

section FiveB

variable {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop} (h14 : AX14 Q 𝓕 Integral Bracket)
  (h10 : AX10 Q 𝓕 Integral) (h11 : AX11 𝓕) (hX : Setting Q 𝓕 X T)
  (hconst : ∀ t ω, X t ω = X (min t T) ω) (hpos : ∀ᵐ ω ∂Q, ∀ t ≤ T, 0 < X t ω)
include h14 h10 h11 hX hconst hpos

/-- **(5)**: the unstopped recursion converges ucp on `[0, T]`. -/
theorem part5_ucp {g : ℕ → ℕ → ℝ≥0} {N : ℕ → ℕ} (hgr : Grids T g N) {L A : ℝ≥0 → Ω → ℝ}
    (hL : Integral (fun t ω => 1 / X t ω) X L) (hA : Bracket L A) (π : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => Q {ω | ∃ t ≤ T,
      ε < |gridWealth π X (N n) (g n) t ω - expo π L A t ω|}) atTop (𝓝 0) := by
  have := hX.prob
  set E : ℕ → Set Ω := fun k => {ω | ∃ s ≤ T, X s ω ∈ band (k + 2)}
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    measurableSet_enter (fun t => (hX.adapted t).mono (𝓕.le t) le_rfl)
      (fun ω => (hX.cont ω).isRightContinuous) (isOpen_band _) T
  have hEanti : Antitone E := fun a b hab ω ⟨s, hs, hx⟩ =>
    ⟨s, hs, band_anti (by omega) (by omega) hx⟩
  have hEnull : Q (⋂ k, E k) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hpos)
    simp only [mem_ofPred_eq]
    intro hgood
    simp only [mem_iInter, E, mem_ofPred_eq] at hω
    obtain ⟨a, ha, hmin⟩ := exists_min_pos (hX.cont ω) hgood
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      (hX.cont ω).continuousOn
    obtain ⟨k, hk⟩ := exists_nat_gt (max C (1 / a))
    obtain ⟨s, hs, hx⟩ := hω k
    have hk2 : (max C (1 / a)) < (k + 2 : ℕ) := by push_cast; linarith
    rcases hx with h | h
    · have h1 : 1 / ((k + 2 : ℕ) : ℝ) < a := by
        have h3 : 1 / a < ((k + 2 : ℕ) : ℝ) := (le_max_right C (1 / a)).trans_lt hk2
        rw [div_lt_iff₀ ha] at h3
        rw [div_lt_iff₀ (by positivity)]
        linarith
      linarith [hmin s hs]
    · have := hC s ⟨bot_le, hs⟩
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (X s ω), (le_max_left C (1 / a)).trans_lt hk2]
  have hElim := tendsto_measure_iInter_atTop (μ := Q) (fun k => (hEm k).nullMeasurableSet) hEanti
    ⟨0, measure_ne_top _ _⟩
  rw [hEnull] at hElim
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨k, hk⟩ := ((ENNReal.tendsto_nhds_zero.1 hElim) (δ / 2)
    (ENNReal.half_pos hδ.ne')).exists
  set m := k + 2
  have hm : 1 < m := by omega
  have hXm := contLocMart_Xm (m := m) h14 h11 hX hconst
  have hKm := integrand_invXm h14 h11 hX hconst hm
  obtain ⟨Lm, hLm⟩ := h14.integral_exists _ _ hX.prob hX.usual hXm hKm
  obtain ⟨Am, hAm⟩ := h14.bracket_exists _ hX.prob hX.usual
    (h14.integral_contLocMart _ _ _ hX.prob hX.usual hXm hKm hLm)
  have hrel := LA_relate h14 h11 hX hconst hpos hm hL hA hLm hAm
  have h4 := part4_ucp h14 h11 hX hconst hm h10 hgr hLm hAm π T ε hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 h4) (δ / 2) (ENNReal.half_pos hδ.ne')] with n hn
  set Nset := {ω | ¬ ∀ t, Lm t ω = L (min t (rr X T m ω)) ω ∧ Am t ω = A (min t (rr X T m ω)) ω}
  have hN : Q Nset = 0 := ae_iff.1 hrel
  calc Q {ω | ∃ t ≤ T, ε < |gridWealth π X (N n) (g n) t ω - expo π L A t ω|}
      ≤ Q (E k ∪ {ω | ∃ t ≤ T, ε < |gridWealth π (Xm X T m) (N n) (g n) t ω -
          expo π Lm Am t ω|} ∪ Nset) := by
        refine measure_mono fun ω ⟨t, ht, hε'⟩ => ?_
        by_cases hE : ω ∈ E k
        · exact Or.inl (Or.inl hE)
        by_cases hNs : ω ∈ Nset
        · exact Or.inr hNs
        refine Or.inl (Or.inr ⟨t, ht, ?_⟩)
        have hrr : rr X T m ω = T := rr_eq_T_of hE
        simp only [Nset, mem_ofPred_eq, not_not] at hNs
        have hW : gridWealth π (Xm X T m) (N n) (g n) t ω = gridWealth π X (N n) (g n) t ω := by
          rw [← gridWealth_stop hX hm ((hgr.1 n).2.1), hrr, min_eq_left ht]
        have hV : expo π Lm Am t ω = expo π L A t ω := by
          simp only [expo, (hNs t).1, (hNs t).2, hrr, min_eq_left ht]
        rw [hW, hV]; exact hε'
    _ ≤ Q (E k) + Q {ω | ∃ t ≤ T, ε < |gridWealth π (Xm X T m) (N n) (g n) t ω -
          expo π Lm Am t ω|} + Q Nset :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ δ / 2 + δ / 2 + 0 := by rw [hN]; exact add_le_add (add_le_add hk hn) le_rfl
    _ = δ := by rw [add_zero, ENNReal.add_halves]

/-- The breach limit: `Q(inf_{t≤T} W⁽ⁿ⁾_t ≤ 0) → 0`. -/
theorem part5_breach {g : ℕ → ℕ → ℝ≥0} {N : ℕ → ℕ} (hgr : Grids T g N) {L A : ℝ≥0 → Ω → ℝ}
    (hL : Integral (fun t ω => 1 / X t ω) X L) (hA : Bracket L A) (π : ℝ) :
    Tendsto (fun n => Q {ω | ∃ t ≤ T, gridWealth π X (N n) (g n) t ω ≤ 0}) atTop (𝓝 0) := by
  have := hX.prob
  have hXc := contLocMart_X hX hconst
  have hK := integrand_invX hX hconst hpos
  have hLc := h14.integral_contLocMart _ _ _ hX.prob hX.usual hXc hK hL
  obtain ⟨hAad, -, hAc, -⟩ := h14.bracket_conventions hA
  set V := expo π L A
  have hVc : ∀ ω, Continuous fun t => V t ω := fun ω =>
    Real.continuous_exp.comp ((continuous_const.mul (hLc.cont ω)).sub
      (continuous_const.mul (hAc ω)))
  have hVm : ∀ t, Measurable (V t) := fun t =>
    Real.measurable_exp.comp ((measurable_const.mul ((hLc.adapted t).mono (𝓕.le t) le_rfl)).sub
      (measurable_const.mul ((hAad t).mono (𝓕.le t) le_rfl)))
  set Z : ℕ → Set Ω := fun k => {ω | ∃ t ≤ T, V t ω ∈ Iio (1 / ((k : ℝ) + 1))}
  have hZm : ∀ k, MeasurableSet (Z k) := fun k =>
    measurableSet_enter hVm (fun ω => (hVc ω).isRightContinuous) isOpen_Iio T
  have hZanti : Antitone Z := fun a b hab ω ⟨t, ht, hx⟩ => ⟨t, ht, lt_of_lt_of_le hx
    (one_div_le_one_div_of_le (show (0 : ℝ) < (a : ℝ) + 1 by positivity)
      (by exact_mod_cast Nat.add_le_add_right hab 1))⟩
  have hZempty : (⋂ k, Z k) = ∅ := by
    refine eq_empty_of_forall_notMem fun ω hω => ?_
    simp only [mem_iInter, Z, mem_ofPred_eq, mem_Iio] at hω
    obtain ⟨a, ha, hmin⟩ := exists_min_pos (hVc ω) fun t _ => Real.exp_pos _
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt ha
    obtain ⟨t, ht, hlt⟩ := hω k
    linarith [hmin t ht]
  have hZlim := tendsto_measure_iInter_atTop (μ := Q) (fun k => (hZm k).nullMeasurableSet) hZanti
    ⟨0, measure_ne_top _ _⟩
  rw [hZempty, measure_empty] at hZlim
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨k, hk⟩ := ((ENNReal.tendsto_nhds_zero.1 hZlim) (δ / 2)
    (ENNReal.half_pos hδ.ne')).exists
  have hε : (0 : ℝ) < 1 / (2 * ((k : ℝ) + 1)) := by positivity
  have h5 := part5_ucp h14 h10 h11 hX hconst hpos hgr hL hA π hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 h5) (δ / 2) (ENNReal.half_pos hδ.ne')] with n hn
  calc Q {ω | ∃ t ≤ T, gridWealth π X (N n) (g n) t ω ≤ 0}
      ≤ Q (Z k ∪ {ω | ∃ t ≤ T, 1 / (2 * ((k : ℝ) + 1)) <
          |gridWealth π X (N n) (g n) t ω - V t ω|}) := by
        refine measure_mono fun ω ⟨t, ht, hW⟩ => ?_
        by_cases hv : V t ω < 1 / ((k : ℝ) + 1)
        · exact Or.inl ⟨t, ht, hv⟩
        · refine Or.inr ⟨t, ht, ?_⟩
          push Not at hv
          have h2 : 1 / (2 * ((k : ℝ) + 1)) < 1 / ((k : ℝ) + 1) := by
            rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
          rw [abs_sub_comm]
          exact h2.trans_le (hv.trans (by rw [abs_of_nonneg (by linarith)]; linarith))
    _ ≤ Q (Z k) + Q {ω | ∃ t ≤ T, 1 / (2 * ((k : ℝ) + 1)) <
          |gridWealth π X (N n) (g n) t ω - V t ω|} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hk hn
    _ = δ := ENNReal.add_halves δ

end FiveB

/-! ## The D1 identification -/

theorem integrand_const (c : ℝ) : Integrand Q 𝓕 (fun _ _ => c) :=
  integrand_of_cont (fun _ => measurable_const) fun _ => continuous_const

theorem integrand_mul {H K : ℝ≥0 → Ω → ℝ} (hH : Integrand Q 𝓕 H) (hK : Integrand Q 𝓕 K) :
    Integrand Q 𝓕 (fun t ω => H t ω * K t ω) := by
  refine ⟨fun i => (hH.progressive i).mul (hK.progressive i), ?_⟩
  filter_upwards [hH.locBdd, hK.locBdd] with ω h1 h2 T'
  obtain ⟨C₁, hC₁⟩ := h1 T'
  obtain ⟨C₂, hC₂⟩ := h2 T'
  exact ⟨C₁ * C₂, fun t ht => by
    rw [abs_mul]
    exact mul_le_mul (hC₁ t ht) (hC₂ t ht) (abs_nonneg _) ((abs_nonneg _).trans (hC₁ t ht))⟩

/-- The grid `i ↦ i` used for constant elementary integrands. -/
theorem natGrid_strictMono : StrictMono fun i : ℕ => (i : ℝ≥0) := Nat.strictMono_cast

section D1

variable {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop} (h14 : AX14 Q 𝓕 Integral Bracket)
  (hX : Setting Q 𝓕 X T) (hconst : ∀ t ω, X t ω = X (min t T) ω)
  (hpos : ∀ᵐ ω ∂Q, ∀ t ≤ T, 0 < X t ω)
include h14 hX hconst hpos

omit hconst hpos in
/-- A constant holding `c` against a continuous local martingale `M` integrates to `c (M − M₀)`. -/
theorem integral_const {M : ℝ≥0 → Ω → ℝ} (hM : ContLocMart Q 𝓕 M) (c : ℝ) :
    Integral (fun _ _ => c) M (fun t ω => c * (M t ω - M 0 ω)) := by
  have h := h14.elementary M (fun i => (i : ℝ≥0)) 0 (fun _ _ => c) hX.prob hX.usual hM
    natGrid_strictMono (by simp) fun _ _ => measurable_const
  have h1 : elemIntegrand (fun i : ℕ => (i : ℝ≥0)) 0 (fun _ _ => c) = fun (_ : ℝ≥0) (_ : Ω) => c := by
    funext t ω; simp [elemIntegrand]
  have h2 : elemGain M (fun i : ℕ => (i : ℝ≥0)) 0 (fun _ _ => c) =
      fun t ω => c * (M t ω - M 0 ω) := by
    funext t ω; simp [elemGain]
  rw [h1, h2] at h; exact h

/-- **D1 identification.** Under `X − 1 = ∫ σ(X) 1_{[0,T]} dW` with `⟨W⟩_t = t` and `σ` Borel and
locally bounded on `(0, ∞)`, the exponent of `exp(πL − π²⟨L⟩/2)` is
`∫ b_π(X) 1_{[0,T]} dW − ½ ∫₀ᵗ (b_π(X) 1_{[0,T]})² ds`, with `b_π(x) = πσ(x)/x`. -/
theorem d1_identification {L A : ℝ≥0 → Ω → ℝ} (hL : Integral (fun t ω => 1 / X t ω) X L)
    (hA : Bracket L A) (π : ℝ) (σ : ℝ → ℝ) (Wb : ℝ≥0 → Ω → ℝ) (hσm : Measurable σ)
    (hσloc : ∀ a b : ℝ, 0 < a → ∃ C, ∀ x ∈ Icc a b, |σ x| ≤ C) (hWb : ContLocMart Q 𝓕 Wb)
    (hbr : Bracket Wb (fun t _ => (t : ℝ)))
    (hdX : Integral (fun t ω => if t ≤ T then σ (X t ω) else 0) Wb (fun t ω => X t ω - 1)) :
    (∃ J, Integral (fun t ω => if t ≤ T then bPi π σ (X t ω) else 0) Wb J ∧
      ∀ᵐ ω ∂Q, ∀ t, J t ω = π * L t ω) ∧
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, π ^ 2 * A t ω = ∫ s in (0 : ℝ)..(t : ℝ),
      (if s.toNNReal ≤ T then bPi π σ (X s.toNNReal ω) else 0) ^ 2 := by
  have := hX.prob
  have hXc := contLocMart_X hX hconst
  have hK := integrand_invX hX hconst hpos
  -- `X − 1` is a continuous local martingale.
  have hX1 : ContLocMart Q 𝓕 (fun t ω => X t ω - 1) := by
    refine ⟨fun t => (hX.adapted t).sub measurable_const, fun ω => (hX.cont ω).sub continuous_const,
      ?_⟩
    have h := Novel.D9FiniteGrid.isLocalMartingale_const_add hXc.localMart (-1)
    have heq : (fun t ω => -1 + X t ω) = fun t ω => X t ω - 1 := by funext t ω; ring
    rwa [heq] at h
  -- `∫ (1/X) d(X − 1)` agrees with `L`.
  obtain ⟨L', hL'⟩ := h14.integral_exists _ _ hX.prob hX.usual hX1 hK
  have hone : Integral (fun _ _ => (1 : ℝ)) X (fun t ω => X t ω - 1) := by
    have h := integral_const h14 hX hXc 1
    have heq : (fun t ω => (1 : ℝ) * (X t ω - X 0 ω)) = fun t ω => X t ω - 1 := by
      funext t ω; rw [hX.start]; ring
    rwa [heq] at h
  have hLL' : ∀ᵐ ω ∂Q, ∀ t, L t ω = L' t ω := by
    have h := h14.assoc _ _ _ _ _ hX.prob hX.usual hXc (integrand_const 1) hK hone hL'
    have heq : (fun t ω => 1 / X t ω * (1 : ℝ)) = fun t ω => 1 / X t ω := by funext t ω; ring
    rw [heq] at h
    exact h14.integral_unique _ _ _ _ hX.prob hX.usual hXc hK hL h
  -- The integrand `σ(X) 1_{[0,T]}` is admissible.
  have hK1 : Integrand Q 𝓕 (fun t ω => if t ≤ T then σ (X t ω) else 0) := by
    refine ⟨fun i => ?_, ?_⟩
    · exact (Measurable.ite (measurableSet_le (measurable_subtype_coe.comp measurable_fst)
        measurable_const) (hσm.comp ((progressive_X hX) i).measurable)
        measurable_const).stronglyMeasurable
    · filter_upwards [hpos] with ω hω T'
      obtain ⟨a, ha, hmin⟩ := exists_min_pos (hX.cont ω) hω
      obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
        (hX.cont ω).continuousOn
      obtain ⟨C, hC⟩ := hσloc a B ha
      refine ⟨|C|, fun t _ => ?_⟩
      split_ifs with htT
      · have hb := hB t ⟨bot_le, htT⟩
        rw [Real.norm_eq_abs] at hb
        exact (hC _ ⟨hmin t htT, (le_abs_self _).trans hb⟩).trans (le_abs_self C)
      · simp
  have hKK := integrand_mul hK hK1
  have hL'c := h14.integral_contLocMart _ _ _ hX.prob hX.usual hX1 hK hL'
  -- Associativity in `dX = σ(X) dW`.
  have hW1 := h14.assoc _ _ _ _ _ hX.prob hX.usual hWb hK1 hK hdX hL'
  refine ⟨⟨fun t ω => π * L' t ω, ?_, ?_⟩, ?_⟩
  · have h2 := integral_const h14 hX hL'c π
    have heq : (fun t ω => π * (L' t ω - L' 0 ω)) = fun t ω => π * L' t ω := by
      funext t ω; rw [h14.integral_zero hL' ω, sub_zero]
    rw [heq] at h2
    have h3 := h14.assoc _ _ _ _ _ hX.prob hX.usual hWb hKK (integrand_const π) hW1 h2
    have heq2 : (fun t ω => π * (1 / X t ω * (if t ≤ T then σ (X t ω) else 0))) =
        fun t ω => if t ≤ T then bPi π σ (X t ω) else 0 := by
      funext t ω
      split_ifs <;> (try simp only [bPi]) <;> ring
    rwa [heq2] at h3
  · filter_upwards [hLL'] with ω h t
    rw [h t]
  · have hb1 : Bracket Wb (fun (t : ℝ≥0) (ω : Ω) =>
        ∫ s in (0 : ℝ)..(t : ℝ), (fun (_ : ℝ≥0) (_ : Ω) => (1 : ℝ)) s.toNNReal ω) := by
      have heq : (fun (t : ℝ≥0) (_ : Ω) => (t : ℝ)) = fun (t : ℝ≥0) (ω : Ω) =>
          ∫ s in (0 : ℝ)..(t : ℝ), (fun (_ : ℝ≥0) (_ : Ω) => (1 : ℝ)) s.toNNReal ω := by
        funext t ω; simp
      rw [← heq]; exact hbr
    obtain ⟨A', hA', hA'eq⟩ := h14.bracket_density _ _ _ _ hX.prob hX.usual hWb hKK
      (fun _ => continuous_const) (fun _ _ => zero_le_one) hb1 hW1
    have hAA := h14.bracket_unique _ _ _ hX.prob hX.usual hL'c (h14.bracket_congr hA hLL') hA'
    filter_upwards [hAA, hA'eq] with ω h1 h2 t
    rw [h1 t, h2 t, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    split_ifs <;> (try simp only [bPi]) <;> ring

end D1

/-! ## The statement -/

/-- The limiting exponential is a nonnegative continuous local martingale started at one, so AX-06
makes its terminal value integrable. -/
theorem expo_integrable (h06 : AX06.{u}) (hX : Setting Q 𝓕 X T) {L A : ℝ≥0 → Ω → ℝ}
    (hc : ContLocMart Q 𝓕 (expo π L A)) (hL0 : ∀ ω, L 0 ω = 0) (hA0 : ∀ ω, A 0 ω = 0) :
    Integrable (expo π L A T) Q :=
  (h06 Ω mΩ Q 𝓕 _ 1 hX.prob hX.usual.1 hc.adapted hc.cont
    (fun ω => by simp [expo, hL0 ω, hA0 ω]) one_pos hc.localMart
    fun t ω => (Real.exp_pos _).le).integrable T

theorem statement_holds : Standalone.D9Refinement.statement.{u} := by
  intro h06 Ω mΩ Q 𝓕 Integral Bracket h14 h10 h11 X T g N π hX hT hconst hgr
  have := hX.prob
  refine ⟨fun m hm => ?_, fun hpos => ?_⟩
  · have hXm := contLocMart_Xm (m := m) h14 h11 hX hconst
    have hKm := integrand_invXm h14 h11 hX hconst hm
    have hS := setting_Xm h14 h11 hX hconst hm
    refine ⟨stopping_rho h11 hX, fun t ω => Xm_mem hX hm t ω, ?_, fun L A hL hA => ?_⟩
    · obtain ⟨L, hL⟩ := h14.integral_exists _ _ hX.prob hX.usual hXm hKm
      obtain ⟨A, hA⟩ := h14.bracket_exists _ hX.prob hX.usual
        (h14.integral_contLocMart _ _ _ hX.prob hX.usual hXm hKm hL)
      exact ⟨L, A, hL, hA⟩
    have hU : stoppedW π X T m g N = fun n => gridWealth π (Xm X T m) (N n) (g n) :=
      funext fun n => funext fun t => funext fun ω => stoppedW_eq hX hm (fun n => (hgr.1 n).2.1) n t ω
    obtain ⟨hVD, hVc, -⟩ := V_solves h14 h11 hX hconst hm hL hA π
    have hucp := part4_ucp h14 h11 hX hconst hm h10 hgr hL hA π
    have hT' : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => Q {ω | ∃ t ≤ T,
        ε < |gridWealth π (Xm X T m) (N n) (g n) t ω - expo π L A t ω|}) atTop (𝓝 0) :=
      fun ε hε => hucp T ε hε
    rw [hU]
    refine ⟨hT', pathConv_of_ucp (fun n t => ?_) (fun t => (hVD.adapted t).mono (𝓕.le t) le_rfl)
      (fun n ω => Novel.D9FiniteGrid.gridWealth_cont hS ω) hVc.cont hT', uiConv_of_ucp ?_ hT'⟩
    · exact (Novel.D9FiniteGrid.gridWealth_adapted hS (hgr.1 n).2.1 t).mono (𝓕.le t) le_rfl
    · exact expo_integrable h06 hX hVc (h14.integral_zero hL) (h14.bracket_conventions hA).2.1
  · have hXc := contLocMart_X hX hconst
    have hK := integrand_invX hX hconst hpos
    refine ⟨?_, fun L A hL hA => ?_⟩
    · obtain ⟨L, hL⟩ := h14.integral_exists _ _ hX.prob hX.usual hXc hK
      obtain ⟨A, hA⟩ := h14.bracket_exists _ hX.prob hX.usual
        (h14.integral_contLocMart _ _ _ hX.prob hX.usual hXc hK hL)
      exact ⟨L, A, hL, hA⟩
    have hLc := h14.integral_contLocMart _ _ _ hX.prob hX.usual hXc hK hL
    obtain ⟨hVc, -⟩ := h14.exponential L A π hX.prob hX.usual hLc (h14.integral_zero hL) hA
    have hT' : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => Q {ω | ∃ t ≤ T,
        ε < |gridWealth π X (N n) (g n) t ω - expo π L A t ω|}) atTop (𝓝 0) :=
      fun ε hε => part5_ucp h14 h10 h11 hX hconst hpos hgr hL hA π hε
    refine ⟨hT', part5_breach h14 h10 h11 hX hconst hpos hgr hL hA π,
      pathConv_of_ucp (fun n t => ?_) (fun t => (hVc.adapted t).mono (𝓕.le t) le_rfl)
        (fun n ω => Novel.D9FiniteGrid.gridWealth_cont hX ω) hVc.cont hT',
      uiConv_of_ucp (expo_integrable h06 hX hVc (h14.integral_zero hL)
        (h14.bracket_conventions hA).2.1) hT',
      fun σ Wb hσm hσloc hWb hbr hdX =>
        d1_identification h14 hX hconst hpos hL hA π σ Wb hσm hσloc hWb hbr hdX⟩
    exact (Novel.D9FiniteGrid.gridWealth_adapted hX (hgr.1 n).2.1 t).mono (𝓕.le t) le_rfl

/-! ## The cited premises from the hypothesis structures -/

section Bridges

open Upstream.StochasticIntegration in
theorem toU_clm {Z : ℝ≥0 → Ω → ℝ} (h : Standalone.D9Refinement.ContLocMart Q 𝓕 Z) :
    Upstream.StochasticIntegration.ContLocMart Q 𝓕 Z := ⟨h.adapted, h.cont, h.localMart⟩

theorem ofU_clm {Z : ℝ≥0 → Ω → ℝ} (h : Upstream.StochasticIntegration.ContLocMart Q 𝓕 Z) :
    Standalone.D9Refinement.ContLocMart Q 𝓕 Z := ⟨h.adapted, h.cont, h.localMart⟩

theorem toU_int {K : ℝ≥0 → Ω → ℝ} (h : Standalone.D9Refinement.Integrand Q 𝓕 K) :
    Upstream.StochasticIntegration.Integrand Q 𝓕 K := ⟨h.progressive, h.locBdd⟩

theorem toU_isD {Z : ℝ≥0 → Ω → ℝ} (h : Standalone.D9Refinement.IsD 𝓕 Z) :
    Upstream.EmeryStability.IsD 𝓕 Z := ⟨h.adapted, h.cadlag⟩

theorem ofU_isD {Z : ℝ≥0 → Ω → ℝ} (h : Upstream.EmeryStability.IsD 𝓕 Z) :
    Standalone.D9Refinement.IsD 𝓕 Z := ⟨h.adapted, h.cadlag⟩

theorem toU_adm {a : ℝ} {F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ} (h : OpAdmissible Q 𝓕 a F) :
    Upstream.EmeryStability.Admissible Q 𝓕 a F :=
  ⟨fun U hU => toU_isD (h.mapsD U (ofU_isD hU)),
    fun U V τ hU hV hτ hUV => h.nonanticipating U V τ (ofU_isD hU) (ofU_isD hV) hτ hUV,
    fun U V hU hV => h.lip U V (ofU_isD hU) (ofU_isD hV)⟩

/-- `Upstream.StochasticIntegration.IntegralCalculus` gives the restated AX-14 for its
primitives. -/
theorem ax14_of_upstream {P : Upstream.StochasticIntegration.Primitives Q 𝓕}
    (h : Upstream.StochasticIntegration.IntegralCalculus P) : AX14 Q 𝓕 P.Integral P.Bracket where
  integral_zero := P.integral_zero
  bracket_conventions := P.bracket_conventions
  bracket_congr := P.bracket_congr
  integral_exists K X hQ hu hX hK := h.integral_exists K X hQ hu (toU_clm hX) (toU_int hK)
  integral_contLocMart K X L hQ hu hX hK hL :=
    ofU_clm (h.integral_contLocMart K X L hQ hu (toU_clm hX) (toU_int hK) hL)
  integral_unique K X L L' hQ hu hX hK := h.integral_unique K X L L' hQ hu (toU_clm hX) (toU_int hK)
  bracket_exists L hQ hu hL := h.bracket_exists L hQ hu (toU_clm hL)
  bracket_unique L A A' hQ hu hL := h.bracket_unique L A A' hQ hu (toU_clm hL)
  bracket_density K X L b hQ hu hX hK := h.bracket_density K X L b hQ hu (toU_clm hX) (toU_int hK)
  stop_contLocMart X τ hQ hu hX hτ := ofU_clm (h.stop_contLocMart X τ hQ hu (toU_clm hX) hτ)
  stop_integral K X L τ hQ hu hX hK := h.stop_integral K X L τ hQ hu (toU_clm hX) (toU_int hK)
  stop_local K K' X L L' τ hQ hu hX hK hK' :=
    h.stop_local K K' X L L' τ hQ hu (toU_clm hX) (toU_int hK) (toU_int hK')
  stop_bracket L A τ hQ hu hL := h.stop_bracket L A τ hQ hu (toU_clm hL)
  assoc H K X L I hQ hu hX hK hH := h.assoc H K X L I hQ hu (toU_clm hX) (toU_int hK) (toU_int hH)
  exponential L A π hQ hu hL hL0 hA :=
    ⟨ofU_clm (h.exponential L A π hQ hu (toU_clm hL) hL0 hA).1,
      (h.exponential L A π hQ hu (toU_clm hL) hL0 hA).2⟩
  elementary M g N hh hQ hu hM := h.elementary M g N hh hQ hu (toU_clm hM)

/-- `Upstream.EmeryStability` gives the restated AX-10 for the same primitives. -/
theorem ax10_of_upstream {P : Upstream.StochasticIntegration.Primitives Q 𝓕}
    (h : Upstream.EmeryStability P) : AX10 Q 𝓕 P.Integral where
  exists_solution F a H M hQ hu ha hF hH hM := by
    obtain ⟨U, hU, hI⟩ := h.exists_solution F a H M hQ hu ha (toU_adm hF) (toU_isD hH) (toU_clm hM)
    exact ⟨U, ofU_isD hU, hI⟩
  unique_solution F a H M U U' hQ hu ha hF hH hM hU hU' :=
    h.unique_solution F a H M U U' hQ hu ha (toU_adm hF) (toU_isD hH) (toU_clm hM) (toU_isD hU)
      (toU_isD hU')
  stable F Fn a H M U Un hQ hu ha hF hFn hH hM hU hUI hUn :=
    h.stable F Fn a H M U Un hQ hu ha (toU_adm hF) (fun n => toU_adm (hFn n)) (toU_isD hH)
      (toU_clm hM) (toU_isD hU) hUI (fun n => ⟨toU_isD (hUn n).1, (hUn n).2⟩)

/-- `Upstream.ContinuousHittingTimes` gives the restated AX-11. -/
theorem ax11_of_upstream (h : Upstream.ContinuousHittingTimes 𝓕) : AX11 𝓕 :=
  fun S hrc ha hc Γ hΓ => h.hit_open hrc S ha hc Γ hΓ

end Bridges

end Novel.D9Refinement
