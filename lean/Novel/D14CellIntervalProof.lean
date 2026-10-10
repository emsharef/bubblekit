import Standalone.D14CellSubdivision
import Novel.D14CellEnvelope

/-!
# Claim 030: the Gaussian interval maximum

Proves `Standalone.D14CellSubdivision.interval` (`interval_holds`): (1) = (2), for source and target
intervals of any widths. Deterministic. It reuses claim 029's Gaussian cell library
(`Novel/GaussianCell.lean`).
* A step from `x` with mean `μ` and standard deviation `s` lands in `[L, R)` with probability
  `cellP s L R (x + μ)` (`cell_prob`).
* Over `x ∈ [l, r)` the mean ranges in `[l + μ, r + μ]`, where `cellP` is largest at the clipped
  midpoint (`cellP_le_clip`). So `Wf` bounds every start.
* The clipped start lies in `[l, r] = closure [l, r)`, and `cellP` is continuous
  (`continuous_cellP`), so `Wf` is the least upper bound (`isLUB_of_mem_closure`).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14CellInterval

open Standalone.D14CellSubdivision Novel.GaussianCell

theorem clip_eq {A B : ℝ} (hAB : A ≤ B) (c : ℝ) : clip A B c = min B (max A c) := by
  rw [clip, max_min_distrib_left, max_eq_right hAB]

theorem Wf_eq (l r L R μ s : ℝ) (hlr : l ≤ r) :
    Wf l r L R μ s = cellP s L R (min (r + μ) (max (l + μ) ((L + R) / 2))) := by
  rw [Wf, clip_eq (by linarith)]; rfl

theorem prob_eq (x μ L R : ℝ) {s : ℝ} (hs : 0 < s) (hLR : L ≤ R) :
    (gaussianReal μ (s ^ 2).toNNReal).real {t | x + t ∈ Ico L R} = cellP s L R (x + μ) := by
  have hset : {t | x + t ∈ Ico L R} = Ico (L - x) (R - x) := by
    ext t; simp only [mem_ofPred_eq, mem_Ico]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hset, measureReal_def, cell_prob μ hs, ENNReal.toReal_ofReal, cellP]
  · congr 2 <;> ring
  · rw [sub_nonneg]
    exact (cdf (gaussianReal 0 1)).mono (div_le_div_of_nonneg_right (by linarith) hs.le)

theorem interval_holds : interval := by
  intro l r L R μ s hlr hLR hs
  set m := min (r + μ) (max (l + μ) ((L + R) / 2))
  have hW := Wf_eq l r L R μ s hlr.le
  set g : ℝ → ℝ := fun x => (gaussianReal μ (s ^ 2).toNNReal).real {t | x + t ∈ Ico L R}
  have hg : ∀ x, g x = cellP s L R (x + μ) := fun x => prob_eq x μ L R hs hLR.le
  refine ⟨?_, ?_, ?_⟩
  · rw [hW, cellP, sub_pos]
    exact Φ_lt (div_lt_div_of_pos_right (by linarith) hs)
  · rw [hW, cellP]
    linarith [Φ_le_one ((R - m) / s), Φ_nonneg ((L - m) / s)]
  have hub : Wf l r L R μ s ∈ upperBounds (g '' Ico l r) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hg, hW]
    exact cellP_le_clip hs hLR.le (by linarith) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine isLUB_of_mem_closure hub ?_
  have hcont : Continuous g := by
    have : g = fun x => cellP s L R (x + μ) := funext hg
    rw [this]
    exact (Novel.D14CellEnvelope.continuous_cellP hs L R).comp (continuous_id.add continuous_const)
  have hm : m ∈ Icc (l + μ) (r + μ) :=
    ⟨le_min (by linarith) (le_max_left _ _), min_le_left _ _⟩
  have hx : m - μ ∈ closure (Ico l r) := by
    rw [closure_Ico hlr.ne]; exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  have := hcont.continuousWithinAt.mem_closure_image hx
  rwa [hg, sub_add_cancel, ← hW] at this

end Novel.D14CellInterval
