---
id: "035"
title: "D21: a fair-hearing rerun of experiment 033 with the forecast's CEV scale widened to cover volatile names (matched denominators)"
status: reproduced
direction: D21
claims: ["033", "035", "054", "055"]
code: experiments/035/
---
## Question

D21's second registered experiment (2 of 3), from the PM's note `2026-10-07-exp033-wider-numerator.md`, under math's
contract in `board/FINDINGS.md`, "Experiment 033 numerator range: validity check".

**The problem with 033's numerator.** Experiment 033's v1, claim 033 and certified-bound columns flagged nothing.
Their training-selected CEV forecast's scale stops at κ = 0.45 at the normalized start, while the meme names and
volatile small caps move several times faster. The null's Gaussian profile has no such cap.

**The question:** with only the forecast's scale widened, and with every denominator, record, window, clock and split
of 033 unchanged, what do these columns say?

**Status:**
- This is a follow-up on already inspected records, registered before the rerun.
- It is not an independent replication. The larger of the old and new scores is never selected as a result; both are
  reported side by side.
- No widened score has been computed when this Design is committed.

## Design

**Records:** experiment 033's, unchanged. That is every B, C and W record and the 98 time-matched controls, with the
same hourly closes, durations, declared US shape, ⌊N/2⌋ split and 033's untestable names.

**Widened forecast (numerator only), fixed now.**
- **The scale grid:** K_wide = {0.20, 0.30, 0.45, 0.70, 1.00, 1.50, 2.00, 3.00, 4.00}, at the normalized start price,
  in the same time units and clock normalization as 033. It contains the original grid.
- **(i) v1:** forecast candidates p ∈ {0.5, 0.75, 1, 1.25, 1.5, 2} × K_wide on the calendar clock, 54 in all.
  Selection is the first maximizer of the training likelihood. This keeps v1's forecast p set and its mixed
  zero-atom conventions (claim 054).
- **(ii) claim 033:** the same 54 candidates on each clock of {F, U_US}, 108 in all, with first-maximizer training
  selection.
- **(iii) certified bound's diagnostic numerator:** experiment 028's `forecast034` construction with its p ≥ 1 rule
  kept, over p ∈ {1, 1.25, 1.5, 2} × K_wide on both clocks. A floored or non-finite cell probability scores zero.
- **Support, finiteness and fallback:**
  - every candidate has p > 0 and a finite positive κ, and selection uses training data only;
  - candidates with a non-finite training likelihood are skipped;
  - if none is finite, or the selected forecast's evaluation density is NaN, the column scores zero. This is the same
    deterministic fallback as before.

**Denominators: unchanged, the primary matched comparison.**
- For (i) and (ii), G₀ is 033's original retained null list: p ≤ 1 × {0.20, 0.30, 0.45}, on the calendar clock for
  v1 and on both clocks for claim 033. The Gaussian profiles are 033's.
- For (iii), each record's certified log D upper bound is taken unchanged from experiment 033's `results.json`, from
  the same evaluator, record and settings. The widened score bound is log q_wide − log D_upper.

**Implementation check, before any widened score.**
- (i) and (ii) are recomputed with forecast and null lists kept separate, with candidate counts derived from the lists
  (not hard-coded).
- Run with the original forecast list, the code must reproduce 033's log e-values on every record, within 10⁻⁶ in
  log, or 0 for zero scores. A mismatch stops the run and is recorded.

**Secondary, separately labelled (not the matched comparison): an enlarged retained null.**
- For (i) and (ii), G₀ is enlarged by every old candidate plus p ∈ {0.5, 0.75, 1} × K_wide, keeping the widened
  forecast.
- The denominator rises pointwise, so this column can only be lower than the matched widened column.
- It admits a larger finite CEV null family. It is not coverage of every CEV scale.

**Unchanged columns:** SADF, GSADF and JKP do not involve the forecast. They are reported from 033, not rerun.

**Decisions and outputs.**
- **Flags:** at α ∈ {0.05, 0.10}, original-m e-BH at q ∈ {0.05, 0.10} within 033's groups (B with m = 21, C+W, each
  time-matched negative set).
- **Per record, original and widened side by side:**
  - log e-values and flags;
  - the selected (p, κ, clock);
  - the zero-score fallback count;
  - for (iii): log q_wide, the reused log D_upper and the bound.
- **Group counts** next to experiment 033's.
- **Labels:** (ii) "no guarantee for rounded prices"; (iii) "certified denominator, diagnostic numerator".
- Files: `results.json`, `statuses.json` and `summary.csv`.

**Implementation.**
- Code reuses experiments 021, 027, 028, 032 and 033's record functions, and is committed before any widened score.
- Runs on a fresh branch after this registration merges, with the single-thread BLAS prefix, at most cores − 3
  workers, inside `.worktrees/analyst`.

**Scope.**
- The forecast change cannot repair the observation law: (ii) is uncertified on rounded prices and (iii)'s numerator
  is diagnostic.
- A larger training maximum does not imply a better evaluation score.
- Labels, windows and controls are 033's.

## Deviations

**Deviation 1 (2026-10-07): implementation notes and the registered reproduction check, committed with
`experiments/035/run.py` before any widened score.** Not design changes.
- **Column (i):** reimplemented as experiment 022's `cev.score` drift-null construction (claim 055), with separate
  forecast and null lists and cumulative-duration times.
- **Column (ii):** reimplemented as experiment 027's `scores`, with separate lists.
- **Column (iii)'s numerator:** reimplemented as experiment 028's `forecast034`, with a candidate list and the p ≥ 1
  rule.
- **Reproduction check (`run.py check`):** it computes only the original-list scores, no widened score. On all 127
  records it reproduced experiment 033's stored v1 and claim-033 log e-values and column (iii)'s log q, within 10⁻⁶,
  with **0 mismatches**.
- **Records:** experiment 033's code regenerates them identically.

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/035/run.py`.
- Run inside `.worktrees/analyst` on 7 workers, in a few minutes.
- The run repeated the reproduction check first (0 mismatches on 127 records).
- Outputs: `results.json`, `statuses.json` and `summary.csv`.

**Numerics:** no widened forecast hit the zero-score fallback in (i) or (ii). Floored widened (iii) numerators score
zero by rule: AMC, SMCI, OPEN, BYND, KSS, GPRO, IONQ, RGTI, QBTS, NAKA and ORCL.

**Positive list, matched comparison** ("F" = flagged at 5%; RDDT untestable, as in 033):

| class | name | (i) v1 log e: 033 → widened (selected) | (i) widened, enlarged G₀ | (ii) claim 033 log e: 033 → widened (selected) | (ii) widened, enlarged G₀ | (iii) certified bound: 033 → widened |
|---|---|---|---|---|---|---|
| B | GME | −1,555.7 → −95.0 (p 1.5, κ 1.0) | −95.0 | −648.5 → 21.5 **F** (U, p 2.0, κ 0.7) | 21.5 **F** | zero → 526.7 **F** |
| B | AMC | −1,854.8 → −561.3 (p 0.5, κ 0.7) | −561.3 | −1,185.8 → −665.0 (U, p 1.0, κ 0.7) | −665.0 | zero → zero |
| B | DJT | −214.2 → −24.4 (p 2.0, κ 3.0) | −24.6 | −98.4 → −42.1 (U, p 2.0, κ 2.0) | −43.3 | zero → 7.7 **F** |
| B | SMCI | −1,278.8 → −334.4 (p 1.5, κ 0.7) | −383.0 | −655.7 → −334.5 (F, p 1.5, κ 0.7) | −383.0 | zero → zero |
| B | PLTR | −343.4 → −343.4 (p 2.0, κ 0.45) | −391.1 | −346.5 → −346.5 (F, p 2.0, κ 0.45) | −391.1 | −347.0 → −347.0 |
| B | CRWV | −50.5 → −60.5 (p 0.75, κ 2.0) | −60.5 | −75.4 → −60.7 (U, p 0.5, κ 2.0) | −60.7 | −68.1 → −125.5 |
| B | NVDA | −31.2 → −66.5 (p 0.5, κ 0.7) | −66.5 | −13.6 → −82.7 (F, p 0.5, κ 0.7) | −82.7 | −42.7 → −140.7 |
| B | OPEN | −26,176.2 → −4,395.4 (p 0.5, κ 1.0) | −4,395.4 | −15,834.7 → −1,250.5 (U, p 0.75, κ 1.0) | −1,250.5 | zero → zero |
| B | BYND | −5,642.6 → −1,418.9 (p 1.0, κ 1.0) | −1,418.9 | −2,929.4 → −1,214.7 (U, p 0.75, κ 0.7) | −1,214.7 | zero → zero |
| B | KSS | −146.5 → −1,343.5 (p 1.5, κ 0.7) | −1,363.3 | −188.6 → −1,343.5 (F, p 1.5, κ 0.7) | −1,363.3 | zero → zero |
| B | DNUT | −969.6 → −969.6 (p 1.0, κ 0.45) | −969.6 | −155.9 → −155.9 (U, p 0.75, κ 0.45) | −155.9 | −449.2 → −449.2 |
| B | GPRO | −2,794.2 → −2,516.0 (p 2.0, κ 1.0) | −2,516.0 | −1,504.6 → −3,415.0 (U, p 2.0, κ 0.7) | −3,415.0 | zero → zero |
| B | IONQ | −16,963.1 → −6,215.6 (p 0.5, κ 0.7) | −6,215.6 | −10,680.6 → −199.8 (U, p 1.25, κ 0.7) | −199.8 | zero → zero |
| B | RGTI | −66,971.9 → −69.6 (p 1.5, κ 1.5) | −69.6 | −42,080.4 → −174.4 (U, p 1.25, κ 1.0) | −174.4 | zero → zero |
| B | QBTS | −32,866.0 → −85.7 (p 1.25, κ 1.5) | −85.7 | −21,255.2 → −719.9 (U, p 1.0, κ 1.0) | −719.9 | zero → zero |
| B | OKLO | −2,953.7 → −49.4 (p 1.5, κ 1.0) | −49.4 | −1,418.9 → −263.5 (U, p 2.0, κ 0.7) | −263.5 | zero → −258.3 |
| B | MSTR | −116.6 → −233.3 (p 1.5, κ 1.0) | −253.0 | −184.5 → −243.7 (U, p 1.25, κ 1.0) | −280.4 | −185.1 → −244.3 |
| B | BMNR | −194.3 → −337.1 (p 1.25, κ 3.0) | −337.1 | −268.0 → −337.2 (F, p 1.25, κ 3.0) | −337.2 | −255.4 → −324.6 |
| B | SBET | −106,125.7 → −15.5 (p 1.0, κ 3.0) | −15.5 | −68,068.4 → −64.9 (U, p 1.25, κ 3.0) | −64.9 | zero → 3,842.9 **F** |
| B | NAKA | −1,423.1 → −82.5 (p 1.25, κ 3.0) | −82.5 | −606.8 → −106.6 (F, p 1.25, κ 3.0) | −106.6 | zero → zero |
| B | CRCL | −78.5 → −116.8 (p 1.0, κ 4.0) | −116.8 | −106.9 → −88.7 (U, p 0.75, κ 4.0) | −88.7 | −107.1 → −146.7 |
| C | ORCL | −303.6 → −303.6 (p 0.5, κ 0.45) | −303.6 | −303.6 → −303.6 (F, p 0.5, κ 0.45) | −303.6 | zero → zero |
| W | COIN | −33.6 → −62.0 (p 1.0, κ 1.0) | −62.0 | −70.3 → −57.9 (U, p 0.5, κ 1.0) | −57.9 | −70.2 → −61.9 |
| W | MARA | −1,056.9 → −19.2 (p 0.5, κ 1.0) | −19.2 | −400.6 → −50.1 (F, p 0.5, κ 1.0) | −50.1 | −443.2 → −37.3 |
| W | RIOT | −2,351.3 → −35.5 (p 0.75, κ 1.0) | −35.5 | −1,126.5 → −29.6 (U, p 1.0, κ 1.0) | −29.6 | −495.8 → −28.7 |
| W | CLSK | −3,076.2 → −200.4 (p 0.5, κ 1.0) | −200.4 | −1,574.5 → −63.6 (U, p 0.5, κ 1.0) | −63.6 | zero → 12.7 **F** |
| W | IREN | −13,692.0 → −107.5 (p 1.25, κ 1.5) | −107.5 | −7,781.5 → −4.2 (U, p 1.0, κ 1.0) | −4.2 | zero → 72.4 **F** |
| W | CIFR | −12,960.1 → −1.4 (p 1.0, κ 1.5) | −1.4 | −7,558.7 → −9.5 (F, p 1.0, κ 1.5) | −9.5 | zero → 191.8 **F** |
| W | HUT | −4,675.2 → −429.9 (p 0.5, κ 1.0) | −429.9 | −2,618.4 → −429.9 (F, p 0.5, κ 1.0) | −429.9 | zero → 51.1 **F** |

**Counts at 5%** (e-BH, original m):

| group | records | v1 033 / widened / widened + G₀ | claim 033 033 / widened / widened + G₀ | certified 033 / widened |
|---|---|---|---|---|
| B | 21 | 0 / 0 / 0 | 0 / 1 (GME) / 1 (GME) | 0 / 3 (GME, DJT, SBET) |
| C + W | 8 | 0 / 0 / 0 | 0 / 0 / 0 | 0 / 4 (CLSK, IREN, CIFR, HUT) |
| time-matched calm large caps | 98 | 0 / 0 / 0 | 0 / 0 / 0 | 0 / 0 |

- e-BH rejects GME in claim 033's widened columns (B, q = 0.05 and 0.10), and the same seven names in the certified
  column.
- The calm controls' best widened values are v1 1.4, claim 033 0.0 and certified −0.8.

**Volatility against the certified column's box** (descriptive, flat-clock annualized volatility of the evaluation
half). The certified denominator's declared box is w ≤ 0.64, which is volatility ≤ 0.80. Every name that column (iii)
flags is outside it: GME 2.23, DJT 1.56, SBET 3.64, CLSK 0.91, IREN 1.08, CIFR 1.16, HUT 1.00.

**Readings** (a follow-up on inspected records, not independent replication; the larger of the old and new scores is
never selected).
- **Widening the forecast scale fixes most of 033's numerator mismatch.**
  - Log e-values rise by orders of magnitude on the volatile names: SBET −106,126 → −15.5 in v1, RGTI −66,972 → −69.6,
    MARA −1,057 → −19.2.
  - Most selected forecasts now use κ = 0.7–3.0.
  - On a few names the widened training choice predicts the evaluation half worse (KSS, NVDA, MSTR), as math warned:
    a larger training maximum is not a better evaluation score.
- **v1 still flags nothing.** Its flat calendar null with free drift and scale remains far better than the widened CEV
  forecast on every name.
- **Claim 033 with the declared clock flags only GameStop** (log e 21.5, kept by e-BH). Its widened forecast is CEV
  p = 2, κ = 0.7 on the U clock. The flag holds with the enlarged G₀. **Caveats:**
  - rounded prices, so no guarantee;
  - experiment 033 found GameStop's 2024 window jump-dominated, which the Gaussian/CEV null does not model;
  - its evaluation-half volatility (2.23) is more than three times its training half (0.65).
- **Every certified-column flag is out of class.** The seven flagged names all have evaluation volatility above the
  declared box's 0.80. Like experiment 028's N-k60 null, which false-alarmed outside its narrow box, these flags show
  the box is too narrow for these names, not evidence of a bubble. The column's numerator is also diagnostic.
- **The calm controls stay unflagged** in every column. Widening the forecast did not raise their scores above 1.4.
- **Overall:** with a forecast that can follow their volatility, the volatile names' evidence moves from hugely
  negative to near zero. Only GameStop crosses the threshold in a column without a box cap, and only under the
  caveats above. Most named run-ups are not distinguished from a free-scale Gaussian by these likelihood tests.

## Review

Reviewer, 2026-10-07, against main at `25b7509e`, which contains the results commit `611939ab`.

**Method.** I wrote my own code from the Design, without reading `experiments/035/*.py`. It is committed as `checks/review/exp035/reproduce.py`, with its rerun command in its header, and runs on 2 workers.
- **The scorers.** My experiment-032 and experiment-033 review scorers, generalized to separate forecast and null candidate lists.
- **The widened columns.** The widened grid K_wide, with the 54-candidate calendar v1 forecast and the 108-candidate claim-033 forecast on cent-rounded closes. Each has the original G₀ and the enlarged G₀.
- **Column (iii).** The claim-034 cell forecast over p ≥ 1 × K_wide on both clocks, bounded with experiment 033's published log D_upper.
- **My cell probabilities are exact in their tails.** p = 1 cells use log-space normal differences, and p > 1 cells use non-central χ² with complementary branches. A cell counts as floored only if it is truly below 10⁻³⁰⁰.

**Reproduced.**
- **The original lists** reproduce experiment 033 as in my experiment-033 review: a median difference of about 0.005, and at most 0.3% relative on a few extreme records.
- **Column (i), v1.** Widened v1 flags nothing in any group, with the original or the enlarged G₀.
  - **The large moves reproduce:** SBET −106,102 → −15.4, RGTI −66,801 → −70.1, MARA −1,057 → −19.2, CIFR −12,949 → −1.4.
  - **So does the worsening on KSS, NVDA and MSTR:** −146.5 → −1,343.4, −31.2 → −66.5 and −116.7 → −233.4.
- **Column (ii), claim 033.** Widened claim 033 flags **only GME** in both G₀ variants: log e 20.7 with U, p = 2, κ = 0.7, against 21.5 published, with the same selection. The controls stay at 0.0.
- **The volatilities of the seven published certified-column flags reproduce:** GME 2.23, DJT 1.56, SBET 3.64, CLSK 0.91, IREN 1.08, CIFR 1.16 and HUT 1.00.
- **Differences.**
  1. **Training selection at the largest scales differs on a few records.** It differs for GME's v1 (p = 2, κ = 0.7 against p = 1.5, κ = 1.0), giving −286.9 against −95.0. It also differs for RGTI's claim 033 (−700.5 against −174.4) and CRCL's v1 and claim 033 (−176.4 against −116.8, and −146.5 against −88.7). The original-grid scores agree, so this is most likely kernel numerics at κ ≥ 1, where nearly tied training likelihoods select differently. No decision changes.
  2. **The certified column flags 8 B names in my run against 3 published.**
     - **Where they differ.** OPEN, IONQ, RGTI, QBTS and NAKA score zero in the published run because their widened forecasts had **floored** cells. Their published floored log q values sit far below my exact ones: OPEN −4,995 against −3,736 here, with its selected forecast being p = 1.
     - **The cause.** A cell probability computed as Φ(b) − Φ(a), with both values near 1 in the far tail, cancels to zero and is floored. It is not genuinely below 10⁻³⁰⁰. Evaluated stably, these five bounds are 188 to 816 nats, so all are flagged.
     - **The reading is unchanged.** All 12 of my certified flags have evaluation volatility above the box's 0.80 (the extra five: OPEN 1.91, IONQ 1.52, RGTI 2.23, QBTS 2.07, NAKA 2.73). So the reading "every certified-column flag is out of class" holds and strengthens.
     - **Rule and fix.** Under the registered rule, the published zeros are correct as registered. But the floor fires here from avoidable cancellation, as in experiment 028's Deviation 3. A stable log-space tail evaluation in `forecast034` would remove most floors.

**The Deviations are honest.** The Design was committed at 15:01, and the code with Deviation 1 at 15:05:55, which reports 0 mismatches against experiment 033 before any widened score. `run.py` is unchanged to the results at 15:07:13. Both widened and original scores are reported, and the larger is never selected.

**The readings are fair.** They are strengthened by (2): every certified flag, now 12, lies outside the declared box, so that column's flags are box failures, not bubble evidence. GME's claim-033 flag stands under the stated caveats: rounded prices, a jump-dominated window, and an evaluation-half volatility 3.4 times the training half's.

Verdict: reproduced
