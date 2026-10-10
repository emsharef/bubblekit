---
id: "033"
title: "D21: recent run-ups on free hourly data — experiment 032's design on the librarian's preregistered 2024–2026 episodes"
status: reproduced
direction: D21
claims: ["033", "036", "037", "038", "055", "061"]
code: experiments/033/
---
## Question

D21 step 2, from the PM's notes `2026-10-07-d21-run.md` and `2026-10-07-d21-hold-for-crypto.md`. It is registered
against the librarian's amended entry "Episode list: D21 recent run-ups" (`board/FINDINGS.md`, 2026-10-07), which
includes the crypto-linked equities.

**The question:** on run-ups inside Yahoo's free hourly window that the press called bubbles or manias, and on
negative controls fixed by rule, what do experiment 032's tests and JKP say?

**GameStop 2024 is of specific interest.** Do jump diagnostics separate its spike from smooth volatility growth?

- **Job:** measuring behaviour on real data with consensus labels from press summaries. These are not ground truth,
  and meme spikes are a different mechanism from the diffusion bubbles of the lab's theory.
- **Status of the data:** no price or test output for these names has been examined. The archive has fetched their
  bars (`d21_additions`, counts only).
- **Report counts, not rates,** unless a group supports rates.

## Design

**Names and classes, from the entry only.** The analyst adds no names.
- **B (positives):** GME, AMC, DJT, SMCI, PLTR, CRWV, NVDA, OPEN, BYND, KSS, DNUT, GPRO, IONQ, RGTI, QBTS, OKLO, MSTR,
  BMNR, SBET, NAKA and CRCL.
- **C (reported separately):** ORCL.
- **W (reported separately):** RDDT, COIN, MARA, RIOT, CLSK, IREN, CIFR and HUT.
- **No F names.**
- **Names without usable hourly bars** (NAKA, whose request was refused, and any other the archive cannot serve over
  its window) are listed as untestable and kept in m as zeros.

**Windows (fixed now, mechanically, from the entry's dates).**
- **Each name's window** is the 12 calendar months ending on the last trading day of the month of the latest dated
  event the entry gives for that name.
  - A "year-only" date counts only when the name has no day- or month-dated event; it ends the window on that year's
    last trading day.
  - Each window is truncated at the later of the archive's first bar (2023-11-07) and the name's first bar.
- **Window ends:**
  - 2024-04-30: DJT;
  - 2024-05-31: GME, AMC;
  - 2024-11-29: SMCI;
  - 2025-03-31: IONQ, RGTI, QBTS;
  - 2025-07-31: KSS, DNUT, GPRO, CRCL;
  - 2025-08-29: PLTR;
  - 2025-09-30: MSTR;
  - 2025-10-31: OPEN, BYND, BMNR, SBET, COIN;
  - 2025-12-31: CRWV, NVDA, ORCL, MARA, RIOT, CLSK, IREN, CIFR, HUT;
  - 2026-07-31: OKLO;
  - RDDT: 2024-03-31, which is before its first archived bar (2024-10-08), so it is untestable.
- **Clock:** the US intraday clock shape is experiment 032's declared N24m-3 shares (0.595, 0.0947, 0.0564, 0.0492,
  0.0713, 0.0645, 0.069). That is a lab declaration fixed before any D21 data were read, from other names. No D21
  bars are reserved for declaration.
- **Splits:** a documented split inside a window (SMCI's 10-for-1 in October 2024) is checked against the bars. If
  the bars show the split jump, prices before it are divided by the documented ratio; otherwise nothing is done. The
  source is cited under Deviations.

**Sampling and prices:** hourly regular-session closes from the archive, with experiment 032's session, duration,
half-day, stray-bar and null-bar rules unchanged. The split is at k = ⌊N/2⌋. **5-minute:** the entry preregisters no
run-up inside the 60-day window, so no 5-minute record is run. This is recorded as such.

**Columns** (experiment 032's, plus JKP):
- (i) v1;
- (ii) claim 033 with {F, U_US} on the rounded closes as if exact, labelled **no guarantee for rounded prices**;
- (iii) the certified filtered score, exactly as in experiment 032:
  - claim 038's evaluator, the wide box, δ = 0.01, factor 2 and the 256-evaluation budget;
  - the numerator is the diagnostic `forecast034`, and a floored path scores zero;
  - every US name has the fixed cent tick, so all are eligible;
  - fixed order: B in the table order above, then C, then W, then the negatives below;
  - 7 parallel processes and a 6-hour cap; records not started by the cap are "not attempted";
- (iv) SADF and GSADF, with 021's critical values per length;
- (v) JKP Methods 1 and 2, through experiment 021's wrapper.
- **Descriptive:** each record's median tick-to-price ratio (0.01 over the close).

**Negative controls.**
- **Primary:** the entry's rule exactly, with L = 12 months, quarterly starts inside the archive and no overlap with
  any positive window (any class's window counts as a positive window for this purpose). The calm score, the 3
  lowest-score windows, and ^GSPC, ^DJI plus 5 DJIA members by 021's member rule. **If fewer than 3 such windows exist,
  their number is reported and the rule is not relaxed.** The positive windows cover most of the archive's span, so
  zero is likely.
- **Secondary, pre-specified now and labelled as not the entry's rule: time-matched calm large caps.** For each
  distinct positive window, ^GSPC, ^DJI and the 5 DJIA members chosen by 021's member rule at that window's start,
  over the same window. They overlap the positive windows in time by construction. Point-in-time DJIA membership uses
  experiment 021's committed source and code. A member without hourly data over the window is replaced by the next,
  and every replacement is recorded.

**GameStop and AMC diagnostics** (May 2024 windows):
- the realized variance RV = Σ r² over the window and its last two months;
- the bipower variation BV = (π/2) Σ |r_j||r_(j−1)|;
- the jump share max(0, 1 − BV/RV);
- the largest single hourly-return share max r²/RV, and the top-5 share;
- claim 061's jump-profile score E^prof (`checks/061/scoring.py`, σ_min = 0.10, Λ_J = 252 a year, at most 128
  boxes), set beside v1's E^drift on the same record.

**Decisions:** single-name flags at α ∈ {0.05, 0.10}. Original-m e-BH at q ∈ {0.05, 0.10} within the B group
(m = 21, untestable names as zeros), within C+W, and within each secondary negative window set (m = 7).

**Outputs:**
- per record: n, splits found, dropped bars, every column's value and flags, the tick-to-price ratio, column (iii)'s
  status and bounds, and runtime;
- the GME and AMC diagnostics;
- the primary-negative candidate count;
- `results.json`, `statuses.json` and `summary.csv`.

**Implementation.**
- Code reuses experiments 021, 027, 028 and 032.
- The archive is extended to IREN, CIFR, HUT, BMNR, SBET, CRCL and NAKA before the run (data only).
- Code is committed before any test, on a fresh branch after this registration merges.
- Single-thread BLAS prefix, at most cores − 3 workers, inside `.worktrees/analyst`.

**Scope.**
- Labels rest on press summaries.
- Crypto-linked stocks may move with the coins.
- Meme spikes are not the lab's diffusion mechanism.
- Column (ii) has no guarantee on rounded prices, and column (iii)'s numerator is diagnostic.
- The secondary negatives overlap the positives in time.

## Deviations

**Deviation 1 (2026-10-07): implementation notes and data facts, committed with `experiments/033/run.py` before any
test.** They come from a data-only inventory (`run.py inventory`).
- **Archive:** extended to IREN, CIFR, HUT, BMNR, SBET, CRCL and NAKA, with no errors or gaps.
- **NAKA is testable.** The archive now serves it (2,403 hourly bars from 2025-05-27, via the fallback range), so under
  the registered rule ("names without usable hourly bars are untestable") it is tested. Its tested span is
  2025-05-27 to 2025-10-31, 772 increments. Yahoo's NAKA history before the 2025 merger is the listed company's
  pre-rename history.
- **RDDT is untestable:** its window ends 2024-03-31, before its first archived bar (2024-10-08). It stays in its
  group's m as a zero.
- **SMCI's split:** the bars show no hourly move beyond ×3.16 around the 10-for-1 split of October 2024, so Yahoo's
  hourly bars are already split-adjusted. By the registered rule nothing is adjusted.
- **Tested spans:** these are the registered windows truncated at each name's first archived session. DJT has 174
  increments (from 2024-03-26), CRCL 266, BMNR 721, NAKA 772 and CRWV 1,328. The rest have 989–1,748.
- **Primary negatives (the entry's rule):** 8 candidate 12-month windows with quarterly starts lie inside the archive,
  and **0 avoid every positive window**. So there are no primary negatives, and the rule is not relaxed.
- **Secondary negatives (time-matched calm large caps):** 14 distinct positive windows, each with ^GSPC, ^DJI and 5
  DJIA members by 021's rule, for 98 records. HON has no archived hourly bars and was replaced by the next member,
  which is recorded per window.
- **Code:**
  - `run.py` reuses experiment 032's session, duration and column functions unchanged, with the declared US shares,
    and experiment 021's negatives code (membership, trailing ranks), critical values and JKP wrapper;
  - claim 061's score comes from `checks/061/scoring.py` with σ_min = 0.10, Λ_J = 252 and 128 boxes;
  - the "last two months" of a window is its final 42 sessions.

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/033/run.py`.
- Run inside `.worktrees/analyst` on 7 workers, from 14:21 to 14:45 on 2026-10-07.
- Column (iii) took 1,127 s wall, well inside the 6-hour cap; every record was attempted.
- Outputs: `results.json`, `statuses.json` and `summary.csv`.

**Numerics and coverage.**
- **v1 and claim 033:** no failed v1 or claim-033 score.
- **Column (iii), on the 29 positive-list records:**
  - 26 met tolerance and 3 were budget-exhausted (OPEN, GPRO, RGTI), with bounds;
  - 19 diagnostic forecasts had a floored cell probability and score zero by rule.
- **Column (iii), on the 98 controls:** 84 met tolerance, 14 were budget-exhausted, and 22 forecasts were floored.
- **RDDT** is untestable. **NAKA** was tested, per Deviation 1.
- **Primary negatives (the entry's rule):** 0 of 8 candidate windows avoid the positive windows. **None exist**, and
  the rule was not relaxed.

**Positive list** ("F" = flagged at 5%):

| class | name | increments | (i) v1 log e | (ii) claim 033 log e (no guarantee) | (iii) certified bound | (iv) SADF / GSADF 5% | (v) JKP M2 / M1 | median tick/price |
|---|---|---|---|---|---|---|---|---|
| B | GME | 989 | −1,555.7 | −648.5 | zero (floored forecast) | **F** / **F** | bubble / inconclusive | 0.0007 |
| B | AMC | 989 | −1,854.8 | −1,185.8 | zero (floored forecast) | · / **F** | bubble / inconclusive | 0.0022 |
| B | DJT | 174 | −214.2 | −98.4 | zero (floored forecast) | · / · | bubble / inconclusive | 0.0003 |
| B | SMCI | 1,748 | −1,278.8 | −655.7 | zero (floored forecast) | **F** / **F** | bubble / inconclusive | 0.0002 |
| B | PLTR | 1,730 | −343.4 | −346.5 | −347.0 | **F** / · | bubble / inconclusive | 0.0001 |
| B | CRWV | 1,328 | −50.5 | −75.4 | −68.1 | **F** / **F** | bubble / inconclusive | 0.0001 |
| B | NVDA | 1,737 | −31.2 | −13.6 | −42.7 | · / · | bubble / inconclusive | 0.0001 |
| B | OPEN | 1,737 | −26,176.2 | −15,834.7 | zero (floored forecast), unresolved | **F** / **F** | bubble / inconclusive | 0.0065 |
| B | BYND | 1,737 | −5,642.6 | −2,929.4 | zero (floored forecast) | · / **F** | bubble / inconclusive | 0.0001 |
| B | KSS | 1,737 | −146.5 | −188.6 | zero (floored forecast) | · / **F** | bubble / inconclusive | 0.0008 |
| B | DNUT | 1,737 | −969.6 | −155.9 | −449.2 | · / **F** | bubble / inconclusive | 0.0011 |
| B | GPRO | 1,737 | −2,794.2 | −1,504.6 | zero (floored forecast), unresolved | · / **F** | bubble / inconclusive | 0.0094 |
| B | IONQ | 1,744 | −16,963.1 | −10,680.6 | zero (floored forecast) | **F** / **F** | bubble / inconclusive | 0.0011 |
| B | RGTI | 1,744 | −66,971.9 | −42,080.4 | zero (floored forecast), unresolved | **F** / **F** | bubble / inconclusive | 0.0081 |
| B | QBTS | 1,744 | −32,866.0 | −21,255.2 | zero (floored forecast) | **F** / **F** | bubble / inconclusive | 0.0073 |
| B | OKLO | 1,748 | −2,953.7 | −1,418.9 | zero (floored forecast) | **F** / **F** | inconclusive / bubble | 0.0001 |
| B | MSTR | 1,737 | −116.6 | −184.5 | −185.1 | **F** / **F** | bubble / no bubble | 0.0000 |
| B | BMNR | 721 | −194.3 | −268.0 | −255.4 | **F** / **F** | bubble / inconclusive | 0.0002 |
| B | SBET | 1,695 | −106,125.7 | −68,068.4 | zero (floored forecast) | **F** / **F** | bubble / inconclusive | 0.0011 |
| B | NAKA | 772 | −1,423.1 | −606.8 | zero (floored forecast) | · / **F** | bubble / inconclusive | 0.0000 |
| B | CRCL | 266 | −78.5 | −106.9 | −107.1 | · / **F** | bubble / inconclusive | 0.0001 |
| C | ORCL | 1,737 | −303.6 | −303.6 | zero (floored forecast) | · / · | bubble / inconclusive | 0.0001 |
| W | RDDT | — | untestable (0 closes in the window) | | | | | |
| W | COIN | 1,737 | −33.6 | −70.3 | −70.2 | · / **F** | bubble / inconclusive | 0.0000 |
| W | MARA | 1,737 | −1,056.9 | −400.6 | −443.2 | · / **F** | bubble / inconclusive | 0.0006 |
| W | RIOT | 1,737 | −2,351.3 | −1,126.5 | −495.8 | · / · | bubble / inconclusive | 0.0008 |
| W | CLSK | 1,737 | −3,076.2 | −1,574.5 | zero (floored forecast) | **F** / **F** | bubble / inconclusive | 0.0010 |
| W | IREN | 1,737 | −13,692.0 | −7,781.5 | zero (floored forecast) | **F** / **F** | bubble / inconclusive | 0.0006 |
| W | CIFR | 1,737 | −12,960.1 | −7,558.7 | zero (floored forecast) | **F** / **F** | bubble / inconclusive | 0.0017 |
| W | HUT | 1,737 | −4,675.2 | −2,618.4 | zero (floored forecast) | **F** / **F** | bubble / inconclusive | 0.0005 |

**Counts by group** (5% flags; e-BH rejected nothing in any group, column or level).

| group | records | v1 | claim 033 | certified | SADF | GSADF | JKP M2 bubble | JKP M1 bubble |
|---|---|---|---|---|---|---|---|---|
| B (positives) | 21 | 0 | 0 | 0 | 12 | 18 | 20 | 1 |
| C + W | 8 | 0 | 0 | 0 | 4 | 6 | 8 | 0 |
| time-matched calm large caps | 98 | 0 | 0 | 0 | 4 | 13 | 58 | 3 |

**GameStop and AMC, May 2024 windows (hourly; jump diagnostics, reported separately).**

| name | span | RV | BV | jump share 1 − BV/RV | largest hourly return's share of RV | top-5 share | claim 061 log E^prof / v1's log E^drift |
|---|---|---|---|---|---|---|---|
| GME | whole window (989 increments) | 1.506 | 0.744 | 0.51 | 0.27 | 0.69 | -2,253.6 / -1,555.7 |
| GME | last 42 sessions (293) | 1.332 | 0.603 | 0.55 | 0.30 | 0.78 | |
| AMC | whole window (989) | 1.131 | 0.627 | 0.45 | 0.41 | 0.62 | -2,534.5 / -1,854.8 |
| AMC | last 42 sessions (293) | 0.897 | 0.477 | 0.47 | 0.51 | 0.77 | |

**Readings** (consensus labels from press summaries; counts, not rates).
- **The lab's likelihood tests flag nothing, on any group.**
  - v1, claim 033 (declared clock, rounded prices, no guarantee) and the certified filtered bound flag none of 21
    bubble-narrative names, none of the 8 C and W names, and none of 98 calm controls.
  - On the positives the log e-values are mostly far below zero, down to −106,126 (SBET). The CEV numerator
    catalogue's scale stops at κ = 0.45, at the normalized start price. Volatile small caps and meme names move far
    more than that, so the training-selected forecast predicts their evaluation half much worse than the
    free-volatility Gaussian profile does.
  - The calm controls sit near zero (v1 at most 1.4, claim 033 at most 0.0). The tests' silence on the positives is
    a numerator-range limitation as much as evidence of no bubble.
- **GSADF separates the groups best:** 18 of 21 positives and 6 of 8 C and W names, against 13 of 98 calm controls.
  SADF: 12 of 21 against 4 of 98. Neither has a guarantee under the hourly clock or jumps.
- **JKP Method 2 is uninformative.** It says bubble on 20 of 21 positives and 58 of 98 calm controls. Method 1 is
  almost always inconclusive.
- **GameStop 2024 was a jump-dominated episode, not smooth volatility growth.**
  - About half of its hourly realized variance is jump-type (BV/RV ≈ 0.49).
  - One hourly return carries 27% of the window's realized variance (30% in its last two months), and five carry
    69–78%. AMC is similar: 45–47% jump share, with its largest return 41–51%.
  - Claim 061's jump-profile score is lower still than v1's (−2,254 against −1,556 for GME), as it must be.
  - These spikes are the social-media price shocks the entry's Limits paragraph anticipates. They are not the
    diffusion mechanism of the lab's theory.
- **Negative controls:** the entry's rule yields none. All comparisons use the pre-specified time-matched calm large
  caps, which overlap the positives in time.
- **Scope:**
  - labels rest on press summaries, and crypto-linked names move with the coins;
  - column (ii) has no rounded-price guarantee, and column (iii)'s numerator is diagnostic;
  - no 5-minute record was run, since the entry preregistered none;
  - no rate is estimable.

## Review

Reviewer, 2026-10-07, against main at `eda464eb`, which contains the results commit `db343c3a`.

**Method.** I wrote my own code from the Design and Deviation 1, without reading `experiments/033/*.py`. It is committed as `checks/review/exp033/reproduce.py`, with its rerun command in its header, and runs on 2 workers.
- **Reused code from my earlier reviews.**
  - From experiment 032: the hourly session parser, v1 and 054, claim 033's 36-kernel score on cent-rounded closes with clocks {F, U_US}, and SADF/GSADF.
  - From experiment 003: JKP Methods 1 and 2.
- **New code.** The realized and bipower variation for the GME and AMC diagnostics.
- **Design inputs from `results.json`.** Each record's name, group and tested window, the declared US shares and the per-length critical values. That includes the mechanical windows and the 98 time-matched controls chosen by experiment 021's membership code.
- **A column (iii) spot-check.** On PLTR, NVDA and MSTR, with my float filtered-denominator optimum and my own claim-034 forecast.
- **Not rerun:** claim 061's E^prof and the full certified column.

**Reproduced.**
- **Records.** 127 testable records, with no increment-count mismatch.
- **Every group count is identical.** v1 / 033 / SADF / GSADF / JKP M2 / M1 come out as:

  | Group | Counts |
  |---|---|
  | B (21 records) | 0 / 0 / 12 / 18 / 20 / 1 |
  | C + W (8) | 0 / 0 / 4 / 6 / 8 / 0 |
  | Controls (98) | 0 / 0 / 4 / 13 / 58 / 3 |

- **SADF and GSADF** agree to 3×10⁻¹⁵ on every record.
- **v1 and claim 033.** The median |Δ v1| is 0.005. Only 8 records differ by more than 1 nat, all at extreme negative values: for example RGTI gives −66,801 against −66,972, and SBET −106,102 against −106,126. That is a relative difference of at most 0.3%, plausibly from different Bessel-tail numerics, and it changes no decision.
- **The largest control values.** My largest control v1 is 1.54, against the published 1.43, and both are far below log 20. Claim 033's largest control value is 0.0 in both.
- **The GME and AMC diagnostics reproduce exactly.**

  | Name | RV | BV | Jump share | Largest share | Top-5 share |
  |---|---|---|---|---|---|
  | GME | 1.506 | 0.744 | 0.51 | 0.27 | 0.69 |
  | AMC | 1.131 | 0.627 | 0.45 | 0.41 | 0.62 |

- **The column (iii) spot-check.** My forecasts give log q within 0.6 of the published values. My float denominators lie inside or within 0.5 nats of the published certified intervals. The resulting bounds are −346.5, −42.1 and −184.7, against −347.0, −42.7 and −185.1.

**The Deviations are honest.**
- **Order.** The Design was committed at 14:12:57, and the code with Deviation 1 at 14:21:54. `run.py` is unchanged to the results at 14:46:50, and the logged run (14:21–14:45) began within the minute of the code commit.
- **Deviation 1's facts come from a data-only inventory,** and the rules were applied as registered:
  - NAKA is testable under the registered rule;
  - RDDT's window predates its bars;
  - SMCI's bars are already split-adjusted;
  - zero primary negatives, with the rule not relaxed.

**The readings are fair.** I would keep their emphasis that the likelihood tests' silence is a numerator-range limitation, not evidence of no bubble. These names' hourly volatility far exceeds the CEV catalogue's κ ≤ 0.45 at the normalized start, so v1 and claim 033 sit at −10² to −10⁵ on the positives.
- **What the same CEV catalogue shows across experiments.** It produces both the D6 misses (experiments 021, 031) and these huge negatives. A wider or level-adaptive numerator catalogue, the subject of math's note, is the natural next step before reading any of these zeros as power results.

Verdict: reproduced
