---
id: "032"
title: "D6: first real-data intraday application — hourly bars on SK Hynix (E6) and the calm negative window N24m-3"
status: reproduced
direction: D6
claims: ["033", "034", "036", "037", "038", "055"]
code: experiments/032/
---
## Question

D6's fourth and last registered experiment (PM note `2026-10-07-d6-intraday-application.md`): the lab's first
application of its intraday tests to real prices. It uses the lab's own archive of Yahoo hourly regular-session bars
(`experiments/data/intraday_archive.py`, manifest `intraday_archive_manifest.json`; bars in the gitignored
`data/d6-intraday/`).

The free hourly history covers two of experiment 021's rows:
- **E6:** the SK Hynix positive. Hourly bars start 2023-10-06.
- **N24m-3:** the calm negative window, fully covered.

Names follow experiment 021's rule, not any inspection of results.

**Question:** on these records, what do v1, claim 033 with a declared intraday clock, the certified filtered score
and SADF/GSADF say? At what runtime, and with which caveats?

**Job:** measuring behaviour on real data with consensus labels. There is no ground truth and no rate is estimable
from these few names. No test has been run on these hourly data when this Design is committed. The archive itself has
only been inventoried (bar counts and first and last bars, in the manifest).

## Design

**Rows, names and windows** (experiment 021's rule, unchanged except where hourly data force a change).
- **E6:** 000660.KS only (021's row; Samsung is not used).
  - 021's E6 windows are 2023-01-01 to 2026-10-05 (full) and to 2026-06-22 (to-peak). Hourly bars start 2023-10-06.
  - The bars from the first session through 2023-12-28 are reserved, before any test, for declaring E6's clock
    shape (below).
  - **The tested E6 span** is the first session from 2024-01-02 to 2026-10-05 (full), or to 2026-06-22 (to-peak).
- **N24m-3:** ^GSPC, ^DJI, V, PG, WMT, KO and TRV, as 021 selected them. The windows are 2024-07-01 to 2026-06-30
  (full) and to 2026-06-02 (to-peak).

**Prices and clock time.**
- **Prices:** the regular-session hourly bar closes from the archive's `bars/60m/<symbol>.csv`, first-seen values.
  - Bars with a null close are dropped, and the neighbouring increments merge. The count is reported.
  - The first close of the tested span is the start price.
- **Durations, in years, as in experiment 027:** a bar's hours divided by (24 × 252). Each break between sessions
  (overnight, weekend or holiday alike) counts as one 17.5-hour overnight. The first increment of a session is
  therefore overnight plus first bar.
- **Session structure:** US bars are 09:30–16:00 ET (six full hours and a final half hour), and KRX bars are
  09:00–15:30 KST (the same seven slots). A session with a different bar count is kept, with its bars in order and
  slot index by position, and is counted.
- **Split:** training and evaluation split at k = ⌊N/2⌋ increments, which is experiment 021's split.

**Declared clock catalogue** (fixed before any test, from data strictly before each tested span).
- **Shape U_row:** eight per-increment variance shares. Slot 0 is overnight plus first bar; slots 1–6 are the remaining
  hours, with the half hour last.
  - Each slot's share is the mean over names of each name's share of mean squared log return in that slot, within the
    declaration period.
  - The declaration periods are: N24m-3, 2023-11-07 to 2024-06-28 (all seven names); E6, 2023-10-06 to 2023-12-28
    (SK Hynix).
- **The clock:** an increment in slot j gets variance time share_j/252, so one session plus its overnight sums to
  1/252.
- **Catalogue:** 𝒱 = {F (calendar durations), U_row}. These are declarations, not estimates treated as truth. Their
  shares are printed before the test outputs and committed with the results.

**Columns.**
- **(i) Usable test v1 (claim 055) on hourly closes:** `checks/d13-drift-total/total.py`'s `score_total_path`, with
  times as the cumulative durations above and experiment 021's 18-candidate catalogue. Claim 054's raw score is shown
  beside it, as in 021.
- **(ii) Claim 033 with 𝒱 = {F, U_row}** on the cent- and won-rounded closes, as if they were exact. It is labelled
  **"no guarantee for rounded prices"** (claims 024 and 033 do not cover them).
  - Computed by experiment 027's `scores` function: a CEV numerator with 36 training-selected candidates, and a
    denominator equal to the maximum of the CEV nulls (p ≤ 1) and the Gaussian profiles on F and U_row.
- **(iii) The certified filtered score** (claims 036–038).
  - **Denominator:** math's adaptive evaluator with claim 038's centred integration allowance
    (`checks/038/certify.py`, wrapping `checks/d19-adaptive-filter/certify.py`) at the run's commit.
  - **Settings:** box ℬ = [−0.50, 0.50] × [0.01, 0.64] (experiment 027's wide box), the declared full-record clocks
    {F, U_row}, labels round(close/δ) with δ = 0.01, and the first close of the tested span as the known start. That
    start is a premise the data cannot verify, since it is itself rounded. Factor 2, count 4, max_count 64,
    max_evaluations 256.
  - **Numerator:** claim 034's training-selected CEV cell forecast, as implemented in experiment 028 (`forecast034`).
    It is evaluated in float64, so it is a **diagnostic numerator, not certified**. Any path with a floored or
    non-finite forecast cell probability scores zero (experiment 028, Deviation 3).
  - **Reported:** log q (diagnostic), the certified log D interval, the score bound log q − log D_upper, the
    evaluator status, evaluations, leaves and failures, and seconds.
  - **Coverage of records:**
    - SK Hynix is **not covered.** KRX tick sizes change with price band, and its price crossed bands in this span,
      so a fixed tick δ is false. It is reported as "not covered".
    - **Fixed record order:** N24m-3 full-window records in 021's name order, then its to-peak records in the same
      order.
    - **Budget:** at most 7 parallel single-record processes, and a 6-hour wall cap for column (iii). Records not
      started by the cap are reported "not attempted". Records that end on budget or arithmetic limits are
      "unresolved", with their bounds.
- **(iv) SADF and GSADF:** experiment 021's r₀ rule and its simulated critical values at each series length (2,000
  replications, seed 20261024), at 5% and 10%.

**Decisions and multiplicity.**
- Single-name flags at α ∈ {0.05, 0.10} (score above 1/α) for (i), (ii) and (iii).
- Original-m e-BH within each row and variant at q ∈ {0.05, 0.10}: m = 7 for N24m-3, and m = 1 for E6.
- Failures and uncovered records stay in m, as zeros.

**Outputs, per row, variant and name:**
- n (increments), dropped null bars and irregular sessions;
- every column's log e-value or statistic and its flags;
- the e-BH rejections;
- column (iii)'s certified details;
- runtime per record and column;
- the declared shares.

Files: `results.json`, `statuses.json` and `summary.csv`.

**Implementation.**
- Code is committed before any test, on a fresh branch after this registration merges.
- Runs use the single-thread BLAS prefix and at most cores − 3 workers, inside `.worktrees/analyst`, after no other
  pooled job.

**Scope.**
- Consensus labels (E6 rests on press sources, per the librarian), and one positive name.
- Hourly bars only, from Yahoo, with no bid–ask information (D18 is closed and not applied).
- Column (ii) has no guarantee on rounded prices.
- Column (iii)'s numerator is diagnostic and its start premise unverifiable.
- No rate, size or power is estimable.

## Deviations

**Deviation 1 (2026-10-07): implementation notes and data facts, committed with `experiments/032/run.py` before any
test.** They come from a data-only inventory (`run.py inventory`) and a synthetic timing run (`run.py smoke`).
- **Session structure, corrected:**
  - KRX hourly bars are **six per session** (09:00–14:00 starts, the last spanning 14:00–15:30), not seven.
  - US bars are seven (09:30–15:30 starts, the last a half hour).
  - **US half days** (a bar at 13:00 and none at 13:30) close at 13:00: 7 such days.
  - **Bars starting at or after the session close** are dropped as strays: 8 on each US series, a 16:00 bar and the
    13:00 bars of half days.
  - Each bar's length is the next start minus its start, the last running to the close.
  - Irregular sessions (6 per US series in the tested spans) keep their bars by position. Each bar gets its slot's
    share scaled by (bar minutes / regular minutes of that slot).
- **The registration's "eight shares" was wrong:** there are seven (US) or six (KRX) shares, with slot 0 being overnight
  plus the first bar.
- **Declared shares** (printed before any test, from the declaration periods):
  - E6: (0.686, 0.108, 0.053, 0.051, 0.053, 0.048);
  - N24m-3: (0.595, 0.095, 0.056, 0.049, 0.071, 0.064, 0.069).
  Slot 0 dominates (0.69 and 0.60), as the overnight-plus-open increment should.
- **Record sizes:**
  - E6 has 4,007 (full) and 3,587 (to-peak) increments, with 12 null bars dropped.
  - Each N24m-3 name has 3,482 and 3,349, with 6 null bars dropped.
- **Prices are not all on the cent grid.** The archive stores closes at float32 precision, and 23–54% of the stocks'
  hourly closes are sub-penny last trades (for example 247.6006).
  - Column (iii)'s labels round(close/0.01) are the cent cell of the latent price whether a close is an exact trade
    or already cent-rounded, so the labelling stays consistent.
  - The start is the first close as stored.
  - WMT's 3:1 split (2024-02-26) falls before the tested span. Its split-adjusted pre-split bars enter only the
    declaration period's log returns.
- **Column (iii) code:** the evaluator is `checks/038/certify.py`'s `enclose` (default cached allowances, with claim
  038's centred allowance) with the registered settings. The diagnostic numerator is experiment 028's `forecast034`,
  with start price P0 = first close. A path with any floored cell probability scores zero.
- **Timing, synthetic records only (no archive data):** column (iii) met tolerance in 1.5 s at N = 300. At N = 3,482 it
  exhausted the 256-evaluation budget in 43 s with no failed leaves, so the 14 covered records fit well within the
  6-hour cap. v1's scorer takes about 10 s at N = 3,500.

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/032/run.py`.
- Run inside `.worktrees/analyst`, after experiments 030 and 031 were reproduced.
- Critical values and column (iii) used 7 workers. Column (iii) took 97 s wall for its 14 records, far inside the
  6-hour cap.
- Outputs: `results.json` (with the declared shares, critical values and every column's details), `statuses.json`
  and `summary.csv`.

**Numerics.**
- v1's status is "ok" on all 16 records.
- Claim 033 had no failures and no singular profiles.
- Column (iii):
  - 10 records met tolerance (factor 2, log width at most 0.69);
  - 4 were budget-exhausted and unresolved, with bounds: WMT and KO, full and to-peak (KO's width is 2.6);
  - none had a failed leaf;
  - one diagnostic numerator was floored (V, to-peak) and scored zero, as registered;
  - SK Hynix is not covered.
- **Runtime per record:** v1 10–12 s; claim 033 under 1 s; column (iii) 24–52 s.

| row | window | name | increments | (i) v1 log e (5% flag) | (ii) claim 033 log e, no guarantee for rounded prices | (iii) certified filtered score | (iv) SADF / GSADF (flags) |
|---|---|---|---|---|---|---|---|
| E6 | full | 000660.KS | 4,007 | 138.6 **flag** | −5,761.7 | not covered (variable KRX tick) | 7.53 / 7.53 (5%: sadf, gsadf) |
| E6 | to_peak | 000660.KS | 3,587 | 125.5 **flag** | −2,231.2 | not covered (variable KRX tick) | 7.53 / 7.53 (5%: sadf, gsadf) |
| N24m-3 | full | ^GSPC | 3,482 | −266.8 | −123.8 | tolerance met; log D ∈ [−15,451.1, −15,450.5]; bound −220.0 | 0.60 / 2.06  |
| N24m-3 | full | ^DJI | 3,482 | −14.0 | −142.0 | tolerance met; log D ∈ [−18,820.3, −18,819.7]; bound −228.4 | −0.67 / 2.32 (10% only: gsadf) |
| N24m-3 | full | V | 3,482 | −74.4 | −88.3 | tolerance met; log D ∈ [−10,936.0, −10,935.3]; bound −84.3 | 0.51 / 1.47  |
| N24m-3 | full | PG | 3,482 | −94.4 | −44.0 | tolerance met; log D ∈ [−9,290.2, −9,289.6]; bound −25.6 | −1.12 / 1.12  |
| N24m-3 | full | WMT | 3,482 | −4.8 | −24.8 | budget exhausted; log D ∈ [−9,182.7, −9,181.9]; bound −25.6 | 0.96 / 1.91  |
| N24m-3 | full | KO | 3,482 | 12.8 **flag** | −33.3 | budget exhausted; log D ∈ [−7,942.2, −7,939.6]; bound −52.5 | 0.75 / 2.29 (10% only: gsadf) |
| N24m-3 | full | TRV | 3,482 | −20.0 | −83.3 | tolerance met; log D ∈ [−10,550.4, −10,549.7]; bound −117.6 | 0.33 / 1.69  |
| N24m-3 | to_peak | ^GSPC | 3,349 | −293.7 | −145.0 | tolerance met; log D ∈ [−14,797.2, −14,796.5]; bound −239.7 | 0.60 / 2.06  |
| N24m-3 | to_peak | ^DJI | 3,349 | −318.8 | −151.8 | tolerance met; log D ∈ [−18,066.5, −18,065.8]; bound −233.7 | −0.67 / 2.32 (10% only: gsadf) |
| N24m-3 | to_peak | V | 3,349 | −28.6 | −77.3 | tolerance met; log D ∈ [−10,568.1, −10,567.4]; bound −∞ (zero) (floored forecast → zero) | 0.51 / 1.47  |
| N24m-3 | to_peak | PG | 3,349 | −33.3 | −57.0 | tolerance met; log D ∈ [−8,895.4, −8,894.8]; bound −36.5 | −1.12 / 1.13  |
| N24m-3 | to_peak | WMT | 3,349 | −6.5 | −25.8 | budget exhausted; log D ∈ [−8,801.1, −8,800.3]; bound −26.6 | 0.96 / 1.91  |
| N24m-3 | to_peak | KO | 3,349 | −3.1 | −44.8 | budget exhausted; log D ∈ [−7,557.9, −7,555.2]; bound −72.8 | 0.75 / 2.29  |
| N24m-3 | to_peak | TRV | 3,349 | −30.3 | −77.8 | tolerance met; log D ∈ [−10,090.6, −10,089.9]; bound −119.0 | 0.33 / 1.69  |

**e-BH, original m.**
- E6 (m = 1): v1 rejects in both windows.
- N24m-3 (m = 7): v1 rejects **KO** in the full window at q = 0.05 and 0.10, and nothing in the to-peak window. Claim
  033 and the certified bound reject nothing in either window.

**Readings** (consensus labels, two rows, so no rate; labelling caveats as registered).
- **SK Hynix, the E6 positive.**
  - **v1 flags** in both windows (log e 138.6 full, 125.5 to the peak). Its training selected CEV p = 1.25, κ = 0.45
    on the calendar clock.
  - **SADF and GSADF** flag at 5%.
  - **Claim 033 with the declared clock** (no guarantee for rounded prices) is strongly against (log e −5,762 and
    −2,231). Its training selected a sublinear null-type kernel on the declared clock, p = 0.75 with κ = 0.45. Over the
    evaluation half the price rose about 13× from the span's start and the flat-clock volatility rose from 0.48 to
    0.79. That forecast fared far worse than the clock-aware Gaussian profile, which fits the evaluation half freely.
    This is an observation on one record, not a diagnosis of the method.
  - **Column (iii)** does not cover this record.
- **N24m-3, the calm negatives (seven names).**
  - **Claim 033 and the certified bound flag nothing.** The certified score's log upper bounds run from −25.6 to −240;
    it is unresolved on WMT and KO.
  - **SADF flags nothing.** GSADF flags ^DJI and KO at 10% only.
  - **v1 flags KO in the full window** (log e 12.8, and e-BH rejects it). It is the only flag on a negative name, and
    it does not recur in the to-peak window (−3.1). Under experiment 021's labels this is a false alarm on a calm
    control at hourly sampling.
- **Contrast with daily data:** at daily frequency (experiment 021), v1 flagged SK Hynix in the full window but not to
  the peak, and flagged no calm control. Hourly v1 flags SK Hynix in both windows, but also flags one calm name. At hourly sampling v1's
  flat calendar clock ignores the intraday volatility pattern, which the declared shares show: slot 0 carries 60–69%
  of the variance time. That pattern is outside v1's null (experiment 027 found v1 safe but nearly powerless under a
  simulated clock).
- **Column (iii) feasibility on real hourly records:** a 2-year hourly record (3,349–3,482 increments) certified the
  denominator to within 0.7 nats in 24–52 s, or stopped unresolved at its 256-evaluation budget. That is far cheaper
  than the D19 probes projected without claim 038. The numerator is diagnostic and the start premise unverifiable, as
  registered.
- **Scope:** one positive name, seven negatives and Yahoo hourly bars. Column (ii) has no rounded-price guarantee, and
  23–54% of the stocks' closes are sub-penny trades. No rate, size or power is estimable.

## Review

Reviewer, 2026-10-07, against main at `3cc77337`, which contains the results commit `c329bbe6`.

**Method.** I wrote my own code from the Design and Deviation 1, without reading `experiments/032/*.py`. It is committed as `checks/review/exp032/reproduce.py`, with its rerun command in its header. It reads the archive's `bars/60m/` files and takes `results.json` only for the critical values and the certified intervals to compare against.
- **My own session parser.** It works in local time zones, handles US half days (a 13:00 bar and no 13:30 bar), drops stray bars at or after the close, and sets bar lengths from the next start. It adds one 17.5 h overnight per session break.
- **Declared shares.** Computed over the registered declaration periods, with the U clock scaled for irregular bars.
- **The scorers, from my earlier reviews:**
  - claim 055 and 054, with calendar durations;
  - the experiment-027 36-kernel claim-033 score on cent- or won-rounded closes;
  - SADF and GSADF;
  - my claim-034 CEV cell forecast.
- **A float cross-check of column (iii)'s denominator.** The claim-036 conditional likelihood at M = 8, maximized over the wide box and both clocks (a 21 × 21 grid, then Nelder–Mead), with its claim-038 centred enclosure at the maximizer.

**Reproduced.**
- **Data.** The increment counts are identical: 4,007 and 3,587 for E6, 3,482 and 3,349 for N24m-3. The N24m-3 declared shares match to three decimals. E6's differ in the third decimal: (0.685, 0.106, 0.052, 0.054, 0.055, 0.048) against (0.686, 0.108, 0.053, 0.051, 0.053, 0.048), from a small difference in KRX slot bookkeeping I could not pin down.
- **Column (i), v1.** It matches within 0.2 on every record: E6 138.4 and 125.7 against 138.6 and 125.5, and KO full 12.8. The flags and e-BH outcome are the same: E6 in both windows and KO full, with no other flag.
- **Column (ii), claim 033 on rounded prices.** It matches within 0.4 on N24m-3. E6 gives −5,756.7 and −2,223.6 against −5,761.7 and −2,231.2, consistent with the E6 share difference. The conclusion is the same: strongly against, with no flag anywhere.
- **Column (iv).** The SADF and GSADF statistics are identical to two decimals on all 16 records, and the 5% flags match: both on E6, none on N24m-3.
- **Column (iii), the denominator.**
  - **Upper bounds.** On all 14 records my optimized point value (log g at one parameter, which can only be ≤ log D_filter) lies below the published certified upper bound.
  - **Lower bounds.** It lies 0.3–1.0 nats below the published lower bound, out of about −10⁴. So the certified evaluator found slightly better parameters than my Nelder–Mead, and nothing contradicts the published enclosures.
- **Column (iii), the numerator.** My log q is within 0.6 of the published value on 13 records.
  - **V to the peak** is the exception. My forecast is finite at −10,642.1, against the published floored −11,292.6.
  - **Why.** My p = 1 cells and tail branches avoid the underflow that triggered experiment 028's floor.
  - **The score.** My V to-peak bound would be −10,642.1 − (−10,567.4) ≈ −75, still no flag. Zeroing the record, as registered, changed no decision.

**The Deviations are honest.** The Design was committed at 09:43 and the code and Deviation 1 at 09:49:54, before any test. `run.py` is unchanged to the results at 10:00:40.
- **Deviation 1's data facts reproduce.** KRX has six hourly bars, US half days close at 13:00, and the null-bar and stray-bar handling gives the same increment counts.

**The readings are fair, with one emphasis.** The hourly v1 flag on KO, a calm negative, is a false alarm under 021's labels.
- **Likely cause.** The declared shares show slot 0 carrying about 60% of daily variance time, a strong intraday clock that v1's flat calendar null ignores. That matches experiment 027 and my claim-033 and claim-035 reviews: ignoring the clock is not reliably safe on real hourly data, even if simulations found it nearly powerless rather than anti-conservative.
- **SK Hynix.** Claim 033's large negative log e there reflects its training-selected sublinear kernel failing over a 13× run-up. As the Readings say, that is one record and not a diagnosis.

Verdict: reproduced
