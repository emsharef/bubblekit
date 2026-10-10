---
id: "042"
title: "D29: intraday evaluation at scale on Alpaca IEX 5-minute bars — time-to-flag on 2020–21 and 2024–26 positives, false alarms on calm large caps, forward-outcome regressions"
status: withdrawn
direction: D29
claims: ["033", "036", "037", "038", "039", "055"]
code: experiments/042/
---
## Question

This is LAB_REQUEST.md's fifth addendum, item 21 (PM notes `2026-10-08-addendum5-program.md` and
`2026-10-08-d29-clock-choice.md`).

**The question:** on free intraday data at 5-minute sampling, with the clock declared before the test windows, the
forecast scale grid widened to κ = 4 and D19's exact rounding filter:
- how soon do the intraday scores flag the registered positives relative to their price peak?
- how often do they flag calm large caps over the same dates?
- do they predict forward outcomes as in D24?

**The data start, stated as the PM requires: Alpaca's free IEX minute history starts on 2020-07-27, not 2016**
(`experiments/DATA.md`, probe `experiments/data/alpaca_iex_probe.py`). The 2020–21 positives are covered only from
that date.

**Job:** measuring behaviour on real data with consensus labels: time-to-flag, false alarms on controls, and
predictive content. No test has been run on these data when this Design is committed.

## Design

**Data.**
- **Source:** Alpaca IEX 5-minute bars (`timeframe=5Min`, `feed=iex`, raw prices), regular session 09:30–16:00 ET,
  from 2020-07-27.
- **Keys:** read from the macOS Keychain at run time (`security find-generic-password -s alpaca-key-id -w`,
  `alpaca-secret`), never printed or written to a file.
- **Storage:** bars cached gitignored in `data/d29/` by committed fetch code, with a manifest of requests and SHA-256s.
  A 5-minute slot with no IEX trade has no bar; it is merged into the next bar's duration, as experiment 032 did for
  null bars.
- **Massive cross-check:** for 10 names fixed now (AAPL, MSFT, NVDA, GME, AMC, TSLA, PLTR, SMCI, KO, PG), over the last
  two years. Report the share of 5-minute closes within one cent of the IEX close, and the bars present in only one
  feed. The Massive key comes from the Keychain (`massive-key`) the same way.

**Records.**
- **Positives:**
  - the 2020–21 growth and meme names (Section 6.2's E5 GME, AMC, KOSS, BB; E9 ARKK, TSLA, ZM, PTON). Each record
    runs from 2020-07-27 to its 021 window's end.
  - the 2024–26 narrative names: experiment 033's class-B list, with 033's windows truncated at 2020-07-27 where
    needed.
- **Controls:** calm large caps over the same dates, by experiment 033's time-matched rule. For each distinct positive
  window: SPY and DIA as index proxies (the indices themselves are not on Alpaca), and 5 DJIA members by experiment
  021's member rule at the window's start.
- **Rolling unselected subset (item 16's design where data volume allows):**
  - 100 current S&P 500 members (experiment 039's pinned list), drawn by `SeedSequence(20261042)`;
  - 6-month windows starting each month from 2020-08 for as long as 126 forward trading days remain;
  - forward outcomes as in D24, from experiment 039's Yahoo daily closes.

**Monitoring for time-to-flag.**
- **Checkpoints:** for each positive and its controls, scores at every month-end inside the record, each on the
  trailing 6 months of 5-minute bars, split at ⌊N/2⌋.
- **Time-to-flag:** the first month-end with a flag, minus the record's peak date. The peak is the maximum close
  inside the record, used **only for reporting** this offset, never for choosing windows.

**Clock** (the PM's choice (a)).
- **Windows starting before 2021-07-27:** experiment 027's published U(1.5, 0.25) 5-minute session shape, with
  overnight share 0.25.
- **Windows starting on or after 2021-07-27:** each name's own shape from its prior 12 months of IEX 5-minute bars.
  Each slot's share is that slot's mean squared log return, normalized, with slot 0 = overnight plus first bar.
- **The catalogue:** {F, U}.
- **Labelled subset:** results for windows starting on or after 2021-07-27 are reported separately, which checks the
  addendum's prior-year rule where it is possible.

**Scores per window.**
- **(i) v1** (claim 055) on 5-minute closes with calendar durations.
- **(ii) Claim 033 with {F, U}, labelled no guarantee for rounded prices.** It uses experiment 035's widened forecast
  (p ∈ {0.5, …, 2} × κ ∈ {0.20, 0.30, 0.45, 0.70, 1.00, 1.50, 2.00, 3.00, 4.00} on both clocks) and its original G₀
  and Gaussian denominators, matched.
- **(iii) D19's exact rounding filter, a certified score at the window end:**
  - **Numerator:** the predictable local-lognormal forecast's certified lower numerator
    (`checks/d22-predictable-forecast/forecast.py`, expanding fit), with p ∈ {1, 3/2, 2} × κ ∈ {0.10, 0.20, 0.30,
    0.45, 0.70, 1.00, 1.50, 2.00, 3.00, 4.00} × {F, U}.
  - **Denominator:** claim 038's certified upper denominator (`checks/038/certify.py`). The box is b ∈ [−2, 2],
    w ∈ [0.01, 16] (volatility up to 4), covering the volatilities experiment 035 found outside the old box, with
    δ = 0.01, factor 2, count 4, max_count 64 and max_evaluations 256.
  - **Not covered:** records with a zero label or a tick other than a cent.
  - **Budget:** a fixed order (positives, then controls, then the rolling subset) and a 12-hour wall cap. Records not
    started by the cap are "not attempted", and budget-exhausted ones are "unresolved, with bounds".
- **(iv) SADF and GSADF** on the 5-minute closes, with experiment 021's simulated critical values at each length.

**Decisions:**
- flags at α = 0.05 (score above 20; for (iv) the 5% simulated critical value);
- original-m e-BH per positive group, per control window set, and per rolling month, at q = 0.05.

**Outputs.**
- **Per positive:** the time-to-flag for each column (in months, negative = before the peak), the checkpoint scores,
  and the clock used.
- **Per control set:** the false-alarm rate per column, all windows and the labelled ≥ 2021-07-27 subset.
- **Rolling subset:** D24's regressions (Driscoll–Kraay primary, two-way clustered secondary) and the period table.
- **Column (iii)'s certificate statuses,** and runtime.
- **The Massive cross-check.**
- Files: `results.json`, `statuses.json` and `summary.csv`.

**Implementation.**
- Fetch and run code reuse experiments 021, 027, 032, 033, 035 and 039, and the D19/D22 checks. They are committed
  before any test.
- **Smoke tier:** 2 positives and 2 controls at 2 checkpoints, timed. If it projects more than 24 hours on 7 workers,
  every column but (iii) runs in full, and (iii) keeps its fixed order under the cap.
- Runs on a fresh branch after this registration merges, with the single-thread BLAS prefix, at most cores − 3
  workers, after experiment 039 finishes.

**Scope.**
- IEX-only bars, from 2020-07-27.
- Consensus labels from press summaries.
- Column (ii) carries no guarantee on rounded prices.
- Column (iii) covers only its declared box and clocks.
- Survivorship as in D24.

## Deviations

**Deviation 1 (2026-10-08, before any data fetch is complete and before any test): the consolidated SIP feed from
2016.**
- **Why:** the registration's data limit was a property of `feed=iex` only. The free plan's `feed=sip` (consolidated
  tape) returns full 5-minute bars from 2016-01-04 (`experiments/DATA.md`, correction). An IEX fetch had started and
  was stopped with no file saved.
- **Data:**
  - Alpaca SIP 5-minute bars, raw prices, 2016-01-04 to 2026-10-07;
  - only bars inside the regular session 09:30–16:00 ET are stored;
  - SIP replaces IEX throughout, and the slot rule for a 5-minute slot without a bar is unchanged.
  - The Massive cross-check compares SIP with Massive, both consolidated feeds, using the registered statistics.
- **Records:**
  - the 2020–21 positives run over their experiment 021 windows (E5 from 2020-06-01, E9 from 2019-01-02), no longer
    truncated at 2020-07-27;
  - the 2024–26 names keep experiment 033's windows.
- **Clock:**
  - **Primary:** every window uses each name's prior 12 months of SIP bars (the addendum's rule). This is now possible
    everywhere, since every window starts in 2017 or later.
  - **Labelled secondary:** the PM's choice (a), experiment 027's U(1.5, 0.25) shape for windows starting before
    2021-07-27, is kept for column (ii) only, so that ruling's comparison exists. The ≥ 2021-07-27 subset is still
    reported separately, as the PM asked.
- **Rolling unselected subset:** monthly 6-month windows from 2017-01, no longer from 2020-08, so that each has a
  prior-year clock. The same seeded 100-name draw is used.
- **Controls:** DJIA members from 2018 on, so the E9 controls also get a prior-year clock.
- **Unchanged:** the columns, decisions and outputs.

**Deviation 2 (2026-10-08, before any test), per the PM's note `2026-10-08-d29-sip-probe.md`.**
- **Probe:** `feed=sip` minute bars are reachable for 2019 (AAPL, SPY and GME on 2019-06-03) and for GME on
  2021-01-27 (`experiments/DATA.md`). Deviation 1's switch to SIP stands.
- **IEX as a labelled secondary:**
  - IEX 5-minute bars, regular session, from 2020-07-27, are fetched as well.
  - Columns (i), (ii) and (iv) are recomputed on IEX bars for every record and checkpoint that starts on or after
    2020-07-27.
  - Column (ii)'s clock on IEX is the name's prior 12 months of IEX bars where that exists (windows from 2021-07-27),
    and experiment 027's U(1.5, 0.25) shape before that.
  - Column (iii) is not recomputed on IEX.
  - The IEX results are reported beside SIP's and never pooled with them.
- **Time-to-flag from a stated onset:**
  - **The rule, declared now:** each positive record's onset is the date of its minimum daily close (the last
    regular-session close each day) before the record's peak, both taken within the record. This is the start of the
    trough-to-peak run-up.
  - **Reported:** for each column, the first flagged month-end minus the onset (in trading days and months), beside
    the registered offset from the peak.
  - **Scope:** onset and peak are used only for reporting, never to choose windows or checkpoints. Following the
    librarian's D29 entry, neither offset is a detection delay in the quickest-detection sense; the controls'
    false-alarm rates are reported beside them.

**Deviation 3 (2026-10-08, with the run code and before any test): implementation choices.**
- **Splits.** SIP and IEX bars are raw prices. Every close before a Yahoo split date is divided by that split's
  ratio: the events come from the keyless daily chart, as in experiments 021 and 039, are fetched by
  `fetch.py splits`, and include Yahoo's spin-off ratios.
  - Columns (i), (ii) and (iv), and every clock, use the adjusted closes.
  - Column (iii) needs actual cent prices, so it uses raw closes, and a window that contains a split date is "not
    covered".
  - Without this, AAPL's 4-for-1 split on 2020-08-31 puts 95% of its prior-year clock in slot 0. With it, slot 0 holds
    0.38.
- **Critical values.** A 5-minute window has about 9,800 closes, and one GSADF evaluation takes about 2 s there, so
  2,000 replications at every distinct length are infeasible. Experiment 021's simulation (same seed scheme, 2,000
  replications) runs at a grid of lengths every 1,000 closes spanning the observed lengths, and each window's 5%
  critical value is interpolated linearly in n.
- **Clock fallback.** The prior-year clock needs at least 100 complete regular sessions (all 78 bars, plus the
  previous session's last bar) in the 12 months before the window start. Otherwise the window uses experiment 027's
  U-shape and is labelled "U-fallback" (recent listings).
- **Bars.**
  - A missing slot is merged into the next bar of its session, and trailing empty slots (half-days) add nothing.
  - The first bar of each session carries the overnight duration, 17.5 hours, as in experiment 027.
  - A window with fewer than 1,000 closes is untestable.
- **Checkpoints.**
  - Each checkpoint is the last SPY session of a month inside the record. Its window is the six months of sessions up
    to and including it, which may begin before the record's start, because bars exist from 2016.
  - Controls are scored at their positive record's checkpoints.
- **Peak and onset** use each day's last regular-session close (split-adjusted). Offsets are counted in SPY trading
  days, and the peak offset is also given in months.
- **Rolling subset.**
  - Each window starts at the first SPY session of a month from 2017-01 and ends at the last daily close before six
    months later.
  - Forward outcomes use experiment 039's Yahoo closes and its 99% coverage rule.
  - The regressions are D24's in-sample coefficients, with Driscoll–Kraay errors (lag ⌈1.5 × 6⌉ = 9 months) and
    two-way clustered errors. No out-of-sample split was registered, so none is used.
- **e-BH panels:** each (group, checkpoint) for positives and controls, and each start month for the rolling subset.
- **Smoke tier:** GME and NVDA at two mid-record checkpoints, and SPY and KO at two of their sets' checkpoints.

**Deviation 4 (2026-10-08, after the smoke tier and before the full run): the smoke tier's projection, and column
(iii)'s coverage.**
- **Smoke tier** (`smoke.json`: GME and NVDA at two mid-record checkpoints, SPY and KO at two of their sets'
  checkpoints; scores not tabulated): about 70 s per window for columns (i), (ii) and (iv) with the IEX secondary,
  over 1,604 monitored and 10,600 rolling windows. That projects **34 hours on 7 workers**.
  - It is above the 24-hour trigger, so per the registered rule columns (i), (ii) and (iv) run in full.
- **Column (iii) does not cover these data.** All 8 smoke windows came back "not covered (zero label or sub-cent
  tick)".
  - **The cause:** the consolidated tape includes sub-penny prints (midpoint and dark-pool executions), so 5-minute
    closes are often not on the cent grid. The sub-cent share of closes is 27–49% on SIP and 21–45% on IEX (AAPL,
    KO, GME and SPY, all bars).
  - **The rule applied:** the registration's coverage rule ("not covered: records with … a tick other than a cent")
    applies as written. Column (iii) is reported as not covered for every window, with this share as the reason.
  - **What is not done:** prices are not rounded to the cent, which would put the exact rounding filter outside its
    premise. A cent-rounded or sub-penny-aware variant would need a new registration.
  - The 12-hour cap therefore costs nothing.
- **Unchanged:** everything else. The run starts after experiment 043.

**Deviation 5 (2026-10-08): stopped before results.** Per the human's sixth addendum (NOTICES 2026-10-08, "fix the score"; LAB_REQUEST addendum 6, items 23–25): experiments 042, 044 and 048 stop, and 046 continues, the full run started 16:45 was stopped about 39 minutes in. The main process, then its seven orphaned pool workers, were terminated with SIGTERM. No `results.json`, `windows.json.gz` or `summary.csv` was written, and no score was read. The data (SIP, IEX and Massive manifests), code, smoke tier and Deviations 1–4 stay committed for any later re-registration.
## Results

**Status: withdrawn (2026-10-08), stopped before any result,** per the human's sixth addendum (NOTICES 2026-10-08, "fix the score"; LAB_REQUEST addendum 6, items 23–25): experiments 042, 044 and 048 stop, and 046 continues. No result exists.

## Review
