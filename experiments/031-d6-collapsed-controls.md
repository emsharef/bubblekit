---
id: "031"
title: "D6: survivorship-free additions to the positive controls — collapsed dot-com names and 2003–08 financial casualties"
status: reproduced
direction: D6
claims: ["054", "055"]
code: experiments/031/
---
## Question

Experiment 021 found that usable test v1 flags no calm negative control but misses most consensus bubbles. Its 1995–2001
and 2003–08 rows (E2, E4) contained **only survivors**, because the collapsed names had no free data then. The human's
search has since found free daily prices for most of them (`experiments/DATA.md`, "Delisted daily prices found by the
human's search").

**What this experiment measures:** do the tests behave differently on the names that actually collapsed? It runs
experiment 021's procedure, unchanged, on the librarian's collapsed-name list.

- PM approval: note `2026-10-07-delisted-go.md`, item (B). Registered against the librarian's entry `Episode list:
  D6 positive controls, extension to collapsed names` (`board/FINDINGS.md`, 2026-10-07).
- Job: **measuring behaviour on real data with consensus labels**, which are not ground truth. No test has been run on
  these series when this Design is committed.

## Design

**Names, from the librarian's entry only.** The analyst adds no names.
- **Class F (fraud) is excluded** per the PM's rule: WorldCom and Enron.
- **Class B (bubble narrative) is the positive-control group.** Classes C (casualty) and W (weak) are reported as
  separate, labelled groups and never pooled with B.

| row | class | names (source fixed now) |
|---|---|---|
| E2-C (dot-com, window 1995-01-03 to 2001-12-28) | B | InfoSpace (WIKI BCOR, split-adjusted exactly as in experiment 030); CMGI (Wayback CMGI); Exodus (Wayback EXDS); JDS Uniphase (Yahoo VIAV, the lab's loader); VA Linux (Wayback LNUX); theglobe.com (Yahoo TGLO); Commerce One (Wayback CMRC) |
| E2-C | C | Global Crossing (Wayback GBLX to 2000-05-19, then Wayback GX) |
| E2-C | W | Pets.com (`sye/` IPET), Webvan (`sye/` WBVN). **Unknown provenance** |
| E4-C (financials, window 2003-01-02 to 2008-12-30) | C | Lehman (`qstk/` LEHMQ); Wachovia (Wayback WB, then `qstk/` WB); Countrywide (Wayback CFC, then `sye/` CFC; **partly unknown provenance**); Merrill Lynch (Wayback MER, then `sye/` MER; **partly unknown provenance**); Freddie Mac (Yahoo FMCC) |

**Price series (fixed now).** All are dividend- and split-adjusted, matching experiment 021's primary "adjusted close"
kind.
- **Wayback and `qstk/` files:** their adjusted-close column.
- **Yahoo:** the lab's adjusted close.
- **`sye/`:** the "close" column, a total-return index.
- **InfoSpace:** split-adjusted WIKI closes, as in experiment 030.
- **Joined sources:** daily returns are chain-linked, each taken from the earlier source up to its last day and from
  the later source after. This removes the different adjustment bases of different vintages.
- **Raw-close variant dropped.** Experiment 021's raw-close variant is not run, because these sources' raw columns
  have different split conventions.
- **Gaps:** missing days are not filled. Tests see the available closes in date order, as in experiment 021.

**Mechanical inclusion rule** (fixed now; the PM's 90%).
- A name's span is from the later of the window start and its first available price to the earlier of the window end
  and its last available price.
- A name is tested if its rows cover at least 90% of the trading days in its span, using Yahoo's ^GSPC dates as the
  reference calendar.
- Names that fail are listed with their coverage and not tested.
- From the coverage in DATA.md, Global Crossing (a 2000-05 to 2001-05 hole) is expected to fail and Commerce One to
  pass. The rule decides, not this expectation.

**Windows: experiment 021's E2 and E4, unchanged.**
- **Full windows:** 1995-01-03 to 2001-12-28 and 2003-01-02 to 2008-12-30.
- **To-peak windows:** the same starts, ending at 021's E2 and E4 to-peak ends (2000-03-27 and 2006-12-27). Those
  ends were set by each row's first listed asset (CSCO, C), so the new rows are directly comparable with E2 and E4.
- **Later-listed names** start at their first available date, as AMZN and EBAY did in 021. A name whose span ends
  before the to-peak end uses its whole span in both variants. That is reported, not dropped.

**Tests, columns and decisions: experiment 021's, unchanged** (`experiments/021/run.py`: `score_job`, `flags`, and
the panel test per row).
- **Per name:** v1 (claim 055) and 054 raw at α ∈ {0.05, 0.10}; SADF and GSADF at 5% and 10%, with 021's critical
  values (2,000 replications, seed 20261024) at each series length; JKP Method 1 and Method 2.
- **Panel test:** computed per row-group (E2-C B, E2-C C+W, E4-C C), for groups with at least two tested names.

**Negative controls.** Experiment 021's negative windows for the matched lengths (84 and 72 months) are reused from
its committed `results.json`, not recomputed: the rule and its windows are unchanged.

**Outputs.**
- **Per name:** class, source, `sye/` flag, coverage, span, n, every column's statistic and decision, v1's status
  and fitted candidate.
- **Per group and variant:** flag counts per column, set beside experiment 021's E2 (survivors) and E4 rows and its
  matched-length negative rates.
- **Every `sye/`-based name or segment is labelled in every table.**
- **Sensitivity (fixed now):** the B group with InfoSpace's split dates shifted by one trading day either way, as in
  experiment 030.

**Implementation.**
- `experiments/031/run.py` imports experiment 021's and experiment 030's functions, and is committed before any result.
- It runs after experiments 028 and 029 (PM's order), with the single-thread BLAS prefix and at most cores − 3 workers.
- Outputs: `results.json`, `statuses.json` and `summary.csv`.

**Scope.**
- Labels are consensus from web summaries (the librarian's caveat), not ground truth. Classes C and W are not bubble
  controls of the same kind as B.
- The B group has at most seven names, so counts, not rates, are the honest summary.
- Names are survivorship-free only within the PM's list; the full 1995–2001 constituent universe is still not
  available.

## Deviations

**Deviation 1 (2026-10-07, before any code or result): the PM's label-class ruling** (note
`2026-10-07-exp-b-label-classes.md`). The Design is otherwise unchanged.
- **Positives are class B only.**
- **Class C is reported as a separate labelled group, neither positive nor negative.** That covers Global Crossing and
  all five 2003–08 financials (row E4-C). The C panel test is computed per row (E2-C C, E4-C C).
- **Class W is excluded, like class F.** It is listed with the reason, not tested:
  - Pets.com and Webvan: bubble-era failures without a documented run-up (W);
  - WorldCom and Enron: mainly accounting fraud (F).
  This replaces the Design's "C and W reported as separate groups" for W. The E2-C "C+W" panel group becomes "C"
  (Global Crossing alone, so no panel test if it passes the coverage rule).
- **The 90% coverage rule applies within each class.**
- **Scope statements added:**
  - the candidate names were chosen by the PM's request, so this is **not a census of collapsed names**;
  - the class labels rest on encyclopedic web summaries, as the librarian states.
- **`sye/` dependence after this change:** only Countrywide and Merrill Lynch (C, partly `sye/`) remain. Pets.com and
  Webvan, the `sye/`-only names, are now excluded.

**Deviation 2 (2026-10-07): implementation notes and the inclusion rule's outcome, committed with
`experiments/031/run.py` before any test.**
- **Code:**
  - `run.py` reuses experiment 021's `score_job`, `flags`, critical-value job and panel test unchanged, and experiment
    030's InfoSpace split dates.
  - JDS Uniphase's Yahoo history (VIAV) is fetched by the committed `experiments/031/fetch.py`, with its manifest.
  - Source files are read with case-insensitive column names (the `qstk/` files use "Date" and "Adj Close ").
- **Rows are dropped:** an empty adjusted-close value or a non-positive or NaN value drops that row. The coverage rule
  then counts the missing days.
- **Chain-linking:** each later segment is rescaled to agree with the earlier one on the earlier one's last day. That
  day must exist in both, or the name cannot be joined.
- **Inclusion, from a data-only inventory (`run.py coverage`), before any test:**
  - **Tested, B:** InfoSpace (100% of 763 span days), CMGI (100%), JDS Uniphase (100%), VA Linux (98.3%) and
    theglobe.com (100%).
  - **Tested, C:**
    - Lehman, Freddie Mac (100%);
    - Wachovia (100%, joined at 2006-05-22);
    - Countrywide (100%, joined to `sye/` at 2006-01-04; **partly unknown provenance**; its span ends 2008-06-30);
    - Merrill Lynch (100%, joined to `sye/` at 2007-04-12; **partly unknown provenance**).
  - **Not tested:**
    - **Exodus (B):** the registered source, the Wayback EXDS file, has no adjusted-close values at all;
    - **Commerce One (B):** the Wayback CMRC file has adjusted closes only from 2001-04-11, covering 62.4% of its
      span;
    - **Global Crossing (C):** the Wayback GBLX file has no adjusted closes, and GBLX and GX do not overlap.
  - Per the registered rule these are listed, not tested. I did **not** substitute other sources. Raw Wayback closes
    or `sye/` EXDS would have needed new, unregistered source or split choices, and the per-name sources were fixed
    at registration.
  - The B group is therefore five names.

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/031/fetch.py && uv run python experiments/031/run.py`.
- Run inside `.worktrees/analyst` after experiments 028–030, in under three minutes.
- The critical values used 7 workers, with 021's seed 20261024.
- The first launch stopped on a pool pickling error before any output was written. The fix (one module object) was
  committed before the rerun.
- Outputs: `results.json`, `statuses.json` and `summary.csv`. JDS Uniphase's input is recorded in `data_manifest.json`.

**Numerics.** v1's status is "ok" on all 20 series. No JKP call failed.

**Untested names:**
- Exodus, Commerce One and Global Crossing (Deviation 2: no usable adjusted closes);
- Pets.com and Webvan (W), WorldCom and Enron (F), per Deviation 1.

| row | class | name | variant | n | v1 log e (5%) | 054 raw 5% | SADF / GSADF 5% | JKP M2 | JKP M1 |
|---|---|---|---|---|---|---|---|---|---|
| E2-C | B | InfoSpace | full | 763 | -733.3 (no) | **yes** | **yes** / **yes** | inconclusive | inconclusive |
| E2-C | B | InfoSpace | to_peak | 323 | -209.9 (no) | no | **yes** / **yes** | bubble | inconclusive |
| E2-C | B | CMGI | full | 1762 | -578.9 (no) | **yes** | **yes** / **yes** | bubble | inconclusive |
| E2-C | B | CMGI | to_peak | 1322 | -373.1 (no) | **yes** | **yes** / **yes** | bubble | inconclusive |
| E2-C | B | JDS Uniphase | full | 1762 | -71.9 (no) | **yes** | **yes** / **yes** | bubble | inconclusive |
| E2-C | B | JDS Uniphase | to_peak | 1322 | -82.7 (no) | **yes** | **yes** / **yes** | no bubble | inconclusive |
| E2-C | B | VA Linux | full | 506 | -159.1 (no) | no | no / **yes** | bubble | no bubble |
| E2-C | B | VA Linux | to_peak | 72 | -3.6 (no) | no | no / no | bubble | inconclusive |
| E2-C | B | theglobe.com | full | 784 | -217.2 (no) | no | no / no | bubble | inconclusive |
| E2-C | B | theglobe.com | to_peak | 344 | -16.9 (no) | no | no / no | no bubble | bubble |
| E4-C | C | Lehman | full | 1510 | -1,403.1 (no) | no | no / no | bubble | inconclusive |
| E4-C | C | Lehman | to_peak | 1005 | -41.3 (no) | no | **yes** / no | bubble | inconclusive |
| E4-C | C | Wachovia | full | 1510 | -2,472.8 (no) | no | no / **yes** | bubble | inconclusive |
| E4-C | C | Wachovia | to_peak | 1005 | -1.6 (no) | no | no / no | bubble | inconclusive |
| E4-C | C | Countrywide (partly `sye/`) | full | 1383 | -882.4 (no) | no | **yes** / **yes** | bubble | inconclusive |
| E4-C | C | Countrywide (partly `sye/`) | to_peak | 1005 | -6.5 (no) | no | **yes** / **yes** | bubble | inconclusive |
| E4-C | C | Merrill Lynch (partly `sye/`) | full | 1510 | -631.2 (no) | no | no / no | bubble | inconclusive |
| E4-C | C | Merrill Lynch (partly `sye/`) | to_peak | 1005 | -21.9 (no) | no | no / no | bubble | inconclusive |
| E4-C | C | Freddie Mac | full | 1510 | -1,183.3 (no) | no | no / **yes** | bubble | inconclusive |
| E4-C | C | Freddie Mac | to_peak | 1005 | -71.7 (no) | no | no / no | bubble | no bubble |

**Counts, set beside experiment 021** (same windows, columns and critical-value procedure; 021's survivors and its
matched-length negatives).

| group | variant | names | v1 5% | 054 raw 5% | SADF 5% | GSADF 5% | JKP M2 bubble | JKP M1 bubble |
|---|---|---|---|---|---|---|---|---|
| E2-C, class B (collapsed dot-com) | full | 5 | 0 | 3 | 3 | 4 | 4 | 0 |
| E2-C, class B | to-peak | 5 | 0 | 2 | 3 | 3 | 3 | 1 |
| 021's E2 (survivors) | full | 6 | 0 | 4 | 6 | 5 | 6 | 0 |
| 021's E2 | to-peak | 6 | 0 | 3 | 6 | 5 | 5 | 0 |
| E4-C, class C (financial casualties) | full | 5 | 0 | 0 | 1 | 3 | 5 | 0 |
| E4-C, class C | to-peak | 5 | 0 | 0 | 2 | 1 | 5 | 0 |
| 021's E4 (survivors) | full | 8 | 0 | 0 | 2 | 2 | 8 | 0 |
| 021's E4 | to-peak | 8 | 0 | 0 | 1 | 0 | 8 | 0 |
| 021's negatives, 84-month windows (rate) | full / to-peak | 7 | 0 / 0 | 0 / 0 | 0.29 / 0.29 | 0.43 / 0.43 | 0.71 / 0.86 | 0 / 0 |
| 021's negatives, 72-month windows (rate) | full / to-peak | 7 | 0 / 0 | 0 / 0 | 0.14 / 0.14 | 0.29 / 0.29 | 0.57 / 0.57 | 0 / 0 |

**Panel tests:**
- E2-C class B: only CMGI and JDS Uniphase start within a week of the earliest name; the other three are dropped as
  late starts, as in 021.
  - Full window: t = −0.02 and J = −0.07, no flag.
  - To-peak: t = 1.41 (flags at 10%) and J = 5.68 (flags at 5%).
- E4-C class C (all five names):
  - full window: t = 1.02 (no flag), J = 1.74 (flags at 5%);
  - to-peak: no flag.

**Readings** (consensus labels from encyclopedic summaries, not ground truth; counts, not rates).
- **v1 flags none of the ten collapsed names, in either window.** This matches 021, where it flagged none of the
  E2/E4 survivors either. Adding the names that actually collapsed does not change v1's picture: it misses
  bubble-narrative names whether or not they survived.
  - Its log e-values are all below zero (−1.6 to −2,473). Its training-fitted CEV forecast predicts the evaluation half
    much worse than its nulls do.
- **Claim 054's raw score** flags 3 of 5 collapsed dot-com names (full window), against 4 of 6 survivors in 021. It
  flags none of the financials, as in 021.
- **SADF and GSADF** flag most collapsed dot-com names (3–4 of 5), as they did the survivors. On the financial
  casualties GSADF flags 3 of 5 (full window), more than for 021's E4 survivors (2 of 8). Their 021 false-alarm rates
  on matched-length negatives are 0.14–0.43, so these flags separate the groups only weakly.
- **JKP Method 2** says bubble on most names in every group. Its 021 negative rate is 0.57–0.86, so it does not
  separate them. Method 1 is almost always inconclusive.
- **InfoSpace, cross-reference to experiment 030:** this window starts at InfoSpace's IPO and ends 2001-12-28, so it
  is shorter than JKP's. Method 2 is inconclusive on the full window and says bubble to the peak.
- **Scope:** names chosen by the PM's request, so not a census of collapsed names. Five B names and five C names, so
  no rate is estimable. Countrywide and Merrill Lynch rest partly on `sye/` (unknown provenance).

## Review

Reviewer, 2026-10-07, against main at `1f0e5525`, which contains the results commit `2b49885c`.

**Method.** I wrote my own loaders from the Design and Deviation 2, without reading `experiments/031/*.py`, and reused my own test code from earlier reviews:
- claim 055 and claim 054 scores, from the experiment-021 review;
- the JKP estimator, the GC-J fit and Methods 1 and 2, from the experiment-003 review;
- SADF and GSADF, from the experiment-002 review.

The script is committed as `checks/review/exp031/reproduce.py`, with its rerun command in its header, and reads `data/delisted/` in place.
- **The loaders.** Wayback `adjclose`, `qstk/` "Adj Close", `sye/` "close", Yahoo JSON adjclose, and InfoSpace's split-adjusted WIKI closes.
- **Joins.** Chain-linking at the registered join days.
- **JDS Uniphase.** Its Yahoo file is the analyst's, with SHA-256 `d57d9676…` matching `data_manifest.json`.
- **Critical values.** The published 5% values per length, a design input as in my experiment-021 review.

**Every number reproduces exactly.**
- **All 20 series.** The n, span, v1 and raw log e-values, SADF and GSADF statistics and their 5% decisions, and the JKP Method 1 and 2 verdicts are identical to the table.
- **The group counts are identical.** v1 / 054 raw / SADF / GSADF / M2 / M1 come out as:

  | Group | Full window | To peak |
  |---|---|---|
  | E2-C, class B | 0 / 3 / 3 / 4 / 4 / 0 | 0 / 2 / 3 / 3 / 3 / 1 |
  | E4-C, class C | 0 / 0 / 1 / 3 / 5 / 0 | 0 / 0 / 2 / 1 / 5 / 0 |

- **The exclusions reproduce from my own inventory.** Wayback EXDS, GBLX and GX have **no** adjusted closes. CMRC has adjusted closes only from 2001-04-11.
- **Not rerun:** the panel tests and the shifted-split sensitivity.

**The Deviations are honest.**
- **Order.** The Design was committed at 08:21 and Deviation 1, the PM's class ruling, at 08:22, both before any code. The code, fetch script and Deviation 2 (the inclusion outcome from a data-only inventory) followed at 08:55:47.
- **The pickling fix.** The one-line pickling fix came at 08:55:56, before any output. Its diff only replaces a second module load with `r030.r021`.
- **The results** came at 08:59:38, and `run.py` is unchanged from the fix to them.
- **No substitution.** Not substituting unregistered sources for Exodus, Commerce One and Global Crossing follows the registered rule.

**A caveat on the Wayback adjusted closes.** The Wayback `adjclose` column is rounded to the cent, which matters for heavily split-adjusted early prices.
- **CMGI.** Its 1995 adjusted prices start near $0.35, and 19% of its first-year daily returns are exactly zero. The median non-zero move is 3.5%.
- **Other names.** JDS Uniphase (Yahoo) has 13.5% zero returns in its first year. theglobe.com, a late penny stock reaching $0.035, has 16% zero returns over its window.
- **Why it matters.** These are rounding artefacts of the source, which experiment 028 and claims 028–031 treat as outside an exact-price test's guarantee. They can move the Gaussian profile and the JKP estimates. They are unlikely to change v1's verdicts, which are all strongly negative, but CMGI's and JDS Uniphase's large positive raw-054 and SADF/GSADF values rest partly on these early, coarsely rounded segments.
- **What I'd add to the Scope.** The adjusted-close source's rounding, alongside its provenance caveats.

**The readings are fair.** v1 flags none of the ten names, and claim 054's raw score flags 3 of 5 collapsed dot-com names. SADF and GSADF flag most dot-com names but separate weakly given their 021 negative rates, and JKP Method 2 does not separate the groups. Counts, not rates, are reported, and the selection is not a census.

Verdict: reproduced
