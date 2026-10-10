# Review of the manuscript against the lab record

Date: 2026-10-09. Scope: does `manuscript/` accurately represent the lab's work at revision `55486572`?
Method: every number, formula, attribution and `\source{}` line in the six section files was checked against the
claim files (`claims/`), the experiment registrations and results (`experiments/`), the lab's paper
(`paper/PAPER.md`), `board/STATUS.md`, `board/FINDINGS.md`, `board/NOTICES.md`, `LAB_REQUEST.md` and
`paper/PROOFMAP.md`. No experiment was rerun. The manuscript build and checker were run once; the manuscript files
themselves are unchanged by this review. Line numbers refer to the files in `manuscript/sections/`.

## Verdict

The transcription is sound. Every generated table matches its `results.json`, every quoted number in the prose
traces to a reproduced experiment or a red-passed claim, and no mathematical statement is wrong. The build passes
(43 pages, 20 bibliography entries, no unresolved citations, no overfull boxes), `provenance.json` matches HEAD and
all six input hashes match the current files.

The manuscript is nevertheless not yet a faithful account of the lab's work, for one main reason: it leaves out the
lab's own conclusions. The lab closed with an explicit verdict on its signals, an explicit rejection of the
option-convention route, and a diagnosis that the daily level signal is weak. None of these appears. The result is a
draft that is more favourable to the proposed signals, and more neutral on options, than the record it summarizes.
Section A below lists these framing gaps; sections B to F list omitted results, factual slips, understated caveats,
attribution gaps and cosmetic items.

## A. Framing: what the record says and the manuscript does not

**A1. The lab's bottom line on the signals is missing.** `board/STATUS.md` (digest, 2026-10-09): "The usable answer:
calibrated GSADF (calm-window critical values) is the bubble alarm and a modest drawdown-risk screen (out-of-sample
R² ≈ 1%) ... The intraday monitor (D36) adds modest out-of-sample drawdown prediction to GSADF but is a weaker
episode alarm. The daily market-scale statistic (D37) flags fewer launches than GSADF ... but shows no demonstrated
useful forecasting gain." `paper/PAPER.md` §6.14 opens: "On real prices, no procedure tested both keeps false alarms
down and finds the consensus bubbles." Experiment 054's own reading: "It does not beat calibrated GSADF as an alarm."
The decision rule the human set in `LAB_REQUEST.md` addendum 5 was explicit: if neither new score gives power with
controlled false alarms and out-of-sample predictive content, "the practical monitor on free data is GSADF with
empirical critical values as a run-up screen." That rule was triggered.

The manuscript instead says (front.tex:40-46) "Real-data replays produce different alarm patterns from calibrated
explosive-root tests"; (signals.tex:611-616) "The daily and intraday results suggest complementary descriptions ...
Neither dominates across every application"; (front.tex:197) "It does not establish a universally superior
detector." These are true but softer than the record. The abstract, §1.1, §12 ("Reading and using an alarm") and
§17 ("What remains to be established") should state the verdict: the intraday monitor is the weaker alarm, the daily
statistic shows no demonstrated gain, no tested procedure both controls false alarms and flags the consensus
episodes, and calibrated GSADF is the practical monitor on free data.

**A2. The option-convention critique is missing.** `LAB_REQUEST.md` third addendum (the human): "Option-based bubble
measurement rests on the convention that market call prices carry the bubble ... One-cent far out-of-the-money calls
trade routinely, including in 2000 ... so the convention implies there were no bubbles in exactly the episodes the
literature calls bubbles. That makes it circular as evidence and unusable for a test." Option-convention work was
stopped; results were kept "only as conditional theory, with the convention named in each statement, and with this
critique stated." `paper/PAPER.md` §4 intro states the critique, adds that dealers price far strikes with bubble-free
models, and ends "none is offered as a usable test." Experiment 014 and PAPER §6.1 supply the empirical fact: on the
end-of-day SPY chains the largest-strike call at one to three months is at the one-cent floor on most dates.

options.tex treats the two conventions as "explicit alternatives" (line 26) and says only that "a tiny quoted call
is consequently not an assumption-free certificate" (line 152). The one-cent floor, the circularity, the dealer
point, and the fact that the sponsor stopped this route are absent. Part IV should open with them, and §17's
"For options, it is a justified connection from market observations to the valuation operator" should say that the
tick floor currently denies that connection.

**A3. The diagnosis that the daily level signal is weak is missing.** signals.tex:130-148 attributes the old score's
silence to construction (null-member forecasts, scale misfit), which is correct, but stops there. `PAPER.md` §6.8 and
experiment 049 go further: even in sample, with every parameter fitted on the evaluation data, a free-exponent
alternative beats its β ≤ 0 restriction by more than log 20 on 12.1% of consensus positives and 11.7% of calm
controls; a regression of monthly realized variance on price level, controlling for the market, gives a pooled
elasticity of −0.27 on unselected windows, about zero on run-ups (+0.05 ± 0.04) and consensus positives (+0.02 ± 0.08),
and +0.59 on calm controls. Addendum 7 summarizes: "on daily data the level signature is weak (elasticity about zero
in run-ups)." Without this, the reader is left to infer that the daily signal was merely badly built.

**A4. Novelty is stated more strongly than the record states it.** appendices.tex:385 lists "the exposure
classification and finite-trading comparison" as distinctive. `PAPER.md` §7: "we do not claim that the
discrete-rebalancing results of Section 3.3 are new"; "The literature on investment when an asset has a bubble, for
example herdegen2013strict and herdegen2016strong, may contain special cases of Theorem 1; we have not yet compared
it" (also §8 Outlook, "Prior art"). front.tex:139-146 attaches no such caveat to Theorem 1; the only prior-art
caveat (front.tex:165) is on the signals.

## B. Results in the record that the manuscript omits

- **B1. Jump accounting (experiment 041, PAPER §6.6).** All 185 flags on the historical collections were examined;
  156 survive a declared jump filter, including 137 of 153 explosive-root flags. Flagged daily records differ from
  controls by volatility rising through the window (69% above the controls' 95th percentile of the second/first-half
  ratio), not by jumps. Filtering does not improve calibration (daily calm GSADF 19.4% → 25.2%). Addendum 5 item 18
  asked for this so that "the monitor must say which kind of event it reports." Nothing in the manuscript addresses
  it.
- **B2. Hourly run-ups (experiments 032, 033, 035; PAPER §6.3).** On about two years of hourly bars, the lab's
  likelihood scores flagged 0 of 21 press-labelled names while GSADF flagged 18 of 21 and 13 of 98 calm large caps;
  the one likelihood flag after widening the forecast scales (GameStop) is on a record with about half its variance
  jump-like. The manuscript mentions hourly data only in the GSADF calibration table.
- **B3. Daily-versus-intraday head-to-head (experiment 056, Results 6; PAPER §6.13).** On the 29 run-up records both
  monitors cover, each alarms on 14; the five-minute monitor is first on 13 of those; daily alone 5, intraday alone
  6, neither 4. Relevant to "neither dominates" (signals.tex:616).
- **B4. Measured ETF costs (experiment 007, PAPER §6.1).** Against the total-return underlying, leveraged long funds
  lose a further 0.6–1.7%/yr beyond the expense ratio, inverse funds 0.1–1.1%/yr (SE 0.1–0.4%/yr); against the price
  index, dividends would be misread as cost. funds.tex §9.3 ("Costs are not a bubble") presents only the inequality.
- **B5. Survivorship counts (experiment 010, PAPER §6.1).** 57 of 506 S&P 500 members in January 2020 have no free
  daily series, 40 of 505 by December 2021, 27 of 503 in January 2023. signals.tex:395-399 gives the qualitative
  statement only.

## C. Factual and sourcing errors

| Where | Manuscript says | Record says | Severity |
|---|---|---|---|
| theory.tex:142-143 | Claims 074–076 numerical checks "summarized in the original paper's Sections 3.1 and 5.7" | PAPER §5.7 covers Theorem 1, finite grids, liquidated funds and the visited integral only; the 074–076 checks are inline in §3.1 (PAPER lines 129, 139, 149) | wrong pointer |
| theory.tex:244-247 | Pooled likelihood constructions "did not outperform per-name testing in the experiments run"; source cites experiment 013 | No registered experiment tested claims 062/063. Experiment 013 is the visited-integral sampling study. The figures are the reviewer's own simulations in `claims/062` (0.32 vs 0.43) and `claims/063` (0.39–0.44); FINDINGS line 1661 records the PM cancelling a repeat | mis-sourced |
| theory.tex:185-187 | Obstruction persists "when positive paths are required wherever the alternative has them" | Claim 006 and PAPER Theorem 22 list two restrictions only: positive continuous coefficients, and P = Q. No positive-path restriction appears | not in record |
| signals.tex:349-350 | "two-exponent, three-scale catalogue" | Experiment 019: p ∈ {1, 2}, κ ∈ {0.15, 0.20, 0.30, 0.45}, eight entries, four scales (three GBM nulls were simulated, the likely source of "three") | wrong |
| signals.tex:369-372 | Certified rounded-price calculations "within roughly one log-likelihood unit of the ideal on the tested records" | Claim 038 review: a simulated $5 GBM null at cent ticks, 30 and 125 days (−0.71 vs −0.33; −1.50 vs −0.75). Not real records | overstated |
| appendices.tex:28-30 | "In the D35/D36 likelihood code the stored slope is β/2 ...; D37 already uses the full exponent" | Half-slope: D35 common fitter (`checks/d35-fitting-protocol/model.py:73`, used by 050–051) and D36 monitor (`experiments/054/model.py`). Full exponent: experiment 049, experiments 052–053 (053: "β_053 = 2 β_D36"), and D37 | imprecise |
| appendices.tex:122-125 | GSADF: "some power cells depend materially on incompletely specified simulation details" | `experiments/002-gsadf-baseline.md` Table 4: 8 of 10 power cells outside tolerance, "Table 4 power not reproduced" | understated |
| signals.tex:627 | A cross-sectional clock "helped only within its specified model" | Experiment 029: inside the contract the selected-clock score gained essentially nothing (paired TDP differences −0.005 to 0.000, "It bought no detections here"); outside it, selection was harmful (e-BH FDR 0.255 at q = 0.05) | overstated |
| signals.tex:452-453 | "It alarms late on the 2007 financial names" | True for the consensus E4 set (BAC, JPM, AIG, FNMA); Lehman (−107) and Countrywide (−833) among the collapsed names alarm before their peaks (056 Results 5; PAPER §6.13 names the consensus list) | ambiguous |
| signals.tex:468-470 | Three positive records "lacked enough data" | Experiment 051: 000660.KS, ^N225, 000001.SS lack a complete 379-session ^GSPC-calendar history (non-US calendars) | imprecise |
| signals.tex:491-493 | "historical publication timing of the volatility-index series was not fully documented" | Experiment 047: VIX before 2003-09-22 is a retrospective backcast, so pre-2003 SPX windows are a "retrospective reconstructed-scale analysis". Separately, experiment 048 (math's stricter as-of design) was withdrawn before any score; the index result rests on 047's own fixed clock | understated; omission |
| signals.tex:182-183 | Claim 045's "counterexamples also show why stationarity or past-only selection alone is insufficient" | Claim 045 holds only the past-only-selection counterexample; the stationarity one is `claims/refuted/d34-stationarity-calibration.txt` | misattributed |
| signals.tex:286-287 | "Four exploratory per-cell checks fail" | True, but two of the four are on oracle or no-market variants (I100 oracle monitor; N_C3 g0 batch), not the fitted statistics whose averages precede the sentence | cosmetic |
| theory.tex:263-269 | Small-scale obstruction stated without P = Q | Claim 073: "Conditional on the audited price laws AX-54/55, with P = Q" | missing hypothesis |

## D. Understated caveats and missing hypotheses

- **theory.tex:132-141 (product defect).** Claim 076 requires, beyond independence under Q, that the product is a
  continuous local martingale in the common filtration. Only independence is stated.
- **theory.tex:118-120.** "can lose [its mean] in the infinite-horizon limit": claim 074 and PAPER line 129 say only
  that the family is not uniformly integrable (E[V_t 1{V_t > 10}] → 1). "Lose its mean" is an inference.
- **theory.tex:242-244.** "pooling names can add occupation over price levels and improve estimation": claim 015 is a
  limiting-power statement for the pointwise rule (P(Φ_n = 1) → P(D_union) ≥ max_i P(D_i)); "No independence or rate
  gain is asserted." It is not an estimation-precision result.
- **theory.tex:207-215 (Sin).** No `\source` line (it is claim 003 part 3). The record qualifies the construction as
  holding "on some finite horizon T₀", omitted here.
- **funds.tex:89-97 (eq. meanone).** Claim 009 requires Q(X_t > 0 on [0, T]) = 1 and 0 ≤ π ≤ 1; the equation is stated
  without either.
- **funds.tex:154-155.** "Geometric Brownian controls and the inverse funds are consistent with zero": experiment 017
  marks the GBM inverse cells at π = −3, N ≥ 12 as "unresolved, not evidence" (SE 0.22–0.98) and the GBM long controls
  "fragile at π = 3" (single cells up to about 3 SE; pooled consistent). The strict-underlying inverse cells are
  correctly described.
- **options.tex:205-206.** "an ideal continuum of index options would determine that distribution": textbook
  (Breeden–Litzenberger) but claim 016's Not-shown list explicitly declines "finite-option-panel recovery of ν_T,
  call-derivative identity."
- **options.tex:240-241.** "detects sufficiently large violations as sample size grows": experiment 046 review says
  "detection in finite cases, not a demonstration of asymptotic power, since fixed B and J do not instantiate claim
  044's expanding-range, shrinking-mesh scheme."
- **options.tex:246-247.** "The tested compatibility rules have no power in that basket": experiment 046 says no
  rejection was observed and labels the process rows diagnostic; PAPER §8 uses the same "no power" wording, so this
  matches the paper but is stronger than the experiment record.
- **options.tex:278-294 (What remains).** The funds paragraph omits the record's concrete open mathematics (PAPER §8
  "Other exposures"; claims 009/018 Not shown): the wealth identification (W), convergence of the defect when the
  continuous limit is strict with 1/2 < π < 1, the limit through absorption at zero, exposures above one on a grid
  without a liquidation rule, discretely monitored floors, random grids, and the converse d_H = 0 ⇒ δ_T = 0. Some
  appear in the body (funds.tex:101-103, 146-147) but not in the summary.

## E. Attribution and prior art

- **signals.tex:171.** The marginal rank rule is cited to `vovk2013conditional`. Claim 045 and PAPER (Proposition
  45) take the marginal exchangeable-quantile lemma from `tibshirani2019conformal` Lemma 1 and use Vovk 2013 only for
  the training-conditional guarantee. The registry has both keys.
- **theory.tex:180-205, front.tex:148-151.** No mention of Bahadur–Savage. Claim 003 line 299 and PAPER §3.4: "we
  claim no novelty for the general mechanism, which bahadur1956nonexistence, unread, may anticipate."
- **options.tex:138-139.** Only `bayraktar2011strict` is cited for the American-call relation. The claim 017 reviewer:
  Cox and Hobson 2005 "is the standard source for the dividend-free 'American call = European call + bubble' relation
  ... should be read and cited before the paper presents part 1." `cox2005local` is still "wanted" in the registry.
- **theory.tex:207-215.** PAPER §3.4 and §7 note that `jarrow2007asset`, unread, "may already contain the qualitative
  point" on measure dependence; not mentioned.
- **A4 above** (Herdegen papers; discrete-rebalancing results not claimed new).

## F. Cosmetic

- appendices.tex:260-285: claims 062 and 063 are cited in signals.tex but absent from the claim map.
- `generated/references.bib`: `bayraktar2011strict` carries year 2012 and `obayashi2015lifetime` year 2016 (keys use
  the working-paper year, entries the final year, inherited from the registry); `greenwood2017bubbles` and
  `kurozumi2021time` have an empty `howpublished`. Appendix C's sentence about version years covers this.
- `prepare.py:95` loads and hashes `experiments/045/results.json` but never uses it.
- Build log: two hyperref "Token not allowed in a PDF string" warnings from the math in the subsection title at
  appendices.tex:33; `check.py`'s regex does not catch them. `\texorpdfstring` fixes it.
- funds.tex:130-135: the π = −1, X > 3/2 example comes from claim 004 (price-level exit) and sits under the floor-rule
  subsection of claim 011; claim 011 part 3 shows the two rules coincide for N = 1, a = 1/2, so this is consistent.
- signals.tex:357-358: the 24% GBM flag rate is experiment 022's cell; experiment 019's matching cell gave 28.1%. The
  source line credits 019–028 jointly.

## G. Verified as accurate

- **Theory.** Theorem 1 (iff, endpoint table, π = 1/2 always), coefficient assumptions, the wealth convention, the
  Feller kernels 1/(2π−1) and 1/(1−2π), scale density (x/c)^(−2π), both endpoints bad, the Karatzas–Ruf (7.4) credit,
  the three examples (σ = 1, σ = x², σ = 1 + x²), the correction of PROPOSAL.md's Theorem A and "not a literature
  conjecture", claims 074–076 statements, the compatible-tails proposition and the R²/(2(p−1)σ(R)²) formula, the
  obstruction theorem's remaining content, Sin's identified set, the visited-range identity, claims 071 and 073.
- **Signals design.** Shared model, mixture grid and weights, arctan map, whole-prefix null profile, failure statuses,
  daily construction (20 SPY returns, geometric-mean normalization, A_t = w m_t^g, 252/252), intraday construction
  (252-session clock, λ = 2^(−1/20), 21 sessions, 1,617 returns, overnight excluded, half-exponent storage), the rank
  rule, the 2,287 of 3,000 figure, the three-point scale grid, the 76–83% scale-misfit share.
- **Tables.** `calibration.tex` (6 cells) = experiment 040; `simulation.tex` (24 cells) = experiment 055, with the
  CEV p = 2 cell simulated at the full exponent β = 2; `transport.tex` = 055; `daily_periods.tex` (7 rows, summing to
  153,716) = experiment 056; `intraday.tex` = 054; `forecast.tex` = 054 (0.3906/1.0535/1.3935; 0.3110/1.4869/1.7377).
- **Simulation prose.** Six finite recovery cells, median relative error ≤ 6%, 11 of 12 gates, 79.2% vs 80%, 22 null
  cells at 4.85%/4.61%, the β = −40 stress cell, own-SV p = 2 monitor 10.0–18.6%, ±2.54/−2.58, intraday −4.14, transport
  4.0/22.0, 4.2/40.8, 5.4/69.8, 10 vs 50 substeps with 4 flips in 2,100, exact-model 0.1% null, 24–46% → 96–98%,
  five-minute ≈ 1, the 44.7 → 17.3 → 2.1 switch costs (026), regime breakage (025).
- **Real-data prose.** 416,380 windows; 15.3/19.0/33.2 → 8.2/10.9/23.0 and 6.4/7.4/14.8; 150,519 launches at
  2.91/3.05/6.86%; 3,197 and 153,716; 15 of 30 vs 14, medians 377 vs 142; 4 of 9 vs 3; 7 vs 10 of 18; 4.8% of 3,556
  and 35 of 91; 315 of 650; repaired score 10,000 windows, 4.9%, 1.4–16.2%, 3 of 33, 20 of 103, AUC 0.34 (0.19–0.57);
  Spearman 0.34 on 9,840 windows; implied-vol silence and sensitivity crossings; intraday medians 2.35/1.48/−3.59/−5.94
  already in the full-variance convention; 499 references from 2017–18, targets from 2019-02; 14 vs 20 (+1 on peak);
  142 vs 57.5; 7 and 7; 109 of 449; seven all-failure records; 163 of 182; 1,127/610/30/4.9%; 5.0% vs 5.4% of 8,600,
  2.3–9.8%; gains 0.34 and 0.25; daily R² 0.03–0.16% and "no demonstrated useful incremental gain"; survivorship
  recovery 34% overall and 11–14% before 2008; 1994 start from SPY history.
- **Funds and options.** Signed-gap identity; finite-grid proposition with exponent N; loss decomposition; reversal
  table; L¹ non-convergence; Emery localization; 0.786/0.819/0.833 → 0.8465 (experiment 012); inverse and
  leveraged-long bounds; 0.40–0.96 and 0.36–0.50 (experiments 017–018); cost inequality and Avellaneda–Zhang; Z_F
  bounds and the dip counterexample; the refuted visible-overshoot idea presented as refuted; parity residual table and
  the 2h rule (D31 design, no data run); lowest-strike construction with E[Y] = K₁ + c(K₁) ≥ 1; 0.75^252 ≈ 3.3e−32;
  American-call inequality with distributions and the finite-exercise-date argument; basket additivity; proportional
  example (refuted ordinary-weight idea presented as refuted); killed-weight identity and hazard mixture; recovery
  formula, weaker condition, compatibility check; estimator contract; 0.0041 vs 0.0035; budget bound; experiment 020
  withdrawn so "no demonstrated gain" is accurate.
- **Appendices.** All Appendix A constants, domains, predicates and counts match the code (055/d37stat.py, 054/model.py
  and run.py, 056/run.py, d35 calibrate.py). Appendix B derivations match claims 001, 003, 006, 039, 045, 051, 053.
  Every claim and experiment number in Appendix C exists; claims 046–050 never existed and are never cited. Lean:
  toolchain v4.35.0-rc2, Mathlib pinned by revision, no `sorry`, no axiom declarations; PROOFMAP entries for 001,
  002, 003, 017, 019, 044 support the manuscript's scope statements. Comparator keys `liu2022panel` and
  `obayashi2015lifetime` are the right references for experiments 004 and 005. All 20 bibliography keys are cited in
  PAPER.md for the same purposes.

## Suggested order of repair

1. A1 (abstract, §1.1, §12, §17): state the lab's verdict and the triggered decision rule.
2. A2 (Part IV opening, §17): the one-cent floor, circularity, dealer models, and that the route was stopped.
3. A3 (§5.4): add the in-sample diagnosis and elasticity regression.
4. The table in C, top to bottom; then D and E.
5. B1–B5 as short paragraphs or table rows in Appendix C's experiment map (041, 032–033, 035, 007, 010 are
   currently unmapped).
6. A4 and F last.
