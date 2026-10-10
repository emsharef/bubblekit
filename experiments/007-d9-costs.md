---
id: 007
title: "D9 inputs: cost drag, tracking error and implied financing spreads of eight leveraged and inverse funds, from free daily prices"
status: reproduced
direction: D9
claims: []
code: experiments/007/
---
## Question

Job: **measure the model's inputs** (PM note `2026-10-06-exp-d9-costs-tracking.md`). No hypothesis is tested. This
is a measurement whose outputs are the numbers a D9 claim treats as given.

The proposed claim 004 (on `math/d9-holding-period`; not used here as a premise) models one holding interval of
length Δ as follows:

  L/w = (1 − π)B + πU − C + η,    C = [f + (−π)⁺λ + (π − 1)⁺ℓ]Δ,

with:
- B = 1 + rΔ, the gross return on cash;
- U, the underlying's gross return;
- f, the expense rate;
- λ and ℓ, the financing spreads on short and on levered long exposure;
- η, the tracking deviation, with E|η| ≤ Bε.

This is the accounting of [avellaneda2009path] (1)–(2), proved as AX-07. We measure, for each fund and period:
1. **The daily residual** e_t = R^F_t − [(1 − π)r_tΔ_t + πx_t − fΔ_t], where R^F_t is the fund's simple return and
   x_t the underlying's. Its mean is the cost drag beyond the stated expense ratio. Its distribution per day, and
   compounded over 1-month and 1-year blocks, gives an empirical ε.
2. **The implied financing spread.** It is ℓ̂ = −ē/((π − 1)Δ̄) for π > 1, and λ̂ = −ē/((−π)Δ̄) for π < 0, annualized.
   This attributes the whole mean residual to the spread, so it is an upper-bound-style reading that also absorbs
   any other systematic cost.

These are **market closing prices, not NAV**. The funds' premium or discount to NAV, and its day-to-day change, sit
inside e. Nothing here separates them.

## Design

**Funds and underlyings.** Fund ↔ π ↔ underlying:
- QLD 2, QID −2, TQQQ 3, SQQQ −3, all against QQQ.
- SSO 2, SDS −2, UPRO 3, SPXU −3, all against SPY.

**Data** (sources verified in `experiments/DATA.md`).
- Yahoo daily chart data for the eight funds, QQQ, SPY, ^NDX and ^GSPC, fetched by `experiments/007/fetch.py` into
  `data/d9/` (gitignored). The SHA-256 of each cached file is recorded in the results.
- Yahoo's adjusted close is recomputed by Yahoo as new distributions occur, so a later fetch can differ slightly.
- Last date used: 2026-10-05.

**Returns.**
- Fund and underlying returns use Yahoo's split- and distribution-adjusted close: R_t = A_t/A_{t−1} − 1.
- Primary underlying: QQQ or SPY (the PM's choice). That is a total return net of the ETF's own fee.
- Sensitivity: the price index ^NDX or ^GSPC, which has no dividends and no ETF fee. The funds' benchmarks are the
  indexes, and whether their swaps reference price or total return is not verified, so both are reported.

**Reference rate.**
- r_t is the rate known at the start of the interval: the previous trading day's value.
- Before 2018-04-02: ^IRX close/100, the 13-week T-bill discount rate, used as a simple annual rate without
  discount-to-yield conversion (the difference is a few basis points).
- From 2018-04-02: New York Fed SOFR/100.
- Δ_t = (calendar days from t−1 to t)/365, for both interest and fee.

**Expense rate f.** Current ProShares ratios, as in DATA.md: QLD 0.98%, QID 1.02%, TQQQ 0.97%, SQQQ 0.99%, SSO 0.88%,
SDS 0.91%, UPRO 0.89%, SPXU 0.90%. These are applied to the whole history. Parsing EDGAR's N-CSR history is not cheap
(per-fund tables inside long HTML filings), so it is not done. That is a stated limit: if historical ratios differed,
the gap moves into ē.

**Exclusion rule (fixed now).** A day t is excluded if, on t, the fund or its underlying has a split or a
distribution (dividend or capital gain) ex-date in Yahoo's event lists. A day is also excluded if any of the four
inputs is missing on t or t−1. The adjusted close should already handle such days, and excluding them guards against
adjustment errors. The count of excluded days is reported.

**Periods.**
- Whole history: each fund's first full day through 2026-10-05.
- 2020-01-01 to 2021-12-31.
- 2023-01-01 to 2026-10-05.

**Statistics, per fund × period × underlying (primary, then sensitivity).**
- n, and the mean daily residual ē with its Newey–West SE (lag 5). Also ē annualized as ē/Δ̄ in %/yr.
- Daily |e|: mean, median, 95th and 99th percentiles, and max.
- Horizon tracking error over non-overlapping blocks of h ∈ {21, 252} consecutive included days:
  e_h = Π(1 + R^F)/Π(1 + R^model) − 1, where R^model = (1 − π)rΔ + πx − fΔ.
  - Reported: mean e_h, mean |e_h|, the 95th percentile of |e_h| and the max |e_h|.
  - The empirical ε at horizon h is mean |e_h|.
  - Blocks run across excluded days, which are dropped. Blocks shorter than h at the end of a period are dropped.
- Implied spread: ℓ̂ or λ̂ in %/yr, with SE from the Newey–West SE of ē.

**Not done.** No cross-π test (that is math's, in D9) and no NAV data.

**Outputs.**
- `experiments/007/results.json` and `experiments/007/summary.csv`.
- Regenerate with `uv run python experiments/007/fetch.py` then `uv run python experiments/007/run.py`.

## Deviations
none. The Design ran as registered. The ETF-fee reading of the implied spreads, below, is interpretation added after
the result. It is stated symbolically, and no registered number is altered by it.

## Results

All numbers are from market closing prices, not NAV, so premium and discount sit inside e. The expense ratios are
today's values applied to the whole history. Data was fetched 2026-10-06 and used through 2026-10-05; the file
hashes are in `results.json`.

Exclusions: 99–155 days per fund were removed against the ETF underlying, and 30–74 against the price index. This is
dominated by the ETFs' quarterly distribution ex-dates.

**Whole history, against the ETF underlying (primary).** ē is the mean daily residual, annualized, with its
Newey–West SE. The implied spread attributes all of ē to ℓ (π > 1) or λ (π < 0). The empirical ε at horizon h is the
mean |e_h| over non-overlapping h-day blocks.

| fund | π | from | n | ē (%/yr) ± SE | implied spread (%/yr) ± SE | median \|e\| (bp) | p99 \|e\| (bp) | ε 21d (%) | ε 252d (%) | p95 \|e_252\| (%) |
|---|---|---|---|---|---|---|---|---|---|---|
| QLD | 2 | 2006-06-22 | 4981 | −0.61 ± 0.38 | ℓ = +0.61 ± 0.38 | 4.96 | 110.55 | 0.149 | 0.543 | 1.284 |
| QID | −2 | 2006-07-14 | 4965 | −0.86 ± 0.41 | λ = +0.43 ± 0.20 | 6.50 | 113.84 | 0.192 | 1.143 | 2.883 |
| TQQQ | 3 | 2010-02-12 | 4087 | −1.72 ± 0.39 | ℓ = +0.86 ± 0.20 | 6.24 | 51.85 | 0.169 | 1.181 | 2.769 |
| SQQQ | −3 | 2010-02-12 | 4083 | −1.06 ± 0.40 | λ = +0.35 ± 0.13 | 7.25 | 52.32 | 0.171 | 0.968 | 2.759 |
| SSO | 2 | 2006-06-22 | 4948 | −0.77 ± 0.36 | ℓ = +0.77 ± 0.36 | 4.29 | 73.37 | 0.124 | 0.573 | 1.697 |
| SDS | −2 | 2006-07-14 | 4968 | −0.08 ± 0.36 | λ = +0.04 ± 0.18 | 5.61 | 67.58 | 0.166 | 0.771 | 3.160 |
| UPRO | 3 | 2009-06-26 | 4224 | −0.99 ± 0.31 | ℓ = +0.50 ± 0.16 | 5.82 | 53.90 | 0.157 | 0.968 | 2.032 |
| SPXU | −3 | 2009-06-26 | 4244 | −0.48 ± 0.37 | λ = +0.16 ± 0.12 | 7.40 | 45.63 | 0.160 | 0.846 | 3.033 |

**Sub-periods, and the price-index sensitivity.**

| fund | ℓ̂ or λ̂, 2020–21 | ℓ̂ or λ̂, 2023–26 | ē vs price index, whole (%/yr) |
|---|---|---|---|
| QLD | +0.59 ± 0.99 | +1.05 ± 0.25 | +0.51 ± 0.40 |
| QID | +0.44 ± 0.49 | +0.14 ± 0.17 | −1.98 ± 0.40 |
| TQQQ | +1.64 ± 1.27 | +1.18 ± 0.20 | +0.74 ± 0.40 |
| SQQQ | +1.36 ± 0.78 | +0.04 ± 0.17 | −3.31 ± 0.43 |
| SSO | +0.10 ± 0.66 | +0.60 ± 0.38 | +2.69 ± 0.36 |
| SDS | +0.50 ± 0.45 | +0.21 ± 0.20 | −3.57 ± 0.34 |
| UPRO | +0.40 ± 0.52 | +0.78 ± 0.31 | +3.97 ± 0.35 |
| SPXU | +0.78 ± 0.64 | +0.10 ± 0.21 | −5.53 ± 0.37 |

All per-period values, including the daily |e| quantiles and the 21- and 252-day block statistics, are in
`summary.csv` and `results.json`.

What the measurement says, for D9:
1. **Cost drag beyond the expense ratio is small and of the expected sign.**
   - Against the total-return underlying, the levered long funds lose a further 0.6–1.7 %/yr, which reads as
     ℓ̂ = 0.5–0.9 %/yr on the borrowed exposure.
   - The inverse funds lose 0.1–1.1 %/yr, which reads as λ̂ = 0.0–0.4 %/yr.
   - Precision: SEs are 0.1–0.4 %/yr over the whole history and about 1 %/yr within 2020–21.
2. **The underlying must be total return.** Against the dividend-free price index, the long funds' residual turns
   positive (+0.5 to +4.0 %/yr) and the inverse funds' more negative (−2.0 to −5.5 %/yr). Both scale with π and with
   the index dividend yield. So the funds' exposure includes dividends, with the sign of π, and a model with U equal
   to the price index would misattribute dividends to cost.
3. **The QQQ and SPY returns are net of those ETFs' own expense ratios f_E.**
   - If the funds track the gross index total return, the measured spreads relate to the true ones as
     ℓ = ℓ̂ + πf_E/(π − 1) for π > 1, and λ = λ̂ − f_E for π < 0.
   - f_E was not verified in `experiments/DATA.md`, so no corrected numbers are given here. The correction raises
     ℓ̂ and lowers λ̂ by roughly the ETF's fee.
4. **Empirical ε.**
   - Daily: |e| has median 3–7 bp, and a 99th percentile of 15–130 bp (the highest for QLD and QID, over the 2008
     history).
   - Compounded: ε ≈ 0.1–0.2% per month, and ε ≈ 0.5–1.2% per year (95th percentile 1.3–3.2%).
   - 2020–21 is noisier than 2023–26 for most funds (one-month ε up to 0.35% against at most 0.19%).
   - These values bound E|e_T| only in the empirical sense, over these histories. They are not a guarantee.
5. **Limits.**
   - Market price is not NAV, so premium and discount are in e.
   - Current expense ratios are applied to the whole history, so any historical difference sits in ē.
   - ^IRX is used without discount-to-yield conversion.
   - Δ is a calendar-day/365 day count for both interest and fee.
   - Yahoo's adjusted close can change on refetch.

Regenerate:
- Commands: `uv run python experiments/007/fetch.py`, then `uv run python experiments/007/run.py`.
- The run takes seconds and is deterministic given the cached files. Their SHA-256 hashes are in `results.json`.
- Environment: `uv.lock` at the reporting commit.

## Review

Reviewer, 2026-10-06, against main at `86e2cb5`, which contains the reporting commit `37bec14`.

**Inputs.** I used the experiment's cached files from the analyst's `data/d9/`, copied into a fresh scratch directory. All 14 SHA-256 hashes equal those recorded in `results.json`, so the input data is identical. I did not refetch: Yahoo's adjusted close drifts on refetch, and the Design records hashes for exactly this purpose.

**Method.** I wrote my own computation from the Design, without reading `experiments/007/*.py`. It is reviewer scratch work and is not committed; its method and outputs are below.
- Exchange-local dates come from the Yahoo timestamps plus `gmtoffset`.
- R_t is computed from the adjusted close.
- r_t is the previous trading day's value, carried forward from ^IRX/100 before 2018-04-02 and from SOFR/100 afterwards.
- Δ is calendar days/365.
- The exclusion rule is as registered: fund or underlying dividend or split ex-dates, and missing inputs on t or t−1.
- Newey–West uses lag 5 with Bartlett weights. The blocks are non-overlapping blocks of 21 and 252 included days, with partial blocks dropped.
- The implied spreads are as defined in the Question.

**Headline numbers reproduced.** Every entry in both Results tables reproduces to the printed precision, including the following:
- the first days, the n, and the exclusion counts (99–155 against the ETF underlying, 30–74 against the index);
- ē with its SE, and the implied spreads with their SEs;
- the median and 99th-percentile |e|;
- ε at 21 and 252 days, and the 95th percentile of |e₂₅₂|;
- the 2020–21 and 2023–26 spreads, and the price-index ē.

The only differences are SQQQ's whole-history SE (0.39 against 0.40) and its index ē (−3.32 against −3.31), both last-digit rounding.

**The Design was fixed before the data.** The registration commit `6bc6000` (13:04:37) contains only the Design; the code arrived with the report. The cached data files have modification times 13:05:15–13:05:27, after registration. So the two-minute gap between registration and report was a fetch and a seconds-long run, not a Design written after seeing results. The Design text is unchanged in the report. "Deviations: none" is accurate. The ETF-fee reading is correctly labelled as interpretation added after the result.

**The interpretation checks out, with two wording slips.**
- **Point 2 (total-return underlying).** The shift in ē between the ETF and the price-index underlying scales with π times the dividend yield net of the ETF fee. For example, SSO moves by 3.46 points and UPRO by 4.96, against roughly 2 × 1.8 and 3 × 1.7. The conclusion follows.
- **Point 3 (ETF-fee correction).** If the fund tracks the gross index, then x_true = x + f_EΔ and e_true = e − πf_EΔ. That gives ℓ = ℓ̂ + πf_E/(π−1) and λ = λ̂ − f_E, as stated.
- **Point 4 (empirical ε).** The monthly and yearly ε ranges and the 2020–21 against 2023–26 comparison (0.35% against 0.19%) are right. Two phrases are slightly off.
  - "99th percentile of 15–130 bp (the highest for QLD and QID, over the 2008 history)": over the whole history the 99th percentile spans 46–114 bp, highest for QID and QLD. The 130 bp maximum is SQQQ in 2020–21, and the 15 bp minimum is in 2023–26.
  - "median 3–7 bp" is the whole-history range (4.3–7.4); the sub-periods span 2.6–8.2.

  Neither slip changes a number in the tables or a conclusion.

**Scope.** The stated limits are accurate and material: closing price rather than NAV; today's expense ratios applied to the whole history; ^IRX without yield conversion; refetch drift. Two more points for D9's use of these numbers:
1. **The 252-day block statistics within a sub-period rest on very few blocks.** 2020–21 has two, and 2023–26 three. Their ε values (for example up to 5.4% in 2020–21) are anecdotal and are not quoted in the Results text. Keep them out of any bound.
2. **The implied spreads absorb every systematic residual.** That includes premium/discount drift and expense-ratio history, as the Question says, so they are upper-bound-style readings. They also shift by roughly the ETF fee under point 3. D9 should treat ℓ̂ and λ̂ as interval inputs, for example ℓ ∈ [ℓ̂, ℓ̂ + πf_E/(π−1)], not point values.

Verdict: reproduced
