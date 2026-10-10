# Data availability for D6 (and D9's leveraged funds)

Analyst duty 5; ROADMAP D6 "Now". Every fact below was **verified on 2026-10-06** by
`experiments/data/survey.py`, which fetches each source and writes what it saw to `experiments/data/survey.json`
(committed). Fetched payloads are cached under `data/` (gitignored), and nothing licensed enters the repository.

The data sources named here are endpoints, not literature. Per the librarian's D6 entry in `board/FINDINGS.md`,
none is cited as a source (rule 3). Leads that failed verification are listed as failed, not used.

Regenerate with `uv run python experiments/data/survey.py`. Free endpoints change, so rerun it before relying on any
row below.

## Limits stated from the start

1. **Survivorship.** The one free daily-price source that works (Yahoo's chart endpoint) has no history for
   constituents that failed, were acquired or were delisted.
   - Every probe of such a name returned 404: Yahoo (YHOO, AABA), Enron (ENRNQ), WorldCom (WCOEQ), Lehman (LEHMQ),
     Nortel (NT), CMGI, JDSU, Exodus (EXDS), eToys (ETYS), GeoCities (GCTY), Lastminute (LMC).
   - Worse, old tickers have been **reused by unrelated securities**. JAVA (Sun Microsystems) now returns an ETF
     starting 2021-10-05. LU (Lucent) returns an equity from 2020-10-30. INSP (Infospace) returns an equity from
     2018-05-03. BCOR returns an ETF from 2025-04-30.
   - So a ticker list from 1999–2001 cannot be fed to the price source blindly. Every series must be checked
     against the dates the name was a constituent.
   - The names missing are exactly the ones whose prices collapsed. Any 1999–2001 constituent study on this data
     sees only the survivors, and that bias goes in the bubble test's favourable direction for "no bubble" among the
     survivors.
   - **Update 2026-10-07:** the human's search found free daily prices for most of the collapsed dot-com and 2008
     names outside Yahoo's chart endpoint. See "Delisted daily prices found by the human's search" below. The limit
     still holds for Yahoo's endpoint, and for eToys, Lastminute.com, and Bear Stearns and WaMu in 2005–08.
2. **No free point-in-time weights.** No free source of historical index weights was found.
   - The proxy, price × shares outstanding, is available only from SEC XBRL filings. The Apple probe returned 70
     share counts, the earliest period ending 2009-06-27. So the proxy exists only from 2009 onward, only for
     companies that filed XBRL, and not at all for 1999–2001.
   - Weights for 2020–21 and 2023–26 can be built this way for current and recent filers, with the filing lag
     stated.
3. **No free point-in-time membership.**
   - Wikipedia's S&P 500 list now has a single table: current members, each with a "Date added". The probe found no
     change log on the page. That reconstructs past membership only for names still in the index.
   - The Nasdaq-100 page has no component-change table (no match in 18 tables).
   - The community reconstruction in the GitHub repository `hanshof/sp500_constituents` (S&P 500, 1996-01-02 to
     2025-08-23, 3,482 dates) **fails verification**:
     - It lists 469 names on 1996-01-02, 466 on 2000-03-09, 463 on 2001-12-24 and 443 on 2008-09-12, against the
       index's 500.
     - Enron, WorldCom, Lehman and Yahoo are absent on every date checked.
     - Its script appends today's Wikipedia snapshot to a seed file of unstated origin.
     - It drops failed names and is not used.
4. **Free option history is thin, and only short samples cover the far out-of-the-money calls.** See "Options,
   historical" below.
   - Cboe's delayed-quote endpoint gives a snapshot of the current chain only, intraday and delayed. The counts on
     2026-10-06 were SPX 29,478, NDX 15,914, SPY 13,182, QQQ 11,422, TQQQ 1,818 and SQQQ 1,388 contracts.
   - Yahoo's options endpoint requires a session crumb (401).
   - The free histories found are:
     - the DoltHub mirror, from 2019. For SPY it holds a thin subset (60–216 contracts per date), and it has no QQQ
       or SPX rows;
     - two free vendor samples. historicaldata.net gives six months (July–December 2022) of full SPX, SPXW, SPY,
       TSLA and KO chains. historicaloptiondata.com gives one symbol per month, plus single-day snapshots.
   - Full histories with far-OTM strikes exist only as paid archives or behind accounts, which the human would have
     to buy or download. So the option-anchored test (D4) can be tried on real data only in the windows those
     samples cover. Otherwise it stays simulation-only.

## What is free, verified

| what | source (endpoint) | coverage seen | notes |
|---|---|---|---|
| S&P 500 index | Yahoo chart ^GSPC | 1970-01-02 → 2026-10-06, daily | no dividends; ^SP500TR (total return) from 1988-01-04 |
| Nasdaq-100 index | Yahoo chart ^NDX | 1985-10-01 → 2026-10-06 | ^IXIC (Composite) from 1971-02-05 |
| SPY, QQQ | Yahoo chart | SPY from 1993-01-29; QQQ from 1999-03-10 | OHLC, volume, adjusted close, split and dividend events |
| surviving constituents | Yahoo chart | e.g. AAPL 1980-12-12, MSFT 1986-03-13, CSCO 1990-02-16, ORCL 1986-03-12, QCOM 1991-12-13, NVDA 1999-01-22 | daily only; how "adjusted close" is adjusted is not verified |
| leveraged and inverse funds | Yahoo chart | QLD, SSO 2006-06-21; QID, SDS 2006-07-13; UPRO, SPXU 2009-06-25; TQQQ, SQQQ 2010-02-11 | many reverse and forward splits (4–8 per fund), so use split-adjusted series |
| fund expense ratios (current) | ProShares fund pages | QLD 0.98%, TQQQ 0.97%, SQQQ 0.99%, QID 1.02%, SSO 0.88%, UPRO 0.89%, SPXU 0.90%, SDS 0.91% | current values only |
| fund fees and financing history | SEC EDGAR, ProShares Trust (CIK 1174610) | N-CSR annual reports and 485BPOS prospectuses filed through 2026-09-25; 4 further pages of older filings | the place to get historical expense ratios and swap financing terms; **not yet parsed** |
| short rate, long history | Yahoo chart ^IRX (13-week T-bill) | 1970-01-02 → 2026-10-06 | the financing proxy for 2006–2018 |
| SOFR | New York Fed rates API | 2018-04-02 → 2026-10-05 | the financing reference after 2018 |
| shares outstanding | SEC XBRL company concept | from 2009 (Apple: 70 points, through 2026-07-17) | the weight proxy (limit 2) |
| current S&P 500 membership | Wikipedia list | current members with "Date added" | limit 3 |
| current option chains | Cboe delayed quotes | snapshot of today | limit 4 |

## Leads that failed verification (not used)

| lead | result on 2026-10-06 |
|---|---|
| Stooq daily CSV | the endpoint answers with a JavaScript proof-of-work bot check, not CSV. The survey does not try to get around it. |
| Tiingo free tier | 403, "Please supply a token". It needs a sign-up the lab cannot do. |
| FRED CSV (DTB3, DGS3MO, SOFR, DFF) | connection reset or timeout from this machine (curl gets 200 with an empty body). ^IRX and the New York Fed API replace it. |
| U.S. Treasury daily bill-rate CSV | 403 Access Denied |
| Yahoo options | 401 Invalid Crumb |
| `hanshof/sp500_constituents` | fetched, but drops failed names (limit 3) |
| paid, excluded by the charter | CRSP, Norgate, TAQ, OptionMetrics |

## By window

- **1999–2001.**
  - Indices: yes (^GSPC, ^NDX, and QQQ from 1999-03-10).
  - Constituents: survivors only, with ticker reuse, no membership history, and no weights or share counts.
  - Leveraged funds: none existed.
  - Options: none.
  - The price-only test can run on the indices and on surviving constituents. The survivorship bias here is the
    largest of the three windows, because this is when failures concentrated.
- **2020–21.**
  - Indices, ETFs and leveraged funds: yes.
  - Constituents: mostly survivors. Names delisted since then are missing, and the size of that gap is not yet
    measured.
  - Weights: the XBRL proxy is possible.
  - Financing: ^IRX and SOFR.
  - Options: none historical.
- **2023–26.**
  - The best covered. Survivorship is smallest, the XBRL weight proxy applies, leveraged funds and financing are
    available, and Cboe snapshots could be collected from now on.

## For D9 (leveraged and inverse funds)

- **Prices:** daily market prices, from each fund's inception: 2006 for QLD, QID, SSO and SDS; 2009 for UPRO and SPXU;
  2010 for TQQQ and SQQQ. Fund NAVs were not probed. None of these funds existed in the 1999–2001 window.
- **Fees:** current expense ratios are verified above. Their history, and the funds' swap financing terms and
  counterparties, are in EDGAR N-CSR and 485BPOS filings, which exist but have not been parsed. D9's fee and
  financing model needs that parse, or bounds drawn from it.
- **Financing rates:** ^IRX daily from 1970, and SOFR daily from 2018.
- **Tracking error:** this can be measured directly from fund versus index daily returns on the series above.
- **Options:** the current chains of TQQQ and SQQQ are free as snapshots only.

## Options, historical (verified 2026-10-06)

Probe code:
- `experiments/data/options_survey.py`: DoltHub, sampled per symbol and date. Queries filtered on the symbol alone time
  out, so a symbol's full date range cannot be listed.
- `experiments/data/options_samples.py`: downloads the free samples and measures them.
- `experiments/data/leads_survey.py`: the source pages.

Outputs are committed as `options_survey.json`, `options_samples.json` and `leads_survey.json`, and the downloads stay
in `data/options_survey/` (gitignored). "Max call K/S" is the largest call strike divided by the underlying price on a
date, which measures how far out of the money the chain reaches. For DoltHub it is measured against the
at-the-money strike, because the table has no spot price.

| source | access | tickers present (of SPY, QQQ, SPX/SPXW, NDX, the 8 funds) | dates | quotes | max call K/S | terms |
|---|---|---|---|---|---|---|
| DoltHub `post-no-preference/options` | free API, no account | SPY only. QQQ, SPX, SPXW, NDX and all 8 funds had no rows on any probe date (2020-07, 2023-07, 2026-07) | SPY volatility history 2019-02-09 → 2026-10-05; chain rows on 7 of 9 sample dates (none on 2019-07-15 or 2023-01-15) | bid and ask on all SPY calls sampled, plus IV and Greeks; only 3–4 expirations and 60–216 contracts per date | 1.14–1.30 against at-the-money | public repository; bulk use needs the `dolt` client |
| historicaldata.net free sample | direct download, no account (239 MB) | SPY, SPX, SPXW (+ TSLA, KO) | 2022-07-01 – 2022-12-30, 127 days | bid on 92–96% and ask on ≈100% of rows, plus IV and Greeks | SPX 2.32–3.36; SPXW 1.77–2.24; SPY 1.68–2.02 | free evaluation; no redistribution (license §3) |
| historicaldata.net archive | purchase (human) | US stocks, ETFs and indices | Feb 2002 → today | as the sample | as the sample | full archive $590 one-time (724 GB); last 10 years $699; last year $199; updates $79/month (prices as listed) |
| historicaloptiondata.com Level 2 sample | direct download, no account (60 MB) | all 13 lab tickers, in a whole-market snapshot of 5,888 underlyings | one timestamp, 2026-03-19 11:15 | bid and ask on 100% of rows, IV, Greeks | SPY 2.07, QQQ 1.61, SPX 2.43, NDX 1.69, TQQQ 2.00, SQQQ 1.56, UPRO 1.79, SPXU 1.51 | sample |
| historicaloptiondata.com free tier | download area, one symbol per month | one rotating symbol | Jan 2003 → latest month | as paid | — | about 1/700 of the data, for evaluation |
| historicaloptiondata.com archive | purchase (human) | all US optionable | 2002 → today; SPX since 1990 sold separately | Level 1–3 | — | 24 years: $1,150 (L1), $1,495 (L2), $2,035 (L3) |
| Kaggle `dudesurfin/spy-options-eod-volatility-surface-2010-2023` (MIT; per its listing, sourced from OptionsDX) | downloaded by the human, 2026-10-06, outside git | SPY | 2010-01-04 → 2023-12-29, 3,508 dates, 9.47 M rows | call bid 99.9%, ask 99.9%, underlying 100%; IV and Greeks | median per-date max call K/S with bid > 0: 2020–21: 1.21 (1 month) to 1.50 (12 months); 2023: 1.19 to 1.53 | MIT |
| Kaggle `kylegraupe/spy-daily-eod-options-quotes-2020-2022` (CC0) and `kylegraupe/qqq-daily-option-chains-q1-2020-to-q4-2022` (CC0) | downloaded by the human, 2026-10-06, outside git | SPY; QQQ | SPY 2020-01-02 → 2022-12-30 (758 dates); QQQ **2021-01-04** → 2022-12-30 (508 dates, despite the "Q1 2020" title) | call bid ≥ 99.9%, ask ≥ 99.9%, underlying 100% | QQQ 2021, bid > 0: median 1.26 (1 month) to 1.51 (12 months); SPY: identical to dudesurfin (cross-check below) | CC0 |
| OptionsDX | free account and checkout per year (human) | SPY, SPX, QQQ and seven others (per the listing); none of the 8 funds | 2010–2023, per the listing | per the listing: bid, ask, IV, Greeks, underlying | not verified | some year/frequency variants free, others paid |

What the human would download, if wanted. No paywall or terms restriction is bypassed by any of these.
1. **Kaggle** (free account). *Done: downloaded by the human on 2026-10-06 and measured below.*
   `kaggle datasets download -d dudesurfin/spy-options-eod-volatility-surface-2010-2023`. That is 14 yearly parquet
   files, about 600 MB, covering SPY end-of-day for 2010–2023. Also kylegraupe's SPY and QQQ 2020–2022 chain datasets
   from the same site.
2. **OptionsDX** (free account): from optionsdx.com/shop, the end-of-day variants priced at $0 for SPY, SPX and QQQ,
   one year per checkout.
3. **For the funds' history or a long SPX/SPY/QQQ history with far-OTM strikes**, the cheapest verified paid route is
   historicaldata.net's full archive ($590). historicaloptiondata.com is $1,150 and up. Pricing is for the human to
   decide; the lab buys nothing.

**The Kaggle downloads, measured** (`experiments/data/kaggle_options.py` → `kaggle_options.json`).
- The files are read in place from `/Users/esharef/Documents/Fun/Vibe/proof_bubble/data/kaggle/` and are not
  copied into git. The human downloaded them on 2026-10-06 with `kaggle datasets download -d <slug>`. No token is
  recorded.

Largest call strike over the underlying price, per quote date, by maturity bucket (DTE 21–45, 70–110, 150–210 and
300–400 days). Entries are the min / median / max over dates, for calls with a positive bid:

| set, window | 1 month | 3 months | 6 months | 12 months |
|---|---|---|---|---|
| SPY (dudesurfin), 2020–21, 502 dates | 1.08 / 1.21 / 1.80 | 1.15 / 1.39 / 1.89 | 1.19 / 1.47 / 2.09 | 1.24 / 1.50 / 1.83 |
| SPY (dudesurfin), 2023, 250 dates | 1.13 / 1.19 / 1.33 | 1.21 / 1.32 / 1.58 | 1.19 / 1.48 / 1.89 | 1.43 / 1.53 / 1.90 |
| QQQ (kylegraupe), 2021 only, 252 dates | 1.16 / 1.26 / 1.41 | 1.28 / 1.42 / 1.63 | 1.26 / 1.50 / 1.67 | 1.26 / 1.51 / 1.68 |

- **Cross-check of the two SPY sets.** On 2020-03-16, 2021-06-15 and 2022-09-15 they hold the same contracts (5,648;
  5,113; 4,101), with identical underlying prices and every call bid and ask equal to the cent. They are copies of
  the same OptionsDX data, not independent sources.
- **A data error.** Without the bid filter, SPY has a spurious strike of 4,898 with a zero bid (Nov-2021 expiry) on
  53 quote dates from 2021-08-17 to 2021-10-29. It gives a "max K/S" of about 11. The bid > 0 figures above exclude
  it. Any use of these sets should filter zero-bid quotes or implausible strikes.
- **Coverage of the D6 windows.**
  - 2020–21: SPY full; QQQ 2021 only.
  - 2023: SPY only (dudesurfin).
  - 1999–2001: none.
  - None of these sets carries the leveraged funds, SPX or NDX.

Readings for the bubble work:
- The vendor data (OptionsDX via Kaggle, and the vendor samples) reaches the far out-of-the-money calls the
  identification needs. DoltHub's subset stops near 1.3× at-the-money.
- With the human's Kaggle download (2026-10-06), SPY end-of-day chains cover both modern D6 windows: 2020–21 and 2023.
  Calls with a positive bid reach a median 1.2× (1 month) to 1.5× (12 months) of spot, and up to 1.8–2.1× on the
  most extended dates.
- QQQ is covered in 2021 only.
- SPX, NDX and the leveraged funds remain uncovered by free history, and so does 1999–2001.

## Further data leads (verified 2026-10-06)

| lead | what was verified | lab or human |
|---|---|---|
| FirstRate Data free intraday | two weeks of 1-minute to daily bars per listed ticker (SPY, NDX and others), no sign-up. The "one year free" claim is not on the page. | lab can fetch the two-week samples |
| Delisted list (`apify.com/blackfalcondata/delisted-stocks-list`) | 36,000+ NYSE, Nasdaq and OTC delistings since 2002 from SEC EDGAR; pay per event; Apify account needed | human |
| SEC EDGAR full-text search, Form 25 / 25-NSE | free, no account. Counts: 2001 — 16 Form 25 and 0 Form 25-NSE; 2008 — 295 and 768; 2020 — 109 and 902. Electronic delisting notices are essentially absent before the mid-2000s. | lab, for 2008 onward; it does not cover 1999–2001 |
| Wikipedia "Selected changes" (the robotwealth method) | gone from the current S&P 500 page, but present in the 2025-05-27 revision (oldid 1292523673): 512 dated entries, 1994–2025. They are "selected" changes, not a complete record. | lab can fetch old revisions; reconstructed membership still lacks the delisted names' prices |
| MarketParquet | $79 one-time, bars from 2000 with delisted tickers included (as listed). The last year of daily files is free, no signup. | free year: lab; archive: human |
| Norgate | Platinum (from 1990) and Diamond (from 1950) include delisted securities and historical index constituents; 3-week free trial. The $35/month price did not appear in the page text, so it is not verified. | human |
| Nasdaq Data Link Sharadar | the page renders by script, so nothing was verified | human |

For survivorship (limit 1): a free, verifiable fix for 1999–2001 was not found. The candidates for the human are
Norgate Platinum (point-in-time membership plus delisted prices) and MarketParquet ($79, delisted prices; membership
would come from the Wikipedia revision). From 2008 onward, EDGAR Form 25 filings could at least count the
delistings.

## Intraday data for the D6 controls (D17; verified 2026-10-07)

This answers the D17 backlog item: which free intraday sources cover experiment 021's D6 names and indices, before any
intraday run. No purchase or sign-up was made.

**Yahoo chart bars, measured** (`experiments/data/intraday_probe.py` → `intraday_probe.json`; raw responses in
gitignored `data/d17/`).
- **Coverage:** all 52 D6 symbols answer at every interval: positives, selected negative members, ^GSPC, ^DJI, ^N225,
  000001.SS and 000660.KS. The history limits, quoted from Yahoo's own error messages:

  | interval | history available | US bars per regular session |
  |---|---|---|
  | 1-minute | 8 days per request, about the last 30 days in all | 390 (Tokyo 360, Shanghai 330) |
  | 5-minute (also 15- and 90-minute) | the last 60 days | 78 |
  | 60-minute | the last 730 trading days: 2023-11-07 onward for US names (2023-09/10 for Seoul, Tokyo, Shanghai) | 7 |

  A request for an hourly range further back (e.g. 2022) is refused, and range=max falls back to monthly bars.
- **Gaps:** sessions are complete apart from exchange half-days (at most 7 short sessions in 730 at 60 minutes).
- **Null closes:** each null close marks an interval with no trade.
  - They are frequent for thin names. KOSS has 3,643 of 4,681 five-minute bars null and 287 of 5,097 hourly bars
    null; FNMA (OTC) has 160 five-minute nulls.
  - The ^N225 and 000001.SS grids carry nulls over lunch breaks (600 and 1,020 five-minute nulls).
- **Price kind.** Bars are last-trade OHLC with volume, and no adjusted close at intraday intervals. Whether intraday
  history is split-adjusted is not documented. Pre- and post-market bars are excluded by default and were not
  requested.
- **Ticks.** Prices are on the exchange's tick grid (claims 028–031 apply). Quotes and bid–ask spreads are not
  available, which matters for D18.

**Other free sources.**

| source | free access | history | fit for the D6 windows |
|---|---|---|---|
| Polygon.io / Massive, Basic plan | free key; 5 calls a minute; minute aggregates ([qveris](https://api.qveris.ai/guides/polygon-pricing-optimized), [Alpaca](https://alpaca.markets/learn/the-top-3-differences-between-polygon-and-alpaca-data-plans/)) | 2 years | same reach as Yahoo hourly, at minute resolution; US stocks only; current tickers |
| Alpha Vantage `TIME_SERIES_INTRADAY` with `month=YYYY-MM` | free key; 25 requests a day and 5 a minute ([documentation](https://www.alphavantage.co/documentation/), [macroption](https://www.macroption.com/alpha-vantage-api-limits/)) | documented from 2000-01, at 1–60 minutes, with pre/post hours | **the only free source found reaching the classic US windows** (2000–01, 2003–08, 2019–22) for listed equities and ETFs; indices not covered; one request returns one month of one symbol |
| Tiingo IEX | intraday is not in the free tier; the IEX feed keeps the last 2,000 bars ([riingo](https://rdrr.io/pkg/riingo/man/riingo_iex_prices.html)) | about 5 days at 5 minutes | no |
| FirstRate Data | two-week free samples (above); the full 1-minute S&P 500 archive since 2004 is paid, from $299.95 ([datarade](https://datarade.ai/data-products/s-p-500-components-historical-intraday-dataset-firstrate-data)) | 2 weeks | no (samples only) |
| Dukascopy historical feed | free download for many CFDs, including index and stock CFDs ([Dukascopy](https://www.dukascopy.com/swiss/cz/marketwatch/historical)) | per instrument; start dates not verified | possible for index CFDs. These are CFD quotes, not exchange prices, and the terms need the human's review before any use |
| Kaggle | no minute-level US equity dataset with a free licence found for these names (search) | — | no |

- **Alpha Vantage is unverified.** Its public `demo` key refuses the `month` parameter, and claiming a free key is a
  sign-up for the human. Its depth claim (2000 onward) has not been checked here, and should be before any design
  relies on it.
- **Alpha Vantage's daily cap.** At 25 requests a day, the D6 set needs about 5,000 symbol-months: about 1,700 for the
  positive rows (E2–E5, E9) and about 3,100 for the negative windows' members. That is over half a year of requests.
  A single row, such as E5's four names over 13 months, needs 52 requests (3 days).

**Coverage of the D6 rows by free intraday data.**

| D6 row or window | Yahoo (5-minute / hourly) | Polygon free | Alpha Vantage (claimed) |
|---|---|---|---|
| E1 (^IXIC, ^NDX 1995–2001) | none | none | indices not covered; QQQ only from 1999 |
| E2 (dot-com leaders 1995–2001) | none | none | 2000-01 onward only, after the peak |
| E3/E4 (homebuilders, financials 2003–08) | none | none | yes, survivors only |
| E5 (meme stocks 2020-06 to 2021-06) | none | none | yes |
| E6 (SK Hynix 2023-01 to 2026-10) | hourly from 2023-10-06 (about 3 of 3.8 years); 5-minute for the last 60 days | not covered (US only) | Korean listing not verified |
| E7 (Nikkei 1985–92), E8 (SSE 2014–15) | none | none | not covered |
| E9 (ARKK, TSLA, ZM, PTON 2019–22) | none | none | yes |
| Negative N24m-3 (2024-07 to 2026-06) | hourly, fully covered | covered from 2024-10 | yes |
| Other negative windows (1990–2018) | none | none | from 2000 for listed members; indices not covered |

**Archive started (2026-10-07).** `experiments/data/intraday_archive.py` freezes Yahoo's rolling bars before they roll
off.
- **What it covers:** 60-minute and 5-minute regular-session bars for the 52 D6 symbols, plus the S&P 100 calm panel
  fixed on 2026-10-07 from a pinned Wikipedia revision (`intraday_archive_universe.json`): 125 symbols.
- **Where it goes:** raw responses go gzipped to gitignored `data/d6-intraday/`. The committed manifest
  (`intraday_archive_manifest.json`) records each file's bars, null bars, fetches and SHA-256, and the next due date.
- **How it updates:** re-runs append only new bars, and log any revised overlapping bar without overwriting it.
- **When to re-run:** every 30 days. 5-minute history older than 60 days is lost if a run is missed.
- **Use:** no test is computed on these data before a registered experiment.

**Conclusion for D17.**
- **Free intraday data exists only for recent years** (2023 onward hourly, the last 60 days at 5 minutes). Among the
  D6 controls that reaches only SK Hynix (E6, hourly) and one negative window.
- **The classic US episodes have no free intraday history** that has been verified. Alpha Vantage's free tier claims
  monthly 5-minute history from 2000 for listed names, at 25 requests a day. Whether that is usable needs the human to
  claim a free key and a one-month check first (the "verify before buying" rule applies equally to free sign-ups).
- **Bid–ask quotes** are not available from any free source found.

## JKP's dot-com examples (D6 item 14; checked 2026-10-07)

[jarrow2011detect] Sec. 5 (Figs. 1–17) uses four stocks with WRDS tick **bid** prices (its reference [30]):

| stock | JKP data and window | JKP verdict | free data found |
|---|---|---|---|
| Lastminute.com | WRDS bids, 2000-03-14 to 2004-07-30 | bubble (Method 1 conclusive; RKHS m = 8.26, α = 4.63) | none (the human's 2026-10-07 search found nothing usable either) |
| eToys | WRDS bids, 1999-05-20 to 2001-02-26 | inconclusive | fragments only: 131 of the window's 447 trading days, 1999-12-03 to 2000-09-29, with a 111-day hole (Wayback copies of Yahoo downloads) |
| InfoSpace | WRDS bids, 1998-12-15 to 2002-09-19 | bubble (m = 6.17, α = 3.58) | **daily, complete** (945 of 945 days): Quandl WIKI (BCOR), raw prices with splits unadjusted; cross-check in `sye/` (unknown provenance). Details below |
| GeoCities | WRDS bids, 1998-08-11 to 1999-05-28 | no bubble | **daily closes, complete** (202 of 202 days), but only in `sye/` (unknown provenance). Details below |

- **Search:** a web search for free delisted-price archives found only paid or institutional sources (Norgate,
  LSEG/Datastream, per [HBS Library](https://www.library.hbs.edu/services/help-center/delisted-securities-prices);
  [Norgate via Concretum](https://concretumgroup.com/how-to-construct-a-survivorship-bias-free-database-in-norgate-using-python/)).
- **Stooq** is behind a bot check (see above) and was not tried.
- **Result (revised 2026-10-07):** the human's later search found free **daily** prices for InfoSpace and GeoCities
  over JKP's whole windows; there is still nothing usable for eToys or Lastminute.com.
  - JKP used **tick bid** prices, so daily data can only check their verdicts at daily frequency. Their figures
    cannot be reproduced exactly.
  - An exact reproduction still needs licensed tick data (WRDS/TAQ), read in place and never committed.

## Free sources for JKP's dot-com names and failed 1999–2008 names (checked 2026-10-07)

This answers the human's request (via the manager, `2026-10-07-free-data-dotcom-survivorship.md`). The probe is
`experiments/data/delisted_probe.py`, with results in `delisted_probe.json`.
- **What it requested:** only keyless or documented demo-key requests. No key was used, and none is recorded.
- **Stooq** was not tried, because of its bot check.
- **Names tested:**
  - JKP's four: eToys, InfoSpace, GeoCities, Lastminute.com;
  - nine dot-com names: Pets.com, Webvan, Exodus, theglobe.com, CMGI, old Yahoo, AOL, Nortel, WorldCom;
  - eight 2007–09 names: Lehman, Bear Stearns, Wachovia, Washington Mutual, Countrywide, New Century, IndyMac, Merrill
    Lynch.

| source | access | what it returned |
|---|---|---|
| Yahoo chart (no key) | free | **None of JKP's four.** Of the failures, only **theglobe.com (TGLO)** has history: daily from 1998-11-13, about $31.75 falling to $0.04 by end-2001 (786 rows to 2001). **JDS Uniphase** is available under **VIAV** from 1993, with its dot-com run (adjusted about $639 in March 2000, about $120 a year later). Every other failed name returns 404. WB is now Weibo, WM is Waste Management, and INSP is Inspire Medical: tickers reused by other firms. |
| Tiingo, public `supported_tickers.zip` (no key) | free list; prices need a free key from the human | 108,954 tickers. Of 16,263 US-listed stocks, **only 1 ended by 2002 and 49 by 2009**, so the free list has essentially no pre-2010 delistings. It lists old Yahoo (YHOO, 1996–2017), JDSU (1993–2015), Time Warner (TWX, 1992–2018) and Merrill Lynch (MER, 2006-12-28 to 2008-12-31). None of JKP's four, and none of the failed dot-com or 2008 names, is listed. |
| Alpha Vantage `LISTING_STATUS&state=delisted` (demo key) | demo returns nothing; the real list needs a free key | 0 rows with the demo key. With a key it is a delisted-symbol list, not prices. Q-02 found the human's key cannot reach premium endpoints, and whether `TIME_SERIES_DAILY` serves delisted symbols is unverified. |
| EODHD (demo key) | demo key serves its demo tickers only (AAPL: yes, ETYS: 403) | The free plan gives **1 year of history** and 20 calls a day ([EODHD knowledge base](https://eodhd.com/knowledgebase/api-for-)). Delisted data appears to be on paid plans. Not useful for 1999–2008. |
| MarketParquet free year | free, no sign-up (above) | the latest year only; does not reach 1999–2008 |
| SEC EDGAR | free | delisting notices (Form 25), no prices; electronic notices start in the mid-2000s (above) |
| Wikipedia S&P 500 "Selected changes" (revision 1292523673) | free | dated index changes from 1994 (above), with no prices of the removed names |

**Conclusions** (from the lab's own probe; superseded in part by the next section).
- **JKP's four Sec. 5 stocks:** the lab's probe found no free source. The human's later search found InfoSpace and
  GeoCities (next section).
- **Survivorship for 1999–2001 and 2003–2008:**
  - no free source fills it;
  - Tiingo's free tier would add only names delisted after about 2010, plus Merrill Lynch's last two years;
  - EODHD's free tier stops at one year.
- **Free dot-com collapse names that do exist:**
  - **theglobe.com (TGLO)**, a genuine failure;
  - **JDS Uniphase (VIAV)**, a survivor that fell about 80% from its peak in a year.
  They could serve as additional E2-style rows in a later registered experiment. Neither is one of JKP's names.
- **Keys the human could supply.** Neither key would close either gap:
  - a free Tiingo key would add old Yahoo (1996–2017) and Merrill Lynch (2006–08) prices;
  - a free Alpha Vantage key would give the delisted-symbol list, not historical prices of the failed names.

## Delisted daily prices found by the human's search (2026-10-07)

The manager's search agent gathered these files for the human, in the gitignored
`data/delisted/` (`data/delisted/README.md` gives provenance per folder). They are read in place and never
committed.
- **How coverage was checked:** I compared dates against Yahoo's FNMA trading calendar, which spans the period.
  "Complete" means every reference trading day in the window has a row.
- **Inspection scripts:** they ran with `python -I` on the files as data, and are not committed. Nothing here has been
  used in a test yet.

**Sources and their standing.**
| folder | origin | standing |
|---|---|---|
| `wayback_yahoo/` | old Yahoo `table.csv` downloads saved by the Wayback Machine; each row names its capture | public archive of a formerly free download; per-row provenance |
| `wiki/` | Quandl WIKI prices dump (a GitHub mirror of the free, community-maintained Nasdaq Data Link WIKI/PRICES) | known source. **Raw prices; this subset has no split-ratio or adjusted columns** |
| `qstk/` | Georgia Tech QuantSoftwareToolkit's 2012 Yahoo files | known source (Yahoo, as of 2012) |
| `yahoo/` | Yahoo's chart endpoint, today | the lab's usual source |
| `kaggle/` | Kaggle dataset `martynawoniak/enron-stock-prices`, licence "unknown" | unknown licence; split-adjusted |
| `sye/` | GitHub `sye3124/Nasdaq-Cross-Sectional-Return-Prediction`, no licence and no stated source (looks CRSP-derived) | **unknown provenance.** Use as a cross-check, or with that caveat stated in any result; not cleared for redistribution. Its column meanings vary. For BCOR, "open" is the split-adjusted open and "close" a rescaled close. For GCTY, open = high = low = close each day, which looks like one daily price, except the last day's "close" (a merger or delisting return). Check each file |

**Coverage of the names that matter** (trading days with rows / reference trading days in the window).
| name | window | coverage | source and caveats |
|---|---|---|---|
| InfoSpace | JKP's, 1998-12-15 to 2002-09-19 | 945/945 | `wiki/` BCOR, raw prices. The 2:1 splits of May 1999, January 2000 and April 2000 are documented in InfoSpace's FY2000 10-K, and the 1:10 reverse split had record date 2002-09-13. They show in the raw closes on 1999-05-05, 2000-01-05, 2000-04-07 and 2002-09-13. Pre-2002-09 volume is 10× too low. **The two sources agree after adjustment:** `sye/` "open" equals the adjusted WIKI open on 96.7% of days (within 1%), and `sye/` "close" is the adjusted WIKI close times a constant 0.3696 on 99.3% of days. (An earlier version of this row said the levels disagreed; that came from misreading `sye/`'s columns.) |
| GeoCities | JKP's, 1998-08-11 to 1999-05-28 | 202/202 | `sye/` GCTY only (unknown provenance); closes only; no jumps above 40% |
| eToys | JKP's, 1999-05-20 to 2001-02-26 | 131/447 | Wayback fragments; unusable for the window |
| Lastminute.com | JKP's | none | — |
| Pets.com | life, 2000-02-11 to 2000-11-07 | 188/188 | `sye/` only; Wayback has 66 days |
| Webvan | life, 1999-11-05 to 2001-07-06 | 420/420 | `sye/` only; Wayback has 63 days |
| Exodus | 1998-03-19 to 2001-04-17 | 776/777 | Wayback; `sye/` runs to 2001-09-25 |
| CMGI | 1995–2001 | 1,762/1,762 | Wayback and `wiki/` (MLNK) agree on first and last closes |
| JDS Uniphase | 1995–2001 | 1,762/1,762 | `wiki/` (raw, five 2:1 splits in the window); already on Yahoo as VIAV |
| Enron | 1998-01-02 to 2001-11-30 | 977/984 | `kaggle/` (split-adjusted, licence unknown); Wayback has gaps |
| VA Linux | 1999-12-09 to 2001-12-28 | 508/515 | Wayback |
| Global Crossing | 1998–2002 | partial | Wayback GBLX to 2000-05-19 and GX 2001-05 to 2001-11. `sye/` GX has a 626-day gap, and **before 1998 it is another company** |
| WorldCom | 1998–2002 | gap 2000-04-19 to 2001-01-04 | Wayback |
| Commerce One | 1999–2004 | gaps of 95 and 71 days | Wayback |
| theglobe.com | from 1998-11-13 | complete | `yahoo/` (already in DATA.md) |
| Lehman | 2003-01-02 to 2008-09-30 | 1,447/1,447 | `qstk/` LEHMQ (back to 2000); Wayback LEH to 2005-11 |
| Wachovia | 2003–2008 | complete when joined | Wayback WB to 2006-05, then `qstk/` WB 2005–2011. **WB in `sye/` and on Yahoo today is Weibo** |
| Countrywide | 2003-01-02 to 2008-06-30 | 1,383/1,383 | `sye/` only for 2006-01 to 2008-06. Wayback covers 1987 to 2006-01-04 |
| Merrill Lynch | 2003–2008 | 1,511/1,511 | `sye/` only after 2007-04-12. Wayback covers 1977 to 2007-04-12 |
| Fannie Mae, Freddie Mac | 2003–2008 | 1,511/1,511 | `yahoo/` FNMA and FMCC, including the NYSE years |
| Bear Stearns | 2005-11 to 2008-03 | missing | Wayback BSC ends 2005-11-01 |
| Washington Mutual | 2005-09 to 2008-03 | missing | Wayback WM ends 2005-09-13. Wayback WAMUQ covers 2008-03 to 2009-03. **WM in `wiki/` and `sye/` is Waste Management** |

**Rules for using these files.**
- Check every ticker against its dates. Ticker reuse is found in `sye/` (WB, WM, INSP, GX before 1998) and `wiki/`
  (WM, WCIC).
- A raw series is split-adjusted before any test, from documented split dates, and the adjustment is recorded in the
  experiment.
- Any result that rests on `sye/` says so.

## Implied-volatility indices for D28 (item 20; checked 2026-10-08)

Checked by keyless requests on 2026-10-08. Nothing is cached in git, and the fetch will be committed code in D28's
experiment.

| index | free source | daily history | notes |
|---|---|---|---|
| VIX (SPX) | Cboe `cdn.cboe.com/api/global/us_indices/daily_prices/VIX_History.csv` (a plain redirect to `cdn-api.cboe.com`; no bot check); also Yahoo `^VIX` | **1990-01-02** to today (9,289 rows) | Yahoo and Cboe closes agree within 0.01 on 99.9% of 9,257 common days, max \|Δ\| 2.61 |
| VXO (S&P 100, from 1986) | **not available free**: Cboe's file returns 403 (the index was discontinued in 2021) and Yahoo `^VXO` has no data | — | 2000 on SPX is still covered by VIX from 1990 |
| VXN (NDX) | Yahoo `^VXN`; Cboe's own file starts only in 2009 | Yahoo: **2001-01-23** to today (6,465 rows). Cboe: 2009-09-14 to today | **The first VXN date is 2001-01-23, after the March 2000 peak**, as the addendum expected. Yahoo and Cboe agree within 0.01 on 99.7% of 4,293 common days, max \|Δ\| 3.49. For 2001–2009 Yahoo is the only free source; Cboe's archive files return 403 |
| VXD (DJIA) | Yahoo `^VXD`; Cboe file | Yahoo from 2005-11-22; Cboe from 2009-09-18 | — |
| single-stock: VXAPL, VXAZN, VXGOG, VXGS, VXIBM | Cboe files | **2011-01-07** to today | available, but not planned on, per the addendum |

**Consequence for D28:**
- the 2000 bubble is testable on SPX with VIX only;
- NDX runs cover 2001-01-23 onward, which includes 2020–21;
- a few days differ between Yahoo and Cboe by up to 3.5 points, so D28 should use Cboe's file where it exists and
  Yahoo only for VXN before 2009-09-14, with that splice declared.

## Alpaca IEX minute bars for D29 (item 21; checked 2026-10-08)

Checked with the human's Alpaca keys, read from the Keychain at run time and never written anywhere. The probe is
`experiments/data/alpaca_iex_probe.py`, and no bars are stored.
- **The free IEX feed's minute history starts on 2020-07-27, not 2016.**
  - AAPL and SPY return no bars on any date checked from 2016-06-01 through 2020-07-24.
  - They return 292–379 bars on 2020-07-27, and about 390–410 per regular session after that.
  - The same pattern holds for MSFT and GME (empty in 2016 and 2018; full on 2021-01-27).
- **The bars are IEX-only.** A minute with no IEX trade has no bar: AAPL had 275–410 bars per session in 2020.
- **Correction (2026-10-08, the same day): the free plan's consolidated SIP feed reaches 2016.** The librarian's D29
  sweep pointed to Alpaca's documentation ("since 2016", with a choice of feed), and a `feed=sip` probe confirms it.
  - AAPL and GME return full 5-minute bars on 2016-01-04, 2016-06-01, 2018-06-01, 2020-03-16, 2021-01-27 and
    2026-10-06. AAPL has 97 bars between 13:00 and 21:00 UTC, which includes some extended-hours trading.
  - The IEX-only finding above stands for `feed=iex`, but it does not limit D29: experiment 042 uses SIP (Deviation 1).
    The 2020–21 positives are covered in full, and the clock can be declared from the prior year for every window.
  - The probe `experiments/data/alpaca_iex_probe.py` takes the feed as an argument (`sip`). As the PM asked, its SIP run
    covers a 2019 date. 1-minute bars between 13:00 and 21:00 UTC:
    - 2019-06-03: AAPL 461, SPY 481, GME 394;
    - 2021-01-27: GME 469;
    - 2016-06-01 through 2026-10-07: 392–481 for all three names.
    The free plan's 15-minute delay does not affect history.
- Massive (Polygon) covers only the last two years, as the addendum says (cross-check only).

## Survivorship recovery from free sources (D27, item 19; checked 2026-10-09)

**Question:** of the S&P 500's deletions since 1995, how many have free daily prices that reach the deletion date?
Recovered names can join experiment 039's universe for any re-evaluation of calibrated GSADF. That scoring would be
its own registered experiment.
- **Code and output:** `experiments/data/d27_recovery.py` (fetch, then match) writes
  `experiments/data/d27_recovery.json` (per-deletion metadata, no prices).
- **Cache:** gitignored in `data/d27/`. The human's archives in `data/delisted/` are read in place.
- **Access:** no sign-up, purchase or key, and no bot check passed.

**The deletion log is incomplete, so its denominator is a lower bound.** It is the union of three free lists, matched
as the same deletion when the ticker agrees within 60 days:

| list | deletions since 1995 | reason given |
|---|---|---|
| Wikipedia "Selected changes", revision of 2025-05-27 (oldid 1292523673) | 350 | yes (text, classified below) |
| `hanshof/sp500_constituents` membership file (consecutive-date removals; fails verification, limit 3) | 407 not already listed | no |
| `fja05680/sp500` `sp500_ticker_start_end.csv` (MIT licence) | 43 not already listed | no |
| **union** | **800** (772 tickers, 1995–2026) | 350 with a reason |

- **Before 2008 Wikipedia is sparse:** only 36 of its removals fall in 1995–2008, so the pre-2009 log rests mostly
  on hanshof and fja05680. Those two agree closely (664 shared) and are probably not independent.
- **Failures are missing from all three lists:** Enron and WorldCom are in none of them. Washington Mutual's 2008
  deletion is masked by the WM ticker's reuse. Lehman appears only on Wikipedia.
- **Undercount:** the true count is unknown here. The librarian's sweep cites about 750 deletions in 1980–2020
  (Greenwood and Sammon), so the union is of the right order but undercounts failures.

**Sources and matching rule.**
- **The rule:** a deletion is recovered by a source if that source has a series under the removed ticker with at
  least 252 trading days in the 400 calendar days before the deletion, and a price within 10 days before it.
- **Quandl WIKI_PRICES dump** (GitHub LFS mirror `easontia/Past-Works`, `math599/wiki_prices.7z`, 363 MB, SHA-256
  `affdac72…f8d0` checked; 3,199 tickers to 2018-03; extracted with macOS `tar`).
- **Yahoo's chart endpoint:** the removed ticker as it stands today; 770 tickers queried at 0.3 s.
- **The human's archives** (`data/delisted/`), with the documented post-bankruptcy tickers aliased (LEHMQ to LEH,
  WAMUQ to WM, WCOEQ to WCOM). The archive README's reused WIKI series (WM, WCIC) are excluded.
- **Two tiers, because Yahoo back-fills some reused tickers with the new company's older history** (AN, Amoco's
  ticker, returns AutoNation from 1990):
  - **ticker-span:** any source passes the rule;
  - **strict:** the WIKI dump or the archives pass, or Yahoo passes and its company name shares a distinctive word
    with the log's name.
  - **Name-check accuracy:** of 101 Yahoo passes with a log name, 89 match. Of the 12 mismatches, 6 are other
    companies (AN, KG, GENZ, CPWR, EP, GR) and 6 are renames the word check misses (O-I Glass, ATI, CNX, PG&E, V.F.).
    So the strict tier slightly undercounts.
  - **Unchecked:** 63 Yahoo passes have no log name and cannot pass strictly. WIKI-dump tickers are not name-checked.

**Recovery by period:**

| deleted in | deletions | ticker-span | strict |
|---|---|---|---|
| 1995–99 | 123 | 16 (13%) | 14 (11%) |
| 2000–02 | 104 | 16 (15%) | 15 (14%) |
| 2003–07 | 112 | 18 (16%) | 16 (14%) |
| 2008–09 | 66 | 33 (50%) | 31 (47%) |
| 2010–14 | 97 | 52 (54%) | 47 (48%) |
| 2015–18 | 115 | 96 (83%) | 93 (81%) |
| 2019–22 | 98 | 32 (33%) | 30 (31%) |
| 2023–26 | 85 | 47 (55%) | 22 (26%) |
| **all** | **800** | **310 (39%)** | **268 (34%)** |

- **Where each era's recoveries come from:**
  - the WIKI dump carries 2008–18;
  - Yahoo carries names still trading after deletion;
  - from 2019, acquired and failed names are reachable only through Yahoo, which drops them.
- **Calendar years:** in `by_year` of the JSON.

**Recovery by stated reason** (Wikipedia rows only; heuristic classes; spin-off text usually describes the *added*
company):

| reason | deletions | ticker-span | strict |
|---|---|---|---|
| market capitalization or representation | 126 | 101 (80%) | 100 (79%) |
| displaced by a spin-off or restructuring | 41 | 31 (76%) | 31 (76%) |
| acquisition or merger | 164 | 69 (42%) | 65 (40%) |
| bankruptcy or distress | 8 | 3 (38%) | 2 (25%) |
| ineligible (domicile) | 3 | 2 | 2 |
| replaced, no stated reason | 8 | 7 | 7 |
| unknown (hanshof or fja05680 only) | 450 | 97 (22%) | 61 (14%) |

The classifier mislabels some rows from the added company's text: GameStop and Mattel are classed as acquisitions.
The era-by-reason cross-table is in `by_era_reason`.

**Bias direction of what remains** (by reason and era, not a single sign; the librarian's sweep and Greenwood and
Sammon on era-dependent deletion effects).
- **1995–2007: 86–89% of deletions remain unrecovered.** Most have no stated reason. In that era deletions were mostly
  acquisitions in the merger waves, plus the dot-com and accounting failures (Enron and WorldCom, missing even from
  the log).
  - Missing acquisitions remove run-ups that ended in a takeover premium. That biases toward *fewer* bubble-like
    run-ups in the universe.
  - Missing failures remove collapses. That biases toward *fewer* large forward drawdowns: 039's and 051's drawdown
    regressions understate crash frequency, and calm-start false-alarm rates are measured on survivors.
- **Survivor-heavy recovery:** recovered names are mainly market-cap removals still trading (about 80% recovered),
  i.e. names that shrank but survived.
- **Failures are recovered least of all:** 2 of 8 classified bankruptcies strictly. Silicon Valley Bank, Signature,
  First Republic and Ambac are unrecovered.
- **Acquisitions:** about 40% are recovered, mostly 2010–18 via the WIKI dump.
- **Net:** the recovered set is enriched in shrinking survivors and depleted in both tails, takeover run-ups and
  outright collapses. Recovered names alone do not remove survivorship bias in drawdown or run-up tests. Bounds
  should treat the unrecovered as worst cases in each direction.

**Joining the universe.**
- **The list:** the strict-tier deletions (268, with ticker, deletion date and source in the JSON) can join 039's
  universe for a re-evaluation of calibrated GSADF (Q-03's default screen).
- **What joining needs:** each name's series only up to its deletion date, and the same coverage rules.
- **Limits:**
  - the WIKI dump ends 2018-03;
  - Yahoo series for removed-but-trading names continue after deletion, so post-deletion windows are ordinary
    non-member windows;
  - the 63 unnamed Yahoo-only passes need a name check before use.
- **Not done here:** no scoring. That is its own registered experiment.

## What the lab cannot get

Point-in-time membership and weights before 2009, prices of failed or acquired constituents beyond the names in the
previous section, any historical option
quotes, intraday data, and anything licensed. The D6 kill criterion asks whether the free data can support the
price-only test at any window. It can, at every window, on indices, surviving constituents and (from 2006) funds,
but with the survivorship limit above, which is severe for 1999–2001.
