# Asset price bubbles: theory, signals and a detection package

Research on identifying asset-price bubbles from prices, in the strict-local-martingale sense: a bubble is a
shortfall of expected value under a pricing measure, and in a CEV-type model it shows up as return variance
rising with the price level. The repository contains the manuscript, the full research record, machine-checked
proofs in Lean, and `bubblekit`, a Python package implementing the methods from the literature and the new
signals.

## Start here

| | |
|---|---|
| **Manuscript** | [`manuscript/Asset_Price_Bubbles.pdf`](manuscript/Asset_Price_Bubbles.pdf), *Asset Price Bubbles: Theory, Signals, and Traded Contracts*. Sources in `manuscript/` (`bash manuscript/build.sh`). |
| **Python package** | [`bubblekit/`](bubblekit/): SADF/GSADF/BSADF, panel explosive-root tests, Jarrow–Kchia–Protter, Obayashi–Protter–Yang, exact CEV split-likelihood e-values, the daily market-scale and intraday strict-local-martingale signals, calibration, evaluation and simulators. Documentation in [`bubblekit/docs/`](bubblekit/docs/). |
| **Research record (paper)** | [`paper/research_record.pdf`](paper/research_record.pdf): every result with its verification status, all simulation and real-data experiments. Source `paper/PAPER.md`. |
| **Lean proofs** | [`lean/`](lean/): machine-checked claims; see [`lean/README.md`](lean/README.md) for the layout and the verification logs. |

## Main findings

- **Theory.**
  - Continuously rebalanced constant-proportion wealth is a strict local martingale exactly according to the
    exposure (below or above one half) and the volatility integrals at zero and infinity.
  - Finite rebalancing grids reverse the classification.
  - Finite price records cannot uniformly distinguish bubbles from non-bubbles over unrestricted local-volatility
    models (the unobserved volatility tail), and the physical law need not determine the pricing measure.
- **Signals.**
  - A daily statistic that uses the market's volatility as the shared background detects simulated bubbles at
    39–72%, against 7–14% for calibrated GSADF.
  - On real data (S&P 500 members, 1994–2026) it is quiet in crisis years and flagged the 2004–05 homebuilders
    about 400 sessions before their peaks.
  - An intraday session monitor flags meme-stock run-ups and adds out-of-sample drawdown information to GSADF.
- **Calibration.**
  - Conventional critical values and transported thresholds give misleading alarm rates on real prices.
  - Every signal must be calibrated on reference records that resemble the targets.

Neither signal by itself identifies a pricing bubble; the manuscript states the assumptions needed.

## Repository layout

| Path | Contents |
|---|---|
| `manuscript/` | The manuscript (LaTeX sources, generated tables and figures, PDF) |
| `bubblekit/` | Python package, tests, examples, documentation |
| `paper/` | The research record (`PAPER.md`, PDF) and `PROOFMAP.md`, mapping results to claims and Lean |
| `claims/` | One file per mathematical claim: statement, proof, adversarial review, status |
| `experiments/` | Registered experiments: design, deviations, results, independent reproduction, code |
| `checks/` | Exact and numerical check scripts behind the claims |
| `lean/` | Lean 4 formalization (`Upstream`: cited inputs as hypotheses; `Novel`, `Standalone`: the project's proofs) |
| `ledger/` | Cited inputs (`AXIOMS.md`), their source audits (`AUDIT_LOG.md`), terminology |
| `board/FIDELITY.md` | For each formalized claim, a check that the Lean statement matches the claim |
| `refs/` | Bibliography (`BIBLIOGRAPHY.md`); the full texts used during the research are not redistributed |
| `PROPOSAL.md` | The original research proposal |

## Method

Every claim was reviewed adversarially before acceptance, and deterministic parts were formalized in Lean. Every experiment was registered before it ran, every change of design was recorded as a deviation before results were read, and every reported experiment was reproduced independently.

## Data

No market data is included. Experiments used free sources (Yahoo daily prices, Alpaca and Massive intraday
bars), fetched by the code in `experiments/` into the untracked `data/` folder. `bubblekit` takes prices as
arrays and uses synthetic data in its tests.

## License

- **Code** (`bubblekit/`, `lean/`, `experiments/`, `checks/`, `manuscript/*.py`): MIT, see [`LICENSE`](LICENSE).
- **Text** (the manuscript, the research record in `paper/`, `claims/`, `board/`, `ledger/`, documentation): Creative
  Commons Attribution 4.0 International, see [`LICENSE-CC-BY-4.0.txt`](LICENSE-CC-BY-4.0.txt).
