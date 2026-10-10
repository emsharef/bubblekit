# bubblekit

Asset-price bubble detection and method comparison in Python: the main tests from the literature and new
strict-local-martingale signals, with calibration and evaluation tools to compare them honestly.

The package accompanies the manuscript *Asset Price Bubbles: Theory, Signals, and Traded Contracts*
(`../manuscript/`) and the research record in this repository.

## What "bubble" means here

Different methods test different things. A result for one does not establish another.

| Question | Methods in bubblekit | A positive result means |
|---|---|---|
| Explosive price behavior | `sadf`, `gsadf`, `bsadf`, panel tests | Some window behaves like an autoregression with a root above one |
| Volatility growth in the price tail | `jkp_test` | Estimated volatility grows fast enough with the level that the extrapolated tail implies a bubble |
| Price-level variance dependence (strict local martingale) | `daily_score`, `intraday_monitor`, `split_likelihood_score` | Return variance rises with the price level beyond background volatility |
| Future loss risk | `evaluation.forecast_regression` | An association with later drawdowns over a stated horizon |

In the strict-local-martingale theory a bubble is a shortfall of expected value under a pricing measure. A CEV
price dS = κ S^p dW is a bubble exactly when p > 1, i.e. when log-return variance rises with the price
(variance exponent β = 2(p − 1) > 0). The signals here estimate that pattern; turning it into a valuation claim
needs further assumptions (the unobserved tail and the choice of pricing measure), as the manuscript explains.

## Install

```bash
pip install -e .            # from this directory; requires numpy and scipy
pip install -e ".[test]"    # with pytest
```

## Quick start

```python
import numpy as np
import bubblekit as bk
from bubblekit import simulate, calibration

rng = np.random.default_rng(0)

# Explosive-root statistics on a price series
prices = simulate.gbm(rng, 500)
print(bk.gsadf(prices / prices[0]))

# Daily strict-local-martingale statistic: a stock and a market index on the same dates
# (20 warm-up days, 253 training closes, then the scored window)
stock, market = simulate.market_and_stock(rng, beta=2.0)
out = bk.daily_score(stock, market)
print(out["batch"], out["monitor_max"], out["beta_hat"])

# Scores need calibration: score calm reference windows and use the strict rank rule
refs = []
while len(refs) < 99:
    pair = simulate.market_and_stock(rng, beta=0.0)
    if pair is not None:
        refs.append(bk.daily_score(*pair, monitor=False)["batch"])
cutoff = calibration.rank_cutoff(refs, alpha=0.05)
print("alarm" if out["batch"] > cutoff else "no alarm")
```

Intraday monitoring takes regular-session 5-minute closes as arrays of shape `(sessions, 78)`:

```python
train = simulate.intraday_sessions(rng, 252)          # at least 200 complete training sessions
scored = simulate.intraday_sessions(rng, 21, beta=20.0)
res = bk.intraday_monitor(train, scored)               # res["monitor"]: one bounded score per 5-minute bar
```

Compare methods on labelled records, each calibrated on the same reference records:

```python
from bubblekit import compare
records = [{"prices": s, "market": m, "label": True} for s, m in bubbly_pairs] + \
          [{"prices": s, "market": m, "label": False} for s, m in calm_pairs]
reference = [{"prices": s, "market": m} for s, m in reference_pairs]
result = compare.compare(records, ["gsadf", "jkp", "daily_batch", "daily_monitor"], reference=reference)
```

## Documentation and examples

- [docs/methods.md](docs/methods.md): what each method tests, its inputs and outputs, evidence from the research, and cautions
- [docs/calibration.md](docs/calibration.md): turning scores into alarms, the strict rank rule, calibration transport
- [docs/real-data.md](docs/real-data.md): data formats, a rolling daily screen, evaluating usefulness, survivorship

| Example | Shows | Runtime |
|---|---|---|
| `examples/compare_simulation.py` | all daily methods on simulated bubble and calm stocks, calibrated on the same references | ~30 s |
| `examples/daily_screen.py` | a rolling monthly screen on a synthetic universe, or on your CSV (`python daily_screen.py prices.csv SPY`) | ~15 s |
| `examples/calibration_transport.py` | one cutoff applied to different no-bubble volatility laws | ~1 min |
| `examples/gsadf_datestamp.py` | BSADF date-stamping of an Evans bubble | ~30 s |
| `examples/intraday_example.py` | the intraday monitor with a calibrated first-alarm time | ~30 s |

## Modules

| Module | Contents |
|---|---|
| `bubblekit.explosive.psy` | SADF, GSADF, BSADF (Phillips, Wu and Yu 2011; Phillips, Shi and Yu 2015), null distributions, p-values, Evans bubble simulator |
| `bubblekit.explosive.panel` | Postclustering panel t and J tests (Liu, Phillips and Yu 2022) |
| `bubblekit.volatility.jkp` | Jarrow, Kchia and Protter (2011) Methods 1 and 2 |
| `bubblekit.regimes.opy` | Bubble lifetimes by HMM smoothing (Obayashi, Protter and Yang 2017) |
| `bubblekit.slm.cev` | Exact CEV transition densities and samplers; split-likelihood (universal-inference) score |
| `bubblekit.slm.daily` | Daily market-scale statistic and monitor |
| `bubblekit.slm.intraday` | Intraday session-anchor monitor |
| `bubblekit.calibration` | Strict rank calibration, flag rates, calibration-transport diagnostics |
| `bubblekit.multiple` | e-BH, BH and BY across names |
| `bubblekit.evaluation` | Forward drawdowns and returns, Driscoll-Kraay and two-way clustered regressions, out-of-sample R², ROC/AUC with cluster bootstrap, alarm timing |
| `bubblekit.compare` | Method registry and comparison harness |
| `bubblekit.simulate` | GBM, CEV, Heston, Merton jumps, regime switching, market-scale and stochastic-volatility bubble pairs, intraday sessions |

## Cautions learned the hard way

- **Calibration is part of the method.** A threshold calibrated on one population can produce very different
  alarm rates on another (`calibration.transport_rates`). Calibrate on reference records that resemble the
  records you score.
- **Conventional critical values mislead on real prices.** GSADF with simulated random-walk critical values
  flagged 12–52% of calm stock windows in our tests; JKP flags most geometric Brownian paths.
- **Background volatility is the main confound.** A model that lets the stock's own volatility state move freely
  absorbs the level effect; the daily statistic uses the market's volatility as the shared background instead.
- **A positive β is not unique to a local-volatility bubble.** Positively correlated stochastic volatility
  produces the same signature (it is also a strict-local-martingale mechanism in Sin's model).
- **Labelled episodes are chosen with hindsight.** Prefer forward-outcome tests on an unselected universe for
  evidence of usefulness, and report ROC on labelled episodes as optimistic.
- **Likelihood statistics are numerical.** The daily and intraday scores are empirically calibrated statistics,
  not certified e-values; `split_likelihood_score` is an e-value only under its declared CEV null family.

## Tests

```bash
pytest
```

Unit tests use synthetic data. Tests marked `lab` cross-check the package against the reference implementations
in this repository's `experiments/` and `checks/` and are skipped when that tree is absent.

## License

MIT.
