"""Why calibration is part of the method: one cutoff, different no-bubble populations.

Calibrates the daily statistic on no-bubble paths whose background volatility follows the market, then scores
no-bubble paths from other volatility laws (stochastic volatility shared with the market, the stock's own
stochastic volatility, and own stochastic volatility positively correlated with returns). None has a level effect,
yet flag rates differ widely.
"""
import numpy as np

import bubblekit as bk
from bubblekit import calibration, simulate


def draws(rng, n, make):
    out = []
    while len(out) < n:
        pair = make()
        if pair is not None:
            out.append(bk.daily_score(*pair, monitor=False)["batch"])
    return np.array(out)


def main(seed=3, n=60):
    rng = np.random.default_rng(seed)
    ref = draws(rng, 99, lambda: simulate.market_and_stock(rng, beta=0.0))
    pops = {
        "same law as references": draws(rng, n, lambda: simulate.market_and_stock(rng, beta=0.0)),
        "market-driven SV": draws(rng, n, lambda: simulate.market_and_stock_sv(rng, 1.0, 0.0, True)),
        "own SV": draws(rng, n, lambda: simulate.market_and_stock_sv(rng, 1.0, 0.0, False)),
        "own SV, corr +0.7": draws(rng, n, lambda: simulate.market_and_stock_sv(rng, 1.0, 0.7, False)),
    }
    res = calibration.transport_rates(ref, pops, alpha=0.05)
    print(f"cutoff {res['cutoff']:.3f} (alpha 5%)")
    for k in pops:
        r = res[k]
        print(f"  {k:24s} flag rate {r['rate']:.2f}  95% CI {r['ci95'][0]:.2f}-{r['ci95'][1]:.2f}")


if __name__ == "__main__":
    main()
