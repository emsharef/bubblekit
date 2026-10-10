"""Compare detectors on simulated stocks with and without a strict-local-martingale level effect.

Each record is a stock with its market index; bubble records have variance rising with the price (beta = 2 in
variance units), the others do not. Every method is calibrated on separate no-bubble reference records with the
strict rank rule at 5%, and the script prints AUC and flag rates. Runs in about a minute.
"""
import numpy as np

from bubblekit import compare, simulate


def pairs(rng, beta, n):
    out = []
    while len(out) < n:
        p = simulate.market_and_stock(rng, beta=beta)
        if p is not None:
            out.append(p)
    return out


def main(seed=0):
    rng = np.random.default_rng(seed)
    records = [{"prices": s, "market": m, "label": True} for s, m in pairs(rng, 2.0, 40)]
    records += [{"prices": s, "market": m, "label": False} for s, m in pairs(rng, 0.0, 40)]
    reference = [{"prices": s, "market": m} for s, m in pairs(rng, 0.0, 99)]
    res = compare.compare(records, ["sadf", "gsadf", "jkp", "split_likelihood", "daily_batch", "daily_monitor"],
                          reference=reference)
    print(f"{'method':18s} {'target':48s} {'AUC':>5s} {'flag(bubble)':>13s} {'flag(calm)':>11s}")
    for name, r in res.items():
        print(f"{name:18s} {r['target']:48s} {r.get('auc', float('nan')):5.2f} "
              f"{r['flag_rate_positive']['rate']:13.2f} {r['flag_rate_negative']['rate']:11.2f}")


if __name__ == "__main__":
    main()
