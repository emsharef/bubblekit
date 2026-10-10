"""Date-stamp explosive episodes with the backward SADF sequence (Phillips, Shi and Yu 2015).

Simulates an Evans periodically collapsing bubble, computes BSADF at every date, and marks dates where it exceeds
a simulated 95% critical value. Critical values here come from the random-walk null at the full sample length,
a simplification of PSY's date-specific sequence; on real stock prices calibrate on reference series instead.
"""
import numpy as np

from bubblekit.explosive import psy


def main(seed=1, n=200):
    rng = np.random.default_rng(seed)
    y = psy.simulate_evans(rng, 1, n, "monthly")[0]
    L0 = psy.default_min_window(n)
    b = psy.bsadf(y, L0)
    null = psy.null_distribution(n, n_reps=300, seed=seed)       # use 2,000+ replications in practice
    cv = psy.critical_value(null["sadf"], 0.05)
    hot = np.flatnonzero(b > cv)
    print(f"GSADF = {b.max():.2f}, SADF 95% critical value = {cv:.2f}, min window = {L0}")
    if hot.size:
        runs = np.split(hot, np.flatnonzero(np.diff(hot) > 1) + 1)
        for r in runs:
            print(f"explosive episode: dates {r[0]}-{r[-1]}")
    else:
        print("no explosive episode detected")


if __name__ == "__main__":
    main()
