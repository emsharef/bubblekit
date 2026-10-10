"""The intraday session monitor on simulated 5-minute data.

Training: 252 sessions without a level effect. Monitored: 21 sessions with and without variance rising with the
price inside each session (variance exponent beta). The monitor is calibrated on 39 reference paths of the same
length, using each path's maximum score, and the first alarm is reported. Takes a few minutes.
"""
import numpy as np

import bubblekit as bk
from bubblekit import calibration, simulate
from bubblekit.evaluation import first_alarm


def main(seed=2):
    rng = np.random.default_rng(seed)
    train = simulate.intraday_sessions(rng, 252)
    refs = [bk.intraday_monitor(train, simulate.intraday_sessions(rng, 21))["monitor_max"] for _ in range(39)]
    cut = calibration.rank_cutoff(refs, 0.05)
    print(f"cutoff from 39 reference paths: {cut:.3f}")
    for beta in (0.0, 20.0, 60.0):
        out = bk.intraday_monitor(train, simulate.intraday_sessions(rng, 21, beta=beta))
        t = first_alarm(out["monitor"], cut)
        when = "no alarm" if t is None else f"first alarm at bar {t} (session {t // 77 + 1})"
        print(f"beta = {beta:5.1f}: max score {out['monitor_max']:.3f}, {when}")


if __name__ == "__main__":
    main()
