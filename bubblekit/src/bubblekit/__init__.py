"""bubblekit: asset-price bubble detection and comparison.

Detectors answer different questions; keep them apart when reading results:

- explosive-root tests (:mod:`bubblekit.explosive`): does the price series show explosive autoregressive behavior?
  SADF/GSADF/BSADF (Phillips, Shi and Yu) and panel tests (Liu, Phillips and Yu);
- volatility-tail tests (:mod:`bubblekit.volatility`): Jarrow, Kchia and Protter's estimate of how volatility grows
  with the price level, extrapolated to the tail;
- strict-local-martingale signals (:mod:`bubblekit.slm`): does return variance rise with the price level after
  accounting for background volatility? Exact CEV split-likelihood e-values, a daily market-scale statistic and an
  intraday session monitor;
- regime smoothing (:mod:`bubblekit.regimes`): Obayashi, Protter and Yang bubble lifetimes.

Scores become alarms only through calibration (:mod:`bubblekit.calibration`); :mod:`bubblekit.evaluation` and
:mod:`bubblekit.compare` compare methods on simulated or real records; :mod:`bubblekit.simulate` generates paths
with known labels. No method here establishes that a historical price was a pricing bubble.
"""
from . import calibration, compare, evaluation, multiple, simulate
from .explosive import psy
from .explosive.psy import bsadf, gsadf, sadf
from .slm.daily import daily_score
from .slm.intraday import intraday_monitor
from .slm.cev import split_likelihood_score
from .volatility.jkp import jkp_test

__version__ = "0.1.0"

__all__ = [
    "calibration", "compare", "evaluation", "multiple", "simulate", "psy",
    "sadf", "gsadf", "bsadf", "daily_score", "intraday_monitor", "split_likelihood_score", "jkp_test",
]
