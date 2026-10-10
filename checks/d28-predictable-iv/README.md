# D28 predictable-IV evaluator

`evaluate.py` implements approved claim 042's profile and experiment 043's
registered 28-component predictable forecast. It contains no simulation or
data retrieval. It scores exact prices, using floating-point arithmetic.

```python
from evaluate import evaluate, first_crossing

rows = evaluate(prices, lagged_iv, gaps, training=126,
                bands=((0.3, 1.0), (0.25, 1.25), (0.5, 1.0)))
primary_crossing, unresolved = first_crossing(rows, alpha=0.05, band=0)
```

`prices` includes the known initial price. Return `j` uses `lagged_iv[j]`
and `gaps[j]`, with `len(prices) == len(gaps)+1 == len(lagged_iv)+1`.
IV is decimal annualized volatility and gaps use the matching year units.
The caller supplies genuinely lagged inputs. A full input vector does not
establish predictability; no future-IV conditioning is performed here.

The defaults follow experiment 043's **Deviation 2**, in this column order:

| Column | Registered label | Band |
|---|---|---|
| 0 | Primary | [.3,1] |
| 1 | Band M | [.25,1.25] |
| 2 | Sensitivity | [.5,1] |

Every supplied band produces a separate score with the same numerator.
For these nested bands, band M's score is at most primary's, which is at
most sensitivity's. This ordering does not make the larger score the primary
procedure: report each separately. No best-of-bands rule is implemented.
Call `first_crossing` for each column separately; its default remains primary.
Pass any subsequently registered band amendment explicitly. Callers of the
older two-column defaults must update labels as well as array lengths: the
sensitivity output is now column 2, and band M occupies column 1.

Training updates component weights and the past-only clipped drift fit.
Only post-training forecast factors enter the numerator; only post-training
returns enter the common-parameter denominator. The known start in the
level-dependent forecast remains `prices[0]`. Weighted centered updates
compute Q, K and H without subtracting nearly equal uncentered moments.

Each row records its absolute return index, forecast drift and log density,
accumulated log numerator, each band's log denominator and fitted `(b,w)`,
log scores and status. All scored checkpoints are returned, including those
after failures. A zero price or invalid observation, or an arithmetic failure,
freezes all later scores at zero evidence (`-inf` in logs); there is no restart
or silent clipping of input observations. Invalid array lengths, bands,
catalogues or known start raise `ValueError`. The caller must keep such failed
records in experiment counts. For JSON, encode nonfinite log values explicitly
(e.g. `null` with the status), rather than nonstandard `Infinity` tokens.

`first_crossing` returns the first resolved floating-point crossing and all
threshold-near checkpoints. If an earlier checkpoint is unresolved, the
actual first crossing time is also unresolved. Its relative tolerance is the
experiment's proximity heuristic, **not an arithmetic error enclosure**.
Neither this adapter nor its scores are outward certified or Lean-verified.

Run the deterministic checks with the repository's single-thread prefix:

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d28-predictable-iv/check.py
```

The checks compare the stable profile and all forecast factors with an
independent 70-digit density-product calculation, exercise all prefix replays,
change future prices/IV/gaps, compare nested bands, and retain singular and
failed records. They establish no power or empirical null coverage.
