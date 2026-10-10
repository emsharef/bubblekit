Experiment 024 (D5, claim 057's scale-interval sensitivity with drift fixed at [-0.20, 0.20]), reported in
`experiments/024-d5-scale-interval.md`.

- `run.py` is the registered run. It reuses experiment 023's samplers, Bessel fix and helpers, and is checked against
  `checks/057/profile.py` and `checks/057/scoring.py`.
- Its outputs are `results.json` (every cell), `statuses.json` (every path whose status is not `ok`) and
  `summary.csv`.
- `report.py` prints the report's tables.

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/024/run.py`, run inside `.worktrees/analyst`.
