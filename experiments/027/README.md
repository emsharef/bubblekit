Experiment 027 (D17 intraday power), reported in `experiments/027-d17-intraday-power.md`.

- `run.py` is the registered run. It simulates clocked GBM and CEV, and scores them with claims 054, 055 and 033 (and
  034 at hourly sampling), plus "v1 flat".
- Its outputs are `results.json`, `statuses.json` and `summary.csv`.
- `report.py` prints the report's tables.

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/027/run.py`, run inside `.worktrees/analyst`. It takes about 9 minutes on 7 workers.
