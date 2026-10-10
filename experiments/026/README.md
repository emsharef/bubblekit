Experiment 026 (D15/D5, claim 059's single-switch score against claims 055 and 054), reported in
`experiments/026-d15-single-switch.md`.

- `run.py` is the registered run. It reuses experiment 023's code and is checked against `checks/059`.
- Its outputs are `results.json`, `statuses.json` and `summary.csv`.
- `report.py` prints the report's tables.

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/026/run.py`, run inside `.worktrees/analyst`. It takes about 15 minutes on 7 workers.
