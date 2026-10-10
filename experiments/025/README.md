Experiment 025 (D5 realistic panels), reported in `experiments/025-d5-realistic-panels.md`.

- `run.py` is the registered run. It simulates correlated panels and scores them with usable test v1 (claim 055 with
  e-BH) and experiment 015's competitors.
- Its outputs are `results.json` (all 80 cells), `statuses.json` and `summary.csv`.
- `report.py` prints the report's tables.

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/025/run.py`, run inside `.worktrees/analyst`. It takes about 2½ hours on 7 workers.
