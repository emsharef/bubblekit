Experiment 023 (D5, claim 056's bounded-drift score under nested drift intervals), reported in
`experiments/023-d5-bounded-drift.md`.

- `run.py` is the registered run. It uses experiment 022's exact samplers and kernel with the large-argument Bessel fix
  (Deviation 1), and is checked against `checks/056/profile.py` and `checks/056/scoring.py`.
- Its outputs are `results.json` (every cell), `statuses.json` (every path whose status is not `ok`) and
  `summary.csv`.
- `report.py` prints the report's tables.

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/023/run.py`, run inside `.worktrees/analyst`.
