# Experiment 032 (D6: first real-data intraday application)

Registered and reported in `experiments/032-d6-intraday-application.md`.
- `run.py` (a few minutes) reads the gitignored hourly archive `data/d6-intraday/bars/60m/` and writes `results.json`,
  `statuses.json` and `summary.csv`.
- `run.py inventory` is the data-only inventory.
- `run.py smoke [n]` times column (iii) on a synthetic record.
