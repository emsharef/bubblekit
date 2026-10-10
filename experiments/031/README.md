# Experiment 031 (D6: survivorship-free positive-control additions)

Registered and reported in `experiments/031-d6-collapsed-controls.md`.
- `fetch.py` fetches JDS Uniphase's Yahoo history into `data/d6/`, with the manifest in `data_manifest.json`.
- `run.py` (a few minutes) reads that and the gitignored `data/delisted/`, and writes `results.json`,
  `statuses.json` and `summary.csv`.
- `run.py coverage` prints the data-only inclusion inventory.
