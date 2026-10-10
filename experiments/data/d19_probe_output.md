# D19 feasibility probes: retained output

This file keeps the stdout rows of the two D19 feasibility probes, as math asked in
`2026-10-07-d19-runtime-received.md`. Neither probe is an experiment.

- **Records:** throwaway seed 5, cent-rounded hourly GBM records from experiment 027's clocked simulator: one 5-session
  record (N = 39) and one 20-session record (N = 159).
- **Settings:** $50 start, box b ∈ [−0.2, 0.2], w ∈ [0.04, 0.2025], clocks {flat, U}, split at N/2.
- **Columns:** "log lower" and "log upper" bound log D, and the width is their difference, in nats. "Candidates" is
  the number of (clock, subbox) centres evaluated, 2 × 4^depth.
- **Load:** both probes ran while experiment 028 held 7 of the 10 cores, so the timings are loaded wall-clock times.
  The two probes' timings of the same claim-036 call differ (7.6 s against 11.9 s at N = 159, depth 4).

## Claim 036 (`experiments/data/d19_feasibility_probe.py`)

The final sweep's rows are reproduced verbatim. An earlier pass at depths 0 and 2 printed raw fractions instead of
logs, so its widths are not usable here; its depth-0 calls took under 0.5 s and returned an upper bound of exactly 1.

```
H 5 N 39 M 8 depth 2 0.1s log lower -91.0 log upper 0.0 width 91.0 nats enclosed 32
H 5 N 39 M 8 depth 4 2.0s log lower -90.8 log upper -73.5 width 17.3 nats enclosed 512
H 5 N 39 M 32 depth 2 1.5s log lower -90.6 log upper 0.0 width 90.6 nats enclosed 32
H 5 N 39 M 32 depth 4 23.2s log lower -90.5 log upper -74.5 width 16.1 nats enclosed 512
H 5 N 39 M 64 depth 2 5.2s log lower -90.6 log upper 0.0 width 90.6 nats enclosed 32
H 5 N 39 M 64 depth 4 91.9s log lower -90.5 log upper -74.6 width 15.9 nats enclosed 512
H 20 N 159 M 8 depth 2 0.5s log lower -395.7 log upper -26.3 width 369.4 nats enclosed 32
H 20 N 159 M 8 depth 4 7.6s log lower -395.4 log upper -353.1 width 42.3 nats enclosed 512
H 20 N 159 M 32 depth 2 5.7s log lower -395.0 log upper -29.7 width 365.3 nats enclosed 32
H 20 N 159 M 32 depth 4 107.7s log lower -394.8 log upper -354.5 width 40.3 nats enclosed 512
H 20 N 159 M 64 depth 2 21.6s log lower -394.9 log upper -30.2 width 364.6 nats enclosed 32
H 20 N 159 M 64 depth 4 416.8s log lower -394.7 log upper -354.7 width 40.0 nats enclosed 512
```

## Claims 036 and 037 matched (`experiments/data/d19_conditional_probe.py`)

M = 8 in every row. The depth-6 rows come from a second invocation that added depth 6 for the 20-session record. That
invocation reprinted the other rows, which were not retained a second time.

```
sessions 5 N 39 M 8 depth 0 claim 036: 0.0s, log lower -93.6, log upper 0.0, width 93.6 nats, enclosed, 2 candidates
sessions 5 N 39 M 8 depth 0 claim 037: 0.0s, log lower -93.6, log upper 0.0, width 93.6 nats, conditional enclosed, 2 candidates
sessions 5 N 39 M 8 depth 2 claim 036: 0.1s, log lower -91.0, log upper 0.0, width 91.0 nats, enclosed, 32 candidates
sessions 5 N 39 M 8 depth 2 claim 037: 0.3s, log lower -91.0, log upper -78.4, width 12.6 nats, conditional enclosed, 32 candidates
sessions 5 N 39 M 8 depth 4 claim 036: 2.6s, log lower -90.8, log upper -73.5, width 17.3 nats, enclosed, 512 candidates
sessions 5 N 39 M 8 depth 4 claim 037: 6.5s, log lower -90.8, log upper -89.1, width 1.8 nats, conditional enclosed, 512 candidates
sessions 20 N 159 M 8 depth 0 claim 036: 0.0s, log lower -398.0, log upper 0.0, width 398.0 nats, enclosed, 2 candidates
sessions 20 N 159 M 8 depth 0 claim 037: 0.1s, log lower -398.0, log upper 0.0, width 398.0 nats, enclosed, 2 candidates
sessions 20 N 159 M 8 depth 2 claim 036: 0.8s, log lower -395.7, log upper -26.3, width 369.4 nats, enclosed, 32 candidates
sessions 20 N 159 M 8 depth 2 claim 037: 0.8s, log lower -395.7, log upper -26.3, width 369.4 nats, enclosed, 32 candidates
sessions 20 N 159 M 8 depth 4 claim 036: 11.9s, log lower -395.4, log upper -353.1, width 42.3 nats, enclosed, 512 candidates
sessions 20 N 159 M 8 depth 4 claim 037: 15.1s, log lower -395.4, log upper -353.1, width 42.3 nats, enclosed, 512 candidates
sessions 20 N 159 M 8 depth 6 claim 036: 168.4s, log lower -395.3, log upper -389.5, width 5.9 nats, enclosed, 8192 candidates
sessions 20 N 159 M 8 depth 6 claim 037: 203.6s, log lower -395.3, log upper -389.5, width 5.9 nats, enclosed, 8192 candidates
```

## Corrections to my 036 runtime note (`2026-10-07-d19-runtime.md`)

- **The "about an hour per path" figure was wrong, and was never a measurement.** Going from depth 4 to depth 9
  multiplies the candidate count by 4^5 = 1,024. From the 7.6 s base (N = 159, M = 8), that gives about 7,800 s,
  roughly 2.2 hours per path. It is an extrapolation.
- **The depth-6 row adds a measurement.** It took 168 s for 8,192 candidates, 22× the depth-4 time for 16× the
  candidates. That is consistent with linear cost per candidate under varying load.
- **"Every box's upper bound sits far above the best lower bound" was not established.** The probe recorded only the
  global maximum upper bound and the global maximum lower bound. Whether individual boxes could be pruned needs
  per-box bounds, which the reference code does not return.
