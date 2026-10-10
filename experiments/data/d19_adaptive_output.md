# D19 adaptive branch and bound: feasibility probes (retained output)

This file answers two notes:
- the human's (via the manager) `2026-10-07-d19-adaptive-pruning.md`: refine only the boxes near the peak;
- math's `2026-10-07-d19-adaptive-ready.md`: a bounded feasibility assessment of `checks/d19-adaptive-filter/certify.py`.

**Records:** the same throwaway cent-rounded hourly GBM records as the earlier D19 probes. They come from experiment
027's clocked simulator, seed 5: 5, 20, 63 and 250 sessions drawn in that order, which gives N = 39, 159, 503 and
1,999 increments.
- **Settings:** $50 start, box b ∈ [−0.2, 0.2], w ∈ [0.04, 0.2025], clocks {flat, U(1.5, 0.25)}, split at N/2.
- **Load:** both probes ran single-process while other jobs shared the machine (experiment 028's 7 workers until
  08:35), so wall times are approximate.
- **Scope:** no score, power or registered comparison; probes only.

## 1. Math's evaluator (`experiments/data/d19_adaptive_eval_probe.py`)

This uses the reviewed claim 036/037 bounds, with claim 037's arithmetic repaired. It covers the whole box for every
clock, raises the integration resolution M only where integration error dominates, and stops at a target ratio
(factor 2, about 0.69 nats; or factor e, 1 nat) or at an evaluation budget.

```
sessions 5 N 39 factor 2 max_count 64 budget 128: tolerance met; evaluations 45, transition terms 113400, leaves 19, prunable 9, failed 0, largest M 16; log lower -90.647, log upper -89.972, width 0.675 nats; 0.2s
sessions 5 N 39 factor e max_count 64 budget 128: tolerance met; evaluations 36, transition terms 47616, leaves 17, prunable 8, failed 0, largest M 16; log lower -90.725, log upper -89.763, width 0.963 nats; 0.2s
sessions 20 N 159 factor 2 max_count 64 budget 128: tolerance met; evaluations 72, transition terms 2442848, leaves 27, prunable 10, failed 0, largest M 32; log lower -394.785, log upper -394.117, width 0.669 nats; 3.4s
sessions 20 N 159 factor e max_count 64 budget 128: tolerance met; evaluations 56, transition terms 779048, leaves 22, prunable 9, failed 0, largest M 32; log lower -394.804, log upper -393.809, width 0.995 nats; 1.4s
sessions 63 N 503 factor 2 max_count 128 budget 256: tolerance met; evaluations 149, transition terms 145898048, leaves 52, prunable 17, failed 0, largest M 128; log lower -1250.920, log upper -1250.234, width 0.685 nats; 164.2s
sessions 250 N 1999 factor 2 max_count 256 budget 128: budget exhausted; evaluations 128, transition terms 372558752, leaves 48, prunable 16, failed 0, largest M 128; log lower -4772.591, log upper -4768.709, width 3.882 nats; 416.3s
```

The uncertified numerical maximum (float64 midpoint filter, M = 32, L-BFGS-B from 5 starts per clock) took 0.6 s, 1.4
s, 5.2 s and 16.4 s on the four records (section 2). Its value sits below the certified upper bound by 0.44, 0.40, 0.47
and 2.50 nats respectively. On every record it lies inside the certified interval.

## 2. My first probe (`experiments/data/d19_adaptive_probe.py`), kept as run

This is best-first branch and bound at a fixed M. The quadrature floor is ε = ε_N + ε_k at the numerical maximizer,
and the certified width cannot fall below about 2ε. **Correction:** this probe used claim 037's bound *before* math's
arithmetic repair. The "eta037" counts are boxes where that bound came out non-finite and the probe fell back to claim
036's looser bound. Its box counts and times therefore overstate the cost; section 1 is the relevant measurement.

```
box ('-1/5', '1/5', '1/25', '81/400'), clocks {flat, U(1.5, 0.25)}, M_num 32, slack 1.0 nat, eta_min 0.05, caps 20000 boxes / 1800 s per run
sessions 5 N 39: numerical max (M=32, float64, uncertified) log -90.411 at clock 1 b -0.2000 w 0.0526, 0.6s
  M 8: certified lower at the maximizer -90.810, eps 0.399 (width floor about 0.80 nats), one box 0.0s
  M 32: certified lower at the maximizer -90.511, eps 0.100 (width floor about 0.20 nats), one box 0.1s
  M 64: certified lower at the maximizer -90.461, eps 0.050 (width floor about 0.10 nats), one box 0.3s
  branch and bound M 8: converged, boxes 578, max depth 6, open 434, log lower -90.810, log upper -89.810, width 1.000 nats (top box: eps 0.417, allowance 0.196), 3.5s; upper minus numerical max 0.601; unresolved {'lr': 0, 'eta037': 0, 'eta036': 0}
  branch and bound M 32: converged, boxes 138, max depth 5, open 104, log lower -90.511, log upper -89.514, width 0.997 nats (top box: eps 0.131, allowance 0.948), 9.3s; upper minus numerical max 0.897; unresolved {'lr': 0, 'eta037': 0, 'eta036': 0}
sessions 20 N 159: numerical max (M=32, float64, uncertified) log -394.518 at clock 1 b -0.2000 w 0.0903, 1.4s
  M 8: certified lower at the maximizer -395.327, eps 0.809 (width floor about 1.62 nats), one box 0.0s
  M 32: certified lower at the maximizer -394.720, eps 0.202 (width floor about 0.40 nats), one box 0.3s
  M 64: certified lower at the maximizer -394.619, eps 0.101 (width floor about 0.20 nats), one box 1.2s
  branch and bound M 8: quadrature floor, boxes 4342, max depth 11, open 3257, log lower -395.325, log upper -393.654, width 1.671 nats (top box: eps 0.816, allowance 0.048), 103.7s; upper minus numerical max 0.864; unresolved {'lr': 0, 'eta037': 1348, 'eta036': 0}
  branch and bound M 32: converged, boxes 1414, max depth 9, open 1061, log lower -394.720, log upper -393.724, width 0.996 nats (top box: eps 0.186, allowance 0.777), 377.2s; upper minus numerical max 0.794; unresolved {'lr': 0, 'eta037': 594, 'eta036': 0}
sessions 63 N 503: numerical max (M=32, float64, uncertified) log -1250.701 at clock 1 b 0.2000 w 0.0916, 5.2s
  M 8: certified lower at the maximizer -1253.331, eps 2.630 (width floor about 5.26 nats), one box 0.1s
  M 32: certified lower at the maximizer -1251.358, eps 0.658 (width floor about 1.32 nats), one box 0.9s
  M 64: certified lower at the maximizer -1251.029, eps 0.329 (width floor about 0.66 nats), one box 2.8s
  branch and bound M 8: quadrature floor, boxes 8294, max depth 12, open 6221, log lower -1253.313, log upper -1247.996, width 5.318 nats (top box: eps 2.702, allowance 0.044), 505.9s; upper minus numerical max 2.705; unresolved {'lr': 0, 'eta037': 1938, 'eta036': 0}
sessions 250 N 1999: numerical max (M=32, float64, uncertified) log -4771.204 at clock 1 b -0.1620 w 0.0908, 16.4s
  M 8: certified lower at the maximizer -4782.470, eps 11.267 (width floor about 22.53 nats), one box 0.2s
  M 32: certified lower at the maximizer -4774.020, eps 2.817 (width floor about 5.63 nats), one box 1.8s
  M 64: certified lower at the maximizer -4772.612, eps 1.408 (width floor about 2.82 nats), one box 7.0s
  branch and bound M 8: capped, boxes 10126, max depth 13, open 7595, log lower -4782.401, log upper -4759.461, width 22.939 nats (top box: eps 11.885, allowance 0.917), 1801.3s; upper minus numerical max 11.742; unresolved {'lr': 0, 'eta037': 2382, 'eta036': 0}
```

## Readings (feasibility only)

- **Adaptive refinement works, as the human expected.**
  - With the repaired bounds, math's evaluator meets the ~0.69-nat tolerance on N = 39, 159 and 503 within 45–149
    centre evaluations (19–52 leaves, 9–17 of them prunable, no arithmetic failures), in 0.2 s, 3 s and 164 s.
  - Uniform refinement at N = 159 was still 5.9 nats wide at depth 6 (8,192 boxes, 168 s; `d19_probe_output.md`).
- **The box count grows only mildly with N** (45, 72 and 149 evaluations; leaves 19, 27, 52), roughly in line with the
  human's 1/√N reasoning.
- **What does grow with N is the integration error.**
  - At the maximizer, ε is about 11.3, 2.8 and 1.4 nats at M = 8, 32 and 64 for N = 1,999. It scales like N/M.
  - Each centre evaluation costs O(N·M²): one box at N = 1,999 took 0.2, 1.8 and 7.0 s at M = 8, 32 and 64.
  - So at fixed tolerance the cost per path grows roughly like N³ through M, not through the box count.
- **N = 1,999 (a year of hourly bars):** the 128-evaluation budget ran out at a width of 3.88 nats after 416 s,
  with M reaching 128.
  - **Extrapolation, not a measurement:** below 1 nat needs M ≈ 256 or more. At about 4× the M = 128 cost per
    evaluation and ~100–200 evaluations, that is on the order of a few hours per path.
- **Bearing on a registered comparison:**
  - certifying a few real records at a year of hourly bars looks feasible (hours each);
  - experiment 027/028-scale simulation (400–600 paths per cell, many cells) is not, within the CPU budget;
  - 5-minute bars (N ≈ 19,749) are further out still.
  - A registered comparison would need either far fewer paths or a cheaper integration certificate, for example one
    whose error does not grow linearly in N at fixed M.
- **Unchanged limits:** this certifies only the whole-prefix compact Gaussian denominator, with no numerator
  certificate and no wider null coverage. No full-year runtime or power is established from one record per length.

## Clarifications after math's reading (`2026-10-07-d19-adaptive-reading.md`; output above unchanged)

- **Scaling:** for a fixed record, the integration allowance falls exactly as 1/M. The "N/M" growth and the "roughly
  N³" cost at fixed tolerance are not established. They assume that the record-dependent coefficients grow linearly in
  N, which these four records only illustrate.
- **The N = 1,999 cover is budget-censored:** 48 leaves when the 128-evaluation budget ran out. It cannot show that
  the cover size stays nearly constant in N.
- **The numerical maximum is not exact:** the float64 M = 32 search value is not an exact maximum. Its gap to the
  certified upper endpoint is not an accuracy certificate.
- **The uniform-refinement comparisons** (`d19_probe_output.md`, and my first probe here) used claim 037's bound
  before its arithmetic repair. They therefore do not isolate the gain from pruning alone.
- **No witnesses:** the repaired-evaluator runs in section 1 supplied no numerical witnesses. A seeded comparison is in
  `d19_witness_output.md`.
- **N = 1,999 did not reach 1 nat** (3.88 nats at the budget, 416 s). The "few hours per path" figure is a projection,
  not a measurement. It follows only from:
  - the measured 7.0 s per evaluation at M = 64;
  - the quadratic cost in M;
  - an assumed 100–200 evaluations at M = 256.
  That gives about 3.1–6.2 hours.
- **Integration error at the search point** (math's `checks/d19-adaptive-reading/reproduce.py`): ε = 0.704 at M = 128
  and 0.352 at M = 256. 2ε < 1 first holds at M = 181, before any parameter or arithmetic slack.
