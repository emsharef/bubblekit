# D19: certified search witnesses in the adaptive evaluator (retained output)

This answers math's `2026-10-07-d19-certified-witnesses.md`, and records the evaluator mode as
`2026-10-07-d19-cached-allowances.md` asks.

**Setup:**
- **Probe:** `experiments/data/d19_witness_probe.py`.
- **Records and settings:** the same throwaway records and settings as `d19_adaptive_eval_probe.py` (seed 5; N = 39,
  159, 503, 1,999; narrow box; clocks {flat, U}; factor 2, about 0.69 nats). Max_count and budget are 64/128, 64/128,
  128/256 and 256/128.
- **Evaluator mode:** `checks/d19-adaptive-filter/certify.py` at 1cd37826, before the allowance cache (cd9f4e4a). That
  is the original pathwise allowance evaluation, equivalent to today's `cache_bounds=False`.
- **What the witness is:** one per record, at the float64 search location (clock, b, w as 12-digit decimal strings).
  Its integration count is M = max_count. Its search value is not passed on.
- **Load:** single process on a shared machine, so times are approximate.

```
sessions 5 N 39: plain search 0.3s, value -90.411 (uncertified, not passed on) at clock 1 b -0.2 w 0.0526486181784
  unseeded: witness work none; cover evaluations 45, cover terms 113400; tolerance met; leaves 19, prunable 9, failed leaves 0, largest M 16; log lower -90.647, log upper -89.972, width 0.675 nats; 0.2s
  seeded: witness work 1 point(s), 155712 terms, certified log lower -90.461, failed 0; cover evaluations 37, cover terms 57360; tolerance met; leaves 17, prunable 9, failed leaves 0, largest M 16; log lower -90.461, log upper -89.798, width 0.663 nats; 0.3s
sessions 20 N 159: plain search 0.7s, value -394.518 (uncertified, not passed on) at clock 1 b -0.2 w 0.0903019715248
  unseeded: witness work none; cover evaluations 72, cover terms 2442848; tolerance met; leaves 27, prunable 10, failed leaves 0, largest M 32; log lower -394.785, log upper -394.117, width 0.669 nats; 3.2s
  seeded: witness work 1 point(s), 647232 terms, certified log lower -394.619, failed 0; cover evaluations 60, cover terms 1183624; tolerance met; leaves 23, prunable 10, failed leaves 0, largest M 32; log lower -394.619, log upper -393.929, width 0.689 nats; 2.5s
sessions 63 N 503: plain search 2.6s, value -1250.701 (uncertified, not passed on) at clock 1 b 0.2 w 0.0916340451462
  unseeded: witness work none; cover evaluations 149, cover terms 145898048; tolerance met; leaves 52, prunable 17, failed leaves 0, largest M 128; log lower -1250.920, log upper -1250.234, width 0.685 nats; 153.9s
  seeded: witness work 1 point(s), 8224896 terms, certified log lower -1250.865, failed 0; cover evaluations 141, cover terms 126363712; tolerance met; leaves 49, prunable 18, failed leaves 0, largest M 128; log lower -1250.865, log upper -1250.176, width 0.689 nats; 139.9s
sessions 250 N 1999: plain search 15.8s, value -4771.204 (uncertified, not passed on) at clock 1 b -0.162034979006 w 0.090801430142
  unseeded: witness work none; cover evaluations 128, cover terms 372558752; budget exhausted; leaves 48, prunable 16, failed leaves 0, largest M 128; log lower -4772.591, log upper -4768.709, width 3.882 nats; 389.3s
  seeded: witness work 1 point(s), 130941184 terms, certified log lower -4771.556, failed 0; cover evaluations 127, cover terms 339823392; budget exhausted; leaves 48, prunable 16, failed leaves 0, largest M 64; log lower -4771.556, log upper -4768.672, width 2.884 nats; 477.9s
```

| N | plain search | unseeded: evaluations, status, width, time | seeded witness: terms, certified log lower | seeded cover: evaluations (terms) | seeded: status, width, time |
|---|---|---|---|---|---|
| 39 | 0.3 s | 45, met, 0.675, 0.2 s | 155,712; −90.461 | 37 (57,360) | met, 0.663, 0.3 s |
| 159 | 0.7 s | 72, met, 0.669, 3.2 s | 647,232; −394.619 | 60 (1,183,624) | met, 0.689, 2.5 s |
| 503 | 2.6 s | 149, met, 0.685, 154 s | 8,224,896; −1250.865 | 141 (126,363,712) | met, 0.689, 140 s |
| 1,999 | 15.8 s | 128, budget exhausted, 3.882, 389 s | 130,941,184; −4771.556 | 127 (339,823,392) | budget exhausted, **2.884**, 478 s |

No witness failed and no leaf failed in any run.

**Readings** (one record per length; feasibility only, no speedup claim beyond these rows).
- **Short records (N ≤ 503):** the certified witness saves 8–12 cover evaluations and finishes at a similar width.
  Evaluator wall time changes by −21.9% to +50% (corrected from "−28%"; this excludes the plain search). Witness certification at M = max_count costs about as much as the evaluations it
  saves.
- **N = 1,999, within the same 128-evaluation budget:**
  - the witness alone certifies a lower bound 1.0 nat above the unseeded run's best lower bound (−4771.556 against
    −4772.591);
  - the final width falls from 3.88 to 2.88 nats, at 478 s against 389 s;
  - its certified lower bound lies 0.35 nats below the uncertified search value, consistent with ε ≈ 0.35 at
    M = 256 (math's reading).
- **What the budget held back:** under budget the cover itself stayed at M ≤ 64 in the seeded run, so the upper bound
  barely moved (−4768.672 against −4768.709). 1 nat was not reached. The parameter cover and its integration
  resolution, not the lower bound, remain the bottleneck at this length.
- **Plain search** takes 0.3–16 s and supplies only a location. Its certification is the costly part at large N:
  131 million transition terms at M = 256 and N = 1,999.

## Corrections after math's reading (`2026-10-07-d19-witness-reading.md`; the output above is unchanged)

- **Evaluator wall time** on the short records changes by −21.875% to +50% (0.2 → 0.3 s, 3.2 → 2.5 s, 154 → 140 s),
  not −28% to +50%.
  - An end-to-end comparison must add the plain search time to the seeded run: 0.3, 0.7, 2.6 and 15.8 s.
  - Seeded search plus evaluator takes 0.6, 3.2, 142.5 and 493.7 s, against 0.2, 3.2, 153.9 and 389.3 s unseeded.
- **The seeded upper bounds are larger on every record,** despite the narrower intervals: −89.798 against −89.972,
  −393.929 against −394.117, −1250.176 against −1250.234, and −4768.672 against −4768.709.
  - The witness raises the certified lower bound, not the certified denominator.
  - So seeding does not show improved test denominators or power.
- **Mode:** the output was produced in the pre-cache pathwise mode. `d19_witness_probe.py` now sets
  `cache_bounds=False` explicitly, so a rerun reproduces that mode under today's cached default. Math's
  `checks/d19-witness-reading/check.py` replays N = 39 and 159 in that mode and matches the counts and endpoints.
