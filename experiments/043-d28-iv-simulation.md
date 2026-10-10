---
id: "043"
title: "D28: implied-volatility-scaled sequential score (claim 042) in simulation — false alarms and power with scale-tracking IV, and absorption when IV also tracks the level"
status: reproduced
direction: D28
claims: ["042", "055"]
code: experiments/043/
---
## Question

LAB_REQUEST.md fifth addendum, item 20, the simulation stage. It follows math's design note
`2026-10-08-d28-predictable-iv-design.md` and red-passed claim 042, after the D24–D26 priority work. Real data are
not part of this experiment.

**The score.** Claim 042 is a sequential score with a normalized predictable forecast in the numerator. Its
denominator profiles a Gaussian null whose daily variance is w·IV²_(t−1)·Δ, with w in a declared band and the
previous day's implied volatility as the predictable scale.

**The questions:**
- **Table 1:** with IV tracking the scale, what are the empirical false alarms under the contract's own laws and
  under stress models outside it, and what is the power on CEV alternatives?
- **Table 2:** how much power does IV absorb when it also tracks the level?
- **The addendum's key question:** is there useful daily power for level dependence that IV does not track, in the
  presence of scale switching? If not, the addendum's stop rule moves effort to D29.

**Jobs, kept separate:**
- calibration under claim 042's contract (actual-contract controls);
- empirical false alarms outside it (stress models, not size evidence);
- power and absorption on CEV alternatives.

No result exists when this Design is committed.

## Design

**Record.**
- Daily, Δ = 1/252, exact positive prices from s = 1.
- **Training:** 126 returns.
- **Scored horizons:** N ∈ {252, 504} scored returns after training. The score is monitored at every scored return
  (anytime), and its final value is also kept.

**(1) Actual-contract controls** (claim 042's (2)). Returns are Normal(bΔ − w v_t/2, w v_t) with
v_t = IV²_(t−1)·Δ.
- **b ∈ {−0.10, 0, 0.10}** annually, and **w ∈ {0.5, 1.0}** (the primary band's endpoints).
- **IV processes:**
  - **C-const:** IV = 0.20.
  - **C-switch:** a two-state IV (0.15 or 0.40), Markov with expected stay 20 days. The next step's scale is already
    revealed by IV_(t−1).
  - **C-feedback:** claim 042's (7), with p = 2, κ = 0.30, w₀ = w and IV_(t−1) = κ (S_(t−1)/s)^(p−1)/√w. It rises
    with the level but is a null.

**(2) Stress models** (outside claim 042; empirical false alarms only).
- **Heston:** κ_v = 2, θ = 0.04, ξ = 0.5, ρ = −0.7, v₀ = θ, zero drift. Full-truncation Euler with 20 substeps a day.
  A step-size check against 40 substeps on 200 paths is reported.
- **Within-day regime switching:** latent volatility 0.15 or 0.45, switching with intensity 1/20 per day at a uniform
  time within the day, on 20 substeps a day.
- **Merton:** diffusion σ = 0.25, jump intensity 1 a year, log-jump N(−0.05, 0.10²) (experiment 025's jump law),
  compensated.
- **Causal IV construction** (each IV_(t−1) from the state at t−1 only; never from the next return).
  - Heston: IV² = (model-implied expected average variance over the next 21 trading days under the physical law) / r.
  - Switching: IV² = (expected average variance over 21 days given the current regime) / r.
  - Merton: IV² = (σ² + jump variance rate) / r, with the diffusion share also reported.
  - **Variance ratios:** fixed, r = 0.75; and time-varying, r_t = 0.75 + 0.15 sin(2πt/252).
  - These are **labelled proxies, not option-implied volatilities.**

**(3) Alternatives.**
- **Exact CEV:** experiment 022's absorbed-kernel sampler at daily steps. p ∈ {1.25, 1.5, 2} × initial relative scale
  κ ∈ {0.20, 0.40, 0.80}, from s = 1, with zero physical drift.
- **The IV paired to each path** (from the previous price; a synthetic scale proxy, not option-implied volatility):
  - **background only:** IV = κ/√0.75;
  - **partial:** IV = κ (S_(t−1)/s)^((p−1)/2)/√0.75;
  - **full:** IV = κ (S_(t−1)/s)^(p−1)/√0.75.
- **A-switch (the key question):** a discrete local-lognormal model, explicitly **not exact CEV**.
  - R_t ~ Normal(−a_t/2, a_t), with a_t = κ² m_t (S_(t−1)/s)^(2p−2) Δ.
  - The background m_t ∈ {1, 4} is two-state Markov with expected stay 20 days.
  - IV tracks **only the background:** IV = κ √m_t / √0.75.
  - Cells: p ∈ {1.5, 2}, κ ∈ {0.20, 0.40}.

**Paths and seeds.**
- 2,000 independent records per cell per horizon (worst-case binomial SE ≤ 0.0112).
- `SeedSequence(20261043)`, with one child per (cell, horizon) in table order.
- Forecast and band comparisons use paired records (the same paths).
- **Kept in every rate's denominator:** failures, extreme paths, zero prices (scored as zero evidence after absorption)
  and unresolved values.

**Procedure.**
- **Denominator:** claim 042's closed profile (5), the exact common-b, common-w prefix profile, evaluated at every t
  with stable residual sums. Never a grid maximum or fitted point likelihood.
  - **Primary band:** [0.5, 1.0].
  - **Sensitivity band:** [0.25, 1.25], reported separately, never as a best-of-two.
- **Numerator (primary forecast):** a finite mixture of local-lognormal return forecasts with variance
  c·IV²_(t−1)·(S_(t−1)/s)^(2p−2)·Δ, for p ∈ {1, 1.25, 1.5, 2} and c ∈ {0.25, 0.5, 0.75, 1, 1.5, 2, 4} (28
  components).
  - **Mean:** b̂_(t−1)Δ minus half the component's variance.
  - **Drift fit:** b̂_(t−1) = clip((Σ_(j<t) (R_j + R_j²/2)) / Σ_(j<t) Δ_j, −1, 1), from training and all earlier scored
    returns only.
  - **Weights:** uniform before training, then Bayesian, proportional to the prior times all earlier component
    densities. The training returns set the weights at the first scored step. Every row integrates to one.
  - Realized factors are never revised.
  - It is a forecast approximation, not an exact CEV kernel.
- **Crossing:** at α ∈ {0.05, 0.10}, the first t with E_t ≥ 1/α. A decision whose floating-point log score lies
  within 10⁻⁹ (relative) of log(1/α) is marked unresolved.
- **Comparators** (separately labelled, different scope):
  - claim 055's v1 on the full record (training + scored), with its original fixed split at the midpoint, scored once;
  - GSADF (experiment 021's procedure, simulated critical values at the record length) on the full record.

**Outputs.**
- **Table 1** (controls, stress, alternatives with background-only IV): anytime crossing rates with Wilson intervals,
  by control type and stress model.
- **Table 2** (absorption): power for background, partial and full tracking, paired, by p and κ.
- **A-switch:** power at the controls' observed false-alarm level, the addendum's stop-rule question.
- **Also reported:**
  - score distributions (final and running-maximum quantiles) and ROC (alternatives against C-switch controls);
  - first-crossing delay;
  - numerical failure and unresolved rates;
  - the Heston step-size check;
  - the diffusion share for Merton.
- **Kept for replay:** per-path final, maximum and first-crossing values, with seeds.
- **Prefix-replay check:** on 20 paths per cell, recomputing on prefixes truncated at 10 random times reproduces the
  earlier scores exactly (future blindness).
- **Stress-calibrated thresholds:** if reported at all, they use separate calibration and evaluation seeds and are
  labelled empirical.
- Files: `results.json`, `statuses.json` and `summary.csv`.

**Implementation.**
- Code is committed before any result. Smoke tier: 50 paths per cell on `SeedSequence(20261143)`.
- Runs on a fresh branch after this registration merges and after D24–D26's runs, with the single-thread BLAS prefix
  and at most cores − 3 workers.

**Scope.**
- Exact positive prices only; any rounding study is separate.
- Synthetic IV proxies, not option prices.
- Floating-point evaluation is not an outward certificate.
- A non-rejection is not proof of no bubble, nor of complete surface pricing.

## Deviations

**Deviation 1 (2026-10-08, before any code or result): the bands, per the PM's note `2026-10-08-d28-simulation.md`.**
- **Primary band:** w ∈ [0.3, 1.0]. It covers the sample implied/realized variance ratio near 0.45 that the
  librarian's D28 sweep reports.
- **Labelled secondary:** w ∈ [0.5, 1.0]. The registered sensitivity band [0.25, 1.25] is dropped, so exactly these
  two are reported, each separately and never as a best-of-two.
- **Contract controls:** w ∈ {0.3, 0.5, 1.0}, which covers both bands' endpoints. Their reading is per band: a
  control with w outside a band is outside that band's contract.
- **Everything else is unchanged,** including the stress models (robustness, not size), the CEV alternatives, the
  absorption set, the A-switch stop-rule question and the first-crossing times.
- **Real data:** SPX with VIX, and NDX with VXN from 2001-01-23, come after this experiment as a separate
  registration.

**Deviation 2 (2026-10-08, before any code or result): math's band and history correction (note
`2026-10-08-d28-band-history-correction.md`).**
- **Wording correction to Deviation 1:** 0.45 is the **realized/implied** variance ratio (Bollerslev, Tauchen and
  Zhou 2009, Table 1: 14.93/33.23 = 0.4493). It is a ratio of monthly means, not implied/realized (whose inverse is
  about 2.226), not a mean of ratios, and not a one-day conditional bound. No band here is a coverage interval; each
  is a design choice.
- **Bands.** The PM's ruling, recorded in the ROADMAP, is kept as primary, and math's proposed band is added. All
  three are declared now, before any result, and each is reported separately, never as a best-of:
  - **primary:** [0.3, 1.0] (the PM's ruling);
  - **labelled band M:** [0.25, 1.25] (math's proposed primary);
  - **labelled sensitivity:** [0.5, 1.0].
  Shifted bands are not ordered by evidence: only nested bands with the same numerator and the same IV observations
  are. The comparisons therefore use paired records, and only the nested pair (sensitivity inside primary, and both
  inside band M) is read as an ordering. The PM is asked to confirm or swap the primary, and any swap will be recorded
  here before results.
- **Contract controls:** w ∈ {0.25, 0.3, 0.45, 0.5, 1.0, 1.25}. The constant w = 0.45 is added per math, and the
  endpoints of all three bands are covered. Each control is read only against the bands that contain its w.
- **Time-varying ratio:** a changing w_t is outside claim 042 even when every value lies inside a band. The stress
  models' time-varying ratio r_t, and any control with a changing w_t, are reported as stress, separately from the
  contract controls.
- **Carried to the real-data registration** (SPX with VIX, NDX with VXN), not used here:
  - **Pre-2003 VIX:** it was reconstructed later from historical option quotes (Bekaert and Hoerova 2013,
    footnote 3). Those runs are labelled *retrospective reconstructed-scale analysis*, not contemporaneous
    deployment. The registration states that the reconstruction uses only quotes available by the previous cutoff, a
    fixed algorithm and no future smoothing. Predictability is then a property of that enlarged information set; the
    conditional Gaussian law is a separate assumption.
  - **Release times:** checked for later data too. No index close published after a return interval begins is used
    as that interval's input.
  - **VXN:**
    - no NDX run through March 2000 by backfill;
    - scoring starts only after a prior valid VXN value and the declared training history exist;
    - the Yahoo (from 2001-01-23) and Cboe (from 2009-09-14) splice, the missingness and the discrepancy handling are
      registered;
    - available histories are reported, not nominal ones.
  - **Registration versus observability:** prospective registration decisions are kept apart from any claim that the
    downloaded historical values were observable in real time.

**Deviation 3 (2026-10-08, with the run code and before any result): implementation, using math's evaluator (note
`2026-10-08-d28-evaluator-ready.md`).**
- **Evaluator.**
  - The score is `checks/d28-predictable-iv/evaluate.py`, unchanged: claim 042's stable profile and the registered
    28-component predictable mixture.
  - **Drift fit:** clip(Σ(r + r²/2)/Σ gap, −1, 1) over all earlier returns. The weights start uniform and are updated
    past-only, and the training returns update the fit but give no evidence.
  - **Bands:** Deviation 2's three bands are passed explicitly, each a separate score with the same numerator.
  - **Crossing:** the evaluator's `first_crossing` with relative tolerance 10⁻⁹. A path whose first crossing could
    be preceded by a threshold-near checkpoint is counted as unresolved.
  - **Failures:** zero prices (absorbed CEV paths) and numerical failures stay in every rate's denominator. Their
    later scores are zero evidence.
- **The v1 comparator** runs on the first 500 paired records of each cell and horizon (worst-case Monte Carlo SE
  0.022), not all 2,000. It costs about 2 s a record, so all 364,000 records would take about 29 hours on 7 workers.
  It is labelled with its different monitoring scope, as registered. GSADF runs on every record.
- **Simulation details.**
  - **C-switch and A-switch:** a daily two-state chain switching with probability 1/20 (expected stay 20 days), with
    a uniform first state. The state for return t is revealed by IV_(t−1).
  - **Stress models:** zero drift.
    - **Heston:** IV² is the expected average variance over 21 days given v at the previous close, divided by the
      ratio. The step-size check reruns 200 paths at 20 and 40 substeps.
    - **Within-day switching:** at most one switch per day, with probability 1 − e^(−1/20), at a uniform time, on 20
      substeps. IV² is the 21-day expected average variance given the regime at the previous close, divided by the
      ratio.
    - **Merton:** IV² is the total variance rate σ² + λ(μ² + η²) divided by the ratio. The diffusion share is 0.833
      and is reported.
  - **CEV alternatives:** experiment 027's step-by-step copy of 022's exact sampler, at daily steps from S₀ = 1. An
    absorbed path has no GSADF or v1 evidence, and is counted.
- **The stop-rule comparison.** A-switch's power at an empirical threshold, labelled empirical:
  - **Threshold:** the 95% quantile of the primary band's running-maximum score on calibration paths.
  - **Calibration paths:** C-switch with b = 0 and w ∈ {0.3, 1.0} (the primary band's endpoints), 2,000 per w and
    horizon, on separate seeds `SeedSequence([20261243, 10w, N])`.
  - Nominal-α power and the controls' observed false-alarm rates are reported beside it.
- **ROC:** the running-maximum primary-band score of each alternative against all C-switch controls whose w lies
  inside the primary band, per horizon.
- **Prefix replay:** the first 20 paths of each cell and horizon, truncated at 10 random times, must reproduce the
  full record's scores at every retained index exactly. A code test on a throwaway seed (3 paths of each model type)
  found 0 mismatches.
- **Smoke tier:** 50 paths per cell, v1 on 10, seed `SeedSequence(20261143)`.
- **JSON:** nonfinite logs are written as null, with the status kept.
- **Order:** the run follows D24–D26 (experiments 039–041), as registered.

**Deviation 4 (2026-10-08, before any result): integration fixes from math's note
`2026-10-08-d28-run-integration.md` (FINDINGS "D28 run integration"; reproducer `checks/d28-run-inputs/reproduce.py`).**
1. **Paired CEV arms (seed change).**
   - **Defect:** Deviation 3's code gave the background, partial and full tracking arms different seeds, so Table 2
     was not paired as registered.
   - **Change:** every (p, k, N, batch) now uses the background arm's batch seed for all three arms, so the arms
     share one price record and differ only in the causal IV built from it. Each parent spawns its batch seeds once,
     since `spawn` is stateful.
   - **Check:** all 720 (p, k, N, batch) groups share a seed, and the simulated price arrays are equal across arms.
     All other cells keep their seeds.
   - Band comparisons stay paired.
2. **Comparator guards.**
   - **Defect:** a record with a +∞ price passed the old positivity test and reached GSADF.
   - **Change:** GSADF and v1 now run only on records whose prices are all finite and positive. Each is isolated per
     record with an explicit status ("not run: nonpositive or nonfinite price", "nonfinite statistic" or "error: …").
   - Every record stays in every rate's denominator. A D28 crossing earned before a later failure is kept (the
     evaluator's rows).
3. **Delays.** A resolved crossing preceded by a threshold-near checkpoint has an unresolved first date. Detection
   rates are unchanged; the delay reports now separate:
   - **identified first crossings:** count, median and quartiles;
   - **unresolved first dates:** count, with medians of the earliest near index and of the resolved crossing;
   - **near-only records:** count.
   The first-resolved delay is kept only with the label "not an exact first-crossing delay". On math's witness (near
   at 2, crossing at 7), the record now counts as one unresolved first date in [2, 7].
4. **Held-out false alarms at the empirical threshold.**
   - Before the A-switch stop-rule reading, the same calibrated threshold is applied to the independent main-run
     records.
   - **Reported:** every control cell, labelled inside or outside the primary band; two pools (C-switch with b = 0
     and w ∈ {0.3, 1.0}, and all controls inside the primary band), labelled "not a worst-case guarantee"; and the
     stress models separately. All with counts and Wilson intervals.
   - The threshold keeps its empirical label.

**Deviation 5 (2026-10-08, before the full run): the smoke tier's timing.**
- **Smoke tier:** `run.py smoke` (50 paths per cell and horizon, v1 on 10, seed `SeedSequence(20261143)`) ran
  9,100 paths in 600 s on 7 workers, with 0 replay mismatches. Its scores are not tabulated (`smoke.json`).
- **Projection:** about 0.06 CPU-s per path without v1 and about 2 s per v1 call. The full run is 364,000 paths plus
  91,000 v1 calls, plus the calibration set and the Heston step check: about 8 hours on 7 workers. No design change.

## Results

**Status: reported (2026-10-08).** `experiments/043/run.py` (Deviations 3–5; code as merged), 28,071 s (7.8 h) on 7
workers.
- **Outputs:** `results.json` (summaries, critical values, the empirical-threshold block, ROC, the Heston check),
  `statuses.json`, `summary.csv` and `paths.json.gz` (per-path scores, crossings and seeds, 28 MB).
- **Records:** 364,000, at 2,000 per cell and horizon. v1 ran on the first 500 of each, per Deviation 3.
- **Prefix replay:** 0 mismatches over 20 paths per cell and horizon.
- **Failures:** 1 numerical failure (C-feedback, b = 0.1, w = 1.25, N = 504), kept in its denominator.
- **Unresolved crossings:** none, at either α, in any band.
- Rates below are anytime crossing rates at α = 0.05 unless stated. Worst-case Monte Carlo SE is 0.011.

**1. Calibration under claim 042's contract** (the 108 constant, revealed-switch and feedback controls).
- **Primary band [0.3, 1.0]:** the 72 control cells with w inside the band cross at most **1.45%** (at most 3.4% at
  α = 0.10), across all b, all three IV processes, and both horizons. This includes the feedback scale whose IV rises
  with the level.
- **Band M [0.25, 1.25]:** it covers every control and crosses at most 1.15%.
- **Sensitivity band [0.5, 1.0]:** controls inside it cross at most 0.95%.
- **Outside the band:** controls whose w lies outside a band are outside that band's contract, and they cross
  heavily, as expected.
  - Primary band: 12–61% at w = 0.25 and 32–61% at w = 1.25.
  - Sensitivity band: 94–100% at w = 0.25 and 0.3, and up to 11% at w = 0.45.
  - **A w below the band's lower end is the costly error,** the reason for math's band correction.
- **The guarantee holds as proved.** The band choice is the operative decision: w must be inside the band.

**2. Stress models outside claim 042** (empirical false alarms, not size).

| model | primary, N = 252 | primary, N = 504 | band M | sensitivity |
|---|---|---|---|---|
| Heston (fixed / varying ratio) | 0.1% / 0.0% | 0.1% / 0.0% | ≤ 0.1% | ≤ 1.3% |
| Within-day regime switching | 3.8% / 3.8% | 8.3% / 8.0% | 3.8–8.2% | 7.6–13.1% |
| Merton jumps (diffusion share 0.833) | 7.7% / 9.0% | 14.4% / 17.4% | 5.8–15.7% | 7.7–17.4% |

- **Jumps** break the Gaussian contract and false-alarm above α, increasingly with horizon.
- **Within-day switching** does the same from N = 504.
- **Heston** (continuous, with IV built from its state) does not. Its step-size check (20 against 40 substeps, 200
  paths) gives 0 crossings at both, with median final log scores of −4.06 and −4.17.

**3. CEV alternatives, Table 1** (IV tracks the background scale only; primary band).

| p | κ = 0.2, N = 252 / 504 | κ = 0.4, N = 252 / 504 | κ = 0.8, N = 252 / 504 |
|---|---|---|---|
| 1.25 | 0.0% / 1.0% | 1.3% / 8.8% | 11.8% / 44.4% |
| 1.5 | 1.2% / 9.9% | 14.0% / 45.8% | 46.3% / 84.9% |
| 2 | 12.8% / 44.7% | 47.8% / 86.9% | 88.0% / 99.5% |

**4. Absorption, Table 2** (the same price records, paired).
- **Partial tracking:** power falls to 0–66%. For example, at p = 2 and κ = 0.8 it falls from 99.5% to 66.4% at
  N = 504.
- **Full tracking:** power falls to **at most 0.2%** in every cell, at or below the controls' rates.
- This is **measured** absorption of power on exact CEV transitions: numerical evidence only. Claim 042's exact
  absorption (part 3) concerns the discrete Gaussian feedback law, which the C-feedback controls exercise, not the
  exact CEV transitions of this table. The identified first crossings, where they exist, come at a median of 100–450
  scored days.

**5. The stop-rule question: A-switch** (level dependence that IV does not track, with a switching background that IV
does track; primary band).

| p, κ | N = 252 | N = 504 | at the empirical threshold, N = 252 / 504 |
|---|---|---|---|
| 1.5, 0.2 | 7.9% | 26.9% | 17.0% / 44.5% |
| 1.5, 0.4 | 31.1% | 74.1% | 47.8% / 84.4% |
| 2, 0.2 | 32.5% | 73.3% | 46.8% / 83.1% |
| 2, 0.4 | 75.0% | 97.5% | 86.6% / 98.8% |

- **At nominal α:** the in-band C-switch controls cross at most 1.3%, so this power comes at a controlled
  false-alarm cost. The identified first crossings come at a median of 121–188 scored days for one year of data and
  153–348 for two.
- **The empirical threshold** is labelled empirical and calibrated on separate seeds: horizon-specific log cutoffs
  1.1674080773751596 (N = 252) and 1.167429582220437 (N = 504), each the 95% quantile of the running maximum on
  C-switch with b = 0 and w ∈ {0.3, 1.0}.
  - **Held out at that same threshold,** the pooled C-switch endpoints cross 5.4% (N = 252) and 6.0% (N = 504), and
    all in-band controls pooled cross 3.0% and 3.6%.
  - **But the worst single in-band cell crosses 12.2%** (constant IV, b = −0.1, w = 0.3). So the pooled 5% target is
    not a worst-case guarantee.
  - The stress models at that threshold are higher still: Merton 10.5–23%, within-day switching 9–17%, Heston at most
    0.5%.
  - **The nominal α = 0.05 rule is the one claim 042 covers:** for the exact score, under the full conditional
    Gaussian, common-b, common-w contract. It is not a certified property of this floating-point computation, nor
    of the Heston, hidden-switch or Merton laws.
- **ROC** (primary-band running maximum against the in-band C-switch controls):
  - A-switch AUC is 0.57–0.95 at N = 252 and 0.74–1.00 at N = 504;
  - CEV with background tracking reaches 0.98 (p = 2, κ = 0.8);
  - CEV with full tracking gives 0.38–0.40, below one half: those paths score lower than the controls.

**6. Comparators** (each labelled with its scope).
- **GSADF on the same paths:** 4–17% on constant-IV controls, 11–36% on the feedback controls, 28–42% on C-switch and
  Heston, and 9–42% on within-day switching and Merton. Its rate on a CEV path is the same whatever the IV, since it
  uses prices only.
- **v1 with its fixed split** (500 records per cell):
  - 0% on constant-IV controls, but **9–53% on the feedback controls**. Their level-dependent scale is a null for claim
    042, but not for v1, which ignores IV.
  - 0.2–3.3% on C-switch;
  - 0–33% on the CEV alternatives;
  - 3–28% on A-switch.

**Reading.**
- **Validity (the theorem's job):** in-band controls cross at or below 1.45% at α = 0.05 at both horizons, including
  IV that rises with the level and revealed scale switches. This is consistent with claim 042, which guarantees the
  exact score under its full contract; the floating-point evaluation is not certified.
  Outside the contract it fails in the directions math predicted: w below the band, jumps, and within-day switching.
- **Absorption:** when IV tracks the level dependence fully, the score has almost no power (at most 0.2%) on exact
  CEV transitions. That is numerical evidence, not an exact embedding into the Gaussian null. A non-rejection means no
  departure was detected by this procedure, not proof that IV prices all level dependence or that there is no
  bubble.
- **The addendum's key question:** daily data **does** have useful power for level dependence that IV does not track,
  in the presence of scale switching, at a controlled false-alarm cost: 27–98% with two years of data, and 8–75% with
  one, at nominal α.
  - So the registered stop rule (stop daily price-based testing if this power is absent) **does not trigger** on this
    design.
  - The decision itself is math's, per the PM's note.
- **Scope:**
  - this is a simulation with synthetic IV proxies, not option prices;
  - exact prices only;
  - floating-point evaluation is not an outward certificate;
  - stress-model behaviour is empirical;
  - the real-data registration (SPX with VIX, NDX with VXN) comes next, with Deviation 2's requirements.

**Correction (2026-10-08, math's note `2026-10-08-d28-decision-and-scope.md`; recount
`checks/d28-results-reading/check.py`): scope only, no number changes.**
- Exact absorption (claim 042 part 3) concerns the discrete Gaussian feedback law. The Table 2 CEV rates are measured
  numerical evidence.
- The nominal guarantee is for the exact score under the full contract, not for the floating-point computation or the
  stress laws.
- The empirical cutoffs are horizon-specific (1.1674080773751596 and 1.167429582220437), and the worst in-band cell
  (12.2%) rules out a worst-case 5% reading.
- Math's decision: the stop rule does not trigger, so D28 continues to the index-data registration.

## Review

Reviewer, 2026-10-08, against main at `bafe47b9`, which contains the results commit `a4146ca4`.

**Method.** I wrote my own simulators and score from the Design and Deviations 1–4, without reading `experiments/043/*.py` or math's evaluator `checks/d28-predictable-iv/`. The script is committed as `checks/review/exp043/reproduce.py`, with its rerun command and seed in its header, and runs single-process in about 25 s.
- **The score.**
  - **Denominator:** claim 042's closed profile (5) over the scored returns at every scored step. It is the formula I verified against direct bounded maximization in my claim-042 review, now vectorized.
  - **Numerator:** the registered 28-component predictable mixture, with Bayesian weights and the clipped drift fit updated on training and scored returns, and evidence on scored returns only.
  - **Bands:** all three.
- **The record.** 126 training plus 504 scored returns. The N = 252 rates come from the first 252 scored returns, which is equal in law to a separate 252-return record.
- **The cells,** 14 in all, at 2,000 paths each, on my own seeds:
  - C-switch, b = 0, at w = 0.25, 0.3, 1.0 and 1.25;
  - the held-out worst cell, C-const with b = −0.1 and w = 0.3;
  - C-feedback, b = 0, w = 0.45;
  - Merton with the fixed ratio;
  - exact p = 2 CEV, sampled exactly because 1/(κS) is BES(3): background, partial and full IV on the same price paths at κ = 0.4, and background and full at κ = 0.8;
  - A-switch at (p, κ) = (2, 0.2) and (1.5, 0.4).
- **Not rerun:** the GSADF and v1 comparators, Heston, within-day switching, the p = 1.25 and 1.5 CEV cells, the calibration of the empirical threshold (I applied the published log E = 1.167), and the ROC.

**Reproduced.** Every rate in every band at both horizons agrees within Monte Carlo error, with |z| ≤ 2.3; the few values above 2 are at rates below 2%. Primary band, N = 252/504, mine against published:

| Cell | Mine | Published |
|---|---|---|
| C-switch w = 0.3 | 1.3%/1.7% | 0.7%/1.3% |
| C-switch w = 1.0 | 0.4%/0.4% | 0.2%/0.3% |
| C-switch w = 0.25, outside the band | 17.5%/41.9% | 18.5%/42.4% |
| C-switch w = 1.25, outside the band | 32.6%/51.7% | 33.7%/50.2% |
| C-feedback w = 0.45 | 0.0%/0.2% | 0.0%/0.0% |
| Merton, fixed ratio | 7.0%/13.4% | 7.7%/14.4% |
| CEV p = 2, κ = 0.4, background | 49.7%/85.8% | 47.8%/86.9% |
| CEV p = 2, κ = 0.4, partial | 13.4%/39.4% | 12.0%/38.4% |
| CEV p = 2, κ = 0.4, full | 0.0%/0.1% | 0.2%/0.1% |
| CEV p = 2, κ = 0.8, background | 88.3%/99.6% | 88.0%/99.5% |
| CEV p = 2, κ = 0.8, full | 0.0%/0.0% | 0.1%/0.1% |
| A-switch p = 2, κ = 0.2 | 32.7%/74.6% | 32.5%/73.3% |
| A-switch p = 1.5, κ = 0.4 | 32.4%/72.6% | 31.1%/74.1% |

- **Band M and the sensitivity band** agree likewise. For example, the sensitivity band at w = 0.3 gives 95.1%/99.6% against 94.3%/99.4%.
- **At the published empirical threshold:**
  - pooled C-switch endpoints: 5.8%/6.8% against 5.4%/6.0% held out;
  - the worst in-band cell (C-const, b = −0.1, w = 0.3): 11.3%/12.0% against 12.2%;
  - A-switch power: 48.2%/84.0% against 46.8%/83.1% at (2, 0.2), and 49.0%/82.0% against 47.8%/84.4% at (1.5, 0.4);
  - Merton: 9.8%/18.4%, inside the published 10.5–23% range.

**The Deviations are honest.**
- **Order.** The Design was registered at 06:28. Deviations 1 and 2 (bands and controls, 06:31 and 06:39) came before any code. Deviation 3 (code and implementation, 07:06) and Deviation 4 (07:29) came before any result. Deviation 4's seed change makes Table 2 paired as registered, which a reviewer would otherwise have asked for. Deviation 5 (08:46) records the smoke timing only, and its scores are not tabulated. The results came at 16:36, and `run.py` is unchanged from Deviation 4 to the results.
- **v1 on 500 records per cell** is a stated cost reduction, with its SE.
- **The empirical threshold** uses separate seeds and is labelled empirical. The report itself shows that its 12.2% worst cell makes it no worst-case guarantee.

**The readings are fair.**
- **Validity.** It is shown inside the contract, and the failures outside it go in the predicted directions. A w below the band's lower end is the costly error.
- **Absorption.** Under full tracking it is exact, as claim 042's part 3 states, and my paired exact-CEV arms reproduce it.
- **The stop-rule reading** ("does not trigger on this design") is correctly scoped to this design. Two caveats are worth keeping beside it when D28 is summarized:
  - A-switch's IV reveals the background state exactly and predictably, with a constant variance ratio inside the band. Real IV is noisy and its ratio varies.
  - The stress models show that non-bubble departures also fire: Merton 8–17% and within-day switching 4–8% at nominal α. Claim 042's part 3 says power need not mean a bubble, and the report repeats that.

Verdict: reproduced
