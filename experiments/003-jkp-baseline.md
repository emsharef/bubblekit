---
id: 003
title: "D5 baseline 2: the Jarrow-Kchia-Protter volatility-tail test, implemented from its method paper and run on the paper's stated tail exponents"
status: reproduced
direction: D5
claims: []
code: experiments/003/
---
## Question

Job: **baseline reproduction** (AGENTS.md rule 20; PM notes 2026-10-06-baseline-order and -baselines-texts-arrived).
This verifies an implementation under its authors' own assumptions. It tests no lab hypothesis.

[jarrow2011detect] estimates σ(x) nonparametrically on the visited price range and extrapolates it to infinity. It
then decides whether the JKP integral ∫^∞ x/σ²(x) dx is finite, which by its Theorem 7 decides strictness.

The published output is the dot-com applications: Figs. 1–17 and the verdicts and numbers in Sec. 5.
- Lastminute.com: a conclusive bubble by Method 1 (Sec. 5.1.2), and a bubble by Method 2 with m = 8.26, i.e. α = 4.63.
- eToys: inconclusive by both methods. Method 1's power fits are on the boundary α ≈ 1, and Method 2's m is close to 1.
- Infospace: a bubble, with m = 6.17. The fitted tail is σ(x) ≈ x^{3.58}/127009, and the fixed-α alternative is
  σ(x) ≈ x^{1.8}/5.66.
- Geocities: no bubble, with σ bounded, so the procedure stops at step (iii).

The prices behind these are WRDS tick data. They are licensed, and the four stocks are delisted, so the data is not
free. As the PM's note directs, we therefore **reproduce on paths simulated with the paper's stated parameters, and
say so**. The paper states tail exponents, not a data-generating process: no time unit, sample size, price level or
scale constant usable as one. So this experiment uses the stated exponents and fixes the rest itself (Design).

What this can show: our implementation of the paper's own equations returns the paper's verdicts and exponents when
the truth has the paper's stated tails. It does not reproduce the paper's figures, and this experiment does not claim
it does.

**Hypothesis.** On each simulated case, the modal Method 2 verdict equals the paper's verdict for the corresponding
stock. On the two cases with a stated exponent, Lastminute-like (α = 4.63) and Infospace-like (α = 3.58), the median
estimated α̂ = (m̂ + 1)/2 is within 25% of the stated α.

**What counts against it.** Any case whose modal verdict differs, or a median α̂ outside the band. Each failure is
investigated and recorded under Deviations, and the baseline is labelled by what reproduced.

## Design

**Estimators, from [jarrow2011detect].** Time is normalized to T = 1 with t_i = i/n, as in Sec. 3.
- Florens-Zmirou (5): S_n(x) = Σ 1{|S_i − x| < h} n(ΔS_i)² / Σ 1{|S_i − x| < h}.
  Its 95% interval comes from Theorem 2: σ²(x) ∈ S_n(x)/(1 ± 1.96√(2/N_x)).
- The JKP smooth-kernel estimator (6)–(7): V_n^x / L_n^x, with the paper's kernel
  φ(u) = c^{−1} exp(1/(4u² − 1)) for |u| < 1/2, normalized to integrate to 1.
- The Genon-Catalot–Jacod parametric estimator (Sec. 5.1.2): power form σ(ν, x) = σ_0 x^α.
  - With contrast f_1(G, x) = ln G + x²/G (the paper's GC-J and GC-J1), σ_0² has a closed form given α, and α is
    minimized over [−1, 8].
  - With contrast f_2(G, x) = (x² − G)² (GC-J3), the fit is least squares in σ_0² given α, then minimized over α.

**Method 1 (Sec. 5.1, Theorem 8).** The JKP estimate is evaluated on the grid points below, and the GC-J f_1 fit
gives α̂_1.
- *Bubble, conclusive* if α̂_1 > 1 and the JKP estimate lies at or above the parametric curve at every grid point.
- *No bubble, conclusive* if α̂_1 ≤ 1 and the JKP estimate lies at or below the parametric curve at every grid point.
- Otherwise *inconclusive*.

The paper says "lies above". We read it as holding at every grid point; that reading is ours. We also report a
tolerant version where "above" means above within the Florens-Zmirou 95% band.

**Method 2 (Sec. 5.2.3, steps (i)–(iv)).**
- **(i) Estimation grid.** The bandwidth is h_n = n^{−1/4} × (max S − min S). The paper's Infospace step (ii) uses
  n^{−1/4}; measuring it in units of the observed range is our reading, since the paper gives no unit. The grid
  points are x_k = min S + h_n(2k − 1), for k = 1..M, with M = ⌊n^{1/4}/2⌋, which is spacing 2h_n.
  - We use n = 22^4 = 234,256, which gives M = 11, the paper's Infospace value.
  - Grid points with fewer than 10 observations in their window are dropped.
  - σ̂(x_k) is the JKP smooth-kernel estimate.
- **(ii) Interpolation on D = [min S, max S].** Interpolate f_k = 1/σ̂(x_k)² with the H¹(D) kernel K_{1,τ} of
  Lemma 10, with τ = 6 (Lastminute's choice), by the normal solution (9). Then σ_b = f_b^{−1/2}.
  - The paper's text for f_k is garbled in extraction. We use 1/σ̂², which is consistent with σ_b = 1/√f_b.
  - x is in price units divided by max S. K is evaluated in an overflow-free exponential form.
- **(iii) Is extrapolation needed?** The paper gives no operational rule. Ours: if the least-squares slope of
  log σ_b against log x on [a, max S] is ≤ 0, σ is treated as bounded. The verdict is then *no bubble*, and step (iv)
  is skipped.
- **(iv) Extrapolation.** With n = 2, q^{RP}_{2,m}(x, y) = 4 x_>^{−(m+1)} B(m+1, 2) ₂F₁(−1, m+1; m+3; x_</x_>) from
  Proposition 2. Interpolate the same f_k with q by (9). If the matrix's condition number exceeds 10^{12}, use the
  Tikhonov solution (11) with α_T = 10^{−12}·trace/M.
  - Set σ_m = f_m^{−1/2}, and choose m̂ ≥ 0 minimizing (12): the L² distance between σ_m and σ_b on [a, max S],
    with a = max S − (max S − min S)/3, the paper's choice.
  - The search is a grid m ∈ {0, 0.01, …, 20}, refined by a bounded scalar minimization. If f_m is not positive
    somewhere on [a, max S], that m is infeasible.
  - Then α̂ = (m̂ + 1)/2.
  - Verdict: *bubble* if m̂ > 1, *no bubble* if m̂ ≤ 1. Both are by Proposition 3 with Theorem 7.
  - It is *inconclusive* if |α̂ − 1| ≤ 0.1, i.e. m̂ ∈ [0.8, 1.2]. The paper's eToys verdict is "m close to one"
    with no band, so this band is our choice.

**Simulated cases.** All start at S_0 = 100 on T = 1 with n = 234,256 observations, and are absorbed at 0.

| case | mirrors | σ(x) | source of the exponent |
|---|---|---|---|
| C1 | Infospace | c·x^{3.58} | stated, Sec. 5.2.4 step (iv) |
| C2 | Infospace, fixed α | c·x^{1.8} | stated, Remark 10 |
| C3 | Lastminute.com | c·x^{4.63} | stated, m = 8.26 |
| C4 | eToys | c·x (GBM) | stated "close to linear" |
| C5 | Geocities | constant c | stated "nice bounded function" |

- Scale (our choice, because the paper's constants 1/127009 and 1/5.66 are in its unstated units): C1–C4 have local
  relative volatility σ(S_0)/S_0 = 0.6. C5 has c = 30, so S hits 0 by T with probability about 0.001.
- Expected verdicts, i.e. the paper's: C1–C3 bubble, C4 inconclusive, C5 no bubble.
- Simulation is exact on the observation grid:
  - Power cases with α ≠ 1 use the Bessel-type transform R = S^{1−α}/(c(α − 1)), whose square is BESQ(δ) with
    δ = (2α − 1)/(α − 1). Its transitions are drawn as scaled noncentral χ² (`Generator.noncentral_chisquare`).
  - GBM is drawn as exact lognormal.
  - C5 uses Gaussian increments, absorbed at the first nonpositive observation.
- 200 paths per case. Seeds: `SeedSequence(20261007)`, spawned per case.

**Metrics, per case.**
- Verdict frequencies for Method 2 and Method 1 (both versions).
- Median and interquartile range of m̂ and α̂.
- Median absolute relative error of the JKP and Florens-Zmirou σ̂ against the true σ at the grid points.
- Coverage of Florens-Zmirou's 95% interval.

Monte Carlo SEs:
- Frequencies: binomial.
- Medians: order-statistic intervals.

**Not in scope.** The size and power of this test on the D5 designs. Those are the lab's own measurement, reported
later as such.

**Outputs.**
- `experiments/003/results.json`.
- Regenerate with `uv run python experiments/003/run.py`.

## Deviations

1. **A noiseless diagnostic, added after a 4-path smoke test.** The smoke test showed m̂ scattering widely, so before
   the registered run I checked the implementation on exact inputs. `experiments/003/noiseless_check.py` feeds
   Method 2 the true σ² at 11 grid points:
   - Step (iv) (q^{RP}_{2,m}, (9), (12)) recovers the true m = 2α − 1 to 0.01 when (12) targets the true σ. Its
     interpolant matches a power law to 2e-5. So our q kernel and m search are right.
   - The registered pipeline instead targets σ_b from step (ii). With exact inputs it returns m̂ ≈ 2α − 1.5, for
     every α tested from 1 to 4.63.
   - The cause is that the H¹(D) interpolant with K_{1,6} departs from the true σ by up to 17.5% on [a, max S]. Part
     of [a, max S] lies beyond the last grid point, where that kernel flattens.

   This is the method as specified, under our readings: x scaled by max S, τ in scaled units, and f = 1/σ². It is not
   a coding error. The other τ values the paper lists (1, 3 and 9) give the same offset. With x in raw price units,
   τ = 6 makes K nearly diagonal and m̂ collapses to 0, so the scaled reading is the favourable one. The registered
   run is unchanged.

## Results

**Hypothesis: fails on one case of five.** The modal verdict matches the paper's for the Infospace-like,
Lastminute-like and Geocities-like cases (C1, C2, C3, C5). The median α̂ is within 25% of the stated α for both
stated-exponent cases. The eToys-like case C4 (GBM, α = 1) has a modal path verdict of *no bubble*, at 0.48 against
0.42 bubble and 0.10 inconclusive. The paper's verdict there is *inconclusive*. That is outside the registered rule.

**Label: the JKP volatility-tail test is implemented from [jarrow2011detect]'s equations.**
- On simulated paths with the paper's stated tail exponents, it returns the paper's Method 2 verdict in 4 of 5
  cases.
- The two stated exponents are recovered in median: α̂ = 3.58 for 3.58, and 4.64 for 4.63.
- It does not return "inconclusive" as the modal verdict at α = 1.
- This is **not** a reproduction of Figs. 1–17. The paper's tick data is licensed and its stocks are delisted, so
  this experiment only shows that our implementation behaves as the paper says on the paper's stated tails.

Results: n = 234,256 observations, M = 11 grid points (median), 200 paths per case.

| case | mirrors | true α | paper | Method 2 bubble / no / inconclusive | modal | α̂ median [95% CI] | α̂ IQR |
|---|---|---|---|---|---|---|---|
| C1 | Infospace | 3.58 | bubble | 0.930 / 0.055 / 0.015 | bubble ✓ | 3.58 [3.27, 3.93] | 2.29–4.91 |
| C2 | Infospace, fixed α | 1.8 | bubble | 0.730 / 0.200 / 0.070 | bubble ✓ | 1.62 [1.45, 1.83] | 1.07–2.45 |
| C3 | Lastminute.com | 4.63 | bubble | 0.970 / 0.015 / 0.015 | bubble ✓ | 4.64 [4.15, 4.97] | 3.14–6.19 |
| C4 | eToys | 1 (GBM) | inconclusive | 0.420 / 0.480 / 0.100 | no bubble ✗ | 0.93 [0.81, 1.03] | 0.57–1.51 |
| C5 | Geocities | 0 (bounded) | no bubble | 0.265 / 0.705 / 0.030 | no bubble ✓ | 1.07 [0.73, 1.58] (paths not stopped at step iii) | 0.50–2.57 |

Binomial SEs on the frequencies are at most 0.035. In C5, 91 of the 200 paths stopped at step (iii). No path failed
in step (ii), and none was absorbed. Tikhonov regularization was used on 9 to 21 paths per power case, and on none in
C5.

What the table says about the test, for D5. These are observations from this design, not the D5 measurement:
- **Per-path tail estimates are very noisy.** The C1 interquartile range of α̂ is 2.3–4.9.
- **Many verdicts are false bubbles.** The test calls a bubble on 42% of GBM paths and on 26.5% of bounded-volatility
  paths. Both are true martingales. GBM sits on the boundary α = 1, which the paper itself treats as undecidable.
- **The C4 median is the paper's verdict, but the path mode is not.** The median α̂ in C4, 0.93, does lie in the
  inconclusive band. This aggregate reading is noted after the fact and is not the registered rule.
- **The step-(ii) bias (Deviation 1)** moves m̂ down by about 0.5 on exact inputs. On noisy paths, the median α̂ still
  lands on the truth for C1 and C3, so noise roughly offsets it there. This is an observation, not a correction.

Method 1 and the estimators:

| case | Method 1 strict B / N / I | Method 1 within FZ band B / N / I | GC-J α̂ (f1), median | rel. error JKP / FZ | FZ 95% coverage |
|---|---|---|---|---|---|
| C1 | 0 / 0 / 1.00 | 0.03 / 0 / 0.97 | 3.579 | 0.009 / 0.015 | 0.52 |
| C2 | 0 / 0 / 1.00 | 0.10 / 0 / 0.91 | 1.800 | 0.007 / 0.009 | 0.61 |
| C3 | 0 / 0 / 1.00 | 0.03 / 0 / 0.97 | 4.631 | 0.010 / 0.018 | 0.50 |
| C4 | 0 / 0 / 1.00 | 0.19 / 0.07 / 0.74 | 1.001 | 0.006 / 0.006 | 0.74 |
| C5 | 0 / 0 / 1.00 | 0 / 0.85 / 0.14 | −0.001 | 0.006 / 0.004 | 0.96 |

- **Method 1 under the strict reading is never conclusive here.** When the parametric family is correct, the
  nonparametric estimate straddles the parametric curve. So Method 1's Lastminute.com "conclusive" verdict requires
  the data to lie on one side of the fit, which correctly specified power laws do not produce.
- **The GC-J f1 fit recovers α to three decimals.** That makes it a far sharper tail estimator than Method 2 on these
  designs, though it can only extrapolate its own parametric family.
- **Both nonparametric estimators are accurate to 1–2%.** Florens-Zmirou's Theorem 2 interval undercovers on the
  power cases (0.50–0.74). The bandwidth n^{−1/4} violates its condition nh³ → 0, which the paper itself notes, and
  σ² varies steeply across each window. On bounded σ the interval covers at 0.96.

Regenerate:
- Main run: `uv run python experiments/003/run.py`. It writes `experiments/003/results.json` and prints both tables,
  in about 1.5 minutes on 10 cores.
- Diagnostic: `uv run python experiments/003/noiseless_check.py`.
- Environment: `uv.lock` at the reporting commit.

## Review

Reviewer, 2026-10-06, against main at `b435aad`, which contains the reporting commit `be3d32a`.

**What the verdict means.** "Reproduced" means the experiment's reported results and label reproduce, including its registered hypothesis failing on C4. It is not a reproduction of [jarrow2011detect]'s figures, which the experiment itself disclaims.

**Method.** I wrote my own implementation from the Design and from [jarrow2011detect] §§2–5 in `refs/text/`, without reading `experiments/003/*.py`. It is reviewer scratch work and is not committed; its method and outputs are below.
- **Simulation.** Exact on the grid: the transform R = S^{1−α}/(c(α−1)) is BESQ(δ) with δ = (2α−1)/(α−1), which I derived independently. I draw it as scaled noncentral χ², with exact lognormal steps for GBM and Gaussian steps for C5.
- **Estimators.** Florens-Zmirou (5) with its Theorem 2 interval, the JKP kernel estimator (6)–(7) with the paper's φ, and the GC-J f₁ power fit, profiled over α ∈ [−1, 8].
- **Method 1.** Strict reading as registered. For the FZ-band reading I used: bubble if α̂₁ > 1 and the parametric σ² ≤ the FZ upper bound at every point; no bubble if α̂₁ ≤ 1 and the parametric σ² ≥ the FZ lower bound at every point.
- **Method 2, steps (i)–(iv).**
  - K_{1,6} from Lemma 10, on x/max S.
  - q^{RP}_{2,m} from Proposition 2, using ₂F₁(−1, b; c; z) = 1 − bz/c.
  - The normal solution (9), Tikhonov (11) above condition number 10¹², and the criterion (12) on [a, max S].
  - An m-grid with step 0.01, then a bounded refinement. The verdict bands are as registered.
- **Runs.** 200 paths per case, n = 22⁴, seeds from my own `SeedSequence(31337)`.

**Headline numbers reproduced.** Each row is mine against the experiment's.

| case | Method 2 B / N / I, mine (theirs) | modal | α̂ median [95% CI], mine (theirs) | GC-J α̂ | rel. err JKP / FZ | FZ cover |
|---|---|---|---|---|---|---|
| C1 | 0.935 / 0.040 / 0.025 (0.930 / 0.055 / 0.015) | bubble | 3.38 [3.19, 3.68] (3.58 [3.27, 3.93]) | 3.582 (3.579) | 0.009 / 0.015 (0.009 / 0.015) | 0.53 (0.52) |
| C2 | 0.735 / 0.190 / 0.075 (0.730 / 0.200 / 0.070) | bubble | 1.61 [1.50, 1.75] (1.62 [1.45, 1.83]) | 1.800 (1.800) | 0.007 / 0.009 (same) | 0.63 (0.61) |
| C3 | 0.965 / 0.015 / 0.010 (0.970 / 0.015 / 0.015) | bubble | 4.44 [3.87, 4.96] (4.64 [4.15, 4.97]) | 4.630 (4.631) | 0.010 / 0.020 (0.010 / 0.018) | 0.49 (0.50) |
| C4 | 0.435 / 0.480 / 0.085 (0.420 / 0.480 / 0.100) | no bubble | 0.93 [0.81, 1.10] (0.93 [0.81, 1.03]) | 1.001 (1.001) | 0.006 / 0.006 (same) | 0.75 (0.74) |
| C5 | 0.255 / 0.705 / 0.040 (0.265 / 0.705 / 0.030) | no bubble | 1.10 [0.85, 1.56] (1.07 [0.73, 1.58]) | 0.000 (−0.001) | 0.006 / 0.004 (0.006 / 0.003) | 0.95 (0.96) |

- **Frequencies.** Every Method 2 frequency agrees within |z| < 1 (two-sample binomial).
- **Medians.** The α̂ median intervals overlap in every case. Both stated exponents land inside the registered 25% band in my run: C1 is −5.6% and C3 is −4.1%.
- **Hypothesis outcome.** The registered hypothesis fails on C4 alone, as reported.
- **Other figures.**
  - Method 1 under the strict reading is inconclusive on all 1,000 paths, as reported.
  - Step (iii) stopped 97 of the C5 paths in my run, against 91 in theirs.
  - M = 11 on every path.
  - No path failed in step (ii).

**Two secondary figures differ for implementation reasons. Neither enters the hypothesis or the label.**
- **Method 1 within the FZ band.** I get bubble rates of 0.03, 0.175, 0.015, 0.14 and 0 against their 0.03, 0.095, 0.03, 0.19 and 0. The Design's phrase "above within the Florens-Zmirou 95% band" does not fix the comparison (which curve, which bound), and my reading evidently differs in the C2 and C4 cells. The qualitative statement (rarely conclusive except "no bubble" on C5) holds in both.
- **Tikhonov counts.** I get 0–1 per case against their 9–21. The condition number depends on the units in which q is evaluated: I scaled x by max S; theirs may differ. The interpolant (9) is unit-free, and the agreement of all m̂-based figures shows this does not matter. The Results sentence about Tikhonov counts is implementation-specific.
- **One absorbed path.** One of my 200 C5 paths was absorbed; none of theirs was. With P(hit 0) ≈ 0.001 per path, about 18% of 200-path runs contain one, so this is consistent.

**The Deviations are honest, and Deviation 1 understates the step-(ii) bias outside this design.**
- **The Design was fixed before the run.** The Design text is unchanged from registration (`64b2fce`) to the report.
- **Deviation 1 reproduces.** I fed exact power-law σ at the 11 grid points of the step-(i) grid.
  - Step (iv) aimed at the true σ recovers m = 2α − 1 to 0.01.
  - The registered pipeline aimed at σ_b returns m̂ = 2α − 1 − 0.50 for α ∈ {1, 1.8, 3.58, 4.63}, on price ranges like the simulated ones: [66, 126], [60, 137] and [78, 119].
  - The offset is the same for τ ∈ {1, 3, 6, 9}: −0.503 throughout.
  - My maximum σ_b error on [a, max S] is 1.3–10.8% on those ranges, against their "up to 17.5%". Their domain is not stated, and the error grows with the range.
- **The bias depends on the price range.** I also ran a range spanning a factor of 15, [20, 300], at α = 4.63. There the pipeline offset is −2.58 to −2.59 in m, five times larger, again at every τ. The Deviation says "for every α tested", which is true. But the ≈ −0.5 figure belongs to a max S/min S ratio near 2, not to the method. The paper's stocks are boom-and-bust series over 1999–2005. Its price figures are images and are not legible in the registered text, so I cannot state their ranges, but ratios well above 2 are likely. If so, the interpolation step would shift the paper's own m̂ by more than the 0.5 seen here, in the direction of "no bubble". D5 should treat the step-(ii) bias as range-dependent when it measures this test's size and power.
- **"Garbled" is not the right word for f_k.** The Design calls the paper's f_k "garbled in extraction". The registered text is legible and reads f_k = 1/√σ_est(x_k). That is inconsistent with σ_b = 1/√f_b and with f = 1/σ² in §5.2.2, so it is a typo in the source, not an extraction error. The Design's 1/σ̂² is the consistent reading, so nothing changes.

**Scope.** "What this can show" and the label are accurate. The observations for D5 hold up in my run:
- per-path α̂ is noisy;
- the false-bubble rates are 43.5% on GBM and 25.5% on bounded σ;
- Method 1 under the strict reading is never conclusive with a correctly specified power law;
- GC-J recovers α to three decimals.

These are observations about this design, as the experiment says, not D5's measurement.

Verdict: reproduced
