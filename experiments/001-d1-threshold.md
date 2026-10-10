---
id: 001
title: "D1 threshold: martingale defect of constant-proportion wealth on CEV processes"
status: reproduced
direction: D1
claims: []
code: experiments/001/
---
## Question

Job: **break a conjecture**, and with the same runs **verify** it where it is expected to hold. No D1 claim exists
yet, so this tests the charter's conjecture (ROADMAP D1) directly.

Under Q let dS = S^β dW, S_0 = 1, absorbed at zero (a CEV process), and let V = V^π be the wealth of the
constant-proportion strategy with fraction π > 0 in S and the rest in cash at rate 0, V_0 = 1. Then
dV = π V σ(S)/S dW with σ(x) = x^β, so V = Z in the notation of [mijatovic2010martingale] (7) with b(x) = πσ(x)/x.
The quantity measured is the martingale defect D(β, π, T) = 1 − E_Q[V_T]/V_0.

**Hypothesis H0 (from the PM's note and the ROADMAP D1 question).** D > 0 exactly when β > 1 and π > 1/2. (By the
JKP integral, [mijatovic2010martingale] Cor. 4.3 (AX-03), S is a strict local martingale exactly when β > 1.)

**What counts against H0.** On the H0 grid below: a defect clearly above zero (decision rule below) in a cell with
β ≤ 1 or π ≤ 1/2; or a defect indistinguishable from zero in a cell with β > 1 and π > 1/2.

**Alternative H1, recorded before running.** Applying the two-endpoint test of [mijatovic2010martingale] Thm 2.1
(AX-01) by hand to b(x) = πx^{β−1} suggests the zero boundary also matters. For β < 1, S hits 0 under Q, and the
left endpoint 0 is bad (s(x) = x, and x·b²/σ² = π²/x is not integrable near 0). The auxiliary diffusion exits at 0
when π < 1/2. So H1 predicts D > 0 exactly when (β > 1 and π > 1/2) or (β < 1 and π < 1/2). This is an expectation
that fixes what the runs can distinguish, not a claim. It differs from H0 only in the cells β = 0.5, π < 1/2.

## Design

**Exit convention (named: the AX-01 absorption convention).** S is absorbed at 0 at τ_0. V is the process Z of
[mijatovic2010martingale] (7) and AX-01: before the exit time it is the stochastic exponential. After a finite exit it
keeps its exit value when ∫_0^{τ_0} b²(S_u) du < ∞, and it is set to 0 when that integral is infinite. In trading
terms, the position is closed at τ_0 and the wealth carried forward is the left limit V_{τ_0−}. The ledger entries
AX-01..03 are already merged on main (46a64f4), so the Design uses the ledger's convention from the start.

What the convention does here (an argument, not a computation). On {τ_0 < ∞},
∫_0^{τ_0} b²(S_u) du = π² ⟨log S⟩_{τ_0}. Write log S = N − ½⟨N⟩ with N = ∫ σ(S)/S dW. If ⟨N⟩_{τ_0} were finite,
N would converge and so would log S, but log S → −∞. So the integral is infinite, and V = 0 after τ_0 for every
π > 0. Under Q, S does not exit at ∞ (AX-03 setting). It exits at 0 only when β < 1: s(x) = x, and v(0) < ∞ iff
∫_0 x^{1−2β} dx < ∞ (AX-02). Hence, under this convention,
E_Q[V_T] = E_Q[V_T ; ζ > T], where ζ is the exit time of S from (0,∞).

**Parameter grid.**
- β ∈ {0.5, 1, 1.5, 2}.
- T ∈ {1, 5}.
- S_0 = V_0 = 1.
- H0 grid: π ∈ {0.25, 0.4, 0.5, 0.6, 0.75, 1, 1.5, 2}.
- Threshold points: π ∈ {0.45, 0.49, 0.499, 0.501, 0.51, 0.55}. These show how D behaves as π → 1/2 from each
  side. They are reported, but they are not used to judge H0: near the threshold, a true defect can lie below
  numerical resolution by continuity.

**Method P (primary): backward equation under Q, no change of measure.** For a truncation 0 < ε < 1 < M, let
τ = inf{t : S_t ∉ (ε, M)}. Up to τ, V is the stochastic exponential of a bounded integrand, so it is a true
martingale there. By Feynman–Kac for the Markov pair (S, V), E_x[V_t ; τ > t]/V_0 = u(t, x), where u solves

    u_t = ½σ²(x) u_xx + πσ²(x)/x · u_x  on (ε, M),   u(0,·) = 1,   u(t, ε) = u(t, M) = 0.

The source of the drift term is d⟨S, V⟩ = π V σ²(S)/S dt. Now let ε ↓ 0 and M ↑ ∞. Then τ ↑ ζ and V ≥ 0, so
u(T, 1) increases to E_Q[V_T ; ζ > T] = E_Q[V_T] by monotone convergence (the convention paragraph above). Hence
D_P(ε, M) := 1 − u(T, 1) is an upper bound on D for every truncation, and it decreases to D.

Discretization:
- Coordinate y = log x. With a(y) = σ²(e^y)e^{−2y} = e^{(2β−2)y}, the equation becomes
  u_t = a(y)[½u_yy + (π − ½)u_y].
- Space: uniform grid in y with central differences.
- Time: BDF2 started with one implicit Euler step, on a uniform time grid. u is recorded at t = 1 and t = 5 from a
  single run to T = 5.
- To keep the scheme finite when a spans hundreds of orders of magnitude, each row is divided by a. For example,
  BDF2 solves (3w − 2Δt L_h)u^{n+1} = w(4u^n − u^{n−1}) with w = 1/a = e^{−(2β−2)y}. Here L_h is the
  constant-coefficient operator ½D² + (π − ½)D. Where w underflows to 0, the row is the quasi-static equation
  L_h u = 0, which is the correct limit.
- The linear systems are solved by a sparse LU factorized once per run (`scipy.sparse.linalg.splu`).

Truncation ladder, with k = 1..8:
- β ∈ {1.5, 2}: ε = 10^{−6} fixed and M_k = 10^{2^k}, so the largest is M = 10^{256}. One extra run at k = 8 uses
  ε = 10^{−12} to check the lower cut.
- β = 0.5: M = 10^6 fixed and ε_k = 10^{−2^k}. One extra run at k = 8 uses M = 10^{12} to check the upper cut.
- β = 1: ε_k = 1/M_k and M_k = 10^{2^k}.

Grids:
- G2 (h = 0.01, Δt = 0.002): runs the whole ladder.
- G3 (h = 0.005, Δt = 0.001): runs at k = 8 only.

Reported quantities and error estimate:
- Reported value: D_P = D_P(k = 8, G3).
- Discretization error: e_disc = |D_P(8, G3) − D_P(8, G2)|.
- Truncation increment: e_trunc = |D_P(8, G2) − D_P(7, G2)| + |extra-cut run − D_P(8, G2)|.
- Total error: e = e_disc + e_trunc.
- Method P counts as converged in a cell when e_trunc ≤ 10^{−6}.

Expected weak spot, stated in advance: when the auxiliary diffusion has a logarithmic scale function at the cut
boundary (π = 1/2, and π near 1/2 on the non-exit side), the truncation leak decays only like 1/log M (or 1/log(1/ε)).
Such cells are reported as "P: upper bound only", with the ladder shown.

**Method X (cross-check): exit probability of the auxiliary diffusion, exact.** By [mijatovic2010martingale]
Lemma 6.3, dP̃/dQ = Z on F_{t∧τ_n}, where P̃ is the law of the auxiliary diffusion
dS̃ = πσ²(S̃)/S̃ dt + σ(S̃)dW̃ (MU (15), absorbed at exit). Letting n → ∞ gives E_Q[Z_T ; ζ > T] = P̃(ζ̃ > T).
With the convention paragraph, this gives D = P̃(ζ̃ ≤ T).

For β = 1 the auxiliary diffusion is a geometric Brownian motion, which does not exit, so D_X = 0.

For β ≠ 1, set R = S̃^{1−β}/|1−β|. Itô's formula gives dR = (δ−1)/(2R) dt + dB for a Brownian motion B, with
δ = (1 − 2β + 2π)/(1 − β). This is [karatzas2015distribution] (6.6), started at ξ = S_0^{1−β}/|1−β|. R → 0
corresponds to S̃ → ∞ when β > 1 and to S̃ → 0 when β < 1, and R does not explode. So:
- if δ < 2, then by [karatzas2015distribution] (6.10), D_X = 1 − H_ν(ξ²/(2T)) = Γ_upper-regularized(ν, ξ²/(2T)),
  with ν = 1 − δ/2;
- if δ ≥ 2, the scale density r^{1−δ} gives s(0+) = −∞ and v(∞) = ∞ (AX-02), so R does not exit and D_X = 0.

Here ν = (2π − 1)/(2(β − 1)) for β > 1, and ν = (1 − 2π)/(2(1 − β)) for β < 1. The value is computed with
`scipy.special.gammaincc`. Method X relies on the change of measure and the Bessel-type hitting law. Method P relies
on neither: it uses only Feynman–Kac on bounded domains and monotone convergence. Their agreement is therefore
evidence that neither has an error. (A naive Monte Carlo estimate of E_Q[V_T] misses the tail mass that is the
defect, so it is not run.)

**Decision rules (fixed now).**
- A cell is *clearly positive* if D_P − e > 10^{−5}.
- A cell is *indistinguishable from zero* if D_P − e ≤ 10^{−5}, unless P is not converged, in which case it is
  "upper bound only".
- Methods P and X *agree* in a converged cell if |D_P − D_X| ≤ 2e + 10^{−6}. A disagreement in a converged cell is
  reported as a failure, investigated, and recorded under Deviations before any rerun.
- Verdict on H0: against if any H0-grid cell meets the "against" condition of the Question on method P where P is
  converged, and on method X where P is not.
- The same rule decides H1.

**Seeds and precision.** Both methods are deterministic, so there are no seeds. The numerical precision target is an
absolute error of 10^{−6} on D where P converges. Stopping rule: the grid and ladder above, run once.

**Outputs.**
- `experiments/001/results_ladder.csv`: every run.
- `experiments/001/summary.csv`: one row per (β, π, T) with D_P, e_disc, e_trunc, D_X and verdicts.
- Regenerate both with `uv run python experiments/001/run.py`.

## Deviations

The grid, truncation ladders, discretization grids, both methods and the decision rules ran as registered. Three
reporting changes were made after the first run. None changes a number.

1. `run.py`'s table formatter printed numpy booleans as `True`. It was fixed, and the run was repeated. The repeat
   wrote a byte-identical `summary.csv`.
2. A diagnostic was added after seeing the near-threshold ladders: D_P(k)·2^k on the G2 ladder for
   π ∈ {0.499, 0.5, 0.501}. It is computed from the registered runs, and it shows the 1/log M leak the Design
   predicted. It is printed by `run.py` and used only to describe the cells reported as "upper bound only".
3. The registered rule labels a cell "positive" when D_P − e > 10^{−5}, even where method P has not converged. At six
   threshold cells (π ∈ {0.49, 0.499} for β = 0.5; π ∈ {0.501, 0.51} for β ∈ {1.5, 2}), this label comes from an
   unconverged upper bound. The tables below show those cells with the method X value beside them. As registered,
   their verdict reading is method X's. They are threshold points, so they are not used for H0.

## Results

**Verdict on H0: against.** Of the 64 H0-grid cells, H0 fails in four: β = 0.5 with π ∈ {0.25, 0.4}, at both T.
There the defect is clearly positive, and P and X agree:

| β | π | T | D_P | D_X | D_P − D_X |
|---|---|---|---|---|---|
| 0.5 | 0.25 | 1 | 0.045500 | 0.045500 | −1.5e-7 |
| 0.5 | 0.25 | 5 | 0.371093 | 0.371093 | −3.6e-8 |
| 0.5 | 0.4 | 1 | 0.012987 | 0.012987 | −2.3e-8 |
| 0.5 | 0.4 | 5 | 0.147663 | 0.147663 | −3.3e-8 |

S is a true martingale at β = 0.5 (AX-03), and S hits 0 under Q. Under the AX-01 absorption convention, V^π is
therefore not a martingale for these π < 1/2. The source is the zero boundary, not the bubble.

**Verdict on H1 (registered alternative): no cell against.** D > 0 exactly in the cells (β > 1, π > 1/2) and
(β < 1, π < 1/2). Every other H0-grid cell reads zero to within 10^{−10} on method P, or is an upper bound at π = 1/2.

**P against X.** The two methods agree in every cell where P converged (the agreement rule held throughout). The
largest |D_P − D_X| over converged cells is 2.5e-6, and the largest discretization estimate e_disc is 7.4e-6. No
disagreements.

Method P values, reported as D_P on G3 at k = 8. Notation in the tables:
- "0 (≤x)": converged, with |D_P| + e ≤ x.
- "≤x (X: y)": P not converged, so x is an upper bound and y is method X's value.
- Entries with "X" beside a number: unconverged cells, where X decides.

T = 1, H0 grid

| β \ π | 0.25 | 0.4 | 0.5 | 0.6 | 0.75 | 1 | 1.5 | 2 |
|---|---|---|---|---|---|---|---|---|
| 0.5 | 0.0455 | 0.0130 | ≤8.3e-05 (X: 0) | 0 (≤1e-11) | 0 (≤9e-12) | 0 (≤1e-12) | 0 (≤5e-12) | 0 (≤5e-12) |
| 1 | 0 (≤1e-12) | 0 (≤3e-12) | 0 (≤6e-12) | 0 (≤3e-12) | 0 (≤2e-12) | 0 (≤7e-12) | 0 (≤4e-12) | 0 (≤6e-12) |
| 1.5 | 0 (≤8e-12) | 0 (≤1e-11) | ≤8.3e-05 (X: 0) | 0.0130 | 0.0455 | 0.1353 | 0.4060 | 0.6767 |
| 2 | 0 (≤1e-11) | 0 (≤2e-11) | ≤4.8e-04 (X: 0) | 0.0586 | 0.1535 | 0.3173 | 0.6065 | 0.8013 |

T = 5, H0 grid

| β \ π | 0.25 | 0.4 | 0.5 | 0.6 | 0.75 | 1 | 1.5 | 2 |
|---|---|---|---|---|---|---|---|---|
| 0.5 | 0.3711 | 0.1477 | ≤1.2e-03 (X: 0) | 0 (≤7e-11) | 0 (≤3e-11) | 0 (≤2e-12) | 0 (≤1e-11) | 0 (≤9e-12) |
| 1 | 0 (≤2e-12) | 0 (≤2e-11) | 0 (≤3e-11) | 0 (≤2e-11) | 0 (≤1e-11) | 0 (≤3e-11) | 0 (≤2e-11) | 0 (≤3e-11) |
| 1.5 | 0 (≤3e-11) | 0 (≤7e-11) | ≤1.2e-03 (X: 0) | 0.1477 | 0.3711 | 0.6703 | 0.9384 | 0.9921 |
| 2 | 0 (≤3e-11) | 0 (≤7e-11) | ≤1.5e-03 (X: 0) | 0.1724 | 0.3917 | 0.6547 | 0.9048 | 0.9776 |

T = 1, threshold points

| β \ π | 0.45 | 0.49 | 0.499 | 0.501 | 0.51 | 0.55 |
|---|---|---|---|---|---|---|
| 0.5 | 0.0057 | 0.0010 (X 0.0010) | 0.0001 (X: 9.81e-05) | ≤4.4e-05 (X: 0) | ≤7.7e-09 (X: 0) | 0 (≤2e-12) |
| 1 | 0 (≤4e-12) | 0 (≤6e-12) | 0 (≤3e-12) | 0 (≤6e-12) | 0 (≤3e-12) | 0 (≤4e-12) |
| 1.5 | 0 (≤2e-12) | ≤7.7e-09 (X: 0) | ≤4.4e-05 (X: 0) | 0.0001 (X: 9.81e-05) | 0.0010 (X 0.0010) | 0.0057 |
| 2 | 0 (≤6e-12) | ≤4.3e-08 (X: 0) | ≤2.5e-04 (X: 0) | 0.0008 (X: 5.60e-04) | 0.0056 (X 0.0056) | 0.0287 |

T = 5, threshold points

| β \ π | 0.45 | 0.49 | 0.499 | 0.501 | 0.51 | 0.55 |
|---|---|---|---|---|---|---|
| 0.5 | 0.0724 | 0.0141 (X 0.0141) | 0.0020 (X 0.0014) | ≤6.2e-04 (X: 0) | ≤1.1e-07 (X: 0) | 0 (≤2e-11) |
| 1 | 0 (≤2e-11) | 0 (≤3e-11) | 0 (≤1e-11) | 0 (≤3e-11) | 0 (≤1e-11) | 0 (≤2e-11) |
| 1.5 | 0 (≤2e-11) | ≤1.1e-07 (X: 0) | ≤6.2e-04 (X: 0) | 0.0020 (X 0.0014) | 0.0141 (X 0.0141) | 0.0724 |
| 2 | 0 (≤2e-11) | ≤1.4e-07 (X: 0) | ≤8.1e-04 (X: 0) | 0.0026 (X 0.0018) | 0.0181 (X 0.0181) | 0.0887 |

**Approach to the threshold.**
- For β > 1, D falls continuously to 0 as π ↓ 1/2, with no jump. Method X gives D ≈ ν·E₁(ξ²/(2T)) for small
  ν = (2π − 1)/(2(β − 1)), which is linear in π − 1/2. The ROADMAP's "blow-up as π ↓ 1/2" is the Feller integral
  v(∞), not the defect.
- For β = 0.5, the mirror image holds as π ↑ 1/2.
- At π = 1/2, method P cannot separate a zero defect from a slowly closing truncation. D_P(k)·2^k settles to a
  constant along the ladder: 0.0213 (β ∈ {0.5, 1.5}, T = 1), 0.305 (β ∈ {0.5, 1.5}, T = 5), 0.122 and 0.396
  (β = 2). So the upper bound decays like 1/log M, or 1/log(1/ε), toward 0, as the Design predicted. At π = 0.501
  the scaled values grow, so the bound is heading to a positive limit. At π = 0.499 (β > 1) they fall, so the bound
  is heading to zero. These cells are decided by X, which gives zero at π = 1/2 for every β.

**Observation, not a claim.** The β = 0.5 rows equal the β = 1.5 rows with π replaced by 1 − π, to every printed
digit and in both methods. In method X the two cases have the same ν and ξ, so the auxiliary diffusions' exit times
have the same law. Whether this is a general duality between the zero boundary and the bubble boundary is math's
question.

**Sanity value.** β = 2, π = 1 is the inverse three-dimensional Bessel process. Its defect at T = 1, S_0 = 1 is
2Φ(−1) = 0.317311, and method P gives 0.317310.

**What this does not show.** These are numerical results for the CEV family at S_0 = 1 and T ∈ {1, 5}. They are
evidence about these cases and prove nothing in general (AGENTS.md rule 4). The four counter-cells also depend on the
AX-01 absorption convention. If the position were instead liquidated at any level ε > 0, the stopped wealth would be a
true martingale. Method X's derivation (MU Lemma 6.3 plus KR (6.10)) is an argument written for this experiment, not
a reviewed claim.

Regenerate:
- Command: `uv run python experiments/001/run.py`. It prints all tables above and writes
  `experiments/001/results_ladder.csv` (every run) and `experiments/001/summary.csv`.
- Run time: about 3 minutes on 10 cores.
- Environment: `uv.lock` at the reporting commit. The methods are deterministic, so there are no seeds.

## Review

Reviewer, 2026-10-06, against main at `387c185`, which contains the reporting commit `34e8625`. I wrote my own script without reading `experiments/001/*.py`. It is reviewer scratch work and is not committed; its methods and outputs are below. Everything here is numerical evidence about these cells, not proof.

**Headline numbers reproduced.**
- **R1, closed form re-derived by hand.** Under R = X^{1−β}/|1−β|, the auxiliary diffusion dX = πX^{2β−1}dt + X^β dW becomes dR = (δ−1)/(2R)dt + dB with δ = (1−2β+2π)/(1−β). I obtained the Design's δ, ν and ξ independently. For δ < 2, D = P(G ≥ ξ²/(2T)) with G ~ Gamma(ν), which is the hitting law in [karatzas2015distribution] (6.10).
  - Against all 112 rows of `summary.csv`, this matches D_X to 1.1e-16. It matches D_P to 2.5e-6 in the 82 cells where P converged.
  - In none of the 30 unconverged cells does D_P fall below the closed form, so every "≤" entry is a valid upper bound.
  - On the H0 grid it disagrees with H0 in exactly the four reported cells, β = 0.5 with π ∈ {0.25, 0.4} at both T. It disagrees with H1 in none.
  - Sanity value β = 2, π = 1, T = 1: 0.3173105 = 2Φ(−1).
  - The β = 0.5 ↔ β = 1.5, π ↔ 1 − π symmetry holds exactly in the closed form (same ν and same ξ at S₀ = 1), to 1e-16.
- **R2, different numerics for the same quantity.** I used implicit finite differences for the survival probability of R in the variable r on (0, L), with Dirichlet 0 at r = 0. The Design's method P uses log x and BDF2.
  - Ten cells, including all four counter-cells, converge toward the reported values. Where ν ≥ 1/4 they agree to ≤ 2e-5 on the fine grid. For example, β = 0.5, π = 0.25: 0.045504 against 0.045500; β = 2, π = 2, T = 1: 0.801222 against 0.801254.
  - Where ν is small, the solution behaves like r^{2ν} at 0 and a uniform grid converges slowly. At β = 0.5, π = 0.4 (ν = 0.1) the sequence 0.013992, 0.013544, 0.013302 extrapolates (Aitken) to 0.01302, against 0.012987. At β = 2, π = 0.6 (ν = 0.05) it extrapolates to 0.0607, against 0.0586, and is still moving toward it.
- **R3, no change of measure at all.** I ran an Euler Monte Carlo of the wealth SDE itself under Q for β = 0.5, with dS = √S dW killed at 0 and 50 000 paths:
  - π = 0.25: 0.0468 ± 0.0020 (T = 1) and 0.3736 ± 0.0052 (T = 5), against 0.0455 and 0.3711.
  - π = 0.4, T = 1: the estimate falls with the step from 0.0192 ± 0.0024 to 0.0155 ± 0.0024 at 128 000 steps, which is within 1σ of 0.0130.
  - The excess at coarse steps has the expected sign: killing paths at the grid overstates the defect when ν is small.
  - This route shares nothing with methods P and X except the model. The four counter-cells are therefore confirmed without the measure change of [mijatovic2010martingale] Lemma 6.3.

**Deviations are honest.**
- **The Design was fixed before the run.** The Question and Design sections are byte-identical between the registration commit `9d35deb` and the reporting commit `34e8625`. The diff touches only `status`, Deviations and Results.
- **Deviation 1 checks out.** I re-ran `uv run python experiments/001/run.py` unmodified (about 4 minutes). It regenerated `summary.csv` and `results_ladder.csv` byte-for-byte and printed "P/X disagreements in converged cells: none".
- **Deviation 3 checks out.** The CSV has exactly the listed cells labelled positive by an unconverged bound. One wording nit: "six threshold cells" are six (β, π) pairs, each at both T, so 12 table entries. The verdict reading is unaffected: method X is positive in all of them, and they are off the H0 grid.
- **The summary sentences check out.**
  - Max |D_P − D_X| over converged cells is 2.47e-6.
  - Max e_disc is 7.42e-6.
  - Max |D_P| + e_disc over the H0-grid zero cells is 7.0e-11, which is within the stated 10⁻¹⁰.
  - The small-ν approximation D ≈ ν E₁(ξ²/(2T)) also checks: β = 1.5, π = 0.501 gives 9.78e-5, against X = 9.81e-5.

**Scope.**
- **"What this does not show" is accurate.** It covers CEV at S₀ = 1 and T ∈ {1, 5} under the AX-01 absorption convention, and π = 1/2 is decided by method X, not by P.
- **Agreement with claim 001.** The counter-cells are exactly what claim 001 (red-passed) predicts. At β = 0.5, I₀ = ∫₀ x^{1−2β} dx < ∞ and I∞ = ∞, so wealth is strict precisely for π < 1/2. The experiment's H1 is that claim's criterion. The experiment adds a measured defect, not a new condition.
- **Method X is not a separate check of claim 001.** It goes through the same Girsanov route and is not a reviewed claim, as the write-up says. R3 above is the route that does not depend on it.

Verdict: reproduced
