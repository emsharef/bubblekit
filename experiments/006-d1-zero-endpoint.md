---
id: 006
title: "D1 zero endpoint: martingale defect of constant-proportion wealth for sigma = 1 and sigma = 1 + x^2"
status: reproduced
direction: D1
claims: [1]
code: experiments/006/
---
## Question

Job: **break a conjecture**, and **verify a claim under its assumptions**. Math asked for this in
`board/inbox/analyst/2026-10-06-d1-zero-endpoint-candidate.md`. The test target stays the charter's original
conjecture (ROADMAP D1, H0 of experiment 001). The approved claim 001's criterion (1) is the alternative. It is not
used as a premise: both methods below compute the defect without it.

Setup, as in experiment 001:
- dS = σ(S)dW under Q, with S_0 = 1, absorbed at 0.
- Constant proportion π, so V = Z with b(x) = πσ(x)/x and AX-01's exit convention.
- The defect is D = 1 − E_Q[V_T]/V_0, with T ∈ {1, 5}.
- I₀ = ∫₀¹ x/σ²(x) dx and I∞ = ∫₁^∞ x/σ²(x) dx.

Cases:
- **Case A: σ ≡ 1.** This is math's analytic candidate counterexample, with I₀ = 1/2 and I∞ = ∞. S is a true
  martingale that hits 0.
  - π ∈ {0.1, 0.25, 0.4, 0.45, 0.49, 0.5, 0.51, 0.55, 0.6, 0.75, 1, 1.5, 2}.
- **Case B: σ(x) = 1 + x².** Here I₀ < ∞ and I∞ < ∞, so S is strict and can hit 0. This case needs both endpoints:
  a method that sees only one of them predicts the wrong sign on one side of π = 1/2.
  - π ∈ {0.25, 0.4, 0.5, 0.6, 0.75, 1}.
- The σ(x) = √x case is experiment 001's β = 0.5 row, which is already reported and reproduced. It is cited, not
  rerun.

**H0 (charter):** D > 0 exactly when S is strict and π > 1/2.
- Case A: D = 0 for every π.
- Case B: D > 0 exactly for π > 1/2.

**H1 (claim 001, (1)):** D > 0 exactly when (0 < π < 1/2 and I₀ < ∞) or (π > 1/2 and I∞ < ∞).
- Case A: D > 0 exactly for π < 1/2.
- Case B: D > 0 for every π ≠ 1/2.

**What counts against each hypothesis:** a clearly positive defect where it predicts 0, or one indistinguishable from
zero where it predicts D > 0. The decision rules are experiment 001's, reused unchanged.

## Design

**Method P (primary), as in experiment 001.**
- Backward equation under Q on a truncation (ε, M), with Dirichlet 0 at both cuts. There is no change of measure,
  so it sees mass leaving through either endpoint.
- Coordinates y = log x, with a(y) = σ²(e^y)e^{−2y}.
  - Case A: a(y) = e^{−2y}.
  - Case B: a(y) = 4cosh²y, computed in log form so it neither overflows nor underflows.
- Discretization: BDF2, with rows divided by a.
- Truncation ladder, k = 1..8:
  - Case A: ε_k = 10^{−2^k}, with M = 10^6. One extra run at k = 8 uses M = 10^{12}.
  - Case B: ε_k = 10^{−2^k} and M_k = 10^{2^k}.
- Grids: G2 (h = 0.01, Δt = 0.002) runs the whole ladder; G3 (h = 0.005, Δt = 0.001) runs at k = 8 only.
- The error measures e_disc and e_trunc and the convergence criterion are those of experiment 001.
- Implementation: experiment 001's `pde_defect` is generalized to a supplied log a(y), in `experiments/006/`.
  Experiment 001's committed code is not modified.

**Method X (cross-check, Case A only).** This is experiment 001's `exact_defect` with β = 0:
- δ = 1 + 2π and ν = (1 − 2π)/2;
- ξ = S_0 = 1;
- D_X = Γ_upper-regularized(ν, 1/(2T)) for π < 1/2, and 0 for π ≥ 1/2.

The derivation is experiment 001's: [mijatovic2010martingale] Lemma 6.3 and [karatzas2015distribution] (6.10).
Case B has no closed form, so it is checked by method P only. Its convergence is reported as such.

**Decision rules.** Experiment 001's, unchanged:
- *clearly positive:* D_P − e > 10^{−5};
- *zero:* converged and D_P − e ≤ 10^{−5};
- *upper bound only:* otherwise;
- P and X *agree* if |D_P − D_X| ≤ 2e + 10^{−6}.

**Resources.** A single process, so that experiment 005 (running) and Lean CI keep their cores. Deterministic, so
there are no seeds.

**Outputs.**
- `experiments/006/summary.csv` and `experiments/006/results_ladder.csv`.
- Regenerate with `uv run python experiments/006/run.py`.

## Deviations

1. **The literal "clearly positive" rule fires on one unconverged cell.** This is the same issue as experiment 001,
   Deviation 3. In Case B at π = 1/2, T = 5, method P gives D_P = 0.0163 with e_trunc = 0.0163. The registered rule's
   literal reading is "positive", but P has not converged, so D_P is only an upper bound.
   - The ladder diagnostic settles the cell: D_P(k)·2^k levels off at 4.18, so the bound decays like 1/log M toward 0.
     That diagnostic is experiment 001's, applied after the result.
   - The cell is reported as "upper bound only".
   - It does not bear on either hypothesis, because H0 and H1 both predict D = 0 at π = 1/2.
2. **No other change.** The run was single-process, as registered. It shared the machine with experiment 005, which
   affected only wall time.

## Results

**H0 (the charter's criterion) fails in both cases. H1 (claim 001's criterion (1)) holds in every decided cell.**
No P/X disagreement occurred in any converged cell.

**Case A, σ ≡ 1** (S is a true martingale and hits 0).
- The defect is clearly positive for every π < 1/2 and zero for every π ≥ 0.55.
- Math's candidate counterexample, π = 1/4, gives:

  | T | D_P | D_X (exact) |
  |---|---|---|
  | 1 | 0.153513 | 0.153514 |
  | 5 | 0.391661 | 0.391661 |

- H0 predicts D = 0 for every π here. So the cells π ∈ {0.1, 0.25, 0.4, 0.45} at both T, where P and X agree and
  are converged, are against H0. The cells at π = 0.49 are positive under X (0.0056 and 0.0181) and on P's
  unconverged bound.

| π | 0.1 | 0.25 | 0.4 | 0.45 | 0.49 | 0.5 | 0.51 | ≥ 0.55 |
|---|---|---|---|---|---|---|---|---|
| D, T = 1 | 0.2520 | 0.1535 | 0.0586 | 0.0287 | 0.0056 (X) | 0 (X; P ≤ 4.8e-4) | 0 (X; P ≤ 1.5e-5) | 0 (≤ 1e-10) |
| D, T = 5 | 0.5638 | 0.3917 | 0.1724 | 0.0887 | 0.0181 (X) | 0 (X; P ≤ 1.5e-3) | 0 (X; P ≤ 5e-5) | 0 (≤ 1e-10) |

**Case B, σ = 1 + x²** (I₀ < ∞ and I∞ < ∞, so S is strict and can hit 0). Method P only, as registered.
- The defect is clearly positive on both sides of 1/2, at every π tested other than 1/2.
- H0 predicts D = 0 at π ∈ {0.25, 0.4}, so those cells are against H0.
- H1 predicts D > 0 at every π ≠ 1/2, and that holds.
- A method that saw only exit at ∞ would have missed the π < 1/2 side.
- π = 1/2 is an upper bound decaying like 1/log M (Deviation 1).

| π | 0.25 | 0.4 | 0.5 | 0.6 | 0.75 | 1 |
|---|---|---|---|---|---|---|
| D, T = 1 | 0.417370 | 0.171329 | ≤ 0.0029 (bound → 0) | 0.171329 | 0.417370 | 0.732149 |
| D, T = 5 | 0.952175 | 0.656282 | ≤ 0.0163 (bound → 0) | 0.656282 | 0.952175 | 0.999336 |

**Observation, not a claim.** In Case B, D(π) = D(1 − π) to all printed digits. Note that σ(1/x) = σ(x)/x², and
experiment 001 saw the analogous β ↔ 2 − β, π ↔ 1 − π coincidence. Whether this reflects an inversion duality between
the zero and the infinite endpoint is math's question.

These are numerical results for the two volatility functions, at S_0 = 1 and T ∈ {1, 5}. They are evidence about
these cases, not a proof (rule 4). They depend on AX-01's exit convention, as claim 001 does.

Regenerate:
- Command: `uv run python experiments/006/run.py`. It writes `experiments/006/summary.csv` (with the scaled ladders)
  and `experiments/006/results_ladder.csv`.
- It is single-process and deterministic.
- Environment: `uv.lock` at the reporting commit.

## Review

Reviewer, 2026-10-06, against main at `16974d0`, which contains the reporting commit `6573294`. I wrote my own script without reading `experiments/006/run.py`. It is reviewer scratch work and is not committed; its method and outputs are below. These are numerical results about these cases, not proof.

**Method.** I used a different route from the experiment's method P throughout.
- **Representation.** D = P̃(the auxiliary diffusion exits by T), from [mijatovic2010martingale] Lemma 6.3. This holds here because both endpoints are bad for every 0 < π (claim 001), and wealth is 0 after S exits at 0, as shown in claim 001's review.
- **Case A.** The auxiliary process is dY = (π/Y)dt + dW, a Bessel process of dimension 1 + 2π. I re-derived the closed form D = Γ_upper-regularized((1−2π)/2, 1/(2T)) for π < 1/2 and 0 otherwise. I also ran a finite-volume scheme in x as a check of the scheme.
- **Case B.** The Lamperti transform y = arctan(Ỹ) maps the auxiliary process onto the bounded interval (0, π/2), with drift μ(y) = 2π/sin 2y − tan y.
  - The exits are at y = 0 (Bessel dimension 1 + 2π, attainable iff π < 1/2) and at y = π/2 (dimension 3 − 2π, attainable iff π > 1/2).
  - The scheme is finite volumes in conservative form (1/(2p))(p u′)′ with p = tan^{2π}y·cos²y, using exact scale increments and speed masses per cell, on a grid graded toward both ends. Time stepping is implicit Euler, extrapolated in Δt.
  - This uses no truncation ladder, so π = 1/2 comes out as exactly 0: neither end is attainable.

**Headline numbers reproduced.**
- **Case A.** My closed form gives the experiment's table to every printed digit: 0.2520, 0.1535, 0.0586, 0.0287 and 0.0056 at T = 1, and 0.5638, 0.3917, 0.1724, 0.0887 and 0.0181 at T = 5. At π = 1/4 it gives 0.153514 and 0.391661. That matches the experiment and my own claim-001 review (E Z₁ = 0.84649). It is zero for π ≥ 1/2. My finite-volume check converges to the closed form (0.153501 at π = 1/4, against 0.153514).
- **Case B.** The scheme is grid-stable from N = 800 to 12,800. After Richardson extrapolation in Δt it agrees with the experiment's D_P to about 1e-6, inside their e_disc:

  | π | T | mine | experiment |
  |---|---|---|---|
  | 1 | 1 | 0.732150 | 0.732149 |
  | 0.25 | 1 | 0.417371 | 0.417370 |
  | 0.25 | 5 | 0.952175 | 0.952175 |
  | 0.4 | 5 | 0.656282 | 0.656282 |

  The unextrapolated values agree to 3–8e-5 in every cell, including π ∈ {0.6, 0.75} and T = 5, π = 1 (0.999331 against 0.999336).
- **Case B now has a cross-check.** The experiment registered method P alone for Case B, and this review supplies the independent check.

**H0 fails and H1 holds, in my computation too.** The defect is positive for π < 1/2 in Case A, and for every π ≠ 1/2 in Case B.

**The Deviations are honest.**
- **The Design was fixed before the run.** The Design text is unchanged across registration (`a837512`), the code commit (`58d3f47`) and the report.
- **Deviation 1 is accurate.** `summary.csv` shows Case B, π = 1/2, T = 5 with D_P = 0.01634 and e_trunc = 0.01612: "positive" under the literal rule, but unconverged. The scaled ladder levels at 4.18, so the bound decays like 1/log M. The T = 1 cell is already labelled "upper bound only". My scheme gives 0 at π = 1/2, confirming the reading, and as the deviation says, neither hypothesis turns on these cells.

**The "observation" is an exact duality.** I derived it; it is not yet a claim. Let Ỹ be the π-auxiliary diffusion for σ. By Itô's formula, R = 1/Ỹ satisfies dR = (1−π)σ*(R)²/R dt − σ*(R)dW̃, where σ*(r) = r²σ(1/r). That is the (1−π)-auxiliary diffusion for σ*, started at 1/s₀, with the exits at 0 and ∞ swapped. With the representation above, for 0 < π < 1 this gives

  D_π(σ, s₀, T) = D_{1−π}(σ*, 1/s₀, T).

- **Case B.** σ = 1 + x² is self-dual (σ* = σ) and s₀ = 1 is fixed, so D(π) = D(1−π) exactly. `summary.csv` agrees to 3e-13.
- **Experiment 001's coincidence** is the case σ = x^β, for which σ* = x^{2−β}.
- **Case A against experiment 001.** σ ≡ 1 has σ* = x². So Case A at π is experiment 001's β = 2 row at 1 − π. For example, 0.1535 at π = 1/4 matches 0.1535 at β = 2, π = 3/4, and 0.0586 at π = 0.4 matches 0.0586 at β = 2, π = 0.6.

The restriction 0 < π < 1 matters, because at π = 0 an endpoint becomes good (b = 0) and the representation fails. This is for math to state and prove as a claim, with AX-01 and the Itô step registered properly. It would make claim 001's two endpoint conditions images of each other under inversion.

**Scope.** "These are numerical results for the two volatility functions" and the AX-01 dependence are accurate. The experiment adds nothing beyond claim 001's criterion except measured defects, and the claim did not need it. Its value is confirming that criterion where the charter's fails, including the two-sided Case B.

Verdict: reproduced
