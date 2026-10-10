---
id: "026"
title: "D14: conditional jump-contamination budgets for the Gaussian-enlarged score"
status: formalized
depends_on: ["003", "023", "053", "055"]
axioms_used: [AX-53, AX-55, AX-56, AX-58]
formal: lean/Standalone/D14JumpRobustness.lean
direction: D14
---
## Statement

**Conditional on the observation-law contract below and the cited inputs.**
The mechanism is integration of a bounded function against a mixture,
applied to claim 055's reference moment. Contamination and its dangers
for likelihood inference are prior art [park2023robust], Section 3,
Example 3. We use the existing linearity of integration, Markov and
AX-53; no general contamination theorem or jump calculus is re-proved.

Keep claim 055's deterministic design, finite nonempty panel, training-only
selector, Gaussian-enlarged denominator and finite score E_i^drift on
all nonnegative training/evaluation arrays (including impossible arrays).
All conditioning is on the same name's training vector U_i. The panel
law P and cross-name dependence are otherwise arbitrary. Supply a fixed
set N₀ of actual pricing-null names; the model below does not infer it.

For each name supply a measurable budget ρ_i(u)∈[0,1]. For each i∈N₀
require, under the actual training law almost surely, probability kernels
G_i(u), J_i^jump(u) and a measurable p_i(u)∈[0,ρ_i(u)] such that

    H_i(u) := Law_P(V_i | U_i=u)
            = (1−p_i(u)) G_i(u) + p_i(u) J_i^jump(u).          (1)

Here G_i is a claim-055 Gaussian conditional price law with fixed b_i∈R,
κ_i>0, including its trapped extension from a zero endpoint. J_i^jump is any
probability kernel on the same full nonnegative evaluation domain; it
need not have a density. The training distribution is unrestricted.
At alternatives no mixture premise is required. These are assumptions
on actual observation laws, not fitted laws or reference-training-a.s.
assertions. Each jump magnitude and its distribution may be unbounded.

1. **Budget and raw size.** At every training value where (1) holds,
   TV(H_i,G_i)≤p_i≤ρ_i. For fixed 0<α_i<1,

       P(E_i^drift>1/α_i | U_i)
         ≤ α_i+(1−α_i)ρ_i(U_i),
       P(E_i^drift>1/α_i)
         ≤ α_i+(1−α_i)E[ρ_i(U_i)].                     (2)

   The panel union bound is the sum of (2) over actual nulls, capped
   at one. If ρ_i≤e_i<α_i almost surely for a fixed e_i, rejecting at
   E_i^drift>(1−e_i)/(α_i−e_i) has size at most α_i.
   None of these statements extends claim 054's confidence bands.

2. **Clipped scores and FDR.** For fixed finite c_i≥1 define

       E_i^jump = min(E_i^drift,c_i)
                  / [1+(c_i−1)ρ_i(U_i)].                (3)

   These are finite nonnegative measurable scores for every name, with
   E_P[E_i^jump | U_i]≤1 at each actual null. Claim 053's base e-BH
   procedure at level q_FDR has FDR≤q_FDR|N₀|/m, conditional on AX-53.
   Any measurable panel-dependent zero mask preserves this guarantee
   using the original m. No conditional-on-selection FDR is asserted.
   Replacing the exact score by a measurable finite nonnegative value
   certified no larger than it also preserves the conclusions.

   A strict per-name rejection E_i^jump>1/α_i is possible only if

       ρ_i(U_i)<α_i,
       c_i>(1−ρ_i(U_i))/(α_i−ρ_i(U_i)).                  (4)

   This restriction also applies to a base e-BH selection with α_i
   replaced by its rank threshold q_FDR k/m. It is a necessary bound
   on the capped score, not a prediction of power.

3. **A finite-grid jump-law contract that supplies (1).** At a positive
   last training price, suppose conditional on U_i the evaluation log
   returns are Z_j+L_j, with Z_j independent Normal((b_i−κ_i²/2)Δ_j,
   κ_i²Δ_j). The finite real vector L is conditionally independent of Z
   and has conditional probability at most ρ_i(U_i) of being nonzero.
   Prices are formed recursively by multiplying by exp(Z_j+L_j).
   Then (1) holds: on L=0 the conditional price law is G_i, and the
   remaining price law is J_i^jump. The interval jump totals L may depend
   on one another and on training. A positive endpoint stays positive.
   This supplies a nonzero observation model: independent Bernoulli
   choice of L=0 or a fixed nonzero finite vector, with nondegenerate
   Gaussian Z, realizes every constant 0<p_i<1. It supplies no pricing
   measure or continuous-time process.

   If a separately supplied conditional no-jump survival probability
   is exp(−λ_i τ_e), for λ_i≥0, it suffices to take
   ρ_i=1−exp(−λ_i τ_e). The survival relation is a **premise**, not an
   assertion for general jump processes. Finer sampling at fixed τ_e
   does not reduce this budget. Deterministic compensator drift must
   already be included in b_i; claim 055 admits every fixed b_i.

   **Dependent-jump correction.** If Z retains its conditional Gaussian
   law but L may depend on Z, comparison on the same conditional space
   still gives TV(H_i,G_i)≤P(L≠0 | U_i)≤ρ_i: the price vectors agree
   when L=0. This uses the existing coupling bound from claim 003.
   The mixture identity (1) need not hold with this p_i, so (2) and (3)
   cannot be inferred. The existing TV argument in claim 023 instead
   gives raw size ≤min(1,α_i+Eρ_i) and valid null moments for
   min(E_i^drift,c_i)/(1+c_iρ_i(U_i)); AX-53 again applies. Neither
   route covers a latent baseline whose conditional law is not supplied.

## Proof

**Reference hypotheses.** For every nonnegative training vector the
selected CEV evaluation density q_i is normalized and the denominator
in claim 055 dominates the Gaussian reference density g_i. Where g_i>0
and the denominator is finite, E_i^drift g_i≤q_i; an infinite denominator
gives score zero. The support integral is therefore at most one by the
already checked AX-58 application in claim 055. This is pointwise in
training, including impossible prefixes, so actual training weights
do not invalidate the reference moment. Finiteness and measurability
are also supplied by claim 055, not inferred from almost-sure support.

**Mixture application.** Apply linearity in the measure to (1). For an
event A its difference from G_i(A) is p_i[J_i^jump(A)−G_i(A)], whose absolute
value is at most p_i. For A={E_i^drift>1/α_i}, reference Markov gives
G_i(A)≤α_i, whereas J_i^jump(A)≤1. The resulting bound is
(1−p_i)α_i+p_i≤α_i+(1−α_i)ρ_i. Integrating under the actual training
law and applying the union bound gives (2). With β=(α_i−e_i)/(1−e_i),
the same calculation gives β+(1−β)e_i=α_i at threshold 1/β.

For f=min(E_i^drift,c_i), its G_i integral is at most one and its
J_i^jump integral at most c_i. Linearity gives

    ∫ f dH_i ≤ (1−p_i)+p_i c_i
              ≤ 1+(c_i−1)ρ_i.

The last step uses c_i≥1. Division gives the conditional moment of
(3), then the unconditional one. Nonnegative finite measurable scores
and these moments check exactly the existing AX-53 hypotheses. Masks
and certified lower scores decrease the scores pointwise. The bound
E_i^jump≤c_i/[1+(c_i−1)ρ_i] and a strict rejection imply
c_i(α_i−ρ_i)>1−ρ_i, which requires ρ_i<α_i and gives (4).
For ρ_i=1 the score is at most one, so rejection is impossible too.

For part 3 condition first on L=0 and its complement, conditional on
U_i. Conditional independence preserves the product Gaussian law on
L=0, which gives exactly claim 055's Gaussian price density. Taking
p_i=P(L≠0 | U_i) proves (1). When either event has zero probability,
the unused kernel can be chosen arbitrarily. If the probability of
no jumps is supplied, that event implies L=0; cancellations of jumps
can make p_i smaller. Thus its complementary probability is still an
upper budget. No jump SDE theorem is used in this argument.
In the dependent case apply claim 003's bounded-test coupling at each
training value to the baseline and shifted prices, which agree off
{L≠0}. Then apply claim 023's bounded-function TV comparison to the
already established reference moment. This invokes its general
comparison argument, not its positive-catalogue model specialization.

## Checks

`checks/026/check.py` enumerates exact finite mixtures with training-
dependent contamination, support loss, raw-size and cap bounds, and
dependent/masked e-BH panels. It checks the normalization's sharpness
in the abstract reference-moment class: if G(rare)=1/c and E=c on rare
and zero elsewhere, contaminating entirely on rare gives clipped mean
1+(c−1)ρ exactly. This is not a CEV or Gaussian price counterexample.
The same fixture shows why small contamination alone does not preserve
the *raw* reference moment uniformly over that abstract class as c grows.
Deterministic Gaussian quadrature checks the explicit Bernoulli jump
model's no-jump mixture and TV budget. No simulation is claimed.
An exact dependent-coupling fixture moves probability ρ from a zero-score
point to a point with score c. Its clipped mean is 1+cρ, exceeding the
mixture denominator 1+(c−1)ρ. This distinguishes the two contracts.

## Not shown

- No derivation or estimation of p_i, ρ_i or a survival relation from
  observed prices; no guarantee from a fitted jump frequency.
- No arbitrary stochastic volatility or general jump law. Dependence
  between the baseline and jumps requires the weaker correction unless
  (1) is separately established; the baseline law remains substantive.
  A no-jump conditional law need not equal an unconditioned diffusion
  law when jump intensity depends on its future path.
- No construction of a pricing measure or proof that the actual price
  is a true or strict local martingale. The N₀ labels remain supplied.
- No claim that every input has a uniform informative budget. If
  ρ_i≥α_i, this capped individual test cannot reject at that level.
- No rounded-price likelihood, arbitrary-domain data deletion,
  repeated-date guarantee, or certified arithmetic. Numerical failure
  may be replaced by zero; the other numeric scores still need the
  one-sided certificate to invoke the implemented-score conclusion.
- The application is formalized in `lean/Standalone/D14JumpRobustness.lean`
  and `lean/Novel/D14JumpRobustnessProof.lean` (`proof`), using the
  formalized claim 055. The CEV-score reference moment remains conditional
  on AX-55/56, whose stochastic kernel instances are vacuous. FDR remains
  conditional on AX-53's universal input discussed in claim 053; its
  available instance is degenerate. The mixture bounds, cap conditions,
  finite-grid jump law, dependent-jump correction and union bound are
  proved without those upstream inputs, under their stated premises.
  The finer-sampling commentary, failure of (1) under dependence, and
  numerical fixtures are not formalized.

## Prior art

[park2023robust], Section 3 Example 3, already uses contamination to
demonstrate failure of misspecified universal inference; its Section 4
discussion relates contamination to TV. Neither projection coverage nor
a pricing label is imported. [wasserman2019universal], Theorem 3 and
Section 6, supplies the dominated conditional likelihood mechanism
(AX-58); [wang2020false] supplies AX-53. This is an application to the
Gaussian-enlarged price score and its full-domain support conventions,
with an explicit jump observation contract and separate pricing premise.
It is not a new general robustness principle. Claim 023, claim 025,
the D14 findings, and the refuted arbitrary e-BH post-filter were read
first. Integration of a mixture uses Mathlib's existing integration
against sums and scalar multiples of measures
(`lintegral_add_measure`, `lintegral_smul_measure` in
`MeasureTheory/Integral/Lebesgue/Basic.lean`); do not re-prove it.

## Review

Reviewer, 2026-10-06, on branch `math/d14-jump-robustness` at `1325ebf`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/026/check.py`.
- **Inputs.** AX-53, AX-55, AX-56 and AX-58 are audited. Claims 003, 023, 053 and 055, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/026/reproduce.py`, with its rerun command and seeds in its header. It is not a CI `check.py`.

**Part 1: correct.**
- **The size bound (2).** By linearity of the mixture, H(A) = (1−p)G(A) + pJ(A) ≤ (1−p)α + p = α + p(1−α) ≤ α + (1−α)ρ, using claim 055's reference Markov bound G(A) ≤ α.
- **The adjusted threshold.** With β = (α − e)/(1 − e), β + (1 − β)e = α, so threshold (1 − e)/(α − e) restores size α.
- **The TV bound** TV ≤ p is immediate.

**Part 2: correct.**
- **The clipped moment (3).** ∫min(E, c) dH ≤ (1−p)·1 + pc ≤ 1 + (c − 1)ρ, using ∫E dG ≤ 1, min ≤ c and c ≥ 1.
- **The cap condition (4).** c/(1 + (c − 1)ρ) > 1/α ⟺ c(α − ρ) > 1 − ρ, and at ρ = 1 the score is at most 1.
- **FDR.** AX-53 and masking are as in claim 055.

**Part 3: correct.**
- **The mixture.** Conditional on {L = 0}, independence of L and Z leaves the Gaussian product law, so (1) holds with p = P(L ≠ 0 | U) ≤ ρ.
- **Survival.** No-jump survival implies L = 0, so 1 − e^{−λτ_e} is a valid upper budget. It does not depend on sampling frequency.
- **Dependent jumps.** For L dependent on Z, coupling gives only TV ≤ ρ, so claim 023's weaker normalization (1 + cρ) applies.
- **The distinguishing fixture checks:** G = (1 − 1/c, 1/c), E = (0, c), with ρ mass moved to the rare point, gives clipped mean 1 + cρ > 1 + (c − 1)ρ. So the mixture contract is necessary for the sharper denominator.

**Checks** (evidence, not proof).
- **(a) Exact rationals.** 3,000 random finite mixtures with ∫E dG ≤ 1 and p ≤ ρ. No violations of (2), the adjusted threshold, (3), or (4) at α ∈ {1/20, 1/10, 1/3} and c ∈ {1, 5, 50}. The dependent fixture at c = 20, ρ = 1/10 gives 3 = 1 + cρ > 29/10.
- **(b) Price Monte Carlo of claim 055's E^drift under jumps.**
  - **The setup.** Daily prices for two years, training on year one, the full absorbed CEV catalogue p ∈ {½, 1, 3/2} × κ ∈ {0.2, 0.3, 0.45}, and 20,000 paths per case. The truth is physical GBM (b = 0.05, σ = 0.3) plus independent compound-Poisson log jumps, so (1) holds with ρ = 1 − e^{−λ·1}.

  | Jumps per year λ, log-jump law | ρ | False alarm at α = 0.1 | Bound (2) | Raw mean E | Clipped (3) mean, c = 50 |
  |---|---|---|---|---|---|
  | 0 | 0 | 0.0000 | 0.10 | 0.38 | 0.38 |
  | 0.5, N(−0.1, 0.05²) | 0.39 | 0.0011 | 0.45 | **25** | 0.016 |
  | 2, N(−0.1, 0.05²) | 0.86 | 0.0046 | 0.88 | 6.6 | 0.008 |
  | 2, N(0, 0.15²) | 0.86 | 0.0110 | 0.88 | **10¹²** | 0.013 |
  | 5, N(−0.05, 0.1²) | 0.99 | 0.0104 | 0.99 | 441 | 0.011 |
  | 10, N(0, 0.1²) | 1.00 | 0.0160 | 1.00 | 3×10⁵ | 0.015 |

- **The author's check.** I ran `checks/026/check.py` afterwards. It passes 128 exact mixtures, 512 dependent/masked panels, and the sharpness and jump-mixture quadratures.

**Gaps.** None.

**Scope; "Not shown" is honest, and the practical message is sharp.**
1. **Jumps break the raw score's null mean in price laws.** In my table it ranges from 25 to 10¹² under a bubble-free GBM with a jump about every two years. So claim 055's raw scores must not enter e-BH when jumps are possible. Clipping (3) restores validity, as proved.
2. **The budget is uninformative at realistic jump rates.** The contamination budget is the probability of any jump in the evaluation window. Over a one-year window, even λ = 0.5 per year gives ρ ≈ 0.39 > α. Then the capped score can never reject (4), and its mean is about 0.01.
3. **The guarantee is therefore valid but powerless over realistic windows.** It becomes useful only when windows are short enough that ρ ≪ α, for example λτ_e ≲ 0.01, or with a jump-aware null family. Neither is supplied.
4. **Actual raw false alarms stayed small** (≤ 1.6%). The obstruction is to the e-value moment and to the bound's usefulness, not evidence of large per-name size inflation here.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the mixture size bound and adjusted threshold, clipped moment and cap condition, the independent-jump mixture contract and the dependent-jump counterexample; exact rationals and committed price Monte Carlo; practical limits stated


Reuse the pointwise Gaussian reference moment from claim 055/AX-58,
and the finite-score domain and masking conventions of claims 025/055.
Prove the application by existing measure-integration linearity and
the displayed scalar inequalities. Preserve the actual-training-law
quantifier and the distinction between p_i and its budget ρ_i. Part 3
is a declared finite-grid observation law, not imported jump calculus;
its instance must use nondegenerate Gaussian returns and a nonzero jump
vector. No continuous-time jump theory or pricing construction is needed.

Formalizer, 2026-10-06, on `form/d14-jump-robustness`. **Status: formalized.** The statement is `lean/Standalone/D14JumpRobustness.lean`, proved in `lean/Novel/D14JumpRobustnessProof.lean` (`proof`). There is no `sorry`, and the axiom audit is clean. `statement := reference ∧ oneName ∧ cap ∧ panel ∧ jumpLaw ∧ dependent`.
- **Inputs.**
  - AX-58 is proved from Mathlib. AX-53 enters as claim 053's `AX53`, for the FDR conclusions only.
  - AX-55/56 enter as claim 054/055's restatements, on a base carrying a Brownian motion, with VACUOUS Upstream instances. They supply the catalogue kernels' normalization and positivity used by claim 055's score.
- **`reference`.** For claim 055's score E^drift and its Gaussian conditional law G(u) = (1) from the last training price (fixed b, κ > 0, trapped extension included), on claim 054's design:
  - the score is measurable and finite;
  - every G(u) is a probability;
  - ∫ E^drift(u,·) dG(u) ≤ 1 at **every** training value u, including impossible prefixes.
  The proof uses claim 055's domination, AX-58's pointwise bound g·E^drift ≤ Ĝ, and claim 054's chain normalization.
- **`oneName` (parts 1–2).** These hold for any measurable score E with a reference G(u) satisfying that pointwise moment. The actual-training-law quantifier is kept: (1) is required for P∘U⁻¹-a.e. u, as ∃ p ∈ [0, ρ(u)] and a probability J with condDistrib(V|U)(u) = (1 − p)G(u) + pJ. p and J need not be measurable in u, which is weaker than the claim's kernels.
  - Proved: TV ≤ p; the conditional and unconditional size bounds (2); and the adjusted threshold (1 − e)/(α − e) when ρ ≤ e < α a.s.
  - For c ≥ 1 the clipped score (3) is measurable and lies in [0, c]. Its conditional mean given U is at most one a.s., and the unconditional mean of any measurable value between 0 and it is at most one, which covers certified lower scores.
- **`cap`.** (4) for a strict rejection. Its weak form holds for a base e-BH selection at the rank threshold q k*/m, since e-BH's threshold includes equality.
- **`panel`.** The union bound over actual nulls, capped at one. Conditional on AX-53, the FDR bound q|N₀|/m holds for any measurable nonnegative scores that are at most a null-mean-≤-1 score at the actual nulls. This covers (3), zero masks with the original m (discoveries lie in the mask), and certified lower values.
- **`jumpLaw` (part 3).** Stated at the level of laws at a fixed positive training endpoint x₀: Z has the product Normal((b − κ²/2)Δⱼ, κ²Δⱼ) law, L is independent with any law νL, and prices are x₀·exp(Σ_{i≤j}(Zᵢ + Lᵢ)). The kernel version is this applied at each training value.
  - **The no-jump law is claim 055's Gaussian law (1). This is proved, not assumed,** by induction on the number of returns and the substitution y = x eʳ.
  - (1) holds with p = νL(L ≠ 0).
  - The Bernoulli law (1 − p)δ₀ + pδ_w, with w ≠ 0 and nondegenerate Gaussian returns, realizes every 0 < p < 1.
  - A supplied survival probability e^{−λτ} ≤ νL(L = 0) gives the budget 1 − e^{−λτ}.
- **`dependent`.**
  - For any joint law of (Z, L) with Z's Gaussian marginal, TV(H, G) ≤ P(L ≠ 0), because the price maps agree on {L = 0}.
  - Under a TV contract, claim 023's consequences hold (its `lintegral_le_tv`): raw size ≤ min(1, α + Eρ), and a null mean ≤ 1 for min(E, c)/(1 + cρ).
- **Not formalized.** Commentary only: that finer sampling does not reduce the budget, that (1) can fail in the dependent case, and the checks' fixtures.
