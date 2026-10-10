---
id: "044"
title: "D32: estimating survival-weighted contributions and testing necessary compatibility"
status: formalized
depends_on: ["016"]
axioms_used: [AX-06, AX-17]
formal: lean/Standalone/D32RecoveryEstimator.lean
direction: D32
---
## Statement

**Mechanism and scope.** Apply bounded-variable concentration and the law of
large numbers to a regression integral under a different, finite measure.
These general results already exist in Mathlib; they are not new theorems
of this claim. The contribution is an estimator of claim 016's corrected
recovery quantity and a test of its necessary coordinate inequalities.
The stochastic interpretation is conditional on claim 016's common pricing
model, AX-06 and AX-17. The test does not identify a pricing kernel.

**Observation contract.** Fix a maturity T, d≥1 positive holdings and starts,
I₀>0 and initial weights omega_i>0 summing to one as in claim 016. Let H be
the physical probability law of (I_T,mu(T)) on (0,infinity) times the d-name
simplex. Write P_I for its index marginal and choose Borel conditional means
m_i(x)=E_H[mu_i|I_T=x] in [0,1], with their vector in the simplex everywhere
(changing a common null set to omega if necessary). Supply independently
the pricing index probability nu_T on (0,infinity), with

    nu_T equivalent to P_I,   p_I := integral x nu_T(dx)/I₀ ≤ 1,
    eta_T(dx) := x nu_T(dx)/I₀,
    theta_i := integral m_i d eta_T.                         (1)

Thus 0<p_I≤1. Outside the identifying restriction theta is a pseudo-target;
it need not be a vector of constituent fundamental values. Under the full
terminal restriction dQ/dP=k_T(I_T) and the other assumptions of claim 016,

    b_i := n_i beta_i(T)/I₀ = omega_i−theta_i,
    0≤theta_i≤omega_i,   sum_i theta_i=p_I.                  (2)

Observe an infinite iid sequence (Y_r,U_r) with law H and a separate iid
sequence X_l with law nu_T, the two sequences independent. The sample sizes
N,M are deterministic positive integers. All probabilities below refer to
this sampling experiment. This is a synthetic repeated-terminal-panel
contract, not overlapping windows from one historical path. nu_T is supplied;
no option-panel inversion or estimated pricing marginal is assumed valid.

1. **Estimator and pointwise consistency.** Let m_hat_i,N(x) be jointly
   measurable in the training data and x, depending only on the first N
   physical observations, and simplex-valued for every x. Define

       theta_hat_i,N,M = (1/(M I₀)) sum_(l=1)^M X_l m_hat_i,N(X_l),
       b_hat_i,N,M = omega_i−theta_hat_i,N,M.               (3)

   Suppose, at a fixed law satisfying the identifying restriction, that
   A_i,N=integral |m_hat_i,N−m_i| dP_I tends to zero in probability for
   every i. Then theta_hat_i,N,M tends to theta_i and b_hat_i,N,M tends
   to b_i in probability along any deterministic N,M→infinity. No second
   moment of nu_T or bounded density ratio is required. The estimator
   using the exact integral integral m_hat_i,N d eta_T has the same limit.
   For every sample, irrespective of the restriction,

       sum_i b_hat_i,N,M = 1−(1/(M I₀)) sum_l X_l.          (4)

   Do not normalize by the sampled index mean or clip negative b_hat.

2. **Histogram accuracy, including random counts.** Fix in advance
   B=[a,R], 0<a<R<infinity, a Borel partition C_1,...,C_J of B, J≥1,
   each cell of diameter at most h>0, and a supplied L_B≥0 such that
   every m_i is L_B-Lipschitz on B. Take cell sample means of U_r as the
   vector m_hat_N on occupied cells. On empty cells and outside B set
   m_hat_N=omega. Let N_j be the cell counts. For any 0<delta<1 set

       e_N(B,delta) = 1                          if some N_j=0;
       e_N(B,delta) = min(1, L_B h +
         max_j sqrt(log(2 d J/delta)/(2 N_j)))   otherwise. (5)

   With probability at least 1−delta, simultaneously for all i and x∈B,

       |m_hat_i,N(x)−m_i(x)| ≤ e_N(B,delta).                (6)

   No independence across names is required. L_B is a known bound on a
   chosen version, not a fitted slope. Zero-probability cells cause no
   exception: they are empty almost surely and (5) then gives radius one.

   Here is one explicit sufficient route to the premise of part 1. Use
   deterministic B_N=[a_N,R_N] increasing to (0,infinity), partitions
   with J_N cells and diameters h_N, supplied Lipschitz bounds L_N,
   and deterministic delta_N→0 in (0,1). Assume

       L_N h_N→0,
       min_j N_j / log(2 d J_N/delta_N)→infinity
         in probability.                                 (7)

   The convention min_j N_j=0 applies to an empty cell. Then the resulting
   histogram is L1(P_I)-consistent. Condition (7) is an additional overlap
   and sample-size condition, not implied by the density restriction.
   A sufficient deterministic condition for its count part is, with
   pi_N=min_j P_I(C_j)>0,

       N pi_N / log(2 d J_N/delta_N)→infinity,
       J_N exp(−N pi_N²/2)→0.                             (8)

   This deliberately conservative condition is sufficient, not necessary.

3. **A finite-sample necessary-compatibility test.** Fix B, its partition
   and L_B as in part 2 before observing either sample. Fix
   0<alpha_reg,alpha_price<1 with alpha_reg+alpha_price<1. Put

       theta_hat_i,B = (1/(M I₀)) sum_l
                          X_l 1{X_l∈B} m_hat_i,N(X_l),
       c_M(B) = (R/I₀) sqrt(log(2 d/alpha_price)/(2 M)),
       lower_i = theta_hat_i,B−e_N(B,alpha_reg)−c_M(B).     (9)

   Reject if lower_i>omega_i for some i. For every fixed observation law
   satisfying the contract, the Lipschitz premise, and theta_i≤omega_i
   for all i, rejection probability is at most alpha_reg+alpha_price.
   In particular this holds for compatible claim-016 models with these
   additional observation/accuracy premises. More precisely, with that
   simultaneous coverage probability,

       lower_i ≤ theta_i,B := integral_B m_i d eta_T
               ≤ theta_i  for every i.                   (10)

   There is no omitted-upper-tail penalty in this one-sided rule because
   the omitted integral is nonnegative. Non-rejection is not acceptance
   of the terminal-density restriction or existence of a pricing model.

   Exact real arithmetic is used in (9). The same size bound holds if a
   computation returns a certified value no greater than each lower_i
   and rejects only on its strict excess over omega_i. An unresolved
   computation must not reject. An arbitrary floating-point approximation
   has no certification guarantee from this statement.

4. **Separated alternatives and limits of power.** Suppose a fixed law
   in the observation contract has theta_i>omega_i for some i. Then some
   deterministic positive compact B captures theta_i,B>omega_i. For a
   fixed such B with the part-2 Lipschitz premise, take deterministic
   partitions with h_N→0 and

       min_j N_j/log(2 d J_N/alpha_reg)→infinity
         in probability,   M→infinity.                   (11)

   At fixed alpha_reg,alpha_price, the exact rule (9) rejects with
   probability tending to one. A certified implementation has this power
   conclusion only if its downward numerical error also tends to zero
   in probability; size alone does not supply that accuracy.

   A conditional construction of a separated alternative is available
   without changing the pricing index marginal: take any compatible Q
   model in which all constituents are true martingales and let

       dP/dQ = (1+epsilon mu_1(T))/E_Q[1+epsilon mu_1(T)],
       epsilon>0.                                        (12)

   Writing g=E_Q[mu_1|I_T] and v=Var_Q(mu_1|I_T), its physical mean is

       m_1 = g + epsilon v/(1+epsilon g).                 (13)

   If integral x v(x) nu_T(dx)>0, theta_1>omega_1, while sum_i theta_i=1.
   This violates necessary compatibility although the sum remains right.
   It supplies power via (11) only when the regression and count premises
   hold; these are not proved for all such pricing models. Only coordinate
   violations are targeted. The test has no power assertion against every
   failure of the terminal-density restriction.

## Proof

**General results reused.** For independent variables in an interval of
length D, apply Mathlib's
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` to centered variables,
with parameter D²/4, then `measure_sum_ge_le_of_iIndepFun` to their sum.
Applying it also to the negatives gives, for a sample mean of n variables,

    Pr(|mean−its mean|>t) ≤ 2 exp(−2 n t²/D²),  t≥0.       (14)

We use this existing bounded-variable result with D=1 and D=R/I₀; we do
not re-prove it. `ProbabilityTheory.strong_law_ae_real` supplies the law of
large numbers for the fixed integrable variable used below. The elementary
integration, conditional-expectation and convergence lemmas are likewise
existing library results, not new stochastic inputs.

**Part 1.** Claim 016 proves (2). Under its terminal density restriction,
eta_T has density W_T(x)=x k_T(x)/I₀ relative to P_I, with integral p_I≤1.
Write f_i,N=|m_hat_i,N−m_i|, so 0≤f_i,N≤1. For every fixed L>0,

    D_i,N := integral f_i,N d eta_T
      ≤ L A_i,N + integral W_T 1{W_T>L} dP_I.             (15)

The last term tends to zero as L→infinity by integrability of W_T. For any
tolerance first choose a fixed L controlling this term, then use convergence
of A_i,N in probability. Thus D_i,N→0 in probability. Also 0≤D_i,N≤p_I;
existing bounded convergence in probability gives E[D_i,N]→0. Equivalently,
E[D_i,N]≤t+p_I Pr(D_i,N>t), which gives the same conclusion for every t>0.
Joint measurability and boundedness ensure these random integrals exist.

Condition on the training data. Independence of every X_l gives

    E[ |theta_hat_i,N,M − (1/M) sum_l X_l m_i(X_l)/I₀| ]
      ≤ E[D_i,N].                                        (16)

Tonelli applies to the nonnegative error and its expectation is finite,
since D_i,N≤p_I. Markov's inequality makes (16) vanish in probability,
uniformly in the deterministic M. The fixed variables X_l m_i(X_l)/I₀
are iid and integrable, dominated by X_l/I₀, so the cited law of large
numbers gives their sample mean limit theta_i. This proves (3) and the
exact-integral variant. Finite summation of the simplex fit proves (4)
without using any identifying assumption. No uniform-in-model assertion
follows from the model-dependent tail term in (15).

**Part 2.** Give each training observation its cell label, adding an
outside-B label. Condition on the entire finite vector of labels, not on
the observed indices inside a cell. At every positive-probability label
configuration, independence of the original observations implies that the
selected pairs in cell j are independent with law H conditional on Y∈C_j.
Indeed their conditional product probabilities factor after dividing the
product law by the product of label probabilities. This is conditioning on
finite events, not an assumed regular conditional law on path space.

If every count is positive, let m_bar_i,j=E[U_i|Y∈C_j]. The selected U_i
lie in [0,1]. Applying (14) at the now fixed count N_j and radius
sqrt(log(2dJ/delta)/(2N_j)) bounds each cell/name failure probability by
delta/(dJ). A finite union bound gives total at most delta at each label
configuration; average over labels. Conditional expectation and the
Lipschitz assumption give, for every x∈C_j,

    |m_bar_i,j−m_i(x)|
      = |E[m_i(Y)−m_i(x)|Y∈C_j]| ≤ L_B h.                 (17)

Adding the cell-mean error proves (6) with the uncapped radius. Both fit
and target lie in [0,1], so capping at one preserves the bound. When a
cell is empty, radius one is valid without a concentration event. This
also handles all zero-probability cells.

For the expanding-range construction, (7) implies e_N(B_N,delta_N)→0 in
probability. On the event (6),

    A_i,N ≤ e_N(B_N,delta_N) + P_I(B_N complement).         (18)

The event fails with probability at most delta_N→0 and the deterministic
last term tends to zero by exhaustion, proving the required L1 convergence.
For (8), each cell count is a sum of iid Bernoulli variables of mean
pi_j=P_I(C_j)≥pi_N. The one-sided instance of (14) bounds
Pr(N_j<N pi_j/2) by exp(−N pi_j²/2). Thus

    Pr(min_j N_j<N pi_N/2) ≤ J_N exp(−N pi_N²/2).          (19)

On the complementary event, the first limit in (8) gives (7). No
independence between different cells' counts is used.

**Part 3.** Conditional on training, the independent pricing variables
X_l 1_B(X_l) m_hat_i,N(X_l)/I₀ lie in [0,R/I₀]. By (14), for each i the
sample average differs from integral_B m_hat_i,N d eta_T by at most c_M
except with probability alpha_price/d. Union over i and average over
training. Combine with part 2 at delta=alpha_reg. On the joint event,

    theta_hat_i,B ≤ integral_B m_hat_i,N d eta_T + c_M
       ≤ theta_i,B + e_N eta_T(B) + c_M
       ≤ theta_i,B + e_N + c_M.                           (20)

Here eta_T(B)≤p_I≤1; the fit's simplex property alone would not justify
that mass bound. Nonnegative m_i proves theta_i,B≤theta_i, yielding (10).
Under the null theta_i≤omega_i, strict rejection is impossible on this
event. The union bound gives the asserted size, without needing independence
of the two good events. A certified downward replacement preserves that
inclusion of rejection events.

**Part 4.** The nonnegative integrand x m_i(x)/I₀ is integrable. Its integrals
over [1/k,k] tend to theta_i by monotone convergence. Hence a strict excess
above omega_i is captured on one such range with k>1. This is an existence
statement at a fixed alternative, not license to select B after seeing data.

Under (11), the radius at fixed alpha_reg tends to zero. For any other
fixed 0<delta<1, the ratio
log(2dJ_N/delta)/log(2dJ_N/alpha_reg) stays bounded uniformly in J_N≥1.
Consequently e_N(B,delta)→0 too. By (6), for each t>0 the limit superior
of the probability of uniform regression error exceeding t is at most
delta. Let delta decrease to zero. The uniform error thus tends to zero
in probability. Its eta_T integral is bounded by that error, and the
conditional concentration argument (14), with fixed B and M→infinity,
makes the pricing-sample error vanish in probability. It follows that
theta_hat_i,B→theta_i,B, while e_N and c_M vanish. A strict positive margin
therefore yields rejection probability tending to one. The numerical-error
qualification follows by the same margin argument.

Finally the tilt (12) is bounded above and away from zero, so it defines a
probability equivalent to Q. Conditional change of measure gives

    E_P[mu_1|I_T]
      = E_Q[mu_1(1+epsilon mu_1)|I_T]/(1+epsilon g)
      = g + epsilon v/(1+epsilon g).

These are applications of the same conditional pull-out identity as claim
016; all weights and the tilt are bounded. True-martingale constituents
give integral x g(x) nu_T(dx)/I₀=omega_1. The additional term in (13) has
strictly positive integral under the stated variance condition, proving
theta_1>omega_1. The conditional means still sum to one, and the true
basket has p_I=1. This establishes the alternative and the automatic sum,
without claiming that arbitrary finite terminal tables are process models.

## Checks

`checks/044/check.py` enumerates finite training-count configurations and
binomial tails rather than drawing paths. It checks histogram coverage
including empty cells, bounded-mean concentration constants, the coordinate
lower-bound implication, preservation of a survival mass below one, and a
separated weight-tilt fixture whose sum identity still holds. The fixtures
are terminal probability tables, not local-martingale process instances.
These checks do not prove consistency, smoothness of any diffusion's
conditional means, or general finite-sample size. No simulation is run.

## Not shown

- No recovery from finite actual option quotes, no weakly estimated nu_T
  plug-in theorem, no reconstruction of physical laws from pricing laws.
  iid terminal replicates and an independent pricing sample are additional
  supplied observations, not available from one path by declaration.
- No implication from the density restriction to Lipschitz conditional
  means, known L_B, or adequate bin counts. Parts 1 and 2 state exactly
  the extra conditions used. No uniform rate over arbitrary density ratios
  or tails, minimax rate, or useful finite-sample power is established.
- No two-sided full-contribution confidence interval without a tail bound.
  The compact lower bound supports only the stated necessary-compatibility
  rejection. A genuine bubble within a compatible model is not its null
  violation: the null concerns compatibility, not absence of bubbles.
- No full test of terminal-density measurability, converse to claim 016(3),
  or inference of a pricing model from non-rejection. Negative estimated
  contributions must be retained. Equation (4) cannot validate the model.
- Range, partition, constants and sample sizes are fixed in advance; no
  data-chosen range, repeated look, optional stopping or multiple-horizon
  guarantee is proved. Part 4's compact-range existence is not a selection
  algorithm. Empty cells can make the stated radius and test uninformative.
- No certified numerical implementation or stochastic sampler is supplied
  here. Finite tables are not model realizations. The lower-priority
  uniform-integrability and exposure extensions belong to D33, not this
  claim.

The statistical statement is formalized in
`lean/Standalone/D32RecoveryEstimator.lean`, proved by
`Novel.D32RecoveryEstimator.statement_holds` in
`lean/Novel/D32RecoveryEstimatorProof.lean`. Its seven conjuncts cover
consistency, actual-histogram coverage, histogram L1 consistency, sufficient
counts, size, power and the terminal tilt, using Mathlib. The interpretation
as constituent contributions still uses claim 016 and its stochastic inputs.
The tilt is encoded on a generic probability space with the martingale
expectation identities supplied; its link to claim 016's process model is
not formalized. Nor is the raw histogram made an everywhere-simplex-valued
`Fit` on exceptional training inputs outside the simplex: the sampling
contract excludes those inputs only almost surely. The formal count-tail
argument uses twice the bound in (19), which suffices for the same
asymptotic condition (8). The review's per-cell-radius variant is outside
the formal statement. See the Formalizer note below for the precise scope.

## Prior art

Read the D32 input and librarian sweep in FINDINGS, claims 010/016 and the
refuted ordinary-weight loss. The share-survival source is
[kardaras2015strict], already audited as AX-17 and used through claim 016;
no share process or recovery theorem is reconstructed. Searched the pinned
Mathlib before proving anything: `Probability/StrongLaw.lean` supplies
`strong_law_ae_real`, and `Probability/Moments/SubGaussian.lean` supplies
the bounded-mgf and independent-sum lemmas named above. Conditional
expectation, measure integration and monotone convergence are standard
library inputs. No new literature axiom or general statistical theorem is
imported. The new application is the survival-weighted estimator, explicit
additional accuracy contract, and a compact-range test of claim 016's
coordinate restrictions that does not mistake the automatic sum for a test.

## Review

Reviewer, 2026-10-08, on branch `math/d32-recovery-estimator` at `442373e3`.

**Method.** I checked every inequality by hand. I then simulated a model with known conditional means, using my own script written before I read `checks/044/`. It is committed as `checks/review/044/reproduce.py`, with its rerun command and seed in its header, and runs single-process. The author's `checks/044/check.py`, run from a scratch copy, prints PASS.
- **The model.** d = 2, I₀ = 1 and ω = (0.5, 0.5).
  - **Pricing law ν_T:** lognormal with mean 1 (so p_I = 1) and log-sd 0.25.
  - **Compatible null:** P = Q, with μ₁ | I = x ~ Beta(φg, φ(1 − g)) and g(x) = 0.5 + 0.4 tanh(log x − c). The constant c is solved so that θ₁ = ω₁ exactly, the boundary null.
  - **Alternative:** the claim's tilt (12) with ε = 3, sampled exactly. P_I is obtained by rejection from ν_T. Under P, μ₁ | I is a two-Beta mixture with weights 1 : εg.

**The steps hold.**
- **(2)** is claim 016's (7), with η_T and p_I as defined there.
- **Part 1.**
  - **(15)** uses only f ≤ 1 and the density W_T of η_T with respect to P_I, so the tail term vanishes by integrability.
  - **(16)** is the conditional first-moment bound, uniform in M. The law of large numbers needs only E X < ∞.
  - **(4)** is finite summation of a simplex-valued fit. On every simulated sample its residual is ≤ 3×10⁻¹⁶.
  - **An observation.** Part 1's convergence θ̂ → θ uses only ν_T ~ P_I and p_I ≤ 1. The identifying restriction is needed only to read θ as ω − b. The premise is stronger than needed but harmless.
- **Part 2.**
  - **The radius.** Hoeffding with D = 1 at radius √(log(2dJ/δ)/(2N_j)) gives δ/(dJ) per cell and name. The union over dJ events and the conditioning on the finite label vector are correct.
  - **(17)** holds by the tower property and the diameter bound.
  - **(19).** The one-sided Hoeffding bound at t = π_j/2 gives exp(−Nπ_j²/2). It holds against exact binomial tails on all 20 (N, π) pairs I tried.
  - **Coverage (6)** in simulation (N = 3,000, J = 10, δ = 0.2): 0 failures in 200 runs. The sup-error is a median 0.28 of the radius, with a maximum of 0.78.
- **Part 3.**
  - **c_M.** It is Hoeffding on [0, R/I₀] with α_price/d per name. A one-sided bound would allow log(d/α_price), so the stated constant is conservative.
  - **(20)** uses (6) only on B, and η_T(B) ≤ p_I ≤ 1.
  - **Size.** The union bound gives the size, and the omitted tail has the right sign. At the boundary null there were 0 rejections in 450 simulated tests.
- **Part 4.**
  - **The capture step** is monotone convergence. The ratio-of-logs step is correct, since 2d/α_reg > 2.
  - **The tilt formula (13)** matches the exact mixture mean to 10⁻¹⁶. In my model θ₁ = 0.6465 > ω₁ while θ₁ + θ₂ = 1 to 10⁻¹⁰, exactly the separated alternative the claim describes.
  - **The tilted model is outside the restriction.** Its dQ/dP depends on μ₁(T), not only on I_T, so θ is a pseudo-target, as the claim says.

**Power: a finding for the analyst's D32 design, not a defect.**
- **Part 4's asymptotic power appears.** With B = [0.6, 1.7] and J = 20 fixed in advance (θ₁,B = 0.621), the tilt alternative is rejected in 0/200, 134/200 and 50/50 runs at N = M = 10⁴, 10⁵ and 10⁶. There were no null rejections.
- **The radius is driven by the sparsest cell.** The radius (5) uses the smallest cell count min_j N_j for every cell. With the wider range B = [0.4, 2.5], whose edge cells are nearly empty under ν_T, the radius stays at 0.35–1. There is no power even at N = 10⁶, because a single sparse cell inflates the radius everywhere.
- **A per-cell variant is also valid.** Take per-cell radii e_j, at the same union level, and integrate them with the pricing sample. Use lower_i = (1/(MI₀)) Σ_l X_l 1_B(X_l)(m̂_i − e_{j(X_l)}) − 2c_M, where the summand range doubles. The proof of (20) goes through unchanged.
  - **Simulated size:** no null rejections in 450 tests.
  - **Simulated power:** 200/200 already at N = M = 10⁵, about ten times sooner.
- **This is a design option, not a defect.** The claim states only size and asymptotic power, and its "Not shown" disclaims useful finite-sample power.

**Prior art.** The claim cites the Mathlib concentration and strong-law results it uses, and claim 016 and AX-17 for the recovery identity. I found nothing in the registered literature that anticipates a survival-weighted plug-in estimator of claim 016's corrected contribution. The histogram and Hoeffding machinery is standard and is correctly not claimed as new.

**Scope.** "Not shown" is honest. The claim makes no statement about option quotes, estimated ν_T, rates, or a two-sided interval, and non-rejection is not acceptance of the restriction. One point the analyst's design should keep visible: the observation contract, with iid terminal panels and an independent pricing sample, is synthetic. The claim says so. It gives D32 a validated synthetic comparison, not a procedure for one historical path. It does not sharpen or contradict a published result.

Verdict: red-passed

## Formalization notes

Approved 2026-10-08 by pm: Red re-derived the survival-weighted plug-in and its consistency, the Hoeffding coverage with union bound, the size of the coordinate compatibility test and asymptotic power on the tilt; committed review script with simulated size and power; synthetic scope stated


Use the existing Mathlib probability results, including the finite-event
conditioning application for random bin counts. Do not replace the actual
iid histogram experiment by an assumed good event without recording that
as a formal/prose gap. Likewise the generic L1 premise in part 1 does not
encode the sufficient histogram construction in part 2. Keep (1)'s total
mass bound, training/pricing independence, and exact or downward numerical
comparison explicit. Conditional pricing interpretation inherits claim
016's stated stochastic inputs; no new stochastic theory is required.

Formalizer, 2026-10-08, on `form/d32-recovery-estimator` (promoted from `provisional/form-d32-recovery-estimator`). **Status: formalized.** The statement is `lean/Standalone/D32RecoveryEstimator.lean`, with
`statement := consistency ∧ coverage ∧ histogramL1 ∧ countSufficient ∧ size ∧ power ∧ tilt`.
It is proved in `lean/Novel/D32RecoveryEstimatorProof.lean` (`statement_holds`), from `D32RecoveryEstimator{Tools,Coverage,Meas,Size,Tilt,Counts,Hist,Power,Consistency}`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** Only Mathlib:
  - `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` and `measure_sum_ge_le_of_iIndepFun`, giving the two-sided (14);
  - `strong_law_ae_real`;
  - conditional expectation and its pull-out, Fubini, and Radon–Nikodym.
  No axiom is used, and the AX-06 and AX-17 interpretation enters only through claim 016.
- **Encoding.**
  - **The contract (1)** (`Contract`). `H` is a probability on `ℝ × ℝ^d`, carried by `(0,∞) × simplex`. `m_i` is Borel and simplex-valued everywhere, with `m_i(I_T) = E_H[μ_i | I_T]` in its defining form. `ν_T` is equivalent to `P_I`, integrable, with `p_I ≤ 1`. `η_T = (x/I₀) ν_T` and `θ_i = ∫ m_i dη_T`.
  - **The sampling experiment** (`Sampling`). An iid training sequence with law `H`, an iid pricing sequence with law `ν_T`, and the two sequences independent.
  - **A fit** (`Fit`). A jointly measurable, simplex-valued function of the first `N` pairs and `x`.
  - **The histogram, (5) and (9)** (`histFit`, `eN`, `thetaHatB`, `cM`, `lower`) follow the claim. Empty cells and points outside `B` get `ω`.
  - **Convergence.** "In probability along `N, M → ∞`" is `TendstoInMeasure` along `atTop ×ˢ atTop`. "`min_j N_j / log(2dJ/δ) → ∞` in probability" is: for every `K`, `Pr(some N_j ≤ K log(2dJ/δ)) → 0`.
- **Part 1.**
  - (4) holds on every sample.
  - Under the `L¹(P_I)` premise, `θ̂ → θ` and `b̂ → ω − θ` in probability along `N, M → ∞`, and so does the exact-integral variant.
  - The route is the claim's: (15) via absolute continuity of `η_T` with respect to `P_I`; (16) by Fubini over the independent training and pricing samples, uniformly in `M`; and the strong law. As the review observed, the identifying restriction is not needed for the convergence. `b = ω − θ` is (2), which is claim 016's theorem.
- **Part 2.**
  - **(6)** holds with probability at least `1 − δ`, for the actual iid histogram experiment, not an assumed good event. For each cell, condition on the finite event "exactly the indices in `S` fall in the cell", which is a box. Under it the pairs are independent with laws `H(· | C_j)` there (`pi_cond`). The count is then fixed, and (14) and (17) apply. Summing over `S` and taking a union over cells and names finishes the bound.
  - **(7)** gives `L¹(P_I)` consistency of the expanding-range histogram, through (18).
  - **(8)** gives the count part of (7). The binomial tail is proved with the two-sided (14), so (19) carries an extra factor 2, which still tends to zero under (8).
- **Part 3.** (10) holds with probability at least `1 − α_reg − α_price`. Under `θ ≤ ω`, the rule rejects with probability at most `α_reg + α_price`. The same holds for any value below `lower_i` (the certified-implementation statement).
- **Part 4.**
  - A strict coordinate excess is captured on some `[1/(k+2), k+2]`.
  - Under (11) and `h_N → 0` at a fixed range, any value below `lower_i` whose downward error vanishes in probability rejects with probability tending to one. The exact rule is the case of zero error.
  - **The tilt (12)–(13).** On a probability space with `Q`, it is a probability equivalent to `Q`, and (13) is a version of `E_P[μ_1 | I_T]`.
    - The true-martingale constituents enter as `E_Q[I_T μ_i(T)] = ω_i I₀` and `E_Q[I_T] = I₀`, which is `E_Q[n_i S_(i,T)] = n_i S_(i,0)`.
    - Given `∫ x v dν_T > 0`, `θ_1 > ω_1` while `Σ_i θ_i = 1`, for any simplex-valued `m` with `m_1` given by (13).
    - The versions are chosen with `g ∈ [0, 1]` and `v ≥ 0`.
- **Not formalized.**
  - The link of (12) to claim 016's process model (`Standalone.D4Recovery.Model`); the tilt is stated on a generic probability space with the martingale identities as premises.
  - That the histogram is a `Fit` in part 1's sense off the null event where some training weight leaves the simplex. On that event its cell means need not be simplex-valued, so the chain from `histogramL1` to part 1's conclusions holds for the histogram only almost surely.
  - Part 4's per-cell-radius design option from the review, which is not part of the claim.
