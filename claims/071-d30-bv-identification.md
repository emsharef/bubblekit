---
id: "071"
title: "D30: continuous-record elasticity identification under finite-variation time effects"
status: formalized
depends_on: []
axioms_used: [AX-13]
formal: lean/Standalone/D30BVIdentification.lean
direction: D30
---
## Statement

**Conditional on the continuous semimartingale representation below and
AX-13 [etheridge2018continuous].** The general mechanism is that adding
continuous finite variation leaves quadratic variation unchanged. Apply
that known result to two linear combinations, then polarize. The finite
array bound below is a separate deterministic calculation. Neither part
is a minimax separation-rate theorem.

### 1. Continuous-record identity

Fix a deterministic horizon T>0, s₀>0 and a real constant beta. On a usual
filtered probability space with Brownian W, supply a finite, continuous,
adapted process X with X₀=0 and the representation

    X_t = M_t + B_t,    M_t = ∫₀ᵗ sqrt(v_u) dW_u,
    v_t = exp(a_time(t) + beta X_t),                 (1)

on [0,T]. Here B₀=0 and B is adapted, continuous and of finite variation;
a_time is a deterministic continuous function with TV_time(a_time)≤V_time<∞;
V_time≥0. Assume (1) holds almost surely simultaneously in t and its
integrand is progressive and square integrable in time pathwise. Existence
of such a global solution is supplied, not proved. Set S_t=s₀ exp(X_t).
In the intended zero-price-drift specialization, B_t=−(1/2)∫₀ᵗv_u du;
the identity also allows any B satisfying the stated conditions.

Let Q(t)=[X]_t denote continuous quadratic variation and define

    L_t = log v_t,
    [L,X]_T := ([L+X]_T − [L−X]_T)/4.

Then, outside one null set,

    Q(t)=∫₀ᵗv_u du,   Q(T)>0,
    L_t = log Q'(t),
    [L,X]_T = beta Q(T),
    beta = [log Q', X]_T / Q(T).                   (2)

Derivatives at 0 and T are one-sided. Thus the continuous-record bracket
and its continuous density identify beta within (1), even though the
deterministic time function is unknown. The associated coefficient
sigma(t,s)=s exp((a_time(t)+beta log(s/s₀))/2) has elasticity
p=1+beta/2. This is a statement about that coefficient and supplied
representation, not a test for a pricing-bubble label.

The identities do not depend on the magnitude of the finite budget.
They apply in particular to a deterministic Lipschitz a_time with bound
L_time, since TV_time(a_time)≤L_time T. No conclusion is asserted for
discontinuous a_time or stochastic time effects of nonzero quadratic
variation. No uniform convergence rate is asserted over this class.

### 2. Finite array bound with supplied log-variance accuracy

For any n≥1, real arrays x_j,a_j,e_j (j=0,…,n), beta∈ℝ and nonnegative
V_time,epsilon_L satisfying

    Σ_{j=1}^n |a_j−a_(j−1)|≤V_time,
    |e_j|≤epsilon_L,
    lhat_j=a_j+beta x_j+e_j,

write d_j=x_j−x_(j−1), and define

    Q_grid=Σ d_j²,    w_grid=max_j |d_j|,
    H_grid=|d_1|+|d_n|+Σ_{j=1}^{n−1}|d_j−d_(j+1)|,
    C_grid=Σ (lhat_j−lhat_(j−1)) d_j.

If Q_grid>0, set beta_hat=C_grid/Q_grid and

    r_grid=(V_time w_grid+epsilon_L H_grid)/Q_grid.

Then

    |beta_hat−beta|≤r_grid.                         (3)

For each fixed nonconstant x array and beta, the numerator bound in (3)
is attained by some a,e satisfying the displayed constraints. This
sharpness is only over finite arrays, not over diffusion observation laws.

Consequently, on the stated accuracy event, beta≤0 implies
beta_hat≤r_grid, whereas beta>2r_grid implies beta_hat>r_grid. If the
arrays are measurable data and an accuracy event has probability ≥1−delta
uniformly over a specified null, rejecting only when Q_grid>0 and
beta_hat>r_grid has size ≤delta. The analogous power bound for an
alternative is

    P(reject) ≥ 1−delta−P(Q_grid=0 or beta≤2r_grid),  (4)

provided its accuracy event also has probability ≥1−delta. These are
conditional implications: this claim supplies no lhat or error-coverage
event from discrete prices. At Q_grid=0 define no estimate and do not
reject. For sampled a_time, the path variation bound implies the array
bound. In the exact log-variance oracle case epsilon_L=0, the only
displayed error cost is V_time w_grid/Q_grid.

## Proof

AX-13 gives [X]_t=∫₀ᵗv_u du: M is the supplied Brownian integral and B
is continuous finite variation. On every path in the common full-measure
set, continuity of a_time and X makes v continuous and strictly positive
on the compact interval. Its integral is finite, strictly positive for
T>0 and continuously differentiable with derivative v, by the fundamental
theorem of calculus. This gives the first two lines of (2).

L=a_time+beta X, so

    L±X = (beta±1) M + (a_time+(beta±1)B).

The term in parentheses on the right is continuous finite variation. The
martingale part is the Brownian integral with integrand
(beta±1)sqrt(v), which satisfies the same local square-integrability
condition. Apply AX-13 to each process (including its initial constant):

    [L±X]_T=(beta±1)² Q(T).

Polarization and ((beta+1)²−(beta−1)²)/4=beta give (2); division is
legitimate since Q(T)>0. A finite intersection of the supplied
full-measure sets suffices. This uses the cited stochastic result, not a
new construction of quadratic variation. Differentiating log sigma in
log s gives 1+beta/2. The Lipschitz variation bound follows by summing
L_time(t_j−t_(j−1)) over an arbitrary partition and taking the supremum.

For (3), expand C_grid−beta Q_grid. The a contribution is
Σ (a_j−a_(j−1))d_j, whose absolute value is at most V_time w_grid.
Finite summation by parts gives the exact error contribution

    Σ (e_j−e_(j−1))d_j
      = −e_0 d_1 + e_n d_n
        + Σ_{j=1}^{n−1} e_j(d_j−d_(j+1)).

Its absolute value is at most epsilon_L H_grid. Add the bounds and
divide by positive Q_grid. For sharpness choose k maximizing |d_k|,
set a₀=0 and all increments of a to zero except
Δa_k=V_time sign(d_k). Choose each e_j as epsilon_L times the sign of
its coefficient in the summation-by-parts expression (zero when that
coefficient is zero). The two contributions then equal their respective
nonnegative bounds. Q_grid>0 ensures w_grid>0.

On the accuracy event, (3) gives beta_hat≤beta+r_grid≤r_grid under
beta≤0. If beta>2r_grid, it gives beta_hat≥beta−r_grid>r_grid.
Thus null rejection requires failure of that event. Under an alternative,
nonrejection is contained in its failure union {Q_grid=0 or beta≤2r_grid}.
The union bound gives (4), without independence assumptions.

## Checks

`checks/071/check.py` checks the finite identities and worst-case bounds
with exact rational arithmetic, including all error-box vertices on a
small exhaustive family, sharpness, zero-budget and constant-path cases,
and sign-test implications. These are deterministic checks, not diffusion
simulations or evidence of statistical power. No experiment was run.

## Not shown

- A discrete-price construction of lhat, its uniform error probability,
  or a usable test at any finite observation frequency. True v is not
  observed on a finite price grid. Equation (3) cannot be run on prices
  alone without an additional estimation result.
- A minimax lower bound, a matching upper bound, a separation rate rho_n,
  or the requested frequency/power table. Pointwise continuous-record
  identification does not establish any of these uniform assertions.
- A universal pathwise quadratic-variation algorithm, almost-sure
  convergence on a chosen sampling sequence, or finite-sample recovery
  of Q'. Equation (2) is an identity of continuous semimartingale
  observables under the cited input, not such an algorithm.
- Global solution existence, boundary/nonexplosion guarantees, a
  transformation theorem from every proposed price SDE to (1), jumps,
  rounding/noise, or stochastic time effects with nonzero quadratic
  variation. No claim that a vol-of-vol parameter is a BV budget.
- Identification for arbitrary sigma(t,s), pricing-measure transport,
  strict-local-martingale classification, or a law-distance lower bound
  obtained by treating endogenous X as an external design.

## Prior art

Mechanism without model nouns: a continuous finite-variation perturbation
does not affect quadratic variation, and polarization extracts the
coefficient of a shared martingale component. This is an application of
AX-13 [etheridge2018continuous], Theorem 7.11 equation (42) and Proposition
6.25, already source-audited in `ledger/AUDIT_LOG.md` at 47833c0. The
specialization checks (1), positive Q, the observable density relation,
and the finite-array sensitivity are the claim; stochastic calculus is
not reproved. No new literature input is introduced.

Read the D30 input and librarian source findings in `board/FINDINGS.md`,
the disjoint-window and evaluation-selected-forecast refutations, and
the registered source at the cited passages. The local/stochastic
volatility paper [aitsahalia2025testing] remains wanted; no theorem or
rate from it is used. The prior external-design overlap calculation does
not transfer to the endogenous process in (1). A one-path interpolation
argument does not preserve the deterministic finite-variation nuisance
restriction and therefore does not refute (2).

## Review

Reviewer, 2026-10-08, on branch `mathb/d30-path-identification` at `c83a7733`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/071/`.
- **Inputs.** AX-13 ([etheridge2018continuous], Theorem 7.11 (42) and Proposition 6.25) is source-audited ok at 47833c0, and the key is registered. The claim correctly notes that the current `BracketFormula` Lean structure covers only constant shifts, so it is insufficient for part 1.
- **Script.** My check is committed as `checks/review/071/reproduce.py`, with its rerun command and seed in its header. It is single-process and is not a CI `check.py`.

**Part 1 (the continuous-record identity): correct.**
- **The quadratic variation.** X = M + B with M the Brownian integral and B continuous finite variation, so AX-13 gives [X] = ∫v. Since v is continuous and positive, Q is C¹ with Q′ = v, and Q(T) > 0.
- **The bracket.** L ± X = (β ± 1)M + (a_time + (β ± 1)B). The second term is continuous finite variation, because a_time is deterministic, continuous and of bounded variation. Hence [L ± X] = (β ± 1)²Q, and polarization gives [L, X] = βQ.
- **The elasticity.** It is p = 1 + β/2.
- **The scope.** The deterministic BV budget's size does not enter, as stated. A stochastic time effect with nonzero quadratic variation would add a bracket term and break identification, and is excluded.

**Part 2 (the array bound): correct.**
- **The decomposition.** Δl̂ = Δa + βd + Δe, so C − βQ = ΣΔa·d + ΣΔe·d.
- **The a term.** |ΣΔa·d| ≤ w·Σ|Δa| ≤ Vw.
- **The e term.** Summation by parts gives ΣΔe·d = −e₀d₁ + e_n d_n + Σe_j(d_j − d_j+1), so its absolute value is at most εH.
- **Sharpness.** One a-jump of size V·sign(d_k) at the largest |d|, plus e at the coefficient signs, attains both bounds with the same sign.
- **The tests.** The sign-test size and power implications follow from (3) and the union bound.

**Checks** (evidence, not proof).
- **(a) The array bound.** On 2,000 random arrays (3) always held. Summation by parts holds to 5×10⁻¹⁵, and the sharpness construction attains Vw + εH to 1.5×10⁻¹⁴.
- **(b) The identity (2) by simulation.**
  - **Setup.** Euler at 2¹⁶ steps on [0, 1], with β = 1.5, a_time = log 0.09 + 0.5 sin 2πt (TV = 2) and zero price drift. Brackets on coarser grids, with 200 paths.
  - **Result.** Medians:

  | n | Oracle log variance: β̂ (r_grid) | Log-variance error ε_L = 0.05: β̂ (r_grid) |
  |---|---|---|
  | 256 | 1.501 (1.36) | 1.494 (4.3) |
  | 1,024 | 1.500 (0.78) | 1.473 (6.6) |
  | 4,096 | 1.500 (0.45) | 1.542 (12.1) |
  | 16,384 | 1.500 (0.24) | 1.527 (23.4) |

  - **Reading.**
    - **The oracle.** With exact log variance, β̂ recovers β at every grid, and the radius V·w/Q shrinks roughly like n^{−1/2}.
      - **What 0.24 is.** On this simulated design (a time effect of total variation 2, about one year of 5-minute data), the **median over paths** of that worst-case radius is about ±0.24 in β, or ±0.12 in elasticity.
      - **What it is not.** It is an empirical median of an upper bound on this model and grid, not a universal lower bound on achievable resolution.
    - **A scope point the claim's "Not shown" implies but does not state numerically.** With a log-variance error of fixed size on the *same* grid used for scoring, the radius **grows** with that grid's size, about as √n. That is because H = |d₁| + |d_n| + Σ|d_j − d_j+1| grows with the number of increments while Q does not.
      - **Corrected 2026-10-08, per mathb's note.** My original reading here, "a usable test only if ε_L shrinks faster than n^{−1/2}", extrapolated too far.
      - **Why.** Since |d_j − d_j+1| ≤ |d_j| + |d_j+1|, H_m ≤ 2Σ|d_j| ≤ 2√(m·Q_m) on any scoring grid of m increments, by Cauchy–Schwarz. The proved bound (3) can therefore be applied on a coarser subgrid of m increments, with log variance estimated from N ≥ m fine observations. Its error term is then at most 2ε_N√m/√Q_m.
      - **What that requires.** Sufficient control involves ε_N√m, not necessarily ε_N√N. Under the separately supplied positive-Q and estimation hypotheses, slower accuracy can suffice on a slower-growing subgrid.
      - **Evidence.** My simulation (b) scored on the same grid it used for log variance, so it shows the finest-grid behaviour and does not bound the coarse-grid route. Mathb's exact algebra is in `checks/d30-coarse-recovery/check.py`, which I ran and which passes.
      - **What still holds.** The finite-array verification and the numbers above stand, and no estimator l̂ or rate is supplied by the claim.
- **The author's check.** I ran `checks/071/check.py` afterwards. It passes 69,744 exact array cases, the noise extrema, sharpness, the sign implications and polarization.

**Gaps.** None.

**Scope; "Not shown" is honest.** No discrete-price l̂, error-coverage event, minimax rate or frequency/power table is supplied. Part 1 is a continuous-record identification statement, not a test, and global existence of (1) is a premise. My (b) shows that the missing estimator's accuracy must improve with frequency for part 2 to bite.

Verdict: red-passed

## Formalization notes

Approved 2026-10-08 by pm: Red re-derived the quadratic-variation bracket identity giving elasticity 1 + beta/2 under a deterministic BV time effect, the summation-by-parts array bound and its sharpness, and the sign-test implications; committed review script; estimator-accuracy scope stated


Formalized in `lean/Standalone/D30BVIdentification.lean`, with
`statement_holds` in `lean/Novel/D30BVIdentificationProof.lean`.
Both the continuous-record identity and the finite-array conclusions
are proved. The continuous-record part remains conditional on the
supplied representation and AX-13: `D30BVIdentificationBridge.lean`
derives the restated input from `Upstream.SemimartingaleQV.qv_integral`
and the proved finite-variation-only case `qv_fv`. Quadratic variation
is encoded by convergence in probability of squared-increment sums
along every partition sequence whose mesh tends to zero. The new
Upstream structure covers the continuous finite-variation addition;
the narrower `BracketFormula` is unchanged. The supplied one-point
`SemimartingaleQV` instance is **vacuous**, because that base admits no Brownian motion,
with the rule-6 convention checks recorded below. No genuine Brownian
model is constructed in Lean. The finite-price estimator, error coverage
from prices, and minimax rate remain unproved as stated in "Not shown".

Formalizer B, 2026-10-08, on `formb/d30-bv-identification`. **Stage 1: statement and proof, conditional on AX-13 restated. Status stays approved** until AX-13's Upstream structure carries Proposition 6.25 and the bridge is proved; I have asked formalizer for that field.
- **Files.** The statement is in `lean/Standalone/D30BVIdentification.lean` (`statement := identity ∧ elasticity ∧ lipschitz ∧ arrayBound ∧ sharp ∧ decision ∧ test ∧ sampled ∧ oracle`). The proof is `lean/Novel/D30BVIdentificationProof.lean`, with:
  - `D30BVIdentificationIdent.lean`: part 1;
  - `D30BVIdentificationArray.lean`: part 2 and the deterministic remarks.

  There is no `sorry`, and the axiom audit is clean.
- **The cited input.** `AX13` restates the ledger's Brownian form. Quadratic variation is Proposition 6.25's realized form, `QVat`: sums of squared increments along every partition sequence of `[0, t]` with mesh tending to zero converge in probability.
  - For `Y = c + K•W + F`, with `F` continuous, adapted and of finite variation on `[0, T]`, `[Y]_t = ∫₀ᵗ K²`.
  - For `Y = c + F`, `[Y]_t = 0`.

  The stochastic integral is a relation, quantified over. No stochastic calculus is rebuilt.
- **Part 1.** Under the supplied representation (1) on `[0, T]`, `[X]_t = ∫₀ᵗ v` and `[L ± X]_T = (β ± 1)² ∫₀ᵀ v`. For every continuous version of `[X]` and every version of `[L ± X]_T`, almost surely and simultaneously in `t ≤ T`:
  - `Q(t) = ∫₀ᵗ v`, and `Q(T) > 0`;
  - `Q` has one-sided derivative `v` on `[0, T]`, with `L = log Q'`;
  - `[L, X]_T = β Q(T)`, so `β = [L, X]_T / Q(T)`.

  Also `d log σ / d log s = 1 + β/2`, and a Lipschitz `a_time` has variation at most `L_time T`.
  - **Proof.** Uniqueness of realized quadratic variation (limits in measure), and its `κ²` scaling. `L ± X = a_time + (β ± 1)(M + B)` on `[0, T]`, with `a_time` frozen after `T`. The `β ± 1 = 0` case uses the finite-variation clause. Simultaneity in `t` comes from rational times and continuity.
  - **Encoding.** The integrand `√v` is a process on all times; a representation on `[0, T]` extends by freezing `v` after `T`.
- **Part 2.**
  - (3), by summation by parts: `C − βQ = Σ Δa·d + Σ_j e_j c_j`, with `Σ |c_j| = H`.
  - Sharpness for every nonconstant `x`.
  - The decision rule.
  - The size bound and (4) for measurable random arrays whose accuracy event has probability at least `1 − δ`.
  - The sampled-path constraint (assuming `V_time ≥ 0`, as declared).
  - The oracle case.

Formalizer B, 2026-10-08, on `formb/ax13-fv-field`. **Stage 2. Status: formalized.**
- **AX-13's Proposition 6.25 part** is now an Upstream structure, `lean/Upstream/SemimartingaleQV.lean`, field `qv_integral`. It covers the Brownian integral plus a continuous finite-variation term, in the realized-quadratic-variation form. Its instance is vacuous on the one-point base, with convention checks, and the ledger's `Formal:` paragraph says so. `BracketFormula` is unchanged.
- **Bridge.** `Novel/D30BVIdentificationBridge.lean`, `ax13_of_upstream`, derives the statement's restated `AX13` from that structure. The finite-variation-only clause is proved, not assumed (`qv_fv`): `Σ (ΔF)² ≤ max |ΔF| · V(F) → 0` by uniform continuity.
