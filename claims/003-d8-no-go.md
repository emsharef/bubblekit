---
id: 003
title: "Finite-price tests have power at most uniform size; bubble identified sets depend on the observation law"
status: formalized
depends_on: [002]
axioms_used: [AX-04, AX-05, AX-06, AX-11]
formal: lean/Standalone/D8NoGo.lean
direction: D8
---
## Statement

This result is **conditional on AX-04, AX-05 and AX-06**, and the exactness of the
canonical formula (2) also on AX-11. Their source audits passed in
`ledger/AUDIT_LOG.md` (AX-04–AX-06 against c7770d7, AX-11 against 025b24d); their
Lean structures and instances are in `lean/Upstream/` and audited. Claim 002 is used only for the coefficient-completion
comparison in part 4, not for the statistical argument.

### 1. Observation and testing quantifiers

Fix s₀ > 0, a finite T > 0 and a positive integer k. Prices are discounted and
have no dividends. Let E_T be the Borel space of finite continuous nonnegative
paths on [0,T] starting at s₀, with the uniform topology. An admissible model M
consists of a usual filtered probability space, a physical probability P, a pricing
probability Q equivalent to P on F_T, and an adapted nonnegative continuous
Q-local martingale S with S₀ = s₀. Processes and filtrations are held constant
after T when using infinite-time definitions. The class includes all such models,
including stopped or frozen prices; no coefficient form, tail bound, or uniqueness
of Q is imposed.

Observe k independent copies of S|[0,T] under P. A randomized test is a Borel map
φ : E_T^k → [0,1], its value being the probability of rejection. A fixed finite
sampling grid, or any measurable observation from these paths, is included by
composition. H₀ comprises the models in which S is a true Q-martingale on [0,T];
H₁ comprises those in which it is strict on that interval. Define

    size(φ) = sup_{M ∈ H₀} E_{P_M^⊗k}[φ(S¹,…,Sᵏ)].

Then

    for every M ∈ H₁, E_{P_M^⊗k}[φ(S¹,…,Sᵏ)] ≤ size(φ).       (1)

Thus a bound ε ∈ [0,1] on uniform null size bounds power at **every** alternative,
not just the infimum alternative power. The bound is sharp, attained by φ ≡ ε.
At each sample size the same statement applies to tests with finitely many paths
or observations. Consequently, for fixed T, limsup uniform null size ≤ ε implies
limsup power ≤ ε at each fixed alternative, even as the number of paths grows.
This does not assert the same conclusion for merely pointwise-null asymptotic size.

### 2. Monetary and maturity-curve identified sets

The monetary parameter here is the **unconditional** defect
b_T = s₀−E_Q[S_T]. When initial information is trivial this is β₀(T) at zero rates
and dividends. Conditional values given nontrivial initial or later information
are not the target of this claim.

Identification concerns an observation law, not a realized sample. Fix a physical
path law P on E_T and use the canonical price and its usual natural filtration.
There are no additional traded assets or restrictions on the pricing kernel. Set

    M(P) = {Q ∼ P : S is a Q-local martingale on [0,T]},
    B_T(P) = {s₀−E_Q[S_T] : Q ∈ M(P)}.                       (2)

For feasible P, meaning M(P) ≠ ∅, B_T(P) is the exact assumption-free monetary
identified set for that population observation. It is an interval contained in
[0,s₀]. More precisely, with

    m₋ = inf_{Q∈M(P)} E_Q[S_T],    m₊ = sup_{Q∈M(P)} E_Q[S_T],

its infimum is s₀−m₊ and its supremum is s₀−m₋; it contains all intermediate
points and includes each endpoint exactly when the corresponding extremum is
attained. If the endpoints coincide the set is the resulting singleton. If
S_T > 0 P-almost surely, s₀ is excluded.

For a Borel observation map O on E_T with known population law R, the exact set is

    B_T^O(R) = ⋃_{P : O_#P = R, M(P) ≠ ∅} B_T(P).            (3)

This includes observation of a finite grid. For all maturities 0 ≤ t ≤ T,

    B_[0,T](P) = {(s₀−E_Q[S_t])_{0≤t≤T} : Q ∈ M(P)}         (4)

is the exact joint identified set of unconditional defect curves. It is convex;
each curve starts at zero and is nondecreasing. One common Q is required for all
maturities: replacing (4) by the product of its marginal sets is not justified.
Equations (2)–(4) are sharp variational characterizations, not numerical endpoints
inferred from a sample.

There is no universal answer B_T(P) = [0,s₀]. For the constant-path law, B_T(P) =
{0}. If instead the pricing law R_Q is known, the monetary set is the singleton
{s₀−∫x(T)dR_Q(x)}; knowing its terminal marginal suffices. Population point
identification under known Q therefore does not contradict (1).

### 3. Stochastic volatility with identical physical observations

There exists a finite horizon T₀ and a single physical price law P admitting two
equivalent pricing measures: one makes S true on [0,T₀], the other makes it strict.
The models have identical physical observation laws, including continuous price
observation. Thus their rejection probabilities agree exactly for every test and
finite k. For this P the binary bubble-presence identified set is exactly {0,1},
and there is b > 0 with [0,b] ⊆ B_T₀(P). Terminal prices are strictly positive, so
s₀ is excluded. No value for the supremum of this particular set is asserted.

### 4. Interpretation for confidence sets and visited coefficient ranges

Any measurable random confidence set C for b_T with coverage at least 1−ε
uniformly over the class in part 1 yields the test 1_{0∉C}. That test has power
at most ε at every alternative. This is a coverage implication, not a construction
of a sample confidence procedure.

To distinguish coefficient information from price-path information, suppose instead
that a Borel nowhere-zero coefficient σ is known exactly on [r,R], where
0 < r < c < R, with 1/σ² integrable on [r,R]. Among Borel nowhere-zero extensions
whose reciprocal square is locally integrable on (0,∞), both integrals I₀ and I∞
remain unidentified. The lower tail ∫₀ʳ x/σ² can take any value in (0,∞], and,
independently, the upper tail ∫_R^∞ x/σ² can take any value in (0,∞]. The known
pieces ∫_r^c x/σ² and ∫_c^R x/σ² are added to these respective sets. This is a
deterministic comparison, not a claim that exact knowledge of σ follows from a
realized path.

## Proof

### Bounded stopping gives the testing bound

Fix an admissible model M. For every integer n > s₀ let
τₙ = inf{t ≥ 0 : S_t > n}, with inf ∅ = ∞, and Sⁿ_t = S_(t∧τₙ).
Because S is nonnegative, this is AX-04's exit time defined using |S|. AX-04
makes Sⁿ a bounded nonnegative true Q-martingale. Keep the same P and Q and use
Sⁿ as the price; equivalence Q ∼ P is unchanged. This defines an admissible null
model Mₙ, also when observations follow P rather than Q.

Couple each original path with its stopped version on the same sample point in
the k-fold physical product space. Let Aₙ be the event that at least one original
path has supremum at least n on [0,T]. On Aₙᶜ all original and stopped paths agree
throughout that interval. Hence, pointwise,

    |φ(S¹,…,Sᵏ)−φ((S¹)ⁿ,…,(Sᵏ)ⁿ)| ≤ 1_{Aₙ}.

Integrating gives

    E_{P^⊗k}[φ(S¹,…,Sᵏ)] ≤ size(φ) + P^⊗k(Aₙ).             (5)

Every finite continuous path is bounded on the compact interval [0,T]. For finite
k, the events Aₙ decrease to the empty event up to null sets, so P^⊗k(Aₙ) → 0.
Passing to the limit in (5) proves (1). Applying the same pointwise inequality to
indicators of observation events gives total variation distance at most P^⊗k(Aₙ)
between the original and stopped observation laws, using the convention
sup_A |P(A)−R(A)|. No continuity of φ or convergence of terminal means is used.
Composition with any Borel observation map preserves the argument. Taking limsup
of (1) at successive finite sample sizes proves the stated asymptotic consequence.

This is the unobserved-tail mechanism: null modifications occur above n and the
probability of visiting that region tends to zero. An unbounded terminal price
need not have close expectations under this comparison. The argument's null
models include frozen processes; it does not prove a no-go statement within a
smaller family requiring nowhere-zero volatility everywhere.

### Identified sets and their interval structure

Every Q in (2) gives a compatible canonical pricing model. Conversely, an
admissible model with physical price law P pushes its pricing measure forward to
a probability equivalent to P. For each n, its bounded stopped price is a
martingale by AX-04. Testing its martingale identities against events in the
price's past gives the same identities in the natural price filtration. Its usual
augmentation remains a subfiltration of the original usual filtration, by right
continuity and completeness; equivalence gives the same null sets. The bounded
stopped canonical prices are therefore martingales. Their common exit times tend
to infinity pathwise when paths are extended constantly after T, so they localize
the canonical price. Its pushed-forward Q belongs to M(P), and terminal
expectations are preserved. This proves exactness of (2), even when a compatible
model has hidden factors. Union over path-law completions proves (3); retaining
one common Q proves (4).

For Q₁,Q₂ ∈ M(P) and λ ∈ [0,1], Qλ = λQ₁+(1−λ)Q₂ is equivalent to P. By
AX-04 the same Sⁿ is a bounded martingale under both Qᵢ. For 0 ≤ u ≤ t ≤ T and
every event A in the time-u sigma field,

    E_{Qλ}[1_A(Sⁿ_t−Sⁿ_u)]
      = λ E_{Q₁}[1_A(Sⁿ_t−Sⁿ_u)]
        + (1−λ) E_{Q₂}[1_A(Sⁿ_t−Sⁿ_u)] = 0.

Thus Sⁿ is a martingale under Qλ, and these exit times also localize S under Qλ.
So Qλ ∈ M(P). Terminal expectations are affine in the mixture, proving convexity
of B_T(P). Nonemptiness and the definitions of infimum and supremum give its full
interval and endpoint-attainment description. AX-06 bounds terminal expectations
between zero and s₀. Strict positivity of S_T and equivalence give E_Q[S_T] > 0,
excluding s₀ where asserted. The same mixture proves convexity of (4); AX-06 gives
monotonicity in maturity and S₀ = s₀ gives the zero initial defect.

Equivalence preserves the constant-path event, so a constant observed price forces
B_T(P) = {0}. A known pricing law fixes its terminal expectation directly. These
examples prove the claimed distinction between population identification and the
bounded-test comparison (5).

### Apply Sin's model while keeping physical observations fixed

Use AX-05 with α = κ = L = 1, γ = (1,0), a = (1,1), and deterministic s₀ > 0.
The dot product is 1 > 0, and the vectors are nonparallel since 1 < √2 = |a||γ|.
The source coefficient bounds hold with any bound exceeding √2. AX-05 supplies
a finite T₀ on which S fails to be a Qˢ-martingale, and Qᵐ_T₀ equivalent to Qˢ on
F_T₀ under which the same S is a martingale on [0,T₀]. This uses no claim of
infinite-horizon equivalence or of strictness on every positive horizon.

Choose and fix physical P = Qˢ on this horizon in both models. The null chooses
pricing Qᵐ_T₀; the alternative chooses pricing Qˢ = P. Their physical price laws
are exactly the same. The latent volatility is the same physical process too;
its two pricing drifts are respectively 1−v² and 1−v, as given by AX-05. Thus
uncertainty concerns pricing dynamics, not a different physical sample.

Write b = s₀−E_{Qˢ}[S_T₀]. It is positive: if the terminal expectation equalled
s₀, AX-06's monotone expectations would equal s₀ at all intermediate times. For
u ≤ t ≤ T₀, S_u−E[S_t|F_u] would then be nonnegative and have expectation zero,
hence vanish almost surely. This would make S a martingale on [0,T₀], a
contradiction. The two pricing measures supply 0 and b in B_T₀(P); the interval
argument supplies [0,b]. Both binary labels occur and no other binary label is
possible. AX-05 gives strictly positive terminal prices. Finally identical physical
laws give identical rejection probabilities for all finite k, without a limiting
argument. Restriction to the canonical price law preserves these statements by
the preceding bounded-stopping argument.

### Confidence implication and the two coefficient endpoints

Under a null model b_T = 0, so uniform coverage gives P^⊗k(0∉C) ≤ ε. The indicator
is a bounded test, and (1) bounds its rejection probability at every alternative.
No inference theorem with unverified hypotheses is invoked.

For the lower coefficient tail, choose p ∈ ℝ and put
σ_p(x) = σ(r)(x/r)^p for 0 < x < r, keeping the observed σ on [r,R]. This is
nonzero and has locally integrable reciprocal square on (0,r]; the observed
reciprocal square is integrable at the junction by assumption. Substitution gives

    ∫₀ʳ x/σ_p²(x) dx
      = (r^(2p)/σ²(r)) ∫₀ʳ x^(1−2p) dx
      = r²/[2(1−p)σ²(r)]  if p < 1,
      = ∞                 if p ≥ 1.                       (6)

Every prescribed finite a > 0 is obtained by
p = 1−r²/(2aσ²(r)); p = 1 gives infinity. Any admissible tail has positive
integral, since its integrand is everywhere positive; zero cannot be attained.
After choosing this lower completion, it supplies σ on (0,R] with the hypotheses
of claim 002. That claim supplies any independent positive finite or infinite
upper tail without changing the already fixed lower part. Adding the known
middle integrals proves part 4. Continuity or equality of stochastic observation
laws is not required or asserted for this coefficient calculation. The difference
between (0,R] in claim 002 and [r,R] here is essential before applying claim 001's
lower-endpoint criterion in later D1/D9 work.

## Checks

No numerical experiment is used as a proof, and no stochastic simulation is needed
for the bounded-test inequality. The author checked the limiting cases φ ≡ ε,
k = 1, and the constant-price law directly in the argument. In (6), p = 0 gives
r²/(2σ²(r)), while p = 1 gives logarithmic divergence; the inverse choice of p
above recovers each prescribed positive finite value exactly. These are analytic
checks by the author, not an independent review. Branch CI checks repository
consistency and builds the conditional Lean statement and proof listed below.

## Not shown

The stochastic inputs AX-04–AX-06 and AX-11 are cited, source-audited hypotheses,
not project proofs; their Lean instances are vacuous or degenerate. This
formalized claim remains conditional on those inputs. It does not prove a
no-go result in a smaller model family excluding stopped prices; determine the
numeric supremum of Sin's monetary set; give a converse characterization of all
feasible maturity curves; identify conditional bubble values with nontrivial
initial/later information; or construct a confidence procedure or the D3/D4/D9
restrictions. Arbitrary extra option data and unbounded observation horizons are
outside the testing statement. The abstract statistical impossibility is not
claimed as a new general theorem. A universal numeric identified interval is
false, as the constant-price example shows; equations (2)–(4) are the precise
law-dependent replacement.

## Prior art

Mechanism without the model's nouns: a null approximation that agrees with an
alternative observation with probability tending to one forces every bounded
test's alternative expectation below its supremum null expectation. Before
proposing this claim, the registered sources and the project's Lean files were
searched for the general input. [hulley2019weak] Section 2 / Lemma 2.1 supplies
bounded stopping (AX-04); the new step is its application to this observation
experiment. The expectation comparison is an integrated pointwise inequality,
not a reconstruction of stochastic stopping theory. [mijatovic2010martingale]
Discussion following (9) and [hulley2019weak] supply AX-06. The stochastic inputs
are represented by Upstream hypothesis structures; their instances do not
discharge the hypotheses on general probability spaces.

[jarrow2011detect] Section 1 (printed p. 3) and Section 5 (printed p. 12) already
state the volatility-tail obstruction as the extrapolation problem. Claim 002
is its reviewed exact upper-tail coefficient version. Equation (6) records the
lower endpoint missed when the observed range is [r,R]; the testing argument
explicitly distinguishes coefficient observation from price-path observation.

The open Cornell report [sin1995complications], Theorems 3.2 and 3.6, already
constructs the true/strict pricing-measure example. Its nonparallel-vectors
qualification is preserved in AX-05. We apply that example to the same physical
observation law, not re-prove Girsanov or explosion results. The wanted journal
version [sin1998complications] is not substituted for the report actually read.
[chernozhukov2007estimation] supplies the identified-set framework; no confidence
conclusion from it is used without its own hypotheses. The wanted source
[bahadur1956nonexistence] may anticipate the abstract testing conclusion and is
not used as a theorem. The source search found Sin's original Cornell report,
then checked its displayed theorem pages against the PDF; no claim of exhaustive
novelty for statistical impossibility is made.

## Review

Reviewer, 2026-10-06, on branch `math/d8-no-go` at `acf0c50`. I re-derived each part before reading the author's proof. I checked the cited inputs against `ledger/AXIOMS.md`: AX-04, AX-05 and AX-06 each have an `ok` source-audit line at `c7770d7`, and their Lean structures do not exist, as the claim says. Claim 002, the one dependency, is approved. My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1 (testing bound): correct.**
- **The stopped model is a null.** For any admissible M and n > s₀, Sⁿ is continuous and bounded by n, so it is a bounded Q-local martingale and hence a martingale (AX-04). With the same P and Q, Mₙ is an admissible null.
- **The coupling.** It is pathwise on the k-fold product space, so φ(S) and φ(Sⁿ) differ only on Aₙ, which gives (5). Using "≥ n" in Aₙ against "> n" in τₙ is conservative.
- **The limit.** P^⊗k(Aₙ) ↓ 0 because continuous paths on [0,T] are bounded and k is finite. No continuity of φ is needed.
- **The quantifiers.** "power ≤ uniform size at every alternative", sharpness at φ ≡ ε, and the limsup consequence all hold as stated. So does the explicit non-claim for pointwise-null asymptotic size.
- **Simulated illustration** (evidence, not proof). I used S = 1/R with R a 3-d Bessel process from 1 (σ(x) = x², strict), T = 1, a 500-point grid, 10⁵ paths, and an arbitrary bounded path test. Its simulated E S₁ = 0.682 matches the exact 2Φ(1) − 1 = 0.6827. In every case |E φ(S) − E φ(Sⁿ)| ≤ P(Aₙ), with P(Aₙ) = 0.119, 0.071, 0.026 and 0.008 at n = 3.5, 5, 10 and 20.

**Part 2 (identified sets): correct.**
- **Exactness of (2).** A bounded stopped price that is a martingale in a larger filtration is a martingale in its own natural filtration by the tower property. The τₙ are hitting times of an open set by a continuous process, so they are stopping times of the right-continuous augmentation. Equivalence on F_T passes to the pushforwards. So every compatible model, hidden factors included, lands in M(P) with the same terminal mean.
- **Convexity.** The localizing τₙ are defined pathwise, independently of the measure, so the same sequence localizes S under Q₁, Q₂ and Q_λ. The mixture identity is then linear, and B_T(P) is the affine image of a convex set. The endpoint description, the bound [0, s₀] (AX-06), and the exclusion of s₀ when S_T > 0 follow.
- **The maturity curve (4).** It requires one common Q. It is convex, starts at 0, and is nondecreasing by AX-06.
- **The examples.** The constant-path law gives {0}, and the known-Q case is a singleton.

**Part 3 (Sin's model): correct, given AX-05.**
- **Parameters.** α = κ = L = 1, γ = (1,0), a = (1,1) give a·γ = 1 > 0 and |a||γ| = √2 > 1, so the vectors are nonparallel. The volatility drifts are 1 − v² under Qᵐ (κL − (a·γ)v^{1+α}) and 1 − v under Qˢ (κ(L − v)), as stated.
- **Strictness is filtration-free.** It is witnessed by E_{Qˢ}[S_{T₀}] < s₀, which does not depend on the filtration. So the strict label survives restriction to the canonical price filtration. The b > 0 argument (equal expectations make a supermartingale a martingale) is right.
- **Same physical law.** Fixing P = Qˢ in both models makes the physical laws identical by construction. The rejection probabilities therefore agree exactly for every k, and {0,1} and [0,b] ⊆ B_{T₀}(P) follow.
- **The horizon is not strengthened.** The claim correctly keeps AX-05's "some finite T₀" and does not upgrade it to every horizon.

**Part 4: correct.**
- **The confidence-set implication.** Uniform coverage gives size ≤ ε for 1_{0∉C}, so the coverage implication follows from (1).
- **Equation (6).** I checked it symbolically. ∫₀ʳ r^{2p}σ(r)⁻² x^{1−2p} dx = r²/(2(1−p)σ²(r)) for p < 1, with sample values p ∈ {−3/2, 0, 1/2}. The integral diverges logarithmically at p = 1, and p(a) = 1 − r²/(2aσ²(r)) returns exactly a.
- **Admissibility.** The completion keeps 1/σ_p² locally integrable on (0,∞).
- **Combining with claim 002.** Applying claim 002 after fixing the lower part gives the independent upper tail. This is the "realistic observation" gap I flagged in the claim 002 review, and it is now closed.

**Gaps.** None.

**Scope.** "Not shown" is honest. Two points a reader should carry:
1. **The null family includes frozen prices.** The testing bound uses them, so (1) as proved says nothing about a null family restricted to, say, driftless local-volatility diffusions with nowhere-zero σ (the JKP setting). The claim says this. The restriction looks removable in that family with P = Q. Replace σ above n by the linear tail σ(n)x/n: the result is a true martingale by AX-03, and its law agrees with the original's up to the exit time above n by uniqueness in law. The same coupling-in-law bound then applies. That needs a registered uniqueness-in-law input (Engelbert–Schmidt), and it is a candidate next claim, not a gap in this one.
2. **"Assumption-free" means the class of part 1.** The no-go is exactly what structural restrictions (D3, D4, D9) must break. Any positive-power test must rule out the stopped-price nulls or the hidden-pricing-measure nulls of part 3.

**Prior art the claim does not mention.** [jarrow2007complete] says in its abstract and in §1.1 (ii) that bubbles "can be born in incomplete markets", and it defers incomplete-market bubbles to a companion paper. That companion, [jarrow2007asset], is registered as `wanted` with no text. It likely states the measure-dependence that parts 2–3 make exact (same physical law, different local-martingale measure, different bubble). It should be read before the paper presents part 3 as more than an exact application of [sin1995complications]. Neither omission affects correctness. Bahadur–Savage remains wanted and unread, as the claim says.

**No contradiction with merged claims or the paper.** Part 4 sharpens claim 002 to two endpoints, and part 3 bears on D1's open stochastic-volatility question as far as identification goes, as the roadmap intended.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived all four parts (stopping coupling, convexity via pathwise localization, Sin parameters, lower-tail integral) with simulation; AX-04..06 audited ok; scope honest incl. frozen-price nulls


The statement is in `lean/Standalone/D8NoGo.lean` and its proof is
`lean/Novel/D8NoGoProof.lean`, including formula (2) and canonical exactness.
AX-04–AX-06 and AX-11 remain explicit cited hypotheses: the general-base
requirements are not discharged by their degenerate or vacuous instances.
Sin's example remains conditional on a solution of its system; existence of
that solution is not supplied by the Lean interface. The formalizer's entries
below detail the proved implications and their encodings.

Formalizer, 2026-10-06, on `form/d8-no-go` (the AX-04–AX-06 structures are merged; this branch also makes AX-05's solution conventions hold on every path, which part 3's models need, with a re-audit note to the auditor). The statement is in `lean/Standalone/D8NoGo.lean` and the proof in `lean/Novel/D8NoGoProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean. The gap this entry first recorded (formula (2)) is closed by the next entry.

- **Formalized, conditional on AX-04 and AX-06** (restated in the statement file and derived from their `Upstream` structures by `ax04_of_upstream` and `ax06_of_upstream`):
  - Part 1: (1) at every model, sharpness at φ ≡ ε, and the limsup consequence for tests on k paths. The proof is the coupling with the price stopped above n, a null by AX-04; the event of leaving [−n, n] on [0,T] has probability tending to 0.
  - Part 2: on the exact identified set (defined below), the interval property, inclusion in [0, s₀], exclusion of s₀ under a positive terminal price, (3) as a union, and (4): convex, starting at 0, nondecreasing, one common Q. Also the constant-path law gives {0}, and a known pricing law fixes the defect.
  - Part 3: from one law with a strict and an equivalent true-martingale pricing measure, identical observation laws and rejection probabilities, label set {0,1}, [0, b] ⊆ B with b > 0, and s₀ excluded. `part3_of_sin` supplies this configuration from `Upstream.SinPricingMeasures` (vacuous instance) for any solution of Sin's system with D8's parameters. The solution's existence is in AX-05's prose and is not a field.
  - Part 4: the confidence-set implication, and both coefficient tails ranging independently over (0,∞] × (0,∞] given σ on [r,R], with the known middle pieces added. The lower tail is (6); the upper tail reuses claim 002.
- **Encodings.** Tests are measurable on (Icc 0 T → ℝ)^k with the product σ-algebra. This equals the Borel tests on continuous paths, because the uniform Borel σ-algebra on C[0,T] is the trace of the cylinder σ-algebra. "Q-local martingale on [0,T]" means S stopped at T is a local martingale. Uniform size is a supremum over null models on sample spaces in one universe.
- **How convexity is proved.** The claim mixes pricing measures on one space with a common localizing sequence of exit times. In Lean that would need exit times to be stopping times, which Mathlib proves only in discrete time. The formalization instead mixes two whole models on their disjoint union (filtration, measures, localizing sequences), so no hitting-time theory is used.
- **Decision (human, 2026-10-06): option (b).** The stopping-time fact enters as a cited input. The formula (2) stage is held until its ledger entry is on main (`board/inbox/formalizer/2026-10-06-claim003-formula2-stage.md`). Parts 1–4 as described above are merged (`form/d8-no-go`).

Formalizer, 2026-10-06, on `form/d8-formula2`: formula (2) and its exactness, closing the gap above. **Status: formalized.** The statement gains one conjunct, conditional on AX-04 and AX-11 (AX-11 is restated as `AX11` and derived from `Upstream.ContinuousHittingTimes` by `ax11_of_upstream`).
- **Encoding of (2).** `PathSpace s₀ T` is E_T: continuous nonnegative paths on [0,T] from s₀, with the trace of the product σ-algebra. A path law is a probability `P` on it. The canonical sample space is E_T with its `P`-completed σ-algebra, and `canonFiltration P` is the usual natural filtration: 𝓕_t = ⋂_{s>t} σ(𝓕⁰_s ∪ 𝒩), with 𝓕⁰ the natural filtration of the coordinate price and 𝒩 the `P`-null sets. `MP P` is M(P): probabilities equivalent to the completed `P` on 𝓕_T under which the coordinate price stopped at T is a local martingale. `BT P` is (2) and `BCurve P` is (4).
- **Exactness.** For every probability `P` on E_T, `IdSet (P ∘ val⁻¹) = BT P` and `CurveSet (P ∘ val⁻¹) = BCurve P` (`idSet_eq_BT`). This holds for all P, not only feasible ones; when M(P) = ∅ both sides are empty. (⊆): `canonModel` is admissible. (⊇): the path map of a compatible model is measurable into the completed space, because usual conditions make the model complete. It pulls 𝓕_t into the model's filtration, using right-continuity and 𝒩 ⊆ 𝓕₀. The pushed-forward Q is localized by the canonical exit times, which are stopping times by AX-11, and is a martingale on each stopped piece by AX-04 on the model. Terminal and intermediate means are preserved.
- **Completeness of the reduction.** Every physical law with a nonempty identified set is `P ∘ val⁻¹` for a path law P (`feasible_law`), and (3) holds as a union over feasible path laws P with O_#P = R (`idSetObs_eq_BT`). The canonical conjunct is stated for sample spaces in `Type`, the universe of E_T.
