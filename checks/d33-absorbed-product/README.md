# D33 input: independent absorbed factors

This is preparation for the remaining two-asset application, not a new claim.
Claims 074 and 075 currently occupy mathb's two-ahead allowance. The mechanism
is independence and integration of nonnegative products, already available in
Mathlib's `Probability/Independence/Integration.lean`, followed by the scalar
classification. No stochastic product rule is imported or reconstructed here.

Take two independent scalar models under the **same declared pricing law** Q.
Each meets claim 001's hypotheses, with a nonnegative constant exposure as in
claim 074. Independence is of the full price/exponential systems, not a sample
correlation estimate. Write their normalized exponential factors as Z₁,Z₂ and
specify the all-time wealth representation

    V^(12)_t = v₀ Z₁,t Z₂,t,  v₀>0.

Each factor retains its own source exit convention. No reciprocal price is
evaluated after absorption. A zero factor makes the product zero thereafter;
an unexposed name has factor one, even after its price defaults. This is a
specified wealth representation, not a proof that trading holdings implement
it. A separate joint local-martingale justification is required before calling
the product strict or a martingale. In particular, independence does not grant
permission to silently enlarge the filtration with future information.

## Finite-horizon means and defect

Let m_i^Z(T)=E_Q[Z_i,T] and δ_i^Z(T)=1−m_i^Z(T). Each mean lies in [0,1].
Independence and Tonelli give

    E_Q[V^(12)_T]/v₀ = m_1^Z(T)m_2^Z(T),
    1−E_Q[V^(12)_T]/v₀ = δ_1^Z(T)+δ_2^Z(T)−δ_1^Z(T)δ_2^Z(T).

The product mean equals one iff both scalar means equal one. If the product is
supplied as a nonnegative continuous local martingale in the joint filtration,
AX-06 supplies its supermartingale property, and preservation of mean is then
equivalent to martingality on [0,T]. Thus its candidate finite-horizon
classification is the conjunction of the two scalar tests:

- π_i=0: no endpoint condition;
- 0<π_i<1/2: I₀,i=∞;
- π_i=1/2: no endpoint condition;
- π_i>1/2: I∞,i=∞.

Every failed scalar condition gives a positive product defect at every T>0.
For σ₁=1, π₁=1/4 and σ₂(x)=x, π₂=1/4, both underlying prices are true
martingales but the first wealth factor is strict by claim 001, so the product
mean is below one. This retains the zero-endpoint obstruction. It does not
produce an unconditional two-asset process theorem without the joint premise.

## Tail comparison for the infinite-horizon question

Suppose first both factor means are one at every time. For independent
nonnegative mean-one variables X,Y, set T_X(K)=E[X 1{X>K}], and similarly for
Y and XY. For any K>0,

    T_X(K) ≤ 2 T_XY(K/2),
    T_Y(K) ≤ 2 T_XY(K/2),
    T_XY(K) ≤ T_X(sqrt(K)) + T_Y(sqrt(K)).

For the first inequality E[Y 1{Y≥1/2}]≥1/2 because
E[Y 1{Y<1/2}]≤1/2. Independence then bounds
T_X(K)/2 by E[XY 1{X>K,Y≥1/2}], which is at most T_XY(K/2).
Interchange X,Y for the second inequality. For the third, {XY>K} is contained
in {X>sqrt(K)}∪{Y>sqrt(K)}; factor the two resulting expectations and use
E X=E Y=1. These are elementary integral inequalities, not a new stochastic
uniform-integrability theorem.

Taking suprema over t and then K→∞ proves that the product family is uniformly
integrable iff both factor families are, **when their means are one**. If the
product is a uniformly integrable martingale started at one, its mean is one;
the finite-horizon identity forces both factor means to be one. Scalar
nonnegative local-martingale structure then makes both factors martingales,
and the first two bounds give uniform integrability of each. Claim 074 excludes
this whenever either exposure is positive. Conversely, two zero exposures give
constant wealth. Thus the proposed independent-product application has the
same zero-only infinite-horizon answer, with no inference that a strict local
martingale's family alone must fail uniform integrability.

## Scope and checks

This does not classify correlated assets. The interior covariance calculation
in the D33 finding still contains 2ρ_12 π₁π₂σ₁σ₂/(S₁S₂); the independent
mean factorization cannot be used when that independence hypothesis fails.
Nor does killing the whole two-dimensional model at the first boundary prove
the above all-time factor representation. Before filing the final claim,
either justify its joint local-martingale and wealth representation from an
already audited input, or keep them plainly conditional and state the omitted
trading construction. A raw stochastic product rule is not presently a field
of AX-14 and must not be attributed to it without a source audit.

`check.py` exhaustively checks the moment and tail inequalities on exact finite
product laws, mean-defect algebra, dependence failures and zero-factor
bookkeeping. These fixtures have no Brownian or diffusion interpretation and
are not experimental observations or a proof of the stochastic premises.
