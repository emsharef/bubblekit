# D32: a smoothness input for the registered three-name basket

This input addresses the actual-model smoothness gap in experiment 046. It
uses the supplied independent AX-54/55 terminal laws and existing dominated
differentiation of integrals, not new stochastic theory. Mathlib already has
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` in
`Analysis/Calculus/ParametricIntegral.lean`. This is a pre-claim mathematical
input, not a formalized theorem or a change to the registered test.

## Conditional-moment formula

Let S_1,S_2,S_3 have the registered independent Q laws at T=1, with starts
one: reciprocal Bessel at kappa=.4, and GBM at volatilities .25 and .35.
All three are strictly positive. Put A=S_1+S_2, I=A+S_3, and let f be the
lognormal density of S_3, extended by zero for z≤0. Its log parameters are
mu=−sigma²/2 and sigma=.35. This zero extension is C1, with bounded f and f',
and f(0)=f'(0)=0: Gaussian decay in log z dominates every power of 1/z.

Fix B=[a,R]⊂(0,infinity). For x>0 and s=(s_1,s_2), with A(s)<x, set

    w(x,s) = (s_1/x, s_2/x, 1−A(s)/x),
    D(x) = E_Q[f(x−A)],
    H_F(x) = E_Q[1{A<x} F(w(x,S_1,S_2)) f(x−A)].

Here F is a coordinate w_i (degree r=1), or a coordinate product w_i w_k
(degree r=2). Expectations in these expressions involve only S_1,S_2.
The joint density and Fubini identity show that

    M_F(x) = H_F(x)/D(x)

is a version of E_Q[F(mu(T))|I=x]. Indeed integration against a bounded
Borel function of x is exactly integration against the product terminal
law after the substitution s_3=x−s_1−s_2. Also D(x)>0 for x>0, since
Pr(A<x)>0 and f is strictly positive on the positive half-line.

For A<x, 0≤F≤1. Each |partial_x w_i|≤1/x and hence
|partial_x F|≤r/x. At the moving boundary A=x the factor f and its derivative
are zero, so the integrand extended by zero across that boundary is C1 in x.
On a neighborhood of B contained in (0,infinity), its derivative is bounded
by a fixed multiple of sup f + sup |f'|, integrable under the probability
law of (S_1,S_2). The named dominated-differentiation lemma therefore gives

    D'(x) = E_Q[f'(x−A)],
    H_F'(x) = E_Q[1{A<x} ((partial_x F) f(x−A)+F f'(x−A))].

Thus the quotient is C1. Set

    J(x) = E_Q[|f'(x−A)|],       K_B = sup_(x∈B) J(x)/D(x).

Since 0≤M_F≤1, the quotient derivative gives the explicit estimate

    |M_F'(x)| ≤ r/a + 2 J(x)/D(x) ≤ r/a+2 K_B.            (1)

Continuity plus positive D on B makes K_B finite. No observed Monte Carlo
slope is substituted for this supremum.

## A fully specified, conservative finite constant

For the lognormal density,

    C_1 = exp(−2mu+2sigma²)/(sigma sqrt(2pi))
            * (1+1/(sigma sqrt(e)))

bounds sup_(z>0)|f'(z)|. To see this, write
u=(log z−mu)/sigma+2sigma. Then

    |f'(z)| = exp(−2mu+2sigma²)/(sigma sqrt(2pi))
                * |u/sigma−1| exp(−u²/2),

and use exp(−u²/2)≤1 and |u|exp(−u²/2)≤1/sqrt(e).
(The auxiliary u here is a real argument, not a cap weight.)

On the event S_1≤a/4 and S_2≤a/4, x−A lies in [a/2,R]. The lognormal
density increases to one mode and then decreases, so its minimum on this
interval is the smaller endpoint value. Independence gives

    d_0 = Pr_Q(S_1≤a/4) Pr_Q(S_2≤a/4) min(f(a/2), f(R)) > 0,
    D(x) ≥ d_0,        K_B ≤ C_1/d_0.                     (2)

These are population constants in the specified model. To evaluate them
without simulation, let t>0, v=.4², b=1 (the reciprocal of S_10),
z_minus=(1/t−b)/sqrt(v), z_plus=(1/t+b)/sqrt(v). AX-54's density, with
u=1/y and integration of the normal mean on a half-line, gives

    Pr_Q(S_1≤t) = barPhi(z_minus)+barPhi(z_plus)
                   + sqrt(v) (phi(z_minus)−phi(z_plus)).  (3)

Here phi and barPhi are the standard normal density and upper tail.
For S_2, its CDF is Phi((log t+.25²/2)/.25) by AX-55. Formula (3) is a
change of variables in the existing explicit kernel, not a new Bessel law;
that law and strict positivity are audited AX-54 [karatzas2015distribution].

Combining (1)–(2), all g_i=E_Q[mu_i|I=x] have bound
L_g=1/a+2C_1/d_0, and all r_ik=E_Q[mu_i mu_k|I=x] have bound
L_r=2/a+2C_1/d_0. Thus R0 has this finite bound and R1 has the same bound:
an index-only positive terminal tilt leaves conditional weight means fixed.
For a weight tilt h=1+epsilon mu_k, epsilon≥0,

    m_i(x) = (g_i(x)+epsilon r_ik(x))/(1+epsilon g_k(x)).

Its derivative, using 0≤m_i≤1 and denominator at least one, satisfies

    |m_i'| ≤ (1+epsilon)L_g + epsilon L_r.                (4)

This covers tilts on either the strict or a true name. It says nothing about
whether their coordinate pseudo-target exceeds its initial weight.

## What this resolves and what it does not

For 046's a=1.5, R=6, the explicit small-event lower bound d_0 is tiny and
L_g is enormous. The check prints its scale. Even the untilted L_g times
either registered bin width exceeds one, so inserting this constant makes
all capped cell radii one. Then the signed per-cell lower integrands are
nonpositive and that test never rejects. This proves existence of an actual
model bound, but it is not a useful calibration input for the planned power
comparison. We do not propose replacing its diagnostic input by this bound
or adding another test variant.

A useful justified bound would require a substantially sharper uniform
control of J(x)/D(x), or of the actual conditional covariance in the quotient
derivative. Pointwise quadrature of those functions still does not certify
a supremum over B. The current experiment's declared diagnostic scope is
therefore appropriate; the analytic tanh control remains a separate model.
No new claim slot, source axiom, statistical rejection rule, synthetic run,
process construction, or formalization is supplied here.
