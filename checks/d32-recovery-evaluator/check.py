"""Fixed-panel and algebra checks for the D32 evaluator. No simulation."""
from fractions import Fraction as F
from itertools import product
import math
import numpy as np
from evaluate import evaluate, evaluate_record, tilted_lipschitz


def scalar_reference(Y, U, X, edges, omega, I0, L, ar, ap):
    J, d = len(edges)-1, len(omega)
    def cell(x):
        for j in range(J):
            if edges[j] <= x < edges[j+1] or (j == J-1 and x == edges[-1]):
                return j
        return None
    assigned = [[u for y, u in zip(Y, U) if cell(y) == j] for j in range(J)]
    counts = list(map(len, assigned))
    fit = [[sum(u[i] for u in assigned[j])/counts[j] for i in range(d)]
           if counts[j] else list(omega) for j in range(J)]
    h = max(b-a for a, b in zip(edges, edges[1:]))
    radii = [min(1, L*h+math.sqrt(math.log(2*d*J/ar)/(2*n))) if n else 1 for n in counts]
    c = edges[-1]/I0*math.sqrt(math.log(2*d/ap)/(2*len(X)))
    compact, full, signed = [], [], []
    for i in range(d):
        compact.append(sum(x/I0*fit[cell(x)][i] for x in X if cell(x) is not None)/len(X))
        full.append(sum(x/I0*(fit[cell(x)][i] if cell(x) is not None else omega[i]) for x in X)/len(X))
        signed.append(sum(x/I0*(fit[cell(x)][i]-radii[cell(x)]) for x in X if cell(x) is not None)/len(X)-2*c)
    return counts, fit, radii, compact, full, [x-max(radii)-c for x in compact], signed


# Include both endpoints, an interior bin edge, both outside tails, and
# strongly imbalanced occupancies. The pricing denominator must remain M.
panels = [
    ([.5, 1, 2, 3, 4], [[.2,.8],[.4,.6],[.6,.4],[.8,.2],[.1,.9]], [.5,1,2,3,4]),
    ([1,1,1], [[.2,.8],[.4,.6],[.6,.4]], [1,1.5,2,3]),
    ([.2,4], [[.1,.9],[.7,.3]], [.5,4]),
    ([1.1,1.2,2.2,2.3], [[.2,.8],[.3,.7],[.4,.6],[.5,.5]], [1.1,2.2]),
]
for Y, U, X in panels:
    for I0, L in product((1., 2., 4.), (0., .1)):
        edges, omega, ar, ap = [1.,2.,3.], [.5,.5], .025, .025
        out = evaluate(Y, U, X, edges=edges, omega=omega, initial_index=I0,
                       lipschitz=L, alpha_reg=ar, alpha_price=ap)
        ref = scalar_reference(Y,U,X,edges,omega,I0,L,ar,ap)
        for key, expected in zip(('counts','fitted','cell_radii','theta_compact',
                                  'theta_full','global_lower','per_cell_lower'), ref):
            np.testing.assert_allclose(out[key], expected, rtol=2e-14, atol=1e-14)
        assert abs(out['sum_identity_residual']) < 1e-13
        assert out['status'] == 'diagnostic_float' and not out['certified']
        if Y == panels[0][0]:
            assert out['counts'] == [1,2]  # R belongs to the last bin
            assert out['training_outside'] == 2 and out['pricing_outside'] == 2

# A fixed occupied cell remains useful when a different cell is empty.
Y = np.full(20000, 1.5)
U = np.tile([.8,.2], (len(Y),1))
X = np.full(20000, 1.5)
out = evaluate(Y,U,X,edges=[1,2,3],omega=[.5,.5],initial_index=1.5,lipschitz=0)
assert out['counts'] == [20000,0] and out['cell_radii'][1] == 1
assert out['common_radius'] == 1
assert not out['global_reject_diagnostic'] and out['per_cell_reject_diagnostic']
assert out['contributions'][0] < 0  # never clip away the incompatible estimate
assert abs(out['sample_survival_mass']-1) < 1e-12

# Constants encode the doubled signed range; the common rule can sometimes
# give a larger lower bound, so there is no universal ordering of the rules.
out = evaluate([1,2], [[.5,.5],[.5,.5]], [3]*1000,
               edges=[1,2,3],omega=[.5,.5],initial_index=1,lipschitz=0)
assert out['sample_survival_mass'] > 1  # do not clamp observed means to null means
assert out['global_lower'][0] > out['per_cell_lower'][0]

# Exact arithmetic: derivative formula and the analytic supremum bound.
algebra = 0
for phi, eps, gmin in product((F(1,2),F(1),F(3)), (F(0),F(1),F(3)), (F(1,10),F(1,4))):
    for g in (gmin,F(1,2),1-gmin):
        derivative = 1 + eps*(1-2*g-eps*g*g)/((phi+1)*(1+eps*g)**2)
        rewritten = (phi+(1+eps)/(1+eps*g)**2)/(phi+1)
        upper = (phi+(1+eps)/(1+eps*gmin)**2)/(phi+1)
        assert derivative == rewritten and 0 < derivative <= upper
        algebra += 1
for a, A, phi in product((.4,.6,1.),(.1,.4),(.5,1.,3.)):
    assert math.isclose(tilted_lipschitz(a,A,phi,0), A/a, rel_tol=1e-14)

# Verify signed-range and integrated lower-bound algebra on fixed exact laws.
lower_cases = 0
for fit, truth, radius in product((F(0),F(1,2),F(1)), repeat=3):
    if abs(fit-truth) > radius:
        continue
    for x in (F(1),F(2),F(3)):
        signed = x*(fit-radius)
        assert -3 <= signed <= 3 and signed <= x*truth
        lower_cases += 1

# Record retention is part of the API; no invalid record becomes a success
# or disappears. Configuration errors are visible too.
base = dict(Y=[1,2],U=[[.5,.5],[.5,.5]],X=[1,2],edges=[1,2,3],
            omega=[.5,.5],initial_index=2,lipschitz=.1)
bad_updates = [dict(Y=[]), dict(Y=[math.nan,2]), dict(X=[0]),
               dict(U=[[.5,.6],[.5,.5]]), dict(U=[[-.1,1.1],[.5,.5]]),
               dict(U=[[.5,.5]]), dict(edges=[1,1,3]), dict(edges=[0,1,2]),
               dict(omega=[0,1]), dict(initial_index=0), dict(lipschitz=-1),
               dict(alpha_reg=.9,alpha_price=.2), dict(X=[math.inf]),
               dict(initial_index=1e-320)]
for update in bad_updates:
    result = evaluate_record(**(base|update))
    assert result['status'] == 'failed' and not result['certified']
    assert not result['global_reject_diagnostic'] and not result['per_cell_reject_diagnostic']

print(f'PASS: 24 scalar-reference panels; endpoints/outside/empty cells; '
      f'{algebra} exact derivative identities; {lower_cases} signed lower bounds; '
      f'{len(bad_updates)} retained failures; distinct margins and negative contributions. '
      'No simulation or numeric certification.')
