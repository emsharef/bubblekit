"""Exact finite-law composition and deterministic price arrays; no simulations."""
from fractions import Fraction as F
from itertools import product
from mpmath import mp
from scoring import score_path, module, ROOT

ranked = module('ebh055', ROOT / '053/procedure.py').ranked_discoveries


def price_checks():
    catalogue = (('0.5', '0.7'), (1, '0.7'), ('1.5', '0.7'))
    times = (0, '.2', '.4', '.6', '.8')
    comparisons = 0
    for suffix in product((0, 1, 2), repeat=4):
        prices = (1,)+suffix
        result = score_path(catalogue, times, prices, 2)
        assert result['log_e'] != mp.inf and not mp.isnan(result['log_e'])
        assert result['log_e'] <= result['log_e_old']
        if max(result['training']) == -mp.inf:
            assert result['fit'] == 0
        # No likelihood can support resurrection during evaluation.
        if any(x == 0 and y > 0 for x, y in zip(prices[2:], prices[3:])):
            assert result['log_e'] == -mp.inf
        if prices[2:] == (0, 0, 0):
            assert result['log_e'] == 0
        admissible = all(x > 0 or y == 0 for x, y in zip(prices, prices[1:]))
        if admissible and 0 in prices:
            assert result['log_e'] <= 0
        if all(x > 0 for x in prices[2:]):
            # Direct independent evaluation of each Gaussian price likelihood.
            for drift, sigma in product(map(mp.mpf, ('-.1', '.05', '1')),
                                        map(mp.mpf, ('.3', '.7'))):
                terms = []
                for j in (3, 4):
                    d = mp.mpf(times[j])-mp.mpf(times[j-1])
                    r = mp.log(mp.mpf(prices[j])/prices[j-1])
                    terms.append(-mp.log(prices[j])-mp.log(2*mp.pi*sigma**2*d)/2
                                 -(r-(drift-sigma**2/2)*d)**2/(2*sigma**2*d))
                assert mp.fsum(terms) <= result['log_gaussian']+mp.mpf('1e-40')
                comparisons += 1
    # All one-increment evaluation scores are <=1, including impossible histories.
    for suffix in product((0, 1, 2), repeat=3):
        assert score_path(catalogue, (0, '.2', '.4', '.6'), (1,)+suffix, 2)['log_e'] <= 0
    baseline = score_path(catalogue, times, (1, 1, 2, 1, 2), 2)
    changed = score_path(catalogue, times, (1, 1, 2, 0, 0), 2)
    assert baseline['fit'] == changed['fit'] and baseline['training'] == changed['training']
    assert score_path(catalogue, times, (1, 1, 1, 1, 1), 2)['log_e'] == -mp.inf
    # A valid positive path can give a nonzero finite score; the scorer is not identically zero.
    assert mp.isfinite(baseline['log_e'])
    for bad in ((1, 1, -1, 2, 1), (1, 1, 'nan', 2, 1)):
        try:
            score_path(catalogue, times, bad, 2)
        except ValueError:
            pass
        else:
            raise AssertionError(bad)
    return 81, 27, comparisons


def finite_checks():
    # A conditional-density fixture, not a diffusion. U has weights 1/3,2/3.
    # The pilot picks a point mass at V=0 for U=0 and V=1 for U=1.
    # New nulls form the whole line segment between endpoint distributions;
    # its pointwise supremum is attained at endpoints, outside the old null.
    old = (F(1, 50), F(1, 50), F(48, 50))
    left = (F(2, 50), F(1, 50), F(47, 50))
    right = (F(1, 50), F(2, 50), F(47, 50))
    null_rows = (old,)+tuple(tuple(t*a+(1-t)*b for a, b in zip(left, right))
                            for t in (F(0), F(1, 4), F(1, 2), F(3, 4), F(1)))
    envelope = tuple(max(a, b, c) for a, b, c in zip(old, left, right))
    assert envelope == (F(1, 25), F(1, 25), F(24, 25))
    weights = (F(1, 3), F(2, 3))
    levels = (F(1, 20), F(1, 10), F(1, 2))
    scores = tuple(tuple(F(int(v == u))/envelope[v] for v in range(3)) for u in range(2))
    conditional_cases = size_cases = 0
    for law in null_rows:
        for u in range(2):
            assert sum(p*e for p, e in zip(law, scores[u])) <= 1
            conditional_cases += 1
        for alpha in levels:
            size = sum(weights[u]*law[v] for u, v in product(range(2), range(3))
                       if scores[u][v] > 1/alpha)
            assert size <= alpha
            size_cases += 1

    # Pushforwards of the preceding laws have score 25 or 0. Include one alternative.
    laws = null_rows+((F(1, 2), F(1, 2), F(0)),)
    positive = tuple(weights[0]*row[0]+weights[1]*row[1] for row in laws)
    panels = nonzero = 0
    for i, j, level in product(range(len(laws)), range(len(laws)), levels):
        p, q = positive[i], positive[j]
        nulls = {h for h, truth in enumerate((i, j)) if truth < len(null_rows)}
        for joint_high in (p*q, min(p, q), max(F(0), p+q-1)):
            joint = ((0, 0, 1-p-q+joint_high), (25, 0, p-joint_high),
                     (0, 25, q-joint_high), (25, 25, joint_high))
            assert sum(w for _, _, w in joint) == 1 and all(w >= 0 for _, _, w in joint)
            assert sum(w for a, _, w in joint if a) == p
            assert sum(w for _, b, w in joint if b) == q
            for screen in range(4):
                risk = F(0)
                for a, b, w in joint:
                    selected = ({0, 1}, set(), {0}, {0 if a >= b else 1})[screen]
                    discovered = ranked((F(a), F(b)), level, selected)
                    risk += w*F(len(set(discovered)&nulls), max(1, len(discovered)))
                assert risk <= level*F(len(nulls), 2)
                nonzero += risk > 0
                panels += 1
    assert nonzero
    return conditional_cases, size_cases, panels, nonzero


if __name__ == '__main__':
    mp.dps = 60
    print('Fixed arrays, single-increment arrays, Gaussian dominance comparisons:', price_checks())
    print('Conditional moments, size checks, FDR/screen cases, nonzero FDR:', finite_checks())
    print('PASS: exact finite fixtures and fixed price checks, not simulated performance or proof')
