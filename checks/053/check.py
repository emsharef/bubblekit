"""Exact catalogue-to-e-BH composition checks, not price simulations or an FDR proof."""
import importlib.util
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path

from procedure import ranked_discoveries

spec = importlib.util.spec_from_file_location('catalogue_051', Path(__file__).resolve().parents[1] / '051/check.py')
catalogue = importlib.util.module_from_spec(spec)
spec.loader.exec_module(catalogue)


def fdp(rejected, nulls):
    return F(len(set(rejected) & nulls), max(1, len(rejected)))


def main():
    rank_cases = 0
    for m in range(1, 5):
        subsets = [set(s) for k in range(m+1) for s in combinations(range(m), k)]
        for values, level in product(product((F(0), F(1), F(2), F(6)), repeat=m), (F(1, 5), F(1, 2))):
            result = ranked_discoveries(values, level)
            # Independent characterization: largest feasible cardinality and
            # union of every self-consistent subset, not a second sorting loop.
            feasible = [s for s in subsets if not s or all(values[i] >= F(m)/(level*len(s)) for i in s)]
            assert len(result) == max(map(len, feasible))
            assert set(result) == set().union(*feasible)
            assert result == tuple(sorted(result, key=lambda i: (-values[i], i)))
            rank_cases += 1
    assert ranked_discoveries((2, 2), F(1, 2)) == (0, 1)  # weak equality
    assert ranked_discoveries((100, 100), F(1, 5), ()) == ()
    assert ranked_discoveries((6, 0), F(1, 5), (0,)) == ()  # m stays 2

    selectors = ((0, 1), (2, 3), (3, 2), (2, 2))
    panels = screened_cases = positive_fdr_cases = 0
    for truth1, truth2, selector_index, level in product(range(4), range(4), range(4),
                                                       (F(1, 20), F(1, 5), F(1, 2))):
        p, q = catalogue.law(truth1), catalogue.law(truth2)
        e1 = [catalogue.infer(selectors[selector_index], F(1, 10), s)[3] for s in catalogue.STATES]
        e2 = [catalogue.infer(selectors[(selector_index+1) % 4], F(1, 10), s)[3] for s in catalogue.STATES]
        nulls = {i for i, truth in enumerate((truth1, truth2)) if truth in catalogue.NULLS}
        for i in nulls:
            assert sum(w*e for w, e in zip((p, q)[i], (e1, e2)[i])) <= 1
        independent = [(i, j, a*b) for i, a in enumerate(p) for j, b in enumerate(q)]
        for law in (independent, catalogue.transport(p, q), catalogue.transport(p, q, reverse=True)):
            assert sum(w for _, _, w in law) == 1
            for i in range(len(p)):
                assert sum(w for a, _, w in law if a == i) == p[i]
                assert sum(w for _, b, w in law if b == i) == q[i]
            # Each screen is recomputed from the full outcome, with fixed original m.
            for screen in range(5):
                risk = F(0)
                for i, j, w in law:
                    values = (e1[i], e2[j])
                    selected = ({0, 1}, set(), {0}, {0 if e1[i] >= e2[j] else 1},
                                {h for h, e in enumerate(values) if e > 1})[screen]
                    rejected = ranked_discoveries(values, level, selected)
                    assert set(rejected) <= selected
                    risk += w * fdp(rejected, nulls)
                assert risk <= level * F(len(nulls), 2)
                positive_fdr_cases += risk > 0
                screened_cases += 1
            panels += 1

    boundaries = 0
    for selector, state in product(selectors, catalogue.STATES):
        e = catalogue.infer(selector, F(1, 10), state)[3]
        if e > 1:
            level = 1/e
            kept = catalogue.infer(selector, level, state)[0]
            assert set(kept) & set(catalogue.NULLS)
            assert ranked_discoveries((e,), level) == (0,)
            boundaries += 1
    assert boundaries and positive_fdr_cases
    print(f'PASS: {rank_cases} rank arrays; {panels} finite joint catalogue laws; '
          f'{screened_cases} FDR/screen cases ({positive_fdr_cases} with positive FDR); '
          f'{boundaries} exact confidence-boundary distinctions. '
          'Exact finite checks, not a general theorem or price-data experiment.')


if __name__ == '__main__':
    main()
