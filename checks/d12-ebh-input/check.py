"""Exact rank/screening checks for the registered e-BH input; no simulation."""
from fractions import Fraction as F
from itertools import combinations, product


def ebh(values, level):
    assert values and 0 < level < 1 and min(values) >= 0
    m = len(values)
    order = sorted(range(m), key=lambda i: (-values[i], i))
    kstar = max([0] + [k for k, i in enumerate(order, 1) if k * values[i] >= m / level])
    return frozenset(order[:kstar])


def subsets(m):
    return [frozenset(s) for k in range(m + 1) for s in combinations(range(m), k)]


def fdp(rejected, nulls):
    return F(len(rejected & nulls), max(1, len(rejected)))


def main():
    arrays = screens = 0
    levels = (F(1, 5), F(1, 2), F(3, 4))
    for m in range(1, 5):
        choices = subsets(m)
        for values, level in product(product((F(0), F(1), F(2), F(20, 3), F(20)), repeat=m), levels):
            rejected = ebh(values, level)
            # Independent characterization: enumerate all self-consistent subsets.
            feasible = [s for s in choices if not s or all(values[i] >= m / (level * len(s)) for i in s)]
            assert all(s <= rejected for s in feasible)
            assert rejected in feasible
            if rejected:
                threshold = F(m) / (level * len(rejected))
                assert rejected == {i for i, value in enumerate(values) if value >= threshold}
            for selected in choices:
                masked = tuple(e if i in selected else F(0) for i, e in enumerate(values))
                keep_original = ebh(masked, level)
                assert keep_original <= selected
                # Source Section 5.1: amend the selected-family level by |S|/m.
                selected_order = sorted(selected)
                if selected:
                    local = ebh(tuple(values[i] for i in selected_order), level * F(len(selected), m))
                    assert keep_original == {selected_order[i] for i in local}
                else:
                    assert not keep_original
                screens += 1
            arrays += 1

    level, nulls = F(1, 5), frozenset((0, 1))
    law = (
        (F(3, 20), (F(20, 3), F(0), F(20), F(20))),
        (F(3, 20), (F(0), F(20, 3), F(20), F(20))),
        (F(7, 10), (F(0), F(0), F(20), F(20))),
    )
    assert sum(w for w, _ in law) == 1
    for i in nulls:
        assert sum(w * e[i] for w, e in law) == 1
    base = sum(w * fdp(ebh(e, level), nulls) for w, e in law)
    trimmed = sum(w * fdp(ebh(e, level) & {0, 1}, nulls) for w, e in law)
    masked = sum(w * fdp(ebh((e[0], e[1], F(0), F(0)), level), nulls) for w, e in law)
    reset = F(0)
    for w, e in law:
        selected = tuple(i for i in (0, 1) if e[i] > 0)
        if selected:
            local = ebh(tuple(e[i] for i in selected), level)
            reset += w * fdp(frozenset(selected[i] for i in local), nulls)
    assert base == F(1, 10) == level * F(len(nulls), 4)
    assert trimmed == reset == F(3, 10) > level
    assert masked == 0

    # Nonzero degenerate input proposed for AX-53; also exercises empty output.
    for m, level in product(range(1, 10), levels):
        assert not ebh((F(1),) * m, level)
    # An exact tie at the rejection threshold uses >=, not >.
    assert ebh((F(2), F(2)), F(1, 2)) == {0, 1}
    print(f"PASS: {arrays} rank arrays; {screens} screening identities; "
          "exact filtering counterexample (base 1/10, trimmed/reset 3/10, masked 0); "
          "nonzero degenerate and tie cases. Finite checks, not a general FDR proof.")


if __name__ == '__main__':
    main()
