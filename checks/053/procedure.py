"""Exact base e-BH on supplied rational scores; no score-validity certificate."""
from fractions import Fraction


def ranked_discoveries(values, level, selected=None):
    values = tuple(Fraction(x) for x in values)
    level = Fraction(level)
    m = len(values)
    if not m or not 0 < level < 1 or min(values) < 0:
        raise ValueError('nonempty nonnegative scores and a level strictly between zero and one required')
    selected = frozenset(range(m) if selected is None else selected)
    if not selected <= set(range(m)):
        raise ValueError('screen indices must belong to the original family')
    masked = tuple(value if i in selected else Fraction(0) for i, value in enumerate(values))
    order = tuple(sorted(range(m), key=lambda i: (-masked[i], i)))
    kstar = 0
    for k, i in enumerate(order, 1):
        if k * masked[i] * level >= m:
            kstar = k
    return order[:kstar]
