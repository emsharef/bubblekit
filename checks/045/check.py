"""Exact finite-law checks for claim 045; no simulation or source-theorem proof."""
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import runpy


def tv(left, right):
    # Half the l1 distance is the event-supremum TV on this finite space.
    assert sum(left.values()) == sum(right.values()) == 1
    return sum((abs(left.get(x, 0) - right.get(x, 0))
                for x in left.keys() | right.keys()), F(0)) / 2


def cutoff(c, alpha):
    rank = (len(c) + 1) * (1 - alpha)
    k = -(-rank.numerator // rank.denominator)
    return sorted(c)[k - 1] if k <= len(c) else None


def risk(c, alpha, success):
    q = cutoff(c, alpha)
    return success if q == 0 else F(0)


def main():
    cases = nontrivial_bad = infinite = 0
    for n, p, contamination, kernel_mix in product(
            range(1, 5), (F(1, 4), F(1, 2), F(3, 4)),
            (F(0), F(1, 10), F(1, 4)), (F(0), F(1, 10), F(1, 4))):
        cs = list(product((0, 1), repeat=n))
        reference = {c: p**sum(c) * (1 - p)**(n - sum(c)) for c in cs}
        actual = {c: (1 - contamination) * reference[c]
                  + contamination * (c == (0,) * n) for c in cs}
        eta = tv(actual, reference)
        # U=(calibration scores, extra recorded bit). K depends on both;
        # conditioning on scores alone would average away this dependence.
        records = {(c, h): actual[c] / 2 for c in cs for h in (0, 1)}
        kernels = {(c, h): (1 - kernel_mix) * p
                   + kernel_mix * ((sum(c) + h) % 2) for c, h in records}
        rho = max(abs(value - p) for value in kernels.values())
        joint = {(c, s): sum((records[c, h] *
                 (kernels[c, h] if s else 1 - kernels[c, h])
                 for h in (0, 1)), F(0)) for c in cs for s in (0, 1)}
        ref_joint = {(c, s): reference[c] * (p if s else 1 - p)
                     for c in cs for s in (0, 1)}
        joint_tv = tv(joint, ref_joint)
        assert joint_tv <= eta + rho
        for alpha in (F(1, 4), F(1, 2), F(3, 4)):
            flag = sum((mass * risk(c, alpha, kernels[c, h])
                        for (c, h), mass in records.items()), F(0))
            ref_flag = sum((reference[c] * risk(c, alpha, p) for c in cs), F(0))
            assert ref_flag <= alpha
            assert abs(flag - ref_flag) <= joint_tv
            assert flag <= min(1, alpha + joint_tv)
            assert flag <= min(1, alpha + eta + rho)
            infinite += cutoff(cs[0], alpha) is None
            for e in (F(1, 4), F(1, 2), F(3, 4)):
                x = alpha * (n + 1) - 1
                r = x.numerator // x.denominator
                binomial = sum((F(comb(n, j)) * e**j * (1 - e)**(n - j)
                                for j in range(r + 1)), F(0))
                delta = max(F(1, 100), binomial)
                assert 0 < delta < 1
                ref_bad = sum((reference[c] for c in cs if risk(c, alpha, p) > e), F(0))
                cal_bad = sum((actual[c] for c in cs if risk(c, alpha, p) > e), F(0))
                bad = sum((mass for (c, h), mass in records.items()
                           if risk(c, alpha, kernels[c, h]) > e + rho), F(0))
                assert ref_bad <= binomial
                assert cal_bad <= ref_bad + eta
                assert bad <= cal_bad <= min(1, delta + eta)
                b, d = min(F(1), e + rho), min(F(1), delta + eta)
                assert flag <= b + (1 - b) * d
                cases += 1
                nontrivial_bad += 0 < bad < 1 and d < 1
    assert infinite > 0 and nontrivial_bad > 0

    # Equal unconditional marginals do not give a zero conditional-law budget.
    # C is fair, S=1-C: at C=0 the conditional risk is one, reference risk 1/2.
    fair = {0: F(1, 2), 1: F(1, 2)}
    assert tv(fair, fair) == 0
    assert risk((0,), F(1, 2), F(1)) > risk((0,), F(1, 2), F(1, 2))
    assert tv({0: F(0), 1: F(1)}, fair) == F(1, 2)

    # Claim (9), checked as exact rational probabilities.
    assert F(1, 2) * F(99, 100)**19 > F(2, 5)
    assert F(1, 100) * F(99, 100)**19 < F(1, 20)
    print(f"PASS: {cases} finite-law risk comparisons; {nontrivial_bad} "
          f"nontrivial bad sets; {infinite} infinite-cutoff cases; kernel counterexample")
    root = Path(__file__).resolve().parents[2]
    for previous in ("d34-selection-contract", "d34-calibration-budget"):
        runpy.run_path(str(root / "checks" / previous / "check.py"), run_name="__main__")


if __name__ == "__main__":
    main()
