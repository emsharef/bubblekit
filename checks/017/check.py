"""Exact dividend-cap and certification arithmetic; no real dates certified."""

from fractions import Fraction as F
from itertools import product


def main():
    cases = 0
    for gain, paid, terminal_paid, discount, strike in product(
        [F(0), F(1, 4), F(1), F(3)],
        [F(0), F(1, 4), F(1)],
        [F(0), F(1, 4), F(1), F(2)],
        [F(1, 2), F(1), F(3, 2)],
        [F(0), F(1, 2), F(2), F(5)],
    ):
        if not 0 <= paid <= min(gain, terminal_paid):
            continue
        cap = min(gain, paid + discount * strike)
        payoff = max(gain - paid - discount * strike, 0)
        assert gain - cap == payoff
        assert 0 <= cap <= terminal_paid + F(3, 2) * strike
        cases += 1

    # A distribution jump reduces the ex-dividend price, not the total gain.
    gain, paid_before, paid_after, strike = F(2), F(0), F(1, 2), F(7, 4)
    before = max(gain - paid_before - strike, 0)
    after = max(gain - paid_after - strike, 0)
    assert before == F(1, 4) and after == 0
    assert (gain - paid_before) + paid_before == (gain - paid_after) + paid_after

    # Basket capital 100, one name with 1% weight. A one-cent basket budget
    # permits a 1% relative defect in that name, not the index's 0.01%.
    budget, basket_start, name_start_value = F(1, 100), F(100), F(1)
    assert budget / basket_start == F(1, 10000)
    assert budget / name_start_value == F(1, 100)
    assert budget / name_start_value > budget / basket_start

    # Equal initial scale, terminal tracking discrepancy in either direction.
    for scale, etf_start, etf_mean, error in product(
        [F(1), F(10)], [F(2)], [F(1), F(3, 2), F(2)],
        [F(-1, 10), F(0), F(1, 10)],
    ):
        basket_initial = scale * etf_start
        basket_mean = scale * etf_mean + error
        if basket_mean > basket_initial:
            continue
        etf_defect = etf_start - etf_mean
        basket_defect = basket_initial - basket_mean
        upper_quote = etf_defect + F(1, 100)
        tracking_allowance = abs(error)
        assert basket_defect == scale * etf_defect - error
        assert basket_defect <= scale * upper_quote + tracking_allowance

    # A tiny bid and a small mid are not upper bounds on an admissible value.
    bid, ask, model_value = F(1, 100), F(3, 100), F(1, 40)
    assert bid < (bid + ask) / 2 < model_value <= ask
    # A positive defect fits a positive tolerance: its positivity is not refuted.
    defect, tolerance = F(1, 1000), F(1, 100)
    assert 0 < defect <= tolerance
    print(f"PASS: {cases} dividend-cap cases; payout jump; small-weight scaling; "
          "ETF transfer; bid/mid obstruction; tolerance versus exact null")


if __name__ == "__main__":
    main()
