"""Exact scalar checks for the D31(c) design, not a stochastic pricing model."""
from fractions import Fraction as F
from itertools import product


def payoff_prices(m, strike):
    # A two-point terminal law with mean m. No intervening price process
    # or American optimal-stopping problem is constructed by this fixture.
    terminal = (F(0), 2*m)
    call = sum((max(x-strike, F(0)) for x in terminal), F(0))/2
    put = sum((max(strike-x, F(0)) for x in terminal), F(0))/2
    return call, put


identities = 0
for m, strike, loading, excess in product(
        (F(1, 5), F(3, 5), F(1)),
        (F(0), F(1, 4), F(3, 4), F(3, 2), F(2)),
        (F(0), F(1, 2), F(1)),
        (F(0), F(1, 20), F(1, 5))):
    call, put = payoff_prices(m, strike)
    defect = 1-m
    observed = call+loading*defect
    american = call+defect+excess
    residual = 1-strike-observed+put
    premium = american-observed
    assert call-put == m-strike
    assert residual == (1-loading)*defect
    assert premium == residual+excess
    assert premium-residual == american+strike-put-1 == excess
    assert 1-strike-american+put == -excess
    identities += 1

# Nonzero-defect overlap over a strip of strikes in the declared tables.
for m in (F(1, 5), F(3, 5)):
    restored, american = [], []
    for strike in (F(1, 4), F(3, 4), F(3, 2)):
        call, put = payoff_prices(m, strike)
        restored.append((call+1-m, put))
        american.append((call+1-m+F(0), put))
    assert restored == american and 1-m > 0

corners = 0
for defect, ecall, eput in product(
        (F(0), F(1, 100), F(1, 25), F(1, 10), F(2, 5)),
        (F(0), F(1, 100), F(3, 100)),
        (F(0), F(1, 100), F(3, 100))):
    strike = F(3, 4)
    call, put = payoff_prices(1-defect, strike)
    h = ecall+eput
    for dc, dp in product((-ecall, ecall), (-eput, eput)):
        for loading in (F(0), F(1)):
            ctrue = call+loading*defect
            chat, phat = ctrue+dc, put+dp
            rtrue = 1-strike-ctrue+put
            rhat = 1-strike-chat+phat
            lo, hi = rhat-h, rhat+h
            assert lo <= rtrue <= hi
            if loading == 1 or defect == 0:
                assert lo <= 0
            if loading == 0 and defect > 2*h:
                assert lo > 0
            corners += 1

# Strict-boundary witness: at delta=2h, admissible quote errors can put L=0.
for h in (F(1, 100), F(1, 20), F(1, 5)):
    defect = 2*h
    call, put = payoff_prices(1-defect, F(1))
    chat, phat = call+h, put  # e_C=h, e_P=0; residual error is -h
    assert 1-F(1)-chat+phat-h == 0

# The direct excess expression cancels C exactly, including its quote error.
for dc, dp, da in product((F(-1, 100), F(1, 100)), repeat=3):
    call, put = payoff_prices(F(3, 5), F(3, 4))
    american = call+F(2, 5)+F(1, 20)
    chat, phat, ahat = call+dc, put+dp, american+da
    rhat = 1-F(3, 4)-chat+phat
    dhat = ahat-chat
    assert dhat-rhat == ahat+F(3, 4)-phat-1
    assert dhat-rhat-F(1, 20) == da-dp

uplift_cases = 0
for defect, upper, h, errsign in product(
        (F(0), F(1, 10), F(2, 5)),
        (F(0), F(1, 20)), (F(0), F(1, 100)), (-1, 1)):
    for excess in (F(0), upper/2, upper):
        observed_uplift = defect+excess+errsign*h
        decision = observed_uplift-h > upper
        if defect == 0:
            assert not decision
        if defect > upper+2*h:
            assert decision
        uplift_cases += 1

print(f'PASS: {identities} exact identities; {corners} quote-error corners; '
      f'{uplift_cases} bounded-excess uplift cases; '
      'nonzero-defect overlap, strict boundary and call-error cancellation. '
      'No simulation or market-instance claim.')
