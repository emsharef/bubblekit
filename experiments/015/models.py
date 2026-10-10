"""Experiment 015 path generator: known-answer models on a trading-time clock, with common random numbers.

    from models import MODELS, batch
    daily, tail = batch("cev1.5", 5, b)     # b-th batch of 100 paths for horizon 5 years

`daily[:, d]` is S at the close of trading day d = 0..252T. `tail[:, k]` is S at 5-minute bar k over the last 84
trading days (78 bars a day, no overnight time), so `tail[:, 0] == daily[:, -85]` and `tail[:, -1] == daily[:, -1]`.
Every call with the same (model, T, b) returns the same paths, so later tests can be added to the same design.
"""
import numpy as np

SEED = 20261015
DAYS_PER_YEAR, BARS_PER_DAY, TAIL_DAYS = 252, 78, 84
BATCH, BATCHES = 100, 40
HORIZONS = (1, 5)
VOL = 0.3
MODELS = {                       # name: (kind, parameter, true martingale?)
    "cev0.5": ("cev", 0.5, True), "cev0.9": ("cev", 0.9, True), "cev1.0": ("cev", 1.0, True),
    "cev1.1": ("cev", 1.1, False), "cev1.5": ("cev", 1.5, False), "cev2.0": ("cev", 2.0, False),
    "sin_mart": ("sin", (-1.0, 1.0), True), "sin_strict": ("sin", (1.0, 1.0), False),
}
DT_DAY = 1.0 / DAYS_PER_YEAR
DT_BAR = DT_DAY / BARS_PER_DAY


def seed_for(model, T, b):
    names = sorted(MODELS)
    root = np.random.SeedSequence(SEED)
    cell = root.spawn(len(names) * len(HORIZONS))[names.index(model) * len(HORIZONS) + HORIZONS.index(T)]
    return cell.spawn(BATCHES)[b]


def _record(n_days):
    """Fine step index (5-minute steps) of each daily close and of each tail bar."""
    steps = n_days * BARS_PER_DAY
    return np.arange(0, steps + 1, BARS_PER_DAY), np.arange(steps - TAIL_DAYS * BARS_PER_DAY, steps + 1)


def _euler(rng, n, n_days, step, state0, to_price):
    daily_idx, tail_idx = _record(n_days)
    daily = np.empty((n, daily_idx.size))
    tail = np.empty((n, tail_idx.size))
    state = state0
    di, ti = 0, 0
    for k in range(n_days * BARS_PER_DAY + 1):
        if k:
            state = step(state)
        if di < daily_idx.size and k == daily_idx[di]:
            daily[:, di] = to_price(state)
            di += 1
        if ti < tail_idx.size and k == tail_idx[ti]:
            tail[:, ti] = to_price(state)
            ti += 1
    return daily, tail


def batch(model, T, b, n=BATCH):
    kind, p, _ = MODELS[model]
    rng = np.random.default_rng(seed_for(model, T, b))
    n_days = DAYS_PER_YEAR * T
    if kind == "cev" and p == 1.0:                                   # exact lognormal on the 5-minute grid
        steps = n_days * BARS_PER_DAY
        logS = np.concatenate([np.zeros((n, 1)), np.cumsum(VOL * np.sqrt(DT_BAR) * rng.standard_normal((n, steps))
                                                           - 0.5 * VOL ** 2 * DT_BAR, axis=1)], axis=1)
        d, t = _record(n_days)
        return np.exp(logS[:, d]), np.exp(logS[:, t])
    if kind == "cev" and p > 1.0:                                    # exact BESQ(delta) on the union grid
        delta = (2 * p - 1) / (p - 1)
        dts = np.r_[np.full(n_days - TAIL_DAYS, DT_DAY), np.full(TAIL_DAYS * BARS_PER_DAY, DT_BAR)]
        X = np.empty((n, dts.size + 1))
        X[:, 0] = (1.0 / (VOL * (p - 1))) ** 2
        for i, dt in enumerate(dts):
            X[:, i + 1] = dt * rng.noncentral_chisquare(delta, X[:, i] / dt)
        S = (VOL * (p - 1) * np.sqrt(X)) ** (1.0 / (1.0 - p))
        nd = n_days - TAIL_DAYS
        tail = S[:, nd:]
        daily = np.concatenate([S[:, :nd], tail[:, ::BARS_PER_DAY]], axis=1)
        return daily, tail
    if kind == "cev":                                                # beta < 1: Euler on R = S^{1-b}/(VOL(1-b))
        drift = p / (2 * (1 - p))
        sq = np.sqrt(DT_BAR)

        def step(R):
            nxt = R - drift / np.where(R > 0, R, 1.0) * DT_BAR + sq * rng.standard_normal(n)
            return np.where((R <= 0) | (nxt <= 0), 0.0, nxt)
        return _euler(rng, n, n_days, step, np.full(n, 1.0 / (VOL * (1 - p))),
                      lambda R: (VOL * (1 - p) * R) ** (1.0 / (1 - p)))
    a = np.asarray(p)                                                # Sin: log-Euler, alpha = kappa = L = 1
    g = np.array([VOL, 0.0])
    sq = np.sqrt(DT_BAR)

    def step(st):
        lS, lv = st
        v = np.exp(lv)
        dW = sq * rng.standard_normal((2, n))
        return (lS + v * (g @ dW) - 0.5 * v * v * (g @ g) * DT_BAR,
                lv + a @ dW - 0.5 * (a @ a) * DT_BAR + (1.0 - v) / v * DT_BAR)
    return _euler(rng, n, n_days, step, (np.zeros(n), np.zeros(n)), lambda st: np.exp(st[0]))
