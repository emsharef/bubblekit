"""Recompute experiment 029's decisions from committed per-panel output.

No simulation or imported experiment aggregation code. Saved log scores are
rounded to six decimals; threshold margins are checked against that precision.
This verifies aggregation/reading, not the generator or likelihood calculation.
Run with the repository's single-thread BLAS prefix: uv run python this-file.
"""
import json
import math
from pathlib import Path
from statistics import mean, stdev

ROOT = Path(__file__).resolve().parents[2]
data = json.loads((ROOT / "experiments/029/results.json").read_text())
M, q, cap, delta = 20, .05, 10000, .00001
cost = math.log1p((cap-1)*delta)
thresholds = [math.log(M/(q*k)) for k in range(1, M+1)]
minimum_margin = math.inf


def ebh(logs):
    """Direct count definition, retaining the original m even for zero scores."""
    good = [k for k, threshold in enumerate(thresholds, 1)
            if sum(x >= threshold for x in logs) >= k]
    if not good:
        return [False]*M
    return [x >= thresholds[max(good)-1] for x in logs]


def stats(values):
    return mean(values), stdev(values)/math.sqrt(len(values))


def agrees(values, reported):
    for actual, key in zip(stats(values), ("mean", "se")):
        assert abs(actual-reported[key]) < 1e-12, (actual, reported)


screen = []
totals = dict(alternatives=0, gains=0, already_capped=0, already_rejected=0, surviving_gains=0)
for name, cell in data["cells"].items():
    panels = cell["per_panel"]
    assert len(panels) == 200
    contract = name[:4] in ("0000", "0101")
    truth = int(name[:4], 2) if contract else None
    cols = ("all", "allcap", "safe", "sel", "v1") + (("oracle",) if name != "S-025" else ())
    fdp, tdp = {c: [] for c in cols}, {c: [] for c in cols}
    gains = both_capped = already_rejected = uncapped_gain = alt_count = null_count = wrong_null_argmax = 0
    positive_gain_nonrejections = 0
    for p in panels:
        assert len(p["bubbly"]) == M and not any(p["fail"]) and not any(p["singular"])
        scores = {c: [-math.inf if x is None else x for x in p["scores"][c]] for c in cols}
        for values in scores.values():
            minimum_margin = min(minimum_margin,
                min(abs(x-t) for x in values for t in thresholds if math.isfinite(x)))
        masks = {c: ebh(values) for c, values in scores.items()}
        for c, mask in masks.items():
            fdp[c].append(sum(r and not b for r, b in zip(mask, p["bubbly"]))/max(1, sum(mask)))
            tdp[c].append(sum(r and b for r, b in zip(mask, p["bubbly"]))/max(1, sum(p["bubbly"])))
        if contract:
            assert {j for j, keep in enumerate(p["keep"]) if keep} == {0, truth}
            assert p["fclock"] == truth and not p["true_excluded"]
            assert scores["sel"] == scores["oracle"]
        for j, bubbly in enumerate(p["bubbly"]):
            # Quantization can perturb these identities by at most a few ulps
            # at the six-decimal serialization scale, not change the formula.
            assert abs(scores["safe"][j]-(min(scores["sel"][j], math.log(cap))-cost)) <= 1.1e-6
            assert abs(scores["allcap"][j]-(min(scores["all"][j], math.log(cap))-cost)) <= 1.1e-6
            assert abs(scores["sel"][j]-scores["all"][j]-p["complete_gain"][j]) <= 1.6e-6
            assert scores["safe"][j] >= scores["allcap"][j]-1.1e-6
            if not bubbly:
                null_count += 1
                if contract:
                    assert p["gauss_gain"][j] == p["complete_gain"][j] == 0
                    assert not p["argmaxD_excluded"][j]
                    wrong_null_argmax += p["argmaxD"][j] != truth
            else:
                alt_count += 1
                if p["complete_gain"][j] > 0:
                    gains += 1
                    both_capped += scores["all"][j] > math.log(cap)
                    already_rejected += masks["all"][j]
                    uncapped_gain += scores["safe"][j] > scores["allcap"][j]+1e-6
                    positive_gain_nonrejections += not masks["all"][j]
    for c in cols:
        agrees(fdp[c], cell["ebh_0.05"][c]["FDR"])
        if alt_count:
            agrees(tdp[c], cell["ebh_0.05"][c]["TDP"])
    if alt_count:
        totals["alternatives"] += alt_count
        totals["gains"] += gains
        totals["already_capped"] += both_capped
        totals["already_rejected"] += already_rejected
        totals["surviving_gains"] += uncapped_gain
        diffs = [a-b for a, b in zip(tdp["safe"], tdp["all"])]
        diffs_cap = [a-b for a, b in zip(tdp["safe"], tdp["allcap"])]
        agrees(diffs, cell["ebh_0.05"]["TDP_safe_minus_all"])
        agrees(diffs_cap, cell["ebh_0.05"]["TDP_safe_minus_allcap"])
        avg, se = stats(diffs)
        if name.startswith("0101"):
            screen.append(avg > 2*se)
        print(f"{name}: safe-all TDP={avg:.9f} SE={se:.9f}; "
              f"safe-allcap={stats(diffs_cap)[0]:.9f}; gain names={gains}/{alt_count}; "
              f"gain already all>cap={both_capped}/{gains}; "
              f"gain already E_all eBH-rejected={already_rejected}/{gains}; "
              f"uncapped positive gains={uncapped_gain}; "
              f"gain not already rejected={positive_gain_nonrejections}")
    else:
        print(f"{name}: FDR safe={stats(fdp['safe'])}, all={stats(fdp['all'])}, v1={stats(fdp['v1'])}")
    if contract:
        print(f"  null profile argmax != truth: {wrong_null_argmax}/{null_count}")
        if not alt_count:
            assert sum(fdp["safe"]) == 0
assert len(screen) == 4 and not any(screen)
assert minimum_margin > .5e-6
assert totals["gains"] - totals["already_capped"] == totals["surviving_gains"]
print("Alternative-record totals:", totals)
print(f"Minimum eBH threshold margin across saved finite scores: {minimum_margin:.12g}")
print("PASS: independent saved-score eBH, paired SEs, cap/denominator identities; registered screen NULL")
