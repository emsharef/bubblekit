"""Experiment 015: format results.json as the report's Markdown tables.

    uv run python experiments/015/report.py      (after run.py)
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ORDER = ["cev0.5", "cev0.9", "cev1.0", "sin_mart", "cev1.1", "cev1.5", "cev2.0", "sin_strict"]
LABEL = {"cev0.5": "CEV β = 0.5", "cev0.9": "CEV β = 0.9", "cev1.0": "CEV β = 1", "sin_mart": "Sin a·γ < 0",
         "cev1.1": "CEV β = 1.1", "cev1.5": "CEV β = 1.5", "cev2.0": "CEV β = 2", "sin_strict": "Sin a·γ > 0"}


def f(r):
    return "%.3f" % r["rate"]


def main():
    res = json.load(open(os.path.join(HERE, "results.json")))
    cells = res["cells"]
    print("GSADF critical values (95% / 90%):")
    for N, v in res["critical_values"].items():
        print(f"- N = {N}: SADF {v['sadf']['5%']:.3f} / {v['sadf']['10%']:.3f}, "
              f"GSADF {v['gsadf']['5%']:.3f} / {v['gsadf']['10%']:.3f}")
    for s, title in (("daily", "daily closes over [0, T]"), ("month", "5-minute bars over the last month")):
        print(f"\n**Rejection rates for \"bubble\", {title}.** 5% / 10% for SADF, GSADF and the panel tests; "
              "one rate for JKP (no nominal level).\n")
        print("| model | label | T | SADF | GSADF | JKP M2 bubble | JKP M2 indeterminate | JKP M1 bubble | panel t | panel J |")
        print("|---|---|---|---|---|---|---|---|---|---|")
        for m in ORDER:
            for T in (1, 5):
                c = cells[f"{m}|{T}"]
                x = c[s]
                print(f"| {LABEL[m]} | {c['label']} | {T} | {f(x['sadf']['5%'])} / {f(x['sadf']['10%'])} | "
                      f"{f(x['gsadf']['5%'])} / {f(x['gsadf']['10%'])} | {f(x['jkp_m2']['bubble'])} | "
                      f"{f(x['jkp_m2']['indeterminate'])} | {f(x['jkp_m1']['bubble'])} | "
                      f"{f(x['panel_t']['5%'])} / {f(x['panel_t']['10%'])} | {f(x['panel_J']['5%'])} / {f(x['panel_J']['10%'])} |")
    print("\n**OPY** (5-minute bars over the last 84 days, 63 signal days, 400 paths; no nominal level).\n")
    print("| model | label | T | bubble (≥ 1 birth) | mean indeterminate share | mean + share | absorbed |")
    print("|---|---|---|---|---|---|---|")
    for m in ORDER:
        for T in (1, 5):
            c = cells[f"{m}|{T}"]
            o = c["opy"]
            print(f"| {LABEL[m]} | {c['label']} | {T} | {f(o['bubble'])} ± {o['bubble']['se']:.3f} | "
                  f"{o['indet_share_mean']:.3f} | {o['plus_share_mean']:.3f} | {f(c['absorbed'])} |")
    print("\nMonte Carlo SEs (binomial): single-series n = 1,000, panel n = 200, OPY n = 400.")


if __name__ == "__main__":
    main()
