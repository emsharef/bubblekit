"""Experiment 027: print the Markdown tables of the report from experiments/027/results.json.

    uv run python experiments/027/report.py
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
COLS = ["v1flat", "raw", "d055", "c033", "c034"]
HEAD = ["v1 flat", "054 raw", "055 (shared numerator)", "033 clock", "034 rounded (hourly)"]


def main():
    r = json.load(open(os.path.join(HERE, "results.json")))
    for a in ("0.05", "0.1"):
        print(f"\n**Rejection rates at α = {a}** (5-minute / hourly; † marks a column that does not cover a null row; "
              f"034 is hourly only)\n")
        print("| truth | sessions | " + " | ".join(HEAD) + " |")
        print("|---|---|" + "---|" * len(HEAD))
        for key, cell in r["cells"].items():
            name, H = key.split("|")
            out = []
            for c in COLS:
                m5, mh = cell["5m"], cell["60m"]
                cov = mh["coverage"].get(c, True) if not name.startswith("CEV") else True
                dag = "" if cov else "†"
                if c == "c034":
                    out.append(f"– / {mh[a][c]['rate']:.3f}{dag}")
                else:
                    out.append(f"{m5[a][c]['rate']:.3f} / {mh[a][c]['rate']:.3f}{dag}")
            print(f"| {name} | {H} | " + " | ".join(out) + " |")
    fail = unb55 = unb33 = 0
    mx, rt5, rth, rt34 = 0.0, [], [], []
    for cell in r["cells"].values():
        for f in ("5m", "60m"):
            c = cell[f]
            fail, unb55, unb33 = fail + c["fail"], unb55 + c["unbounded055"], unb33 + c["unbounded033"]
            mx = max(mx, c["max_check_absdiff"] or 0.0)
            (rt5 if f == "5m" else rth).append(c["sec_per_path"])
            if f == "60m":
                rt34.append(c["sec_per_path_034"])
    print(f"\nNumerics: numerical failures {fail}; claim 055 singular profiles {unb55}; claim 033 singular {unb33}; "
          f"max reference-check |Δ| {mx:.1e}; seconds per path: 5-minute {min(rt5):.3f}–{max(rt5):.3f}, hourly "
          f"{min(rth):.4f}–{max(rth):.4f}, claim 034 {min(rt34):.4f}–{max(rt34):.4f}")


if __name__ == "__main__":
    main()
