"""Experiment 026: print the Markdown tables of the report from experiments/026/results.json.

    uv run python experiments/026/report.py
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
COLS = ["raw", "d055", "sw_K1", "sw_K40", "sw_K25", "sw_K10"]
HEAD = ["054 raw", "055", "E^sw K1", "K40", "K25", "K10"]


def table(r, names, title, a="0.05"):
    print(f"\n**{title}** (rejection rate at α = {a}; monthly / daily; † marks a column that does not cover the row)\n")
    print("| truth | T | " + " | ".join(HEAD) + " |")
    print("|---|---|" + "---|" * len(HEAD))
    for n in names:
        for T in (2, 5):
            c = r["cells"][f"{n}|{T}"]
            cells = []
            for k in COLS:
                m, d = c["monthly"], c["daily"]
                dag = "" if (d["coverage"][k] and m["coverage"][k]) or n.startswith("cevalt") else "†"
                cells.append(f"{m[a][k]['rate']:.3f} / {d[a][k]['rate']:.3f}{dag}")
            print(f"| {n} | {T} | " + " | ".join(cells) + " |")


def main():
    r = json.load(open(os.path.join(HERE, "results.json")))
    names = list(dict.fromkeys(k.split("|")[0] for k in r["cells"]))
    table(r, [n for n in names if n.startswith("const")], "Constant Gaussian nulls")
    table(r, [n for n in names if n.startswith("switch")], "Single-switch Gaussian nulls")
    table(r, [n for n in names if n.startswith("cevnull")], "Retained CEV nulls")
    table(r, [n for n in names if n.startswith("cevalt")], "CEV alternatives (power)")
    print("\n**e-BH panels, daily, q = 0.10 (all-null mean FDP; mixed mean true discoveries of 10 / mean FDP).**\n")
    print("| T | switch null | " + " | ".join(HEAD) + " |")
    print("|---|---|" + "---|" * len(HEAD))
    for T in (2, 5):
        for s in (0.50, 0.15):
            out = []
            for k in COLS:
                p = r["panels"][f"{T}|s{s:.2f}|{k}|q0.1"]
                out.append(f"{p['allnull']['mean_FDP']:.2f}; {p['mixed']['mean_true']:.1f}/{p['mixed']['mean_FDP']:.2f}"
                           + ("" if p["covered"] else "†"))
            print(f"| {T} | s = {s} | " + " | ".join(out) + " |")
    st, n, amb, sco, fm, cm, viol, unb = {}, 0, 0, 0.0, 0, 0, 0, {}
    for cell in r["cells"].values():
        for f in ("monthly", "daily"):
            c = cell[f]
            for s, v in c["status_counts"].items():
                st[s] = st.get(s, 0) + v
            cs = c["checks_summary"]
            n, amb, fm, cm = n + cs["n"], amb + cs["ambiguous"], fm + cs["fit_mismatch"], cm + cs["cut_mismatch"]
            sco = max(sco, cs["max_score_absdiff"] or 0)
            viol += c["ordering_violations"]
            for k, v in c["unbounded"].items():
                unb[k] = unb.get(k, 0) + v
    print(f"\nNumerics: statuses {st}; reference checks {n} (ambiguous {amb}), max score |Δ| {sco:.1e}, fit mismatches {fm}, "
          f"cut mismatches {cm}, ordering violations {viol}; zero-residual infinity counts {unb}")


if __name__ == "__main__":
    main()
