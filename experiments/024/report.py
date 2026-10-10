"""Experiment 024: print the Markdown tables of the report from experiments/024/results.json.

    uv run python experiments/024/report.py
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
COLS = ["raw", "d055", "b056", "r0.30-0.30", "r0.25-0.35", "r0.20-0.45", "r0.15-0.60", "r0.10-1.00"]
HEAD = ["054 raw", "055", "056 (B)", "C=[.30,.30]", "[.25,.35]", "[.20,.45]", "[.15,.60]", "[.10,1]"]


def cell(c, a, k, mark):
    v = c[a][k]["rate"]
    return f"{v:.3f}" + ("" if c["coverage"][k] else "†") if mark else f"{v:.3f}"


def table(r, truths, title, freq, a="0.05", mark=True):
    print(f"\n**{title}** ({freq}, rejection rate at α = {a}; † marks a column that does not cover the row)\n")
    print("| truth | T | " + " | ".join(HEAD) + " |")
    print("|---|---|" + "---|" * len(HEAD))
    for n in truths:
        for T in (2, 5):
            c = r["cells"][f"{n}|{T}"][freq]
            print(f"| {n} | {T} | " + " | ".join(cell(c, a, k, mark) for k in COLS) + " |")


def main():
    r = json.load(open(os.path.join(HERE, "results.json")))
    names = sorted({k.split("|")[0] for k in r["cells"]})
    gauss = sorted([n for n in names if n.startswith("gauss")],
                   key=lambda n: (float(n.split("_b")[1].split("_k")[0]), float(n.split("_k")[1])))
    table(r, gauss, "Gaussian rows (b, κ)", "daily")
    table(r, [n for n in names if n.startswith("cevnull")], "Retained CEV nulls", "daily")
    for f in ("daily", "monthly"):
        table(r, [n for n in names if n.startswith("cevalt")], "CEV alternatives (power)", f, mark=False)
    print("\n**Paired difference from claim 056 (B only) on the alternatives, daily, α = 0.05.**\n")
    print("| truth | T | " + " | ".join(HEAD[3:]) + " |")
    print("|---|---|" + "---|" * 5)
    for n in [n for n in names if n.startswith("cevalt")]:
        for T in (2, 5):
            pv = r["cells"][f"{n}|{T}"]["daily"]["0.05"]["paired_vs_b056"]
            print(f"| {n} | {T} | " + " | ".join(f"{pv[k]['diff']:+.3f} ({pv[k]['se']:.3f})" for k in COLS[3:]) + " |")
    print("\n**e-BH panels, daily, q = 0.10, Gaussian κ = 0.35 nulls (all-null mean FDP; mixed mean true of 10 / FDP).**\n")
    print("| T | b | " + " | ".join(HEAD) + " |")
    print("|---|---|" + "---|" * len(HEAD))
    for T in (2, 5):
        for b in (-0.40, -0.20, -0.05, 0.0, 0.05, 0.20, 0.40):
            out = []
            for k in COLS:
                p = r["panels"][f"{T}|b{b:+.2f}|{k}|q0.1"]
                out.append(f"{p['allnull']['mean_FDP']:.2f}; {p['mixed']['mean_true']:.1f}/{p['mixed']['mean_FDP']:.2f}"
                           + ("" if p["covered"] else "†"))
            print(f"| {T} | {b:+.2f} | " + " | ".join(out) + " |")
    st, prof, sco, fitm, amb, viol, fails, kinds = {}, 0.0, 0.0, 0, 0, 0, {}, {}
    for key, cl in r["cells"].items():
        for f in ("monthly", "daily"):
            c = cl[f]
            for s, v in c["status_counts"].items():
                st[s] = st.get(s, 0) + v
            cs = c["checks_summary"]
            prof, sco = max(prof, cs["max_profile_absdiff"] or 0), max(sco, cs["max_score_absdiff"] or 0)
            fitm, amb, viol = fitm + cs["fit_mismatch"], amb + cs["ambiguous"], viol + c["ordering_violations"]
            for k, v in c["rect_failures"].items():
                fails[k] = fails.get(k, 0) + v
            for k, v in c["r0.20-0.45_profile_kind"].items():
                kinds[k] = kinds.get(k, 0) + v
    print(f"\nNumerics: statuses {st}; checks max profile |Δ| {prof:.2e}, max score |Δ| {sco:.2e}, fit mismatches {fitm}, "
          f"ambiguous {amb}, ordering violations {viol}; rectangle failures {fails}; primary active categories {kinds}")


if __name__ == "__main__":
    main()
