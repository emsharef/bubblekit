"""Experiment 023: print the Markdown tables of the report from experiments/023/results.json.

    uv run python experiments/023/report.py
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
HS = (0.0, 0.025, 0.05, 0.10, 0.20, 0.40, 1.00)
COLS = ["raw"] + [f"h{h}" for h in HS] + ["d055"]
HEAD = ["054 raw"] + [f"h={h:g}" for h in HS] + ["055"]


def table(r, truths, title, a="0.05"):
    print(f"\n**{title}** (rejection rate at α = {a}; monthly / daily)\n")
    print("| truth | T | " + " | ".join(HEAD) + " |")
    print("|---|---|" + "---|" * len(HEAD))
    for n in truths:
        for T in (2, 5):
            c = r["cells"][f"{n}|{T}"]
            cells = [f"{c['monthly'][a][k]['rate']:.3f} / {c['daily'][a][k]['rate']:.3f}" for k in COLS]
            print(f"| {n} | {T} | " + " | ".join(cells) + " |")


def main():
    r = json.load(open(os.path.join(HERE, "results.json")))
    names = sorted({k.split("|")[0] for k in r["cells"]})
    gauss = [n for n in names if n.startswith("gauss")]
    order = lambda n: (float(n.split("_b")[1].split("_k")[0]), float(n.split("_k")[1]))
    gauss.sort(key=order)
    table(r, gauss, "Gaussian rows (b, κ); a bounded column covers its row exactly when |b| ≤ h")
    table(r, [n for n in names if n.startswith("cevnull")], "Retained CEV nulls (covered by every column)")
    table(r, [n for n in names if n.startswith("cevalt")], "CEV alternatives (power)")
    print("\n**Paired difference from claim 055 on the alternatives, daily, α = 0.05 (h = 0.20 primary).**\n")
    print("| truth | T | h=0.2 − 055 | SE | h=0.05 − 055 | h=0 − 055 |")
    print("|---|---|---|---|---|---|")
    for n in [n for n in names if n.startswith("cevalt")]:
        for T in (2, 5):
            pv = r["cells"][f"{n}|{T}"]["daily"]["0.05"]["paired_vs_055"]
            print(f"| {n} | {T} | {pv['h0.2']['diff']:+.3f} | {pv['h0.2']['se']:.3f} | {pv['h0.05']['diff']:+.3f} | "
                  f"{pv['h0.0']['diff']:+.3f} |")
    print("\n**e-BH panels, daily, q = 0.10 (all-null mean FDP; mixed mean true discoveries of 10 / mean FDP).**\n")
    print("| T | b | " + " | ".join(HEAD) + " |")
    print("|---|---|" + "---|" * len(HEAD))
    for T in (2, 5):
        for b in (-0.40, -0.20, -0.05, 0.0, 0.05, 0.20, 0.40):
            cells = []
            for k in COLS:
                p = r["panels"][f"{T}|b{b:+.2f}|{k}|q0.1"]
                cells.append(f"{p['allnull']['mean_FDP']:.2f}; {p['mixed']['mean_true']:.1f}/{p['mixed']['mean_FDP']:.2f}")
            print(f"| {T} | {b:+.2f} | " + " | ".join(cells) + " |")
    # numerics
    st, prof, sco, fitm, amb, viol, margin, kinds = {}, 0.0, 0.0, 0, 0, 0, 0, {}
    for key, cell in r["cells"].items():
        for f in ("monthly", "daily"):
            c = cell[f]
            for s, v in c["status_counts"].items():
                st[s] = st.get(s, 0) + v
            cs = c["checks_summary"]
            prof = max(prof, cs["max_profile_absdiff"] or 0.0)
            sco = max(sco, cs["max_score_absdiff"] or 0.0)
            fitm += cs["fit_mismatch"]
            amb += cs["ambiguous"]
            viol += c["ordering_violations"]
            margin += c["train_margin_small"]
            for kk, v in c["h0.2_profile_kind"].items():
                kinds[kk] = kinds.get(kk, 0) + v
    print(f"\nNumerics: statuses {st}; checks max profile |Δ| {prof:.2e}, max score |Δ| {sco:.2e}, fit mismatches {fitm}, "
          f"ambiguous {amb}, ordering violations {viol}, small training margins {margin}; h = 0.20 active profile {kinds}")


if __name__ == "__main__":
    main()
