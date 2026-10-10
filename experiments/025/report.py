"""Experiment 025: print the Markdown tables of the report from experiments/025/results.json.

    uv run python experiments/025/report.py
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
TESTS = [("v1_ebh", "v1 e-BH"), ("raw054_ebh", "054 raw e-BH"), ("sadf_bh", "SADF BH"), ("gsadf_bh", "GSADF BH"),
         ("gsadf_by", "GSADF BY"), ("jkp_m2", "JKP M2"), ("jkp_m1", "JKP M1")]
NULLS = ("gbm", "merton", "regime", "heston")


def f2(x):
    return "–" if x is None else f"{x:.2f}"


def main():
    r = json.load(open(os.path.join(HERE, "results.json")))
    C = r["cells"]
    for q in ("0.05", "0.1"):
        print(f"\n**All-null panels (f = 0): family-wise false-alarm rate (share of panels with any discovery) and mean "
              f"false discoveries per panel, q = {q}.** JKP is per-name verdicts, not a multiple-testing procedure.\n")
        print("| null | m | T | " + " | ".join(t for _, t in TESTS) + " | panel t 5% |")
        print("|---|---|---|" + "---|" * (len(TESTS) + 1))
        for nt in NULLS:
            for m in (20, 100):
                for T in (5, 10):
                    c = C[f"{nt}|f0.00|p0.0|m{m}|T{T}"]
                    cells = [f"{c['tests'][k][q]['FWER_allnull']['mean']:.2f} ({c['tests'][k][q]['false_disc']['mean']:.1f})"
                             for k, _ in TESTS]
                    print(f"| {nt}{'' if nt == 'gbm' else '†'} | {m} | {T} | " + " | ".join(cells)
                          + f" | {c['panel_test_reject']['5%']['mean']:.2f} |")
    for q in ("0.05", "0.1"):
        print(f"\n**Panels with bubbles: mean FDR (SE) and per-name power, q = {q}.**\n")
        print("| null | f | p | m | T | " + " | ".join(t for _, t in TESTS) + " | panel t 5% |")
        print("|---|---|---|---|---|" + "---|" * (len(TESTS) + 1))
        for nt in NULLS:
            for f in (0.10, 0.30):
                for p in (1.5, 2.0):
                    for m in (20, 100):
                        for T in (5, 10):
                            c = C[f"{nt}|f{f:.2f}|p{p:.1f}|m{m}|T{T}"]
                            cells = []
                            for k, _ in TESTS:
                                t = c["tests"][k][q]
                                cells.append(f"{t['FDR']['mean']:.2f} ({t['FDR']['se']:.2f}); {f2(t['power_per_name'])}")
                            print(f"| {nt}{'' if nt == 'gbm' else '†'} | {f:.2f} | {p} | {m} | {T} | " + " | ".join(cells)
                                  + f" | {c['panel_test_reject']['5%']['mean']:.2f} |")
    print("\n**Per-name flag rates at α = 0.05 (single-name versions), pooled over compositions, m and T: null names / "
          "bubbly names.**\n")
    keys = ["v1", "raw054", "sadf", "gsadf", "jkp_m2", "jkp_m1"]
    print("| null type | " + " | ".join(keys) + " |")
    print("|---|" + "---|" * len(keys))
    for nt in NULLS:
        out = []
        for k in keys:
            tot = {"null": [0, 0], "bubbly": [0, 0]}
            for key, c in C.items():
                if not key.startswith(nt + "|"):
                    continue
                for lab in tot:
                    v = c["per_name_flag_rate_a05"][k][lab]
                    if v:
                        tot[lab][0] += v["mean"] * v["n"]
                        tot[lab][1] += v["n"]
            out.append(f"{tot['null'][0] / tot['null'][1]:.3f} / {tot['bubbly'][0] / tot['bubbly'][1]:.3f}")
        print(f"| {nt} | " + " | ".join(out) + " |")
    st, n, amb, rmax, dmax, fm, dm, ji = {}, 0, 0, 0.0, 0.0, 0, 0, []
    for c in C.values():
        for s, v in c["status_counts"].items():
            st[s] = st.get(s, 0) + v
        ck = c["checks"]
        n, amb, fm, dm = n + ck["n"], amb + ck["ambiguous"], fm + ck["fit_mismatch"], dm + ck["decision_mismatch"]
        rmax, dmax = max(rmax, ck["max_raw_absdiff"] or 0), max(dmax, ck["max_d055_absdiff"] or 0)
        ji.append(c["jkp_indeterminate"]["jkp_m2"]["mean"])
    print(f"\nNumerics: statuses {st}; adapter checks {n} (ambiguous {amb}), max |Δ| raw {rmax:.1e}, claim 055 {dmax:.1e}, "
          f"fit mismatches {fm}, decision mismatches {dm}; JKP M2 indeterminate share {min(ji):.2f}–{max(ji):.2f}")


if __name__ == "__main__":
    main()
