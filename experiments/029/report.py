"""Experiment 029: print the Markdown tables of the report from experiments/029/results.json.

    uv run python experiments/029/report.py
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
COLS = ["v1", "all", "allcap", "sel", "sel_shifted", "safe", "oracle"]
HEAD = ["v1", "E_all", "E_all,cap", "E_sel raw*", "E_sel shifted", "E_safe", "oracle (diag.)"]
EBH = ["v1", "all", "allcap", "safe", "oracle", "sel"]
EHEAD = ["v1", "E_all", "E_all,cap", "E_safe", "oracle (diag.)", "E_sel raw*"]


def f(x, k="mean", d=3):
    if x is None:
        return "–"
    v = x.get(k) if isinstance(x, dict) else x
    return "–" if v is None else f"{v:.{d}f}"


def fse(x, d=3):
    if x is None:
        return "–"
    return f"{x['mean']:.{d}f} ± {x['se']:.{d}f}" if x.get("se") is not None else f"{x['mean']:.{d}f}"


def main():
    r = json.load(open(os.path.join(HERE, "results.json")))
    C = r["cells"]
    for a in ("0.05", "0.1"):
        print(f"\n**Per-name rejection at α = {a}: null names / CEV names** (mean over panels of each panel's rejected "
              f"fraction; * raw E_sel is uncalibrated at 1/α)\n")
        print("| cell | " + " | ".join(HEAD) + " |")
        print("|---|" + "---|" * len(HEAD))
        for cell, v in C.items():
            row = []
            for c in COLS:
                x = v[a].get(c)
                if x is None:
                    row.append("–")
                    continue
                s = f(x["null_rate"])
                if x.get("alt_rate") is not None:
                    s += " / " + f(x["alt_rate"])
                row.append(s)
            print(f"| {cell} | " + " | ".join(row) + " |")
    for q in ("0.05", "0.1"):
        print(f"\n**e-BH at q = {q}, original m = 20: FDR / TDP** (panel means; * raw E_sel e-BH is uncalibrated)\n")
        print("| cell | " + " | ".join(EHEAD) + " | TDP safe − all | TDP safe − all,cap |")
        print("|---|" + "---|" * (len(EHEAD) + 2))
        for cell, v in C.items():
            e = v[f"ebh_{q}"]
            row = []
            for c in EBH:
                x = e.get(c)
                if x is None:
                    row.append("–")
                    continue
                s = f(x["FDR"])
                if x.get("TDP") is not None:
                    s += " / " + f(x["TDP"])
                row.append(s)
            row += [fse(e.get("TDP_safe_minus_all")), fse(e.get("TDP_safe_minus_allcap"))]
            print(f"| {cell} | " + " | ".join(row) + " |")
    print("\n**Clock selection diagnostics** (200 panels per cell)\n")
    print("| cell | true-clock exclusions (95% upper) | mean |C| | forecast clock = truth | log T at truth: mean / max "
          "| ref. fallbacks / unresolved |")
    print("|---|---|---|---|---|---|")
    for cell, v in C.items():
        sizes = v["retained_size"]
        mean_c = sum(i * n for i, n in enumerate(sizes)) / max(1, sum(sizes))
        te = v.get("true_exclusions")
        tx = "–" if te is None else f"{te['count']} ({te['upper95']:.4f})"
        lt = v.get("logT_true")
        lts = "–" if lt is None else f"{lt['mean']:.2f} / {lt['max']:.2f}"
        fi = v.get("forecast_is_true")
        print(f"| {cell} | {tx} | {mean_c:.2f} | {'–' if fi is None else f'{fi:.3f}'} | {lts} | "
              f"{v['ref_fallbacks']} / {v['ref_unresolved']} |")
    print("\n**Denominator gains (log), null names / CEV names**\n")
    print("| cell | Gaussian gain mean (share > 0) | complete gain mean (share > 0) | G0 erases a Gaussian gain | "
          "tested max profile excluded | cap binds | mean log E_safe − log E_all |")
    print("|---|---|---|---|---|---|---|")
    for cell, v in C.items():
        parts = []
        for lab in ("null", "alt"):
            g = v.get(f"gains_{lab}")
            parts.append(g)
        def two(fn):
            return " / ".join(fn(g) for g in parts if g is not None)
        print(f"| {cell} | {two(lambda g: f'{g['gauss_mean']:.2f} ({g['gauss_pos_share']:.2f})')} | "
              f"{two(lambda g: f'{g['complete_mean']:.2f} ({g['complete_pos_share']:.2f})')} | "
              f"{two(lambda g: f'{g['g0_erases_share']:.2f}')} | {two(lambda g: f'{g['argmaxD_excluded_share']:.2f}')} | "
              f"{two(lambda g: str(g['cap_binds']))} | {two(lambda g: f'{g['net_safe_minus_all_mean']:.3f}')} |")
    print("\n**Null-name mean of E (level scale), panel mean ± SE**\n")
    print("| cell | v1 | E_all | E_all,cap | E_sel raw | E_safe | oracle |")
    print("|---|---|---|---|---|---|---|")
    for cell, v in C.items():
        m = v["null_mean_E"]
        print(f"| {cell} | " + " | ".join(fse(m.get(c), 4) for c in ("v1", "all", "allcap", "sel", "safe", "oracle"))
              + " |")
    fail = sum(v["fail"] for v in C.values())
    sing = sum(v["singular"] for v in C.values())
    chk = [ck for v in C.values() for ck in v["checks"]]
    mx = max(max([ck["ref_profile_absdiff"], ck["ref_logq_absdiff"]] +
                 [t.get(k, 0) for t in ck["targets"] for k in ("raw_absdiff", "all_absdiff", "safe_absdiff")])
             for ck in chk)
    ok = all(ck["retained_match"] and ck["selection_invariant"] and ck["qref_weights_ok"] and
             all(t.get("decision_match", True) for t in ck["targets"]) for ck in chk)
    sec = [v["sec_per_panel"] for v in C.values()]
    print(f"\nNumerics: failed names {fail}; names with a singular Gaussian profile {sing}; spot checks "
          f"({len(chk)} panels) max |Δ| {mx:.1e}, sets, decisions, mixture and selection invariance all match: {ok}; "
          f"seconds per panel {min(sec):.3f}–{max(sec):.3f}; wall {r['settings']['wall_seconds']:.0f} s.")


if __name__ == "__main__":
    main()
