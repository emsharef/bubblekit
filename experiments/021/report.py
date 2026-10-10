"""Experiment 021: print the Markdown tables of the report from experiments/021/results.json.

    uv run python experiments/021/report.py
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
TESTS = [("lab_0.05", "E^drift 5%"), ("lab_0.1", "E^drift 10%"), ("lab054_0.05", "054 raw 5%"),
         ("sadf_5%", "SADF 5%"), ("gsadf_5%", "GSADF 5%"), ("jkp_m2", "JKP M2"), ("jkp_m1", "JKP M1")]


def f(x):
    return "–" if x is None else f"{x:.2f}"


def main():
    r = json.load(open(os.path.join(HERE, "results.json")))
    S = r["summary"]
    for kind in ("adj", "close"):
        print(f"\n**Per-name flag rates ({kind} closes).**\n")
        print("| set | variant | names | " + " | ".join(t for _, t in TESTS) + " | panel t 5% | panel J 5% |")
        print("|---" * (len(TESTS) + 5) + "|")
        for sign in ("positive", "negative"):
            for var in ("full", "to_peak"):
                c = S[f"{sign}|{var}|{kind}"]
                print(f"| {sign} | {var} | {c['names']} | " + " | ".join(f(c['per_name'][k]['rate']) for k, _ in TESTS)
                      + f" | {f(c['panel']['panel_t_5%']['rate'])} ({c['panel']['panel_t_5%']['n']}) | "
                      f"{f(c['panel']['panel_J_5%']['rate'])} |")
        print("\n| difference (pos − neg) | variant | | " + " | ".join(t for _, t in TESTS) + " | | |")
        print("|---" * (len(TESTS) + 5) + "|")
        for var in ("full", "to_peak"):
            dd = r["positive_minus_negative"][f"{var}|{kind}"]
            print(f"| | {var} | | " + " | ".join(f"{dd[k]['diff']:+.2f} ± {dd[k]['se_descriptive']:.2f}" for k, _ in TESTS)
                  + " | | |")
    print("\n**Per row (adjusted closes, full / to-peak): names flagged by E^drift at 5%, 054 raw, GSADF 5%, JKP M2; "
          "panel t at 5%.**\n")
    print("| row | variant | names | E^drift | 054 raw | GSADF | JKP M2 | panel t | statuses |")
    print("|---|---|---|---|---|---|---|---|---|")
    for row in r["rows"]:
        ss = [s for s in row["series"] if s["kind"] == "adj" and "flags" in s]
        cnt = lambda k: sum(s["flags"][k] for s in ss)
        st = {}
        for s in ss:
            for x in s["status"]:
                st[x] = st.get(x, 0) + 1
        flagged = [s["name"] for s in ss if s["flags"]["lab_0.05"]]
        pt = row["panel"].get("adj")
        print(f"| {row['row']} | {row['variant']} | {len(ss)} | {cnt('lab_0.05')}"
              + (f" ({', '.join(flagged)})" if flagged else "")
              + f" | {cnt('lab054_0.05')} | {cnt('gsadf_5%')} | {cnt('jkp_m2')} | "
              + (f"{pt['t']:.2f}{'*' if pt['flags']['panel_t_5%'] else ''}" if pt else "–")
              + " | " + ", ".join(f"{k} {v}" for k, v in sorted(st.items())) + " |")


if __name__ == "__main__":
    main()
