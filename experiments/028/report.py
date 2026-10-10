"""Experiment 028: print the Markdown tables of the report from experiments/028/results.json.

    uv run python experiments/028/report.py
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
HL_HOURLY = [(2, 2), (2, 4), (4, 2), (4, 4)]
HL_5M = [(2, 2), (4, 2)]


def col(b, h, l):
    return f"E034_{b}_h{h}_l{l}"


def rate(c, a, k):
    v = c[a].get(k)
    return "–" if v is None else f"{v['rate']:.3f}"


def main():
    r = json.load(open(os.path.join(HERE, "results.json")))
    C = r["cells"]
    names = list(dict.fromkeys(k.split("|")[0] for k in C))
    for a in ("0.05", "0.1"):
        cols = ["E033_exact", "E033_round"] + [col(b, h, l) for b in ("W", "N") for h, l in HL_HOURLY]
        head = ["033 exact", "033 on rounded (i)"] + [f"034 {b} h{h} ℓ{l}" for b in ("W", "N") for h, l in HL_HOURLY]
        print(f"\n**Hourly, 250 sessions, α = {a}** (600 paths per null cell, 400 per alternative; † marks a claim-034 "
              f"column whose box does not cover the null)\n")
        print("| truth | " + " | ".join(head) + " |")
        print("|---|" + "---|" * len(head))
        for n in names:
            c = C[f"{n}|250"]["60m"]
            cov = C[f"{n}|250"].get("coverage_034")
            out = []
            for k in cols:
                dag = ""
                if cov is not None and k.startswith("E034") and not cov[k.split("_")[1]]:
                    dag = "†"
                out.append(rate(c, a, k) + dag)
            print(f"| {n} | " + " | ".join(out) + " |")
        cols5 = ["E033_exact", "E033_round"] + [col(b, h, l) for b in ("W", "N") for h, l in HL_5M]
        head5 = ["033 exact", "033 on rounded (i)"] + [f"034 {b} h{h} ℓ{l}" for b in ("W", "N") for h, l in HL_5M]
        print(f"\n**5-minute, 60 sessions, α = {a}** (claim 034 on the first 200 paths per cell; 033 columns on that same "
              f"subset; † as above)\n")
        print("| truth | " + " | ".join(head5) + " |")
        print("|---|" + "---|" * len(head5))
        for n in names:
            c = C[f"{n}|60"]["5m_034_subset"]
            cov = C[f"{n}|60"].get("coverage_034")
            out = []
            for k in cols5:
                dag = "†" if cov is not None and k.startswith("E034") and not cov[k.split("_")[1]] else ""
                out.append(rate(c, a, k) + dag)
            print(f"| {n} | " + " | ".join(out) + " |")
        print(f"\n**5-minute, claim 033 columns on all paths, α = {a}** (2,000 paths per null cell, 1,000 per "
              f"alternative; 60 / 250 sessions)\n")
        print("| truth | 033 exact | 033 on rounded (i) |")
        print("|---|---|---|")
        for n in names:
            c60, c250 = C[f"{n}|60"]["5m"], C[f"{n}|250"]["5m"]
            print(f"| {n} | {rate(c60, a, 'E033_exact')} / {rate(c250, a, 'E033_exact')} | "
                  f"{rate(c60, a, 'E033_round')} / {rate(c250, a, 'E033_round')} |")
    print("\n**Cost (seconds per path) and branch-and-bound boxes evaluated, hourly 250 sessions (mean over cells).**\n")
    cols = [col(b, h, l) for b in ("W", "N") for h, l in HL_HOURLY]
    print("| column | seconds per path | boxes evaluated |")
    print("|---|---|---|")
    for k in cols:
        secs = [C[f"{n}|250"]["60m"]["sec_per_path_034"][k] for n in names]
        ev = [C[f"{n}|250"]["60m"]["evals"][k] for n in names]
        print(f"| {k} | {sum(secs) / len(secs):.2f} | {sum(ev) / len(ev):.0f} |")
    edge, chk = {}, []
    for n in names:
        for f in ("60m",):
            e = C[f"{n}|250"][f]["edge"]
            for k, v in e.items():
                if isinstance(v, dict):
                    edge[k] = edge.get(k, 0) + sum(v.values())
                else:
                    edge[k] = edge.get(k, 0) + v
            chk += C[f"{n}|250"][f]["checks"]
        e = C[f"{n}|60"]["5m_034_subset"]["edge"]
        for k, v in e.items():
            edge[k] = edge.get(k, 0) + (sum(v.values()) if isinstance(v, dict) else v)
    bb = max(ck["bb_vs_full"] for ck in chk)
    ref = max(ck.get("ref_logD_100", 0) for ck in chk)
    print(f"\nEdge cases (all claim-034 cells): {edge}. Checks: branch and bound vs full cover max |Δ| {bb:.1e}; "
          f"reference denominator (100 increments) max |Δ| {ref:.1e}.")


if __name__ == "__main__":
    main()
