"""Experiment 051 (D35 item 25): the repaired score on real data, calibrated on a fixed historical reference, against
v1 and calibrated GSADF, evaluated as item 16 did (experiment 039).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/051/run.py manifest|smoke|full|analyze     (start from inside .worktrees/analyst)

manifest: builds the evaluation frame, the 10,000-window sample, the consensus records and the calibration reference
(math's contract, checks/d35-item25-reference/README.md) from metadata and training-period prices only; writes
manifest.json. No fitter runs and no forward outcome is read. Committed before any score.
smoke: scores 14 windows (timing only; scores not read). full: scores every manifest window on 7 workers, then the
analysis; writes results.json, summary.csv and windows.csv.gz.
"""
from fractions import Fraction
import csv
import datetime as dt
import gzip
import hashlib
import importlib.util
import json
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


r050 = _load("r050", "experiments/050/run.py")      # fitter, calibrate.py, v1 and GSADF exactly as in 050
r021, r039, F, cal = r050.r021, r050.r039, r050.F, r050.cal
WORKERS = 7
NPRICE, TRAIN = 379, 126
H = (63, 126)
COVERAGE = 0.99                                    # 039's forward-coverage rule
SAMPLE_SEED, N_SAMPLE = 20261051, 10000
REF_TAG, N_REF = "20261151", 999
REF_FROM, REF_TO = dt.date(1995, 1, 1), dt.date(2010, 12, 31)
SPLIT = dt.date(2011, 1, 1)
CALM = {"stock_vol": 0.30, "stock_dd": 0.15, "mkt_vol": 0.20, "mkt_dd": 0.10}
LEVELS = (Fraction(1, 20), Fraction(1, 100), Fraction(1, 10))       # primary, charter ROC, secondary
SCORES = ("new", "v1", "gsadf")
FAIL_LOW = r050.FAIL_LOW
DK_LAG = 27                                        # ceil(1.5 x 18 months), 039's rule for an 18-month input
BOOT_SEED, AUC_SEED, NBOOT = 20261351, 20261251, 1000
PERIODS = {"1995-99": (1995, 1999), "2003-07": (2003, 2007), "2009-19": (2009, 2019), "2023-26": (2023, 2026)}
BUDGETS = (0.0, 0.01, 0.025, 0.05)


def iso(d):
    return d.isoformat()


def calm_metrics(p):
    """Annualized RMS log-return volatility and drawdown on the first 127 prices only."""
    q = np.asarray(p[:TRAIN + 1], float)
    r = np.diff(np.log(q))
    vol = math.sqrt(252 * float(np.mean(r * r)))
    dd = float(np.max(1 - q / np.maximum.accumulate(q)))
    return vol, dd


def is_calm(sm, mm):
    return (sm[0] <= CALM["stock_vol"] and sm[1] <= CALM["stock_dd"]
            and mm[0] <= CALM["mkt_vol"] and mm[1] <= CALM["mkt_dd"])


def name_index(sym, gd):
    """Presence and prices of a name on the ^GSPC session calendar; off-calendar dates are ignored."""
    d, p = r039.load(sym)
    pos = np.searchsorted(gd, d)
    ok = (pos < len(gd)) & (gd[np.minimum(pos, len(gd) - 1)] == d) & np.isfinite(p) & (p > 0)
    price = np.full(len(gd), np.nan)
    price[pos[ok]] = p[ok]
    present = ~np.isnan(price)
    return price, np.r_[0, np.cumsum(present)]


def build_manifest():
    gd, gp = r039.load("^GSPC")
    ms = r039.month_starts(gd)
    _, syms = r039.universe()
    frame, refcand = [], []
    for sym in syms:
        price, cs = name_index(sym, gd)
        for ke in ms:
            k0 = ke - (NPRICE - 1)
            if k0 < 0 or cs[ke + 1] - cs[k0] != NPRICE:
                continue                                       # not 379 complete consecutive sessions
            wid = (sym, iso(gd[k0]), iso(gd[ke]))
            if ke + H[-1] < len(gd):                            # evaluation frame: 039's forward coverage rule
                fwd = cs[ke + H[-1] + 1] - cs[ke + 1]
                if fwd >= COVERAGE * H[-1]:
                    frame.append({"id": wid, "k0": int(k0), "ke": int(ke), "fwd_sessions": int(fwd)})
            if REF_FROM <= gd[ke] <= REF_TO:
                sm = calm_metrics(price[k0:ke + 1])
                mm = calm_metrics(gp[k0:ke + 1])
                if is_calm(sm, mm):
                    refcand.append({"id": wid, "k0": int(k0), "ke": int(ke), "stock": sm, "mkt": mm})
    frame.sort(key=lambda w: w["id"])
    rng = np.random.default_rng(SAMPLE_SEED)
    pick = sorted(rng.choice(len(frame), N_SAMPLE, replace=False).tolist())
    sample = [frame[i] for i in pick]
    # consensus: 021's full-window records rebuilt to 379 ^GSPC sessions ending at the original endpoint
    sel = json.load(open(os.path.join(ROOT, "experiments", "021", "selection.json")))
    gidx = {d: i for i, d in enumerate(gd)}
    consensus = []
    for row in r021.build_rows(sel):
        if row["variant"] != "full":
            continue
        for nm in row["names"]:
            dts, adj, _, _ = r021.series(nm)
            k = dts <= r021.d(row["end"])
            rec = {"row": row["row"], "sign": row["sign"], "name": nm, "original": [row["start"], row["end"]]}
            if not k.any() or dts[k][-1] not in gidx:
                rec["unavailable"] = "endpoint not a ^GSPC session"
            else:
                ke = gidx[dts[k][-1]]
                k0 = ke - (NPRICE - 1)
                have = dict(zip(dts, adj))
                need = gd[max(k0, 0):ke + 1]
                if k0 < 0 or not all(x in have and np.isfinite(have[x]) and have[x] > 0 for x in need):
                    rec["unavailable"] = "incomplete 379-session history on the ^GSPC calendar"
                else:
                    rec.update(id=(nm, iso(gd[k0]), iso(gd[ke])), k0=int(k0), ke=int(ke),
                               lookback_changed=iso(gd[k0]) != row["start"])
            consensus.append(rec)
    # reference: exclude evaluation IDs, hash order, no shared date within a name, stop at 999
    excl = {tuple(w["id"]) for w in sample} | {tuple(c["id"]) for c in consensus if "id" in c}
    pool = [c for c in refcand if tuple(c["id"]) not in excl]
    key = lambda c: (hashlib.sha256(f"{REF_TAG}|{c['id'][0]}|{c['id'][1]}|{c['id'][2]}".encode()).hexdigest(),
                     tuple(c["id"]))
    pool.sort(key=key)
    taken, ref = {}, []
    for c in pool:
        iv = taken.setdefault(c["id"][0], [])
        if any(not (c["ke"] < a or c["k0"] > b) for a, b in iv):
            continue
        iv.append((c["k0"], c["ke"]))
        ref.append(c)
        if len(ref) == N_REF:
            break
    # same-name overlap check (must be empty) and cross-name calendar overlap (reported)
    same = sum(1 for s, iv in taken.items() for i, a in enumerate(iv) for b in iv[i + 1:]
               if not (a[1] < b[0] or a[0] > b[1]))
    ends = [c["id"][2][:4] for c in ref]
    man = {
        "frame_count": len(frame), "sample_seed": SAMPLE_SEED, "sample": [w["id"] for w in sample],
        "sample_meta": [{"k0": w["k0"], "ke": w["ke"], "fwd_sessions": w["fwd_sessions"]} for w in sample],
        "reference_candidates_calm": len(refcand), "reference_candidates_after_exclusion": len(pool),
        "reference": [c["id"] for c in ref],
        "reference_features": [{"stock": c["stock"], "mkt": c["mkt"]} for c in ref],
        "reference_count": len(ref), "reference_names": len({c["id"][0] for c in ref}),
        "reference_end_years": {y: ends.count(y) for y in sorted(set(ends))},
        "reference_same_name_overlaps": same,
        "consensus": consensus,
        "cache": {s: hashlib.sha256(open(os.path.join(ROOT, "data", "d24", f"yahoo_{s}.json"), "rb").read()).hexdigest()
                  for s in sorted({w["id"][0] for w in sample + ref} | {"^GSPC"})},
        "calendar": {"first": iso(gd[0]), "last": iso(gd[-1]), "sessions": int(len(gd))},
    }
    with open(os.path.join(HERE, "manifest.json"), "w") as fh:
        json.dump(man, fh, default=str)
    print(json.dumps({k: man[k] for k in ("frame_count", "reference_candidates_calm",
                                          "reference_candidates_after_exclusion", "reference_count",
                                          "reference_names", "reference_same_name_overlaps")},
                     default=str), "consensus available",
          sum("id" in c for c in consensus), "of", len(consensus), "cache files", len(man["cache"]))


# ---- scoring ----------------------------------------------------------------------------------------------------
def score_window(task):
    kind, i, sym, k0, ke = task
    t0 = time.perf_counter()
    gd, gp = r039.load("^GSPC")
    if kind == "consensus":
        dts, adj, _, _ = r021.series(sym)
        have = dict(zip(dts, adj))
        P = np.array([have[d] for d in gd[k0:ke + 1]], float)
    else:
        price, _ = name_index(sym, gd)
        P = price[k0:ke + 1]
    R = np.diff(np.log(P))
    sel, runs = F.fit_window(R, training=TRAIN)
    nul, alt = sel["null"], sel["alt"]
    s = cal.score_fit(cal.FitPair(nul["loglik"] if nul else float("nan"), alt["loglik"] if alt else float("nan"),
                                  nul is not None, alt is not None))
    out = {"kind": kind, "i": i, "new": s.value, "new_status": s.status, "gap": s.signed_gap,
           "null_beta": nul["params"]["beta"] if nul else None, "alt_beta": alt["params"]["beta"] if alt else None,
           "alt_boundary": alt["boundary_selected"] if alt else None,
           "runs": len(runs), "runs_accepted": sum(r.accepted for r in runs),
           "runs_not_success": sum(not r.success for r in runs), "penalty_evals": sum(r.penalty_evals for r in runs)}
    out["v1"], out["v1_status"] = r050.v1_score(P)
    out["gsadf"], out["gsadf_status"] = r050.gsadf_score(P)
    out["calm"] = is_calm(calm_metrics(P), calm_metrics(gp[k0:ke + 1]))
    if kind == "sample":                                # forward outcomes: 039's definitions, from the last close
        price, _ = name_index(sym, gd)
        fp = price[ke:ke + H[-1] + 1]
        fp = fp[~np.isnan(fp)]
        out.update(r039.forward(fp))
    out["seconds"] = time.perf_counter() - t0
    return out


def build_tasks(man):
    gd, _ = r039.load("^GSPC")
    gi = {iso(d): i for i, d in enumerate(gd)}
    T = []
    for i, w in enumerate(man["reference"]):
        T.append(("reference", i, w[0], gi[w[1]], gi[w[2]]))
    for i, (w, m) in enumerate(zip(man["sample"], man["sample_meta"])):
        T.append(("sample", i, w[0], m["k0"], m["ke"]))
    for i, c in enumerate(man["consensus"]):
        if "id" in c:
            T.append(("consensus", i, c["name"], c["k0"], c["ke"]))
    return T


# ---- analysis ---------------------------------------------------------------------------------------------------
def regress(rows, gd_month):
    """039's specification: percentile ranks within end date, intercept; DK primary (end-month groups, lag 27);
    two-way (end date, name) robustness; end-date fixed effects secondary; frozen pre-2011 coefficients on the holdout."""
    end = np.array([r["end"] for r in rows])
    month = np.array([r["end"][:7] for r in rows])
    names = np.array([r["sym"] for r in rows])
    rk = {sc: r039.pct_rank(np.array([r[sc] for r in rows], float), end) for sc in SCORES}
    out = {}
    for h in H:
        for oc in (f"mdd{h}", f"ret{h}"):
            y = np.array([r[oc] for r in rows], float)
            for spec in [[s] for s in SCORES] + [list(SCORES)]:
                X = np.column_stack([np.ones(len(y))] + [rk[s] for s in spec])
                b, u = r039.ols(y, X)
                dk = r039.dk_se(X, u, month, DK_LAG)
                tw = r039.twoway_se(X, u, end, names)
                # end-date fixed effects (within transformation)
                Xd = np.column_stack([rk[s] for s in spec])
                yd, Xdd = y.copy(), Xd.copy()
                for g in np.unique(end):
                    m = end == g
                    yd[m] -= yd[m].mean()
                    Xdd[m] -= Xdd[m].mean(axis=0)
                bfe, ufe = r039.ols(yd, Xdd)
                sefe = r039.dk_se(Xdd, ufe, month, DK_LAG)
                key = f"{oc}|{'+'.join(spec)}"
                out[key] = {"coef": b[1:].tolist(), "se_dk": dk[1:].tolist(), "se_twoway": tw[1:].tolist(),
                            "coef_fe": bfe.tolist(), "se_fe_dk": sefe.tolist(), "n": int(len(y)),
                            "r2": float(1 - u.var() / y.var())}
                # out of sample: train rows whose whole outcome interval ends before 2011; holdout full input >= 2011
                tr = np.array([r[f"out_end{h}"] < iso(SPLIT) for r in rows])
                te = np.array([r["start"] >= iso(SPLIT) for r in rows])
                if tr.sum() > 10 and te.sum() > 10:
                    bt, _ = r039.ols(y[tr], X[tr])
                    pred = X[te] @ bt
                    base = y[tr].mean()
                    sse, sst = np.sum((y[te] - pred) ** 2), np.sum((y[te] - base) ** 2)
                    oos = float(1 - sse / sst)
                    tm = month[te]
                    um = np.unique(tm)
                    rng = np.random.default_rng(np.random.SeedSequence([BOOT_SEED, h, len(spec)]))
                    blocks = [um[i:i + 18] for i in range(len(um))]
                    boots = []
                    for _ in range(NBOOT):
                        pick = []
                        while len(pick) < len(um):
                            pick += list(blocks[rng.integers(len(blocks))])
                        idx = np.concatenate([np.flatnonzero(tm == m) for m in pick[:len(um)]])
                        yy, pp = y[te][idx], pred[idx]
                        boots.append(1 - np.sum((yy - pp) ** 2) / np.sum((yy - base) ** 2))
                    out[key].update(oos_r2=oos, oos_se=float(np.std(boots)), n_train=int(tr.sum()), n_test=int(te.sum()))
    return out


def auc_block(recs, sc, rng):
    pos = np.array([x[sc] for x in recs if x["pos"]], float)
    neg = np.array([x[sc] for x in recs if not x["pos"]], float)
    auc = float((pos[:, None] > neg[None, :]).mean() + 0.5 * (pos[:, None] == neg[None, :]).mean())
    clusters = sorted({x["row"] for x in recs})
    boots = []
    for _ in range(NBOOT):
        pick = rng.choice(clusters, len(clusters), replace=True)
        P = np.array([x[sc] for c in pick for x in recs if x["row"] == c and x["pos"]], float)
        N = np.array([x[sc] for c in pick for x in recs if x["row"] == c and not x["pos"]], float)
        if P.size and N.size:
            boots.append((P[:, None] > N[None, :]).mean() + 0.5 * (P[:, None] == N[None, :]).mean())
    return {"auc": auc, "auc_ci95": [float(np.quantile(boots, 0.025)), float(np.quantile(boots, 0.975))],
            "n_pos": int(pos.size), "n_neg": int(neg.size)}


def analyze(man, recs, wall):
    gd, _ = r039.load("^GSPC")
    ref = [r for r in recs if r["kind"] == "reference"]
    cut = {sc: {str(a): cal.rank_cutoff([r[sc] for r in ref], a) for a in LEVELS} for sc in SCORES}
    res = {"wall_seconds": wall, "reference_count": len(ref), "cutoffs": cut,
           "reference_status": {s: sum(r["new_status"] == s for r in ref) for s in sorted({r["new_status"] for r in ref})},
           "rank_index": {str(a): -(-((len(ref) + 1) * (1 - a)).numerator // ((len(ref) + 1) * (1 - a)).denominator)
                          for a in LEVELS},
           "claim045_assumed_budget_bounds": {str(a): {str(e): min(1.0, float(a) + e) for e in BUDGETS} for a in LEVELS}}
    S = sorted([r for r in recs if r["kind"] == "sample"], key=lambda r: r["i"])
    for r in S:
        sym, start, end = man["sample"][r["i"]]
        meta = man["sample_meta"][r["i"]]
        r.update(sym=sym, start=start, end=end)
        for h in H:
            r[f"out_end{h}"] = iso(gd[min(meta["ke"] + h, len(gd) - 1)])
    flag = lambda r, sc, a: cal.flag(r[sc], cut[sc][str(a)])

    def rates(rows):
        o = {"n": len(rows)}
        for sc in SCORES:
            for a in LEVELS:
                k = sum(flag(r, sc, a) for r in rows)
                o[f"{sc}|{a}"] = {"flags": k, "rate": k / len(rows) if rows else None}
        return o
    groups = {"all": S, "holdout (start >= 2011)": [r for r in S if r["start"] >= iso(SPLIT)],
              "retrospective (start < 2011)": [r for r in S if r["start"] < iso(SPLIT)]}
    res["universe"] = {}
    for gname, G in groups.items():
        blk = {"all starts": rates(G), "calm starts": rates([r for r in G if r["calm"]]),
               "other starts": rates([r for r in G if not r["calm"]])}
        blk["periods"] = {p: rates([r for r in G if a <= int(r["end"][:4]) <= b]) for p, (a, b) in PERIODS.items()}
        res["universe"][gname] = blk
    res["universe_by_end_year"] = {y: rates([r for r in S if r["end"][:4] == y])
                                   for y in sorted({r["end"][:4] for r in S})}
    res["new_status_sample"] = {s: sum(r["new_status"] == s for r in S) for s in sorted({r["new_status"] for r in S})}
    res["method_failures"] = {sc: {k: sum(r[f"{sc}_status"] != "ok" for r in recs if r["kind"] == k)
                                   for k in ("reference", "sample", "consensus")} for sc in ("v1", "gsadf")}
    res["regressions"] = regress(S, None)
    # consensus (optimistic ROC)
    C = [r for r in recs if r["kind"] == "consensus"]
    crec = []
    for r in C:
        c = man["consensus"][r["i"]]
        crec.append({**r, "pos": c["sign"] == "positive", "row": c["row"]})
    rng = np.random.default_rng(np.random.SeedSequence(AUC_SEED))
    res["consensus"] = {
        "requested": len(man["consensus"]), "scored": len(crec),
        "unavailable": [{k: c[k] for k in ("row", "sign", "name", "unavailable")} for c in man["consensus"]
                        if "unavailable" in c],
        "lookback_changed": sum(bool(c.get("lookback_changed")) for c in man["consensus"] if "id" in c),
        "roc": {sc: auc_block(crec, sc, rng) for sc in SCORES},
        "flags": {f"{sc}|{a}": {"positives": sum(flag(r, sc, a) for r in crec if r["pos"]),
                                 "negatives": sum(flag(r, sc, a) for r in crec if not r["pos"]),
                                 "n_pos_requested": sum(c["sign"] == "positive" for c in man["consensus"]),
                                 "n_neg_requested": sum(c["sign"] != "positive" for c in man["consensus"])}
                  for sc in SCORES for a in LEVELS}}
    res["fits"] = {"windows": len(recs), "runs": sum(r["runs"] for r in recs),
                   "runs_accepted": sum(r["runs_accepted"] for r in recs),
                   "runs_not_success": sum(r["runs_not_success"] for r in recs),
                   "penalty_evals": sum(r["penalty_evals"] for r in recs),
                   "alt_boundary_share_sample": float(np.mean([bool(r["alt_boundary"]) for r in S if r["alt_boundary"] is not None])),
                   "seconds_median": float(np.median([r["seconds"] for r in recs]))}
    return res


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "full"
    if mode == "manifest":
        build_manifest()
        return
    man = json.load(open(os.path.join(HERE, "manifest.json")))
    if mode == "analyze":                              # rerun the analysis from the saved per-window records
        with gzip.open(os.path.join(HERE, "windows.json.gz"), "rt") as fh:
            recs = json.load(fh)
        prev = json.load(open(os.path.join(HERE, "results.json"))) if os.path.exists(os.path.join(HERE, "results.json")) else {}
        res = analyze(man, recs, prev.get("wall_seconds", float("nan")))
        res["settings"] = prev.get("settings")
        with open(os.path.join(HERE, "results.json"), "w") as fh:
            json.dump(res, fh, indent=1, default=float)
        return
    T = build_tasks(man)
    if mode == "smoke":
        T = [t for t in T if t[0] == "reference"][:5] + [t for t in T if t[0] == "sample"][:5] + \
            [t for t in T if t[0] == "consensus"][:4]
    t0 = time.time()
    with ProcessPoolExecutor(WORKERS) as pool:
        recs = []
        for j, r in enumerate(pool.map(score_window, T, chunksize=1)):
            recs.append(r)
            if (j + 1) % 500 == 0:
                print(f"{j + 1}/{len(T)} windows, {time.time() - t0:.0f} s", flush=True)
    wall = time.time() - t0
    if mode == "smoke":
        full = len(build_tasks(man))
        med = float(np.median([r["seconds"] for r in recs]))
        print(json.dumps({"smoke_windows": len(recs), "wall_s": wall, "median_s": med,
                          "projected_full_wall_h": full * med / WORKERS / 3600}))
        return
    with gzip.open(os.path.join(HERE, "windows.json.gz"), "wt") as fh:
        json.dump(recs, fh, default=float)
    res = analyze(man, recs, wall)
    res["settings"] = {"fitter_options": F.OPTIONS, "levels": [str(a) for a in LEVELS], "calm": CALM,
                       "uv_lock_sha256": hashlib.sha256(open(os.path.join(ROOT, "uv.lock"), "rb").read()).hexdigest(),
                       "manifest_sha256": hashlib.sha256(open(os.path.join(HERE, "manifest.json"), "rb").read()).hexdigest()}
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["block", "subset", "score", "level", "flags", "n", "rate"])
        for g, blk in res["universe"].items():
            for sub in ("all starts", "calm starts", "other starts"):
                for sc in SCORES:
                    for a in LEVELS:
                        v = blk[sub][f"{sc}|{a}"]
                        w.writerow([g, sub, sc, str(a), v["flags"], blk[sub]["n"], v["rate"]])
    print(json.dumps({"wall_h": wall / 3600, "windows": len(recs)}))


if __name__ == "__main__":
    main()
