#!/usr/bin/env python3
"""analysis: CP-SAT experiments with guarded 3x3-shadow support restrictions.

The purpose is to test whether an extracted shadow contradiction defines a reusable
support family and whether that family intersects the Wang occupation relaxation.
A feasible output is only an A-support candidate; every candidate is rescanned
against the complete E11 Wang table and checked by the shadow relaxation.

Modes:
  family_excluded: search for a support satisfying the *antecedent* of one shadow
    certificate and the opposite parity, hence a family that the certificate would
    reject if all guards are saturated.  Finding one that also passes complete Wang
    would demonstrate trace-vs-Wang separation at A-support level.
  ordinary: solve a Wang-threshold support model with optional guarded certificate
    restrictions added as necessary-condition cuts, mainly as search triage.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np

S0904_SCRIPTS = Path("scripts")
if str(S0904_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(S0904_SCRIPTS))
S0908_SCRIPTS = Path("scripts")
if str(S0908_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(S0908_SCRIPTS))

from core_capacity_all_mip import enumerate_subspace_keys  # type: ignore  # noqa:E402
from core_capacity_from_wang_lut import CoreQuotient  # type: ignore  # noqa:E402
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis  # type: ignore  # noqa:E402
from shadow_certificate_analysis import (  # type: ignore  # noqa:E402
    gf2_rank,
    lambda_to_mat,
    popparity,
    analyze_support,
)

ROOT = Path("research/research_record")
LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
CERT_PATH = ROOT / "workspace/data/shadow_certificate/shadow_certificate_analysis.json"
CACHE_PATH = ROOT / "workspace/data/shadow_certificate/e11_core_wang_records.pkl"
OUTDIR = ROOT / "workspace/data/shadow_certificate/support_search"
S = 19


def load_lut():
    with LUT_PATH.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}, payload.get("meta", {})


def build_or_load_records(cache: Path = CACHE_PATH):
    if cache.exists() and cache.stat().st_size > 0:
        try:
            with cache.open("rb") as f:
                payload = pickle.load(f)
            return payload["records"], payload.get("meta", {})
        except Exception:
            # The runtime may create a declared file before the first write, or a previous run may have died mid-write.
            # Rebuild rather than trusting a partial cache.
            pass
    t0 = time.time()
    lut, meta = load_lut()
    core = CoreQuotient(1)
    records = []
    by_dim = Counter(); by_L = Counter()
    for key8 in enumerate_subspace_keys(8):
        key9 = core.key9_from_key8(key8)
        L = int(lut[key9])
        pts = [int(p) for p in subspace_points_from_basis(unpack_basis(key8))]
        rec = {"key8": int(key8), "key9": int(key9), "dim8": int(key8 & 0xF), "L": L, "cap": S - L, "pts": pts}
        records.append(rec)
        by_dim[rec["dim8"]] += 1; by_L[L] += 1
    rmeta = {"count": len(records), "by_dim8": dict(sorted(by_dim.items())), "by_L": dict(sorted(by_L.items())), "lut_coverage_ok": meta.get("coverage_ok"), "build_sec": time.time() - t0}
    cache.parent.mkdir(parents=True, exist_ok=True)
    with cache.open("wb") as f:
        pickle.dump({"records": records, "meta": rmeta}, f)
    return records, rmeta


def complete_scan(support: Sequence[int], records: Sequence[dict], max_head: int = 20) -> dict:
    ss = set(int(p) for p in support)
    viol = []
    by_L = Counter(); by_dim = Counter(); by_excess = Counter()
    for rec in records:
        occ = sum(1 for p in rec["pts"] if p in ss)
        if occ > int(rec["cap"]):
            ex = occ - int(rec["cap"])
            by_L[int(rec["L"])] += 1; by_dim[int(rec["dim8"])] += 1; by_excess[ex] += 1
            if len(viol) < max_head:
                viol.append({k: rec[k] for k in ["key8", "key9", "dim8", "L", "cap"]} | {"occupancy": occ, "excess": ex, "basis8": list(unpack_basis(int(rec["key8"])))})
    viol.sort(key=lambda v: (v["excess"], v["L"], v["occupancy"], v["dim8"]), reverse=True)
    return {"violation_count": int(sum(by_excess.values())), "max_excess": int(max(by_excess.keys(), default=0)), "violations_by_L": dict(sorted(by_L.items())), "violations_by_dim8": dict(sorted(by_dim.items())), "violations_by_excess": dict(sorted(by_excess.items())), "violations_head": viol[:max_head]}


def rank_weight_lower(lam: int) -> int:
    return 3 * int(gf2_rank(lambda_to_mat(lam)))


def get_cert(bundle: dict, name: str):
    for entry in bundle["certificates"]:
        if entry["certificate"].get("name") == name:
            return entry
    raise KeyError(name)


def add_parity(model, terms, rhs: int, name: str, active=None):
    # sum terms == rhs (mod 2)
    n = len(terms)
    k = model.NewIntVar(0, max(0, n), f"{name}_k")
    ct = model.Add(sum(terms) - 2*k == int(rhs))
    if active is not None:
        ct.OnlyEnforceIf(active)


def solve(args):
    from ortools.sat.python import cp_model

    t0 = time.time()
    records, rmeta = build_or_load_records()
    bundle = json.loads(args.cert_bundle.read_text())
    cert_entry = get_cert(bundle, args.cert_name)
    cls = cert_entry["classification"]
    cert = cert_entry["certificate"]
    guard = [int(q) for q in cls["guard_lambdas"]]
    recs = cls["records"]
    free = [int(r["p"]) for r in recs if r["class"] == "free"]
    inc = [r for r in recs if r["class"] == "local_inconsistent"]
    forced1 = [int(r["p"]) for r in recs if r["class"] == "forced" and int(r.get("forced_value", 0)) == 1]
    tensor_rhs = int(cls["tensor_rhs"])

    points = list(range(1, 256))
    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in points}
    model.Add(sum(x.values()) == S)

    # contraction weights for all lambda; lower bounds are scalar contraction rank constraints.
    w = {}
    lb_hist = Counter()
    for q in range(1, 256):
        var = model.NewIntVar(0, S, f"w_{q}")
        w[q] = var
        model.Add(var == sum(x[p] for p in points if popparity(p & q)))
        lb = rank_weight_lower(q)
        if lb > 0:
            model.Add(var >= lb)
            lb_hist[lb] += 1

    wang_count = 0; wang_by_L = Counter(); wang_by_dim = Counter(); skipped = 0
    for rec in records:
        L = int(rec["L"])
        if args.min_L and L < args.min_L:
            skipped += 1
            continue
        cap = int(rec["cap"])
        if cap >= S:
            continue
        pts = [p for p in rec["pts"] if p]
        if pts:
            model.Add(sum(x[p] for p in pts) <= cap)
            wang_count += 1; wang_by_L[L] += 1; wang_by_dim[int(rec["dim8"])] += 1

    mode_details = {}
    if args.mode == "family_excluded":
        for q in guard:
            model.Add(w[q] == 9)
        if free:
            model.Add(sum(x[p] for p in free) == 0)
        if inc:
            model.Add(sum(x[int(r["p"])] for r in inc) == 0)
        # Search for supports in the family that the certificate parity would reject.
        add_parity(model, [x[p] for p in forced1], tensor_rhs ^ 1, f"{args.cert_name}_opposite_parity")
        mode_details = {"guard_equal_9": guard, "forbid_free_count": len(free), "forbid_local_inconsistent_count": len(inc), "forced1_count": len(forced1), "opposite_parity_rhs": tensor_rhs ^ 1}
    elif args.mode == "ordinary":
        if args.add_cert_cuts:
            # Local odd-dependency cuts: if p is selected, at least one witness q is unsaturated.
            local_cut_count = 0
            for r in inc:
                H = [int(q) for q in r.get("odd_dependency_qs", [])]
                p = int(r["p"])
                if H:
                    # Since w(q)>=9, sum(w(q)-9) >= x[p].
                    model.Add(sum(w[q] for q in H) >= 9*len(H) + x[p])
                    local_cut_count += 1
            # Guarded pure parity: active iff all guard saturated and no free selected.
            sat = {}
            for q in guard:
                b = model.NewBoolVar(f"sat9_{q}")
                sat[q] = b
                model.Add(w[q] == 9).OnlyEnforceIf(b)
                model.Add(w[q] >= 10).OnlyEnforceIf(b.Not())
            g = model.NewBoolVar(f"{args.cert_name}_guard")
            model.AddBoolAnd([sat[q] for q in guard]).OnlyEnforceIf(g)
            model.AddBoolOr([sat[q].Not() for q in guard] + [g])
            nf = model.NewBoolVar(f"{args.cert_name}_nofree")
            model.Add(sum(x[p] for p in free) == 0).OnlyEnforceIf(nf)
            model.Add(sum(x[p] for p in free) >= 1).OnlyEnforceIf(nf.Not())
            active = model.NewBoolVar(f"{args.cert_name}_active")
            model.AddImplication(active, g)
            model.AddImplication(active, nf)
            model.AddBoolOr([g.Not(), nf.Not(), active])
            add_parity(model, [x[p] for p in forced1], tensor_rhs, f"{args.cert_name}_guarded_parity", active=active)
            mode_details = {"local_odd_dependency_cuts": local_cut_count, "guarded_parity_added": True, "free_count": len(free), "guard_size": len(guard)}
    else:
        raise ValueError(args.mode)

    if args.exclude_support:
        ex = [int(z) for z in args.exclude_support.split(',') if z.strip()]
        if ex:
            model.Add(sum(x[p] for p in ex) <= len(ex) - 1)
            mode_details["excluded_support"] = ex
    if args.fix_support:
        fixed = [int(z) for z in args.fix_support.split(',') if z.strip()]
        fs = set(fixed)
        for p in points:
            model.Add(x[p] == (1 if p in fs else 0))
        mode_details["fixed_support"] = fixed
    elif args.hint_support:
        hint = [int(z) for z in args.hint_support.split(',') if z.strip()]
        hs = set(hint)
        for p in points:
            model.AddHint(x[p], 1 if p in hs else 0)
        mode_details["hint_support"] = hint

    build_sec = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = int(args.workers)
    solver.parameters.random_seed = int(args.seed)
    ts = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - ts
    status_name = solver.StatusName(status)

    result = {
        "schema": "s0908_shadow_guided_support_search_v1",
        "field": "F2",
        "mode": args.mode,
        "cert_name": args.cert_name,
        "min_L": args.min_L,
        "meaning": "Search evidence only. Feasible supports are A-side candidates rescanned against complete Wang and checked by shadow; no B/C rank-one completion is implied.",
        "record_meta": rmeta,
        "constraint_summary": {"wang_rows": wang_count, "wang_by_L": dict(sorted(wang_by_L.items())), "wang_by_dim8": dict(sorted(wang_by_dim.items())), "skipped_wang_rows": skipped, "rank_weight_lb_hist": dict(sorted(lb_hist.items()))},
        "certificate_family": {"guard": guard, "class_counts": cls["class_counts"], "forced_value_counts": cls.get("forced_value_counts"), "tensor_rhs": tensor_rhs, **mode_details},
        "build_sec": round(build_sec, 3),
        "solver_time_limit": args.solver_time,
        "workers": args.workers,
        "seed": args.seed,
        "status": status_name,
        "solve_sec": round(solve_sec, 3),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        support = [p for p in points if solver.Value(x[p])]
        weights = {str(q): solver.Value(w[q]) for q in guard}
        result["solution"] = {
            "support": support,
            "guard_weights": weights,
            "free_selected": [p for p in free if p in support],
            "local_inconsistent_selected": [int(r["p"]) for r in inc if int(r["p"]) in support],
            "forced1_parity": int(sum(1 for p in forced1 if p in support) & 1),
            "complete_wang_scan": complete_scan(support, records),
            "shadow_summary": analyze_support("solution", support),
        }
    result["total_elapsed_sec"] = round(time.time() - t0, 3)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in ["mode", "cert_name", "min_L", "build_sec", "status", "solve_sec", "constraint_summary", "certificate_family"]}, indent=2, sort_keys=True)[:6000])
    if "solution" in result:
        print("solution", json.dumps(result["solution"], indent=2, sort_keys=True)[:6000])
    print(f"Saved {args.out}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["family_excluded", "ordinary"], default="family_excluded")
    ap.add_argument("--cert-name", default="L15_min8_A")
    ap.add_argument("--cert-bundle", type=Path, default=CERT_PATH)
    ap.add_argument("--min-L", type=int, default=15, help="include Wang rows with L>=min_L; use 0 for all rows")
    ap.add_argument("--add-cert-cuts", action="store_true")
    ap.add_argument("--solver-time", type=float, default=60.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=905)
    ap.add_argument("--hint-support", default="")
    ap.add_argument("--fix-support", default="")
    ap.add_argument("--exclude-support", default="")
    ap.add_argument("--out", type=Path, default=OUTDIR / "search.json")
    args = ap.parse_args()
    solve(args)


if __name__ == "__main__":
    main()
