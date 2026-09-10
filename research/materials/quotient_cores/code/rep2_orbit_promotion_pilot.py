#!/usr/bin/env python3
"""analysis pilot: add whole prefix-stabilizer Wang-row orbits to rep2 model.

This is an exploratory exact-support computation, not a proof.  It tests whether
row orbits recurrent in the analysis rank-aware supports produce a stronger
rep2 relaxation than isolated adaptive cuts.

Formula for prefix [1,2]:
  * choose exactly 18 additional projective A-points;
  * choose at most 15 additional rank-1 points (exact-k=18 closure -> <=17 total);
  * include all Wang inequalities with residual <= initial_max_residual;
  * include all Wang inequalities in selected prefix-stabilizer row orbits;
  * include transported ruling-line clauses.

Any SAT model is scanned against the full 8,283,458-row LUT.  A zero-violation
support would be exported for fixed-A B/C solving; otherwise the result only
indicates what the current relaxation still misses.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from pathlib import Path
from typing import Iterable

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

from wang_capacity_lazy import (
    make_actions,
    subspace_points_from_basis,
    transform_key,
    transform_mask,
    unpack_basis,
)
from ruling_line_transport import all_ruling_triples, simplify_ruling, all_rank1_set


def span_constraints_for_key(key: int, lb: int, prefix: set[int], cand_set: set[int], cand_idx: dict[int, int]):
    pts = set(subspace_points_from_basis(unpack_basis(key)))
    cap = 20 - int(lb)
    prefix_occ = len(pts & prefix)
    residual = cap - prefix_occ
    if residual < 0:
        return None
    ci = tuple(sorted(cand_idx[p] for p in pts if p in cand_set))
    if residual >= len(ci):
        return None
    return ci, int(residual), len(pts), len(unpack_basis(key)), cap, prefix_occ


def load_tier_keys(path: Path, tier: str, top: int | None):
    obj = json.loads(path.read_text())
    if tier == "all5":
        entries = obj["tier1_all5"]
    elif tier == "strong4plus":
        entries = obj["tier2_strong4plus_top40"]
    elif tier == "hit4plus":
        entries = obj["tier2_all_hit4plus"]
    else:
        raise ValueError(f"unknown tier {tier}")
    if top is not None:
        entries = entries[:top]
    return obj, entries, [int(e["canonical_key_hex"], 16) for e in entries]


def full_lut_scan(lut: dict[int, int], support: set[int]):
    violations = []
    max_excess = 0
    by_dim_lb_res = {}
    for key, lb in lut.items():
        pts = set(subspace_points_from_basis(unpack_basis(key)))
        cap = 20 - int(lb)
        occ = len(pts & support)
        if occ > cap:
            excess = occ - cap
            max_excess = max(max_excess, excess)
            prefix_occ = len(pts & {1, 2})
            residual = cap - prefix_occ
            typ = (len(unpack_basis(key)), int(lb), residual, excess)
            by_dim_lb_res[typ] = by_dim_lb_res.get(typ, 0) + 1
            if len(violations) < 2000:
                violations.append({
                    "key_hex": hex(int(key)),
                    "dim": len(unpack_basis(key)),
                    "lb": int(lb),
                    "cap": cap,
                    "occ": occ,
                    "prefix_occ": prefix_occ,
                    "residual_after_prefix": residual,
                    "excess": excess,
                })
    type_top = sorted(
        [
            {"count": c, "dim": k[0], "lb": k[1], "residual_after_prefix": k[2], "excess": k[3]}
            for k, c in by_dim_lb_res.items()
        ],
        key=lambda x: (-x["count"], x["dim"], -x["lb"], x["residual_after_prefix"], -x["excess"]),
    )[:30]
    return {
        "violation_count": sum(by_dim_lb_res.values()),
        "max_excess": max_excess,
        "violation_examples": violations,
        "type_top": type_top,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", default="data/wang_f2_lb20/wang_subspace_lut.pkl")
    ap.add_argument("--tiers", default="data/corrected_strategy/rep2_orbit_promotion_tiers.json")
    ap.add_argument("--tier", choices=["all5", "strong4plus", "hit4plus"], default="all5")
    ap.add_argument("--top", type=int, default=None)
    ap.add_argument("--initial-max-residual", type=int, default=2)
    ap.add_argument("--time-limit", type=int, default=240)
    ap.add_argument("--out", default="data/corrected_strategy/rep2_orbit_promotion_all5/result.json")
    args = ap.parse_args()

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    prefix = [1, 2]
    prefix_set = set(prefix)
    candidates = [p for p in range(1, 512) if p not in prefix_set]
    cand_set = set(candidates)
    cand_idx = {p: i for i, p in enumerate(candidates)}
    target = 18
    r1_all = all_rank1_set()
    r1_indices = [cand_idx[p] for p in candidates if p in r1_all]

    tier_obj, tier_entries, tier_keys = load_tier_keys(Path(args.tiers), args.tier, args.top)
    print(f"tier={args.tier} entries={len(tier_keys)} prefix={prefix}")

    print("Loading LUT...")
    t0 = time.time()
    with open(args.lut, "rb") as f:
        payload = pickle.load(f)
    lut = {int(k): int(v) for k, v in payload["lut"].items()}
    print(f"  lut={len(lut):,} load_sec={time.time()-t0:.1f}")

    print("Building prefix setwise stabilizer and expanding selected row orbits...")
    t1 = time.time()
    actions = make_actions()
    stab = [img for img in actions if {transform_mask(p, img) for p in prefix} == prefix_set]
    orbit_keys = set()
    orbit_records = []
    for e, key in zip(tier_entries, tier_keys):
        rows = unpack_basis(key)
        expanded = {transform_key(rows, img) for img in stab}
        missing = [k for k in expanded if k not in lut]
        lbs = sorted({int(lut[k]) for k in expanded if k in lut})
        if missing:
            raise RuntimeError(f"orbit key missing from LUT for {hex(key)}: {missing[:5]}")
        orbit_keys.update(expanded)
        orbit_records.append({
            "canonical_key_hex": hex(key),
            "expanded_key_count": len(expanded),
            "lbs_in_expanded_orbit": lbs,
            "tier_hit_model_count": e.get("hit_model_count"),
            "tier_residual_after_prefix": e.get("residual_after_prefix"),
            "tier_lb": e.get("lb"),
            "tier_dim": e.get("dim"),
        })
    print(f"  stab={len(stab)} orbit_keys={len(orbit_keys)} sec={time.time()-t1:.1f}")

    print("Collecting Wang inequalities for base residual tier plus selected orbits...")
    t2 = time.time()
    constraints = {}
    source_counts = {"base_residual": 0, "orbit": 0, "both": 0, "nonbinding_selected_orbit": 0}
    for key, lb in lut.items():
        is_orbit = key in orbit_keys
        # For base residual test we need compute residual.  Compute only once.
        parsed = span_constraints_for_key(int(key), int(lb), prefix_set, cand_set, cand_idx)
        if parsed is None:
            if is_orbit:
                source_counts["nonbinding_selected_orbit"] += 1
            continue
        ci, residual, pts_len, dim, cap, prefix_occ = parsed
        is_base = residual <= args.initial_max_residual
        if is_base or is_orbit:
            constraints[int(key)] = (ci, residual)
            if is_base and is_orbit:
                source_counts["both"] += 1
            elif is_base:
                source_counts["base_residual"] += 1
            else:
                source_counts["orbit"] += 1
    print(f"  constraints={len(constraints)} counts={source_counts} sec={time.time()-t2:.1f}")

    print("Building CP-SAT model...")
    from ortools.sat.python import cp_model

    model = cp_model.CpModel()
    x = [model.NewBoolVar(f"x{i}") for i in range(len(candidates))]
    model.Add(sum(x) == target)
    model.Add(sum(x[i] for i in r1_indices) <= 15)

    for ci, residual in constraints.values():
        model.Add(sum(x[i] for i in ci) <= residual)

    # Transported ruling-line clauses under prefix [1,2].
    rc = simplify_ruling(all_ruling_triples(), prefix_set)
    ruling_counts = {"unit": 0, "binary": 0, "ternary": 0}
    for p in rc["unit"]:
        if p in cand_idx:
            model.Add(x[cand_idx[p]] == 0)
            ruling_counts["unit"] += 1
    for a, b in rc["binary"]:
        if a in cand_idx and b in cand_idx:
            model.Add(x[cand_idx[a]] + x[cand_idx[b]] <= 1)
            ruling_counts["binary"] += 1
    for a, b, c in rc["ternary"]:
        if a in cand_idx and b in cand_idx and c in cand_idx:
            model.Add(x[cand_idx[a]] + x[cand_idx[b]] + x[cand_idx[c]] <= 2)
            ruling_counts["ternary"] += 1

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.time_limit
    solver.parameters.num_workers = 8
    t3 = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - t3
    status_name = {
        cp_model.OPTIMAL: "OPTIMAL",
        cp_model.FEASIBLE: "FEASIBLE",
        cp_model.INFEASIBLE: "INFEASIBLE",
        cp_model.MODEL_INVALID: "MODEL_INVALID",
        cp_model.UNKNOWN: "UNKNOWN",
    }.get(status, f"UNKNOWN_{status}")
    print(f"Solve status={status_name} sec={solve_sec:.1f}")

    result = {
        "schema": "rep2_orbit_promotion_pilot_v1",
        "purpose": "exploratory row-orbit promotion; CP-SAT result is not a proof unless converted and independently replayed",
        "tier_source": args.tiers,
        "tier": args.tier,
        "top": args.top,
        "prefix": prefix,
        "target": target,
        "rank1_candidate_limit": 15,
        "initial_max_residual": args.initial_max_residual,
        "setwise_stabilizer_order": len(stab),
        "tier_entry_count": len(tier_entries),
        "expanded_orbit_key_count": len(orbit_keys),
        "orbit_records": orbit_records,
        "wang_constraint_count": len(constraints),
        "source_counts": source_counts,
        "ruling_counts": ruling_counts,
        "status": status_name,
        "solve_sec": round(solve_sec, 2),
        "total_elapsed_sec": round(time.time() - t0, 2),
    }

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        selected = [candidates[i] for i in range(len(candidates)) if solver.Value(x[i])]
        support = set(prefix) | set(selected)
        result["selected_points"] = selected
        result["support"] = sorted(support)
        result["rank1_total"] = sum(1 for p in support if p in r1_all)
        result["higher_rank_total"] = len(support) - result["rank1_total"]
        print("Scanning SAT support against full LUT...")
        scan = full_lut_scan(lut, support)
        result["full_lut_scan"] = scan
        print(f"  full violations={scan['violation_count']} max_excess={scan['max_excess']} rank1_total={result['rank1_total']}")
    elif status == cp_model.INFEASIBLE:
        result["infeasible_warning"] = "CP-SAT infeasible is not a mathematical proof until regenerated as CNF/PB with independently checked proof."

    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out_path),
        "status": status_name,
        "constraints": len(constraints),
        "orbit_keys": len(orbit_keys),
        "solve_sec": round(solve_sec, 2),
        "violations": result.get("full_lut_scan", {}).get("violation_count"),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
