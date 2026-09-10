#!/usr/bin/env python3
"""Optimized E11 prefix-completion SAT coupled to dim<=2 Wang constraints.

This combines two exact ingredients:
  1. fixed prefix A-terms are eliminated from the variable-A contribution layer
     and enter Brent XORs directly through their B*C products;
  2. all singleton Wang caps and selected dim-2 triple caps from the verified
     E11 rank-19 occupation cache are imposed on the remaining free A terms.

UNSAT for a prefix refutes every rank-19 E11 CPD whose A multiset contains that
prefix.  SAT is decoded and verified as an actual CPD.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
from itertools import combinations
from pathlib import Path

import numpy as np

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))

from e11_prefix_completion_opt_xor_sat import OptimizedPrefixCPD, sha256_file, solve, verify  # noqa: E402


def mask_to_points(mask: int) -> list[int]:
    pts: list[int] = []
    x = int(mask)
    while x:
        lb = x & -x
        pts.append(lb.bit_length())
        x ^= lb
    return pts


def at_most(F, lits: list[int], k: int) -> int:
    lits = [int(x) for x in lits]
    if k < 0:
        F.add([])
        return 1
    if k >= len(lits):
        return 0
    added = 0
    for combo in combinations(lits, k + 1):
        F.add([-v for v in combo])
        added += 1
    return added


def load_cache(path: Path) -> dict:
    with path.open("rb") as f:
        cache = pickle.load(f)
    if cache.get("core_name") != "E11" or cache.get("rank_s") != 19:
        raise ValueError(f"expected E11 rank-19 cache, got {cache.get('core_name')} rank {cache.get('rank_s')}")
    return cache


def add_wang_dim12(pc: OptimizedPrefixCPD, cache: dict, dim2_max_cap: int = 1) -> dict:
    F = pc.F
    free_terms = list(range(len(pc.prefix), pc.rank))
    eq_cache: dict[tuple[int, int], int] = {}
    stats = {
        "free_terms": len(free_terms),
        "eq_indicator_count": 0,
        "eq_indicator_clauses": 0,
        "singleton_constraints": 0,
        "singleton_atmost_clauses": 0,
        "dim2_constraints": 0,
        "dim2_atmost_clauses": 0,
        "static_prefix_violations": 0,
        "dim2_max_cap": int(dim2_max_cap),
    }

    def eq_indicator(t: int, p: int) -> int:
        key = (int(t), int(p))
        if key in eq_cache:
            return eq_cache[key]
        e = F.new()
        # e iff alpha_t equals p.  This is exact because alpha bits are Boolean.
        neg_match_clause = [e]
        for a in range(pc.nU):
            bit = (int(p) >> a) & 1
            var = pc.alpha[(t, a)]
            lit = var if bit else -var
            F.add([-e, lit])
            neg_match_clause.append(-lit)
        F.add(neg_match_clause)
        eq_cache[key] = e
        stats["eq_indicator_count"] += 1
        stats["eq_indicator_clauses"] += pc.nU + 1
        return e

    for mask, cap, dim in zip(cache["masks"], cache["caps"], cache["dims"]):
        if int(dim) != 1:
            continue
        pts = mask_to_points(int(mask))
        if len(pts) != 1:
            continue
        p = pts[0]
        used = sum(1 for u in pc.prefix if int(u) == p)
        residual = int(cap) - used
        if residual < 0:
            stats["static_prefix_violations"] += 1
        lits = [eq_indicator(t, p) for t in free_terms]
        stats["singleton_constraints"] += 1
        stats["singleton_atmost_clauses"] += at_most(F, lits, residual)

    for mask, cap, dim in zip(cache["masks"], cache["caps"], cache["dims"]):
        if int(dim) != 2 or int(cap) > int(dim2_max_cap):
            continue
        pts = mask_to_points(int(mask))
        if len(pts) != 3:
            continue
        used = sum(1 for u in pc.prefix if int(u) in pts)
        residual = int(cap) - used
        if residual < 0:
            stats["static_prefix_violations"] += 1
        lits = [eq_indicator(t, p) for t in free_terms for p in pts]
        stats["dim2_constraints"] += 1
        stats["dim2_atmost_clauses"] += at_most(F, lits, residual)
    return stats


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--core", type=Path, default=Path("data/restricted_cores/mask_001_E11_core.npy"))
    ap.add_argument("--cache", type=Path, default=Path("data/e11_capacity_sat/e11_capacity_cache.pkl"))
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--prefix", required=True)
    ap.add_argument("--dim2-max-cap", type=int, default=1)
    ap.add_argument("--sort-free-a", action="store_true")
    ap.add_argument("--outdir", type=Path, required=True)
    ap.add_argument("--name", default="prefix_opt_wang2")
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--solver", default="cryptominisat5")
    ap.add_argument("--maxconfl", type=int, default=0)
    ap.add_argument("--write-only", action="store_true")
    args = ap.parse_args()
    if args.rank != 19:
        raise ValueError("this script currently uses the E11 rank-19 Wang cache")
    core = np.load(args.core).astype(np.uint8) & 1
    prefix = [int(x) for x in args.prefix.split(",") if x.strip()]
    pc = OptimizedPrefixCPD(core, args.rank, prefix, sort_free_a=args.sort_free_a, allow_zero_a=False)
    cache = load_cache(args.cache)
    wang_stats = add_wang_dim12(pc, cache, args.dim2_max_cap)
    args.outdir.mkdir(parents=True, exist_ok=True)
    cnf_path = args.outdir / f"{args.name}.xor.cnf"
    pc.F.write(cnf_path, [
        "optimized E11 prefix-completion CPD SAT with dim<=2 Wang cuts",
        f"rank={args.rank}", f"prefix={prefix}", f"sort_free_a={args.sort_free_a}", f"dim2_max_cap={args.dim2_max_cap}",
    ])
    result = {
        "purpose": "optimized exact E11 prefix-completion Brent SAT coupled with dim<=2 Wang occupation constraints",
        "field": "F2",
        "rank": args.rank,
        "core": str(args.core),
        "cache": str(args.cache),
        "prefix": prefix,
        "prefix_size": len(prefix),
        "sort_free_a": bool(args.sort_free_a),
        "dim2_max_cap": int(args.dim2_max_cap),
        "vars": pc.F.next - 1,
        "cnf_clauses": len(pc.F.cnf),
        "native_xor_clauses": len(pc.F.xors),
        "wang_stats": wang_stats,
        "cnf_path": str(cnf_path),
        "cnf_sha256": sha256_file(cnf_path),
        "meaning": "UNSAT refutes every E11 rank-19 CPD whose A multiset contains this prefix, using Brent plus exact dim<=2 Wang occupation restrictions. SAT is decoded and verified as an actual CPD.",
    }
    if not args.write_only:
        sol = solve(cnf_path, args.timeout, args.threads, args.solver, args.maxconfl)
        model = sol.pop("model", None)
        result["solve"] = sol
        if sol.get("status") == "SAT" and model:
            us, vs, ws = pc.decode(model)
            ok, diff = verify(core, us, vs, ws)
            sol_path = args.outdir / f"{args.name}.solution.npz"
            pc.save_npz(sol_path, us, vs, ws)
            result["decoded_solution"] = {"u_masks": us, "v_masks": vs, "w_masks": ws, "verified": ok, "diff_count": diff, "solution_npz": str(sol_path), "model_lit_count": len(model)}
    out = args.outdir / f"{args.name}.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "prefix": prefix,
        "rank": args.rank,
        "vars": result["vars"],
        "cnf_clauses": result["cnf_clauses"],
        "native_xor_clauses": result["native_xor_clauses"],
        "wang_stats": wang_stats,
        "status": result.get("solve", {}).get("status", "WRITE_ONLY"),
        "decoded_verified": result.get("decoded_solution", {}).get("verified"),
        "elapsed_sec": result.get("solve", {}).get("elapsed_sec"),
        "json": str(out),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
