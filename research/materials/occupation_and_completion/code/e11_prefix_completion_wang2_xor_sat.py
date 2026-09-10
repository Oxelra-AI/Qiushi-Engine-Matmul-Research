#!/usr/bin/env python3
"""E11 prefix-completion SAT coupled to exact low-dimensional Wang constraints.

This is a shallow-subtree test for the rank-19 E11 route.  Given a fixed A-prefix,
it keeps the remaining A factors and all B/C factors free, encodes the full Brent
CPD equations with native XOR clauses, and adds exact A-side Wang occupation
constraints of dimensions 1 and selected dimension-2 triples from the verified
E11 cache.

UNSAT for a prefix is an exact refutation of every CPD containing that prefix,
provided the CNF translation is trusted or upgraded to proof.  SAT is decoded and
verified as a rank-19 E11 CPD, not merely as support feasibility.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import re
import subprocess
import sys
import time
from itertools import combinations
from pathlib import Path

import numpy as np

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))

from e11_prefix_completion_xor_sat import PrefixCPD, parse_model, sha256_file, solve_native, verify  # noqa: E402


def mask_to_points(mask: int) -> list[int]:
    pts: list[int] = []
    x = int(mask)
    while x:
        lb = x & -x
        pts.append(lb.bit_length())  # cache bit p-1 -> point p
        x ^= lb
    return pts


def at_most(F, lits: list[int], k: int) -> int:
    """Naive exact at-most-k CNF; small k and <=45 literals in this script."""
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


def add_wang_dim12(pc: PrefixCPD, cache: dict, dim2_max_cap: int = 1) -> dict:
    """Add singleton caps and dimension-2 caps up to dim2_max_cap."""
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
        # e -> exact bit pattern; exact pattern -> e.
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

    masks = cache["masks"]
    caps = cache["caps"]
    dims = cache["dims"]

    # Dimension 1 singleton multiplicity caps.
    for mask, cap, dim in zip(masks, caps, dims):
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

    # Strongest 2D exclusions: selected triples with small cap, by default cap=1.
    for mask, cap, dim in zip(masks, caps, dims):
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
    ap.add_argument("--name", default="prefix_wang2")
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--solver", default="cryptominisat5")
    ap.add_argument("--maxconfl", type=int, default=0)
    ap.add_argument("--write-only", action="store_true")
    args = ap.parse_args()

    if args.rank != 19:
        raise ValueError("the loaded Wang cache in this script is for E11 rank 19")
    t0 = time.time()
    core = np.load(args.core).astype(np.uint8) & 1
    prefix = [int(x) for x in args.prefix.split(",") if x.strip()]
    pc = PrefixCPD(core, args.rank, prefix, "native", allow_zero_a=False, sort_free_a=args.sort_free_a)
    cache = load_cache(args.cache)
    wang_stats = add_wang_dim12(pc, cache, args.dim2_max_cap)
    args.outdir.mkdir(parents=True, exist_ok=True)
    cnf_path = args.outdir / f"{args.name}.xor.cnf"
    pc.F.write(cnf_path, [
        "E11 prefix-completion CPD SAT with singleton and selected dim2 Wang cuts",
        f"rank={args.rank}",
        f"prefix={prefix}",
        f"sort_free_a={args.sort_free_a}",
        f"dim2_max_cap={args.dim2_max_cap}",
    ])
    result = {
        "purpose": "exact E11 prefix-completion Brent SAT coupled with dim<=2 Wang occupation constraints",
        "field": "F2",
        "rank": args.rank,
        "core": str(args.core),
        "cache": str(args.cache),
        "prefix": prefix,
        "prefix_size": len(prefix),
        "sort_free_a": bool(args.sort_free_a),
        "dim2_max_cap": int(args.dim2_max_cap),
        "vars": pc.var_count,
        "cnf_clauses": pc.cnf_clause_count,
        "native_xor_clauses": pc.xor_clause_count,
        "wang_stats": wang_stats,
        "cnf_path": str(cnf_path),
        "cnf_sha256": sha256_file(cnf_path),
        "meaning": "UNSAT refutes every E11 rank-19 CPD whose A multiset contains this prefix, using Brent plus exact dim<=2 Wang occupation restrictions. SAT is decoded and verified as an actual CPD.",
    }
    if not args.write_only:
        solve = solve_native(cnf_path, args.solver, args.timeout, args.threads, args.maxconfl)
        model = solve.pop("model", None)
        result["solve"] = solve
        if solve.get("status") == "SAT" and model:
            us, vs, ws = pc.decode(model)
            ok, diff = verify(core, us, vs, ws)
            sol_path = args.outdir / f"{args.name}.solution.npz"
            pc.save_npz(sol_path, us, vs, ws)
            result["decoded_solution"] = {"u_masks": us, "v_masks": vs, "w_masks": ws, "verified": ok, "diff_count": diff, "solution_npz": str(sol_path), "model_lit_count": len(model)}
    result["elapsed_total_sec"] = time.time() - t0
    out = args.outdir / f"{args.name}.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "prefix": prefix,
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
