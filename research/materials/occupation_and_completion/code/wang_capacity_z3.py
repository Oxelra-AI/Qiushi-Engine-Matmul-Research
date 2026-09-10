#!/usr/bin/env python3
"""z3-based Wang capacity solver with UNSAT core extraction.

Uses z3's native PB constraints (no auxiliary variables needed).
When UNSAT, extracts the core constraints causing infeasibility.
The core can then be encoded as a small CNF for DRAT proof.
"""
from __future__ import annotations
import argparse
import json
import pickle
import sys
import time
from pathlib import Path
from typing import Dict, List, Set, Optional

import numpy as np
import z3

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import (
    N, in_rowspace, matrix_rank_of_mask, pack_basis,
    rref_basis, subspace_points_from_basis, unpack_basis, make_actions,
)

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")


def load_lut():
    with LUT_PATH.open('rb') as f:
        data = pickle.load(f)
    return data['lut']


def compute_stab_e11(actions):
    return [a for a in actions if a[0] == 0]


def solve_with_core(
    fixed_points: List[int],
    excluded_points: Set[int],
    rank_s: int,
    include_dims: List[int],
    through_fixed_dims: List[int],
    max_rank1_count: Optional[int],
    outdir: Path,
    timeout_ms: int = 600000,
):
    """Solve Wang capacity problem with z3 and extract UNSAT core."""
    t0 = time.time()
    outdir.mkdir(parents=True, exist_ok=True)
    
    lut = load_lut()
    
    fixed_set = set(fixed_points)
    excl_set = set(excluded_points)
    all_points = list(range(1, 2**N))
    decision_points = sorted(p for p in all_points if p not in fixed_set and p not in excl_set)
    dp_set = set(decision_points)
    n_dp = len(decision_points)
    
    rank1_set = set(p for p in all_points if matrix_rank_of_mask(p) == 1)
    
    # z3 Boolean variables
    x = {p: z3.Bool(f'x{p}') for p in decision_points}
    
    solver = z3.Solver()
    solver.set("timeout", timeout_ms)
    
    # Track constraints for core extraction
    constraint_labels = {}  # label -> (key, dim, lb, description)
    
    # 1. Total support = rank_s - |fixed|
    target = rank_s - len(fixed_set)
    dp_bools = [x[p] for p in decision_points]
    solver.add(z3.PbEq([(b, 1) for b in dp_bools], target))
    
    # 2. Wang constraints with tracking labels
    inc_dims_set = set(include_dims)
    thr_dims_set = set(through_fixed_dims) if through_fixed_dims else set()
    
    n_wang = 0
    assumptions = []
    scan_count = 0
    
    for key, lb in lut.items():
        scan_count += 1
        if scan_count % 2_000_000 == 0:
            print(f"  scanned {scan_count:,}/{len(lut):,}; wang={n_wang}; elapsed={time.time()-t0:.1f}s",
                  file=sys.stderr, flush=True)
        
        basis = unpack_basis(key)
        dim = len(basis)
        cap = rank_s - lb
        
        in_direct = dim in inc_dims_set
        in_through = dim in thr_dims_set
        if in_through:
            for fp in fixed_points:
                if not in_rowspace(fp, basis):
                    in_through = False
                    break
        if not in_direct and not in_through:
            continue
        
        pts = subspace_points_from_basis(basis)
        fixed_in = sum(1 for fp in fixed_points if fp in set(pts))
        remaining_cap = cap - fixed_in
        
        dp_in = [p for p in pts if p in dp_set]
        if not dp_in:
            continue
        
        if remaining_cap >= len(dp_in):
            continue  # trivially satisfied
        
        if remaining_cap < 0:
            # Contradiction
            label = z3.Bool(f'c_{n_wang}')
            solver.assert_and_track(z3.BoolVal(False), label)
            assumptions.append(label)
            constraint_labels[str(label)] = (key, dim, lb, "impossible_cap")
            n_wang += 1
            continue
        
        # PB constraint: at most remaining_cap of dp_in
        dp_bools_in = [x[p] for p in dp_in]
        label = z3.Bool(f'c_{n_wang}')
        solver.assert_and_track(
            z3.PbLe([(b, 1) for b in dp_bools_in], remaining_cap),
            label
        )
        assumptions.append(label)
        constraint_labels[str(label)] = (key, dim, lb, f"wang_dim{dim}_cap{remaining_cap}_pts{len(dp_in)}")
        n_wang += 1
    
    # 3. Max rank-1 count
    if max_rank1_count is not None:
        r1_dp_bools = [x[p] for p in decision_points if p in rank1_set]
        r1_fixed = sum(1 for fp in fixed_points if fp in rank1_set)
        r1_bound = max_rank1_count - r1_fixed
        label = z3.Bool(f'c_r1')
        solver.assert_and_track(
            z3.PbLe([(b, 1) for b in r1_dp_bools], r1_bound),
            label
        )
        assumptions.append(label)
        constraint_labels[str(label)] = (0, 0, 0, f"rank1_max_{max_rank1_count}")
    
    build_elapsed = time.time() - t0
    print(f"Built z3 model: {n_dp} vars, {n_wang} Wang constraints, "
          f"elapsed={build_elapsed:.1f}s", file=sys.stderr)
    
    # Solve
    t_solve = time.time()
    result = solver.check()
    solve_elapsed = time.time() - t_solve
    
    status = str(result)
    print(f"z3 result: {status} in {solve_elapsed:.1f}s", file=sys.stderr)
    
    core_info = None
    model_info = None
    
    if result == z3.unsat:
        # Extract UNSAT core
        core = solver.unsat_core()
        core_labels = [str(c) for c in core]
        core_details = []
        for cl in core_labels:
            if cl in constraint_labels:
                key, dim, lb, desc = constraint_labels[cl]
                core_details.append({"label": cl, "key": key, "dim": dim, "lb": lb, "desc": desc})
        
        core_info = {
            "core_size": len(core),
            "total_constraints": n_wang,
            "core_details": core_details[:200],  # truncate for readability
        }
        print(f"UNSAT core: {len(core)} of {n_wang} constraints", file=sys.stderr)
        
        # Save core for downstream DRAT encoding
        core_keys = [constraint_labels[cl][0] for cl in core_labels if cl in constraint_labels]
        core_path = outdir / "unsat_core_keys.json"
        core_path.write_text(json.dumps(core_keys, indent=2))
    
    elif result == z3.sat:
        model = solver.model()
        support = [p for p in decision_points if z3.is_true(model[x[p]])]
        model_info = {"support": support, "size": len(support)}
        model_path = outdir / "model.json"
        model_path.write_text(json.dumps(model_info, indent=2))
    
    total_elapsed = time.time() - t0
    meta = {
        "n_vars": n_dp,
        "n_wang_constraints": n_wang,
        "build_elapsed_sec": build_elapsed,
        "solve_elapsed_sec": solve_elapsed,
        "total_elapsed_sec": total_elapsed,
        "status": status,
        "fixed_points": fixed_points,
        "rank_s": rank_s,
        "include_dims": include_dims,
        "through_fixed_dims": through_fixed_dims,
        "core_info": core_info,
        "model_info": model_info,
    }
    
    meta_path = outdir / "meta.json"
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True, default=str))
    print(json.dumps(meta, indent=2, sort_keys=True, default=str))
    return meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rep", type=int, required=True)
    ap.add_argument("--rank-s", type=int, default=20)
    ap.add_argument("--include-dims", type=str, default="1,2,3")
    ap.add_argument("--through-fixed-dims", type=str, default="4,5,6")
    ap.add_argument("--max-rank1", type=int, default=None)
    ap.add_argument("--exclude-before", type=str, default="")
    ap.add_argument("--timeout-ms", type=int, default=600000)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    
    inc_dims = [int(x) for x in args.include_dims.split(",")]
    thr_dims = [int(x) for x in args.through_fixed_dims.split(",") if x.strip()]
    
    actions = make_actions()
    stab = compute_stab_e11(actions)
    excluded = set()
    if args.exclude_before:
        for rep in [int(x) for x in args.exclude_before.split(",") if x.strip()]:
            for a in stab:
                excluded.add(a[rep])
    
    solve_with_core(
        fixed_points=[1, args.rep],
        excluded_points=excluded,
        rank_s=args.rank_s,
        include_dims=inc_dims,
        through_fixed_dims=thr_dims,
        max_rank1_count=args.max_rank1,
        outdir=args.out,
        timeout_ms=args.timeout_ms,
    )


if __name__ == "__main__":
    main()
