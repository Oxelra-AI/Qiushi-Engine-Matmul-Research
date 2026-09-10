#!/usr/bin/env python3
"""Encode the fixed-E11 Wang capacity problem as pseudo-Boolean (OPB format).

Key insight: cardinality constraints are NATIVE in PB, not needing auxiliary
variables.  A PB solver using cutting planes can prove infeasibility
exponentially faster than resolution-based SAT on counting problems.

The OPB format encodes each Wang constraint as:
  1 x_p1 + 1 x_p2 + ... + 1 x_pn <= cap ;

where the points are the projective points of F2^9 \ {0} in the subspace Phi,
and cap = s - L(Phi) for a rank-s decomposition search.

Output: .opb file in OPB 2.0 format for RoundingSat, Sat4j, etc.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import pickle
import sys
import time
from pathlib import Path
from typing import Dict, List, Set, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import (
    N,
    in_rowspace,
    matrix_rank_of_mask,
    pack_basis,
    rref_basis,
    subspace_points_from_basis,
    unpack_basis,
    generate_gl3,
)

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(4*1024*1024), b''):
            h.update(chunk)
    return h.hexdigest()


def load_lut():
    with LUT_PATH.open('rb') as f:
        data = pickle.load(f)
    return data['lut']  # {packed_key: lower_bound}


# Stabilizer of E11 (mask 1) under the 56448 A-side actions
def compute_stab_e11(actions):
    return [a for a in actions if a[0] == 0]  # a[0] maps point 1 (E11) to itself


def build_opb(
    fixed_points: List[int],
    excluded_points: Set[int],
    rank_s: int,
    include_dims: List[int] | None,
    through_fixed_dims: List[int] | None,
    include_rank1_proj: bool,
    max_rank1_count: int | None,
    out_path: Path,
    time_limit: float = 0,
):
    """Build OPB encoding of the Wang capacity support problem."""
    t0 = time.time()
    
    # Load LUT
    lut = load_lut()
    total_subspaces = len(lut)
    
    # All 511 projective points of PG(8,2)
    all_points = list(range(1, 2**N))
    point_set = set(all_points)
    
    # Decision variables: one per projective point, excluding fixed and excluded
    fixed_set = set(fixed_points)
    excl_set = set(excluded_points)
    
    # Variables are indexed by projective point number
    # In OPB: x1 means point 1 is selected, etc.
    decision_points = sorted(p for p in all_points if p not in fixed_set and p not in excl_set)
    n_vars = len(decision_points)
    dp_set = set(decision_points)
    
    # Rank-1 points (matrix rank 1 in 3x3 over F2)
    rank1_set = set(p for p in all_points if matrix_rank_of_mask(p) == 1)
    
    constraints = []
    
    # 1. Total support size = rank_s (counting fixed points)
    # sum(x_p for p in decision) = rank_s - |fixed|
    # In OPB: equality is encoded as two inequalities or using =
    target = rank_s - len(fixed_set)
    lhs_total = " + ".join(f"1 x{p}" for p in decision_points)
    constraints.append(f"{lhs_total} = {target} ;")
    
    # 2. Wang capacity constraints
    wang_added = 0
    for key, val in lut.items():
        basis = unpack_basis(key)
        lb = val['lb']
        cap = rank_s - lb
        if cap < 0:
            # Impossible - would need empty clause
            constraints.append(f"1 x{decision_points[0]} >= 2 ;")  # contradiction
            wang_added += 1
            continue
        
        # Get points in this subspace
        pts = subspace_points_from_basis(basis)
        
        # Filter to relevant dimensions
        dim = len(basis)
        if include_dims is not None and through_fixed_dims is not None:
            # Include if dim in include_dims, or if dim in through_fixed_dims
            # and the subspace contains all fixed points
            in_dims = dim in include_dims
            in_through = dim in through_fixed_dims
            if in_through:
                if not all(any(in_rowspace(fp, basis) for _ in [0]) or in_rowspace(fp, basis) for fp in fixed_points):
                    in_through = False
            if not in_dims and not in_through:
                continue
        elif include_dims is not None:
            if dim not in include_dims:
                continue
        
        # Count fixed points in subspace
        fixed_in_phi = sum(1 for fp in fixed_points if in_rowspace(fp, basis))
        
        remaining_cap = cap - fixed_in_phi
        if remaining_cap < 0:
            # Fixed points alone exceed capacity - contradiction
            constraints.append(f"1 x{decision_points[0]} >= 2 ;")
            wang_added += 1
            continue
        
        # Decision points in subspace
        dp_in_phi = [p for p in pts if p in dp_set]
        if not dp_in_phi:
            continue
        
        if remaining_cap >= len(dp_in_phi):
            continue  # trivially satisfied
        
        # Cardinality constraint: sum <= remaining_cap
        lhs = " + ".join(f"1 x{p}" for p in dp_in_phi)
        constraints.append(f"{lhs} <= {remaining_cap} ;")
        wang_added += 1
    
    # 3. Optional rank-1 count constraint
    r1_added = 0
    if max_rank1_count is not None:
        r1_decision = [p for p in decision_points if p in rank1_set]
        r1_fixed = sum(1 for fp in fixed_points if fp in rank1_set)
        r1_cap = max_rank1_count - r1_fixed
        if r1_cap < len(r1_decision):
            lhs = " + ".join(f"1 x{p}" for p in r1_decision)
            constraints.append(f"{lhs} <= {r1_cap} ;")
            r1_added = 1
    
    # 4. Optional rank-1 projection constraints
    r1_proj_added = 0
    if include_rank1_proj:
        # For each Wang row, project onto rank-1 points
        for key, val in lut.items():
            basis = unpack_basis(key)
            lb = val['lb']
            cap = rank_s - lb
            pts = subspace_points_from_basis(basis)
            r1_pts = [p for p in pts if p in rank1_set]
            if not r1_pts:
                continue
            r1_cap_fixed = sum(1 for fp in fixed_points if fp in rank1_set and in_rowspace(fp, basis))
            r1_remaining = cap - r1_cap_fixed  # pessimistic: all cap used by rank-1
            # Actually the rank-1 projection is: among rank-1 points in Phi,
            # at most cap_Phi can be selected (same cap as full Wang row)
            r1_dp = [p for p in r1_pts if p in dp_set]
            if not r1_dp or r1_remaining >= len(r1_dp):
                continue
            if r1_remaining < 0:
                constraints.append(f"1 x{decision_points[0]} >= 2 ;")
                r1_proj_added += 1
                continue
            # Only add if the rank-1 intersection has ≤ some size
            if len(r1_pts) <= 9:
                lhs = " + ".join(f"1 x{p}" for p in r1_dp)
                constraints.append(f"{lhs} <= {r1_remaining} ;")
                r1_proj_added += 1
    
    # Write OPB file
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open('w') as f:
        f.write(f"* #variable= {n_vars} #constraint= {len(constraints)}\n")
        f.write(f"* Wang capacity OPB for fixed {fixed_points}, excl {len(excl_set)}, rank_s={rank_s}\n")
        for c in constraints:
            f.write(c + "\n")
    
    elapsed = time.time() - t0
    meta = {
        "n_vars": n_vars,
        "n_constraints": len(constraints),
        "wang_rows_added": wang_added,
        "r1_proj_added": r1_proj_added,
        "rank_s": rank_s,
        "fixed_points": fixed_points,
        "excluded_count": len(excl_set),
        "decision_count": n_vars,
        "elapsed_sec": elapsed,
        "opb_path": str(out_path),
    }
    return meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rep", type=int, required=True, help="Second fixed point (Stab(E11) rep)")
    ap.add_argument("--rank-s", type=int, default=20)
    ap.add_argument("--include-dims", type=str, default="1,2,3",
                    help="Comma-separated dims to include directly")
    ap.add_argument("--through-fixed-dims", type=str, default="4,5,6",
                    help="Comma-separated dims to include if containing all fixed points")
    ap.add_argument("--include-rank1-proj", action="store_true")
    ap.add_argument("--max-rank1", type=int, default=None)
    ap.add_argument("--exclude-orbits", type=str, default="",
                    help="Comma-separated Stab(E11) orbit reps to exclude")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    
    inc_dims = [int(x) for x in args.include_dims.split(",")] if args.include_dims else None
    thr_dims = [int(x) for x in args.through_fixed_dims.split(",")] if args.through_fixed_dims else None
    
    # Load actions for orbit exclusion
    sys.path.insert(0, str(SCRIPT_DIR))
    from wang_capacity_lazy import make_actions
    actions = make_actions()
    stab_e11 = compute_stab_e11(actions)
    
    # Compute orbits for exclusion
    excluded = set()
    if args.exclude_orbits:
        excl_reps = [int(x) for x in args.exclude_orbits.split(",")]
        for rep in excl_reps:
            orbit = set()
            for a in stab_e11:
                orbit.add(a[rep])
            excluded |= orbit
    
    fixed = [1, args.rep]  # E11 + second point
    
    meta = build_opb(
        fixed_points=fixed,
        excluded_points=excluded,
        rank_s=args.rank_s,
        include_dims=inc_dims,
        through_fixed_dims=thr_dims,
        include_rank1_proj=args.include_rank1_proj,
        max_rank1_count=args.max_rank1,
        out_path=args.out,
    )
    
    print(json.dumps(meta, indent=2))


if __name__ == "__main__":
    main()
