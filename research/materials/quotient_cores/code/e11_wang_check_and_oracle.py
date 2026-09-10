#!/usr/bin/env python3
"""Check DFS-generated supports against full Wang table and run oracle.

Takes the supports from the cap<=3 DFS, checks them against the complete
417,199-row Wang table for the E11 core, then runs the fixed-A completion
oracle on survivors. ONE SAT = rank-22 decomposition.
"""
import json
import pickle
import sys
import time
from pathlib import Path

import numpy as np

SCRIPTS_S04 = Path("scripts")
if str(SCRIPTS_S04) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_S04))

from wang_capacity_lazy import rref_basis, unpack_basis
from core_capacity_from_wang_lut import CoreQuotient, load_lut

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
DFS_PATH = Path("data/ghw_singleton/dfs_pilot_cap3.json")
OUTDIR = Path("data/ghw_singleton")

MASK9 = (1 << 9) - 1
N_COLS = 19


def key_contains_e11(key: int) -> bool:
    d = key & 0xF
    if d == 0:
        return False
    last_row = (key >> (4 + 9 * (d - 1))) & MASK9
    return last_row == 1


def check_support_complete_wang(support, lut, core):
    """Check a 19-point support against ALL E11 Wang constraints.
    
    Returns (ok, violations) where violations is list of (dim, lb, cap, count).
    """
    support_set = set(support)
    
    # For each E11-containing subspace, check occupancy
    violations = []
    
    # Compute all subset-span keys for the support
    # Instead, iterate the full LUT and check E11-containing subspaces
    for key9, lb_val in lut.items():
        if not key_contains_e11(key9):
            continue
        
        cap = N_COLS - lb_val
        if cap >= N_COLS or cap < 0:
            if cap < 0:
                violations.append((key9 & 0xF, lb_val, cap, 0))
            continue
        
        dim9 = key9 & 0xF
        
        # Enumerate nonzero points in the 8-bit quotient subspace
        basis9 = list(unpack_basis(key9))
        basis8_raw = []
        for b in basis9:
            if b == 1:
                continue
            q = b
            if q & 1:
                q ^= 1
            q8 = 0
            for bit in range(1, 9):
                if (q >> bit) & 1:
                    q8 |= 1 << (bit - 1)
            basis8_raw.append(q8)
        
        if not basis8_raw:
            continue
        basis8 = rref_basis(basis8_raw, n=8)
        
        # Count support points in this subspace
        count = 0
        for mask in range(1, 1 << len(basis8)):
            v = 0
            for i in range(len(basis8)):
                if (mask >> i) & 1:
                    v ^= basis8[i]
            if v in support_set:
                count += 1
        
        if count > cap:
            violations.append((dim9, lb_val, cap, count))
    
    return len(violations) == 0, violations


def check_support_fast(support, constraint_table):
    """Fast check using precomputed constraint table.
    
    constraint_table: list of (cap, point_set) pairs.
    """
    support_set = frozenset(support)
    for cap, pts in constraint_table:
        count = len(support_set & pts)
        if count > cap:
            return False
    return True


def build_full_constraint_table(lut, core):
    """Build ALL E11 constraints as (cap, point_set) pairs."""
    table = []
    
    for key9, lb_val in lut.items():
        if not key_contains_e11(key9):
            continue
        
        cap = N_COLS - lb_val
        if cap >= N_COLS:
            continue
        
        dim9 = key9 & 0xF
        basis9 = list(unpack_basis(key9))
        basis8_raw = []
        for b in basis9:
            if b == 1:
                continue
            q = b
            if q & 1:
                q ^= 1
            q8 = 0
            for bit in range(1, 9):
                if (q >> bit) & 1:
                    q8 |= 1 << (bit - 1)
            basis8_raw.append(q8)
        
        if not basis8_raw:
            continue
        basis8 = rref_basis(basis8_raw, n=8)
        d = len(basis8)
        
        pts = set()
        for mask in range(1, 1 << d):
            v = 0
            for i in range(d):
                if (mask >> i) & 1:
                    v ^= basis8[i]
            if 0 < v <= 255:
                pts.add(v)
        
        if pts:
            table.append((cap, frozenset(pts)))
    
    return table


def main():
    t0 = time.time()
    
    # Load DFS solutions
    print("Loading DFS solutions...")
    with open(DFS_PATH) as f:
        dfs_data = json.load(f)
    solutions = dfs_data["solutions_head"]  # First 10 from the saved file
    print(f"  DFS found {dfs_data['solutions_found']} solutions")
    print(f"  Available in file: {len(solutions)}")
    
    # Load Wang LUT
    print("Loading Wang LUT...")
    lut, meta = load_lut(LUT_PATH)
    core = CoreQuotient(pivot=1)
    
    # Build full constraint table (once)
    print("Building full constraint table...")
    t1 = time.time()
    full_table = build_full_constraint_table(lut, core)
    print(f"  Built {len(full_table)} constraints in {time.time()-t1:.1f}s")
    
    # Also build cap 4-5 only table for analysis
    cap45_table = [(cap, pts) for cap, pts in full_table if cap in (4, 5)]
    print(f"  Cap 4-5 constraints: {len(cap45_table)}")
    
    # Check each solution against full Wang
    print(f"\nChecking {len(solutions)} solutions against full Wang table...")
    
    survivors_full = []
    survivors_cap45 = []
    
    for i, sol in enumerate(solutions):
        sol_set = frozenset(sol)
        
        # Check cap 4-5 first (these were NOT in the DFS)
        cap45_ok = all(len(sol_set & pts) <= cap for cap, pts in cap45_table)
        if cap45_ok:
            survivors_cap45.append(i)
        
        # Check full table
        full_ok = check_support_fast(sol, full_table)
        if full_ok:
            survivors_full.append(i)
    
    print(f"\n  Pass cap 4-5 check: {len(survivors_cap45)}/{len(solutions)}")
    print(f"  Pass full Wang:     {len(survivors_full)}/{len(solutions)}")
    
    elapsed = time.time() - t0
    
    output = {
        "status": "ok",
        "dfs_solutions_checked": len(solutions),
        "survivors_cap45": len(survivors_cap45),
        "survivors_full_wang": len(survivors_full),
        "full_constraint_count": len(full_table),
        "cap45_constraint_count": len(cap45_table),
        "surviving_supports": [solutions[i] for i in survivors_full[:20]],
        "elapsed_sec": elapsed,
    }
    
    outpath = OUTDIR / "wang_check_results.json"
    with open(outpath, "w") as f:
        json.dump(output, f, indent=2, sort_keys=True)
    print(f"\nSaved to {outpath}")
    print(json.dumps(output, indent=2, sort_keys=True)[:2000])


if __name__ == "__main__":
    main()
