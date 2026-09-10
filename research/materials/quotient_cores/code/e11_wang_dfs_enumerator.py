#!/usr/bin/env python3
"""Orderly DFS enumeration of Wang-admissible 19-point E11 core A-supports.

For an E11 core rank-19 decomposition, the 19 distinct quotient A-directions
q_1,...,q_19 in F_2^8 must satisfy ALL Wang constraints:
  for every subspace Psi <= F_2^8:
    #{t : q_t in Psi} <= 19 - LB(span(E11, lift(Psi)))

This script performs orderly DFS over columns in increasing order {1,...,255},
with incremental occupancy pruning: each chosen column updates the inside-count
for every Wang row whose subspace contains it, and we prune if any count exceeds
its capacity.

The DFS reports the surviving-node count per depth — this is the key measurement
that tells us whether the support space is finite, manageable, or empty.

Canonicity under the 576-element E11 stabilizer reduces the search by ~576x.
"""
import json
import pickle
import sys
import time
from collections import defaultdict
from pathlib import Path

import numpy as np

SCRIPTS_S04 = Path("scripts")
if str(SCRIPTS_S04) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_S04))

from wang_capacity_lazy import pack_basis, rref_basis, unpack_basis
from core_capacity_from_wang_lut import CoreQuotient, load_lut

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
ORBIT_PATH = Path("data/e11_orbits/e11_quotient_orbits.json")
OUTDIR = Path("data/ghw_singleton")
OUTDIR.mkdir(parents=True, exist_ok=True)

MASK9 = (1 << 9) - 1
N_COLS = 19
N_POINTS = 255


def key_contains_e11(key: int) -> bool:
    d = key & 0xF
    if d == 0:
        return False
    last_row = (key >> (4 + 9 * (d - 1))) & MASK9
    return last_row == 1


def subspace_nonzero_points_from_key8(key8: int) -> list:
    """Enumerate all nonzero points in the F_2^8 subspace encoded by key8."""
    basis = list(unpack_basis(key8))
    d = len(basis)
    # For the 8-bit quotient, basis rows might use 9-bit packing but only 8 bits
    points = set()
    for mask in range(1, 1 << d):
        v = 0
        for i in range(d):
            if (mask >> i) & 1:
                v ^= basis[i]
        if v != 0 and v <= 255:
            points.add(v)
    return sorted(points)


def build_constraints(lut, core, max_cap=None):
    """Build the constraint table: list of (cap, points) for each Wang row.
    
    Returns:
      rows: list of (cap, frozenset_of_points)
      point_to_rows: dict point -> list of row indices
    """
    rows = []
    point_to_rows = defaultdict(list)
    
    for key9, lb_val in lut.items():
        if not key_contains_e11(key9):
            continue
        
        cap = N_COLS - lb_val  # max columns inside
        if cap >= N_COLS:  # trivially satisfied
            continue
        if max_cap is not None and cap > max_cap:
            continue
        if cap < 0:  # impossible
            rows.append((cap, frozenset()))
            continue
        
        # Recover the 8-bit key
        dim9 = key9 & 0xF
        basis9 = list(unpack_basis(key9))
        
        # Project 9-bit basis to 8-bit quotient (remove E11 component)
        basis8_raw = []
        for b in basis9:
            if b == 1:  # E11 itself
                continue
            # Clear bit 0 if set (reduce mod E11)
            q = b
            if q & 1:
                q ^= 1  # XOR with E11 = 1
            # Now q has bit 0 = 0, pack as 8-bit by removing bit 0
            q8 = 0
            for bit in range(1, 9):
                if (q >> bit) & 1:
                    q8 |= 1 << (bit - 1)
            basis8_raw.append(q8)
        
        # Get RREF and enumerate points
        if not basis8_raw:
            continue
        basis8 = rref_basis(basis8_raw, n=8)
        points = set()
        d = len(basis8)
        for mask in range(1, 1 << d):
            v = 0
            for i in range(d):
                if (mask >> i) & 1:
                    v ^= basis8[i]
            if 0 < v <= 255:
                points.add(v)
        
        if not points and cap < N_COLS:
            # Trivial subspace {0} -> no nonzero points -> cap constraint on 0 columns
            continue
        
        row_idx = len(rows)
        rows.append((cap, frozenset(points)))
        for p in points:
            point_to_rows[p].append(row_idx)
    
    return rows, dict(point_to_rows)


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-cap", type=int, default=8,
                    help="Only use Wang rows with capacity <= this")
    ap.add_argument("--max-depth", type=int, default=19,
                    help="Maximum DFS depth")
    ap.add_argument("--time-limit", type=float, default=120,
                    help="Time limit in seconds")
    ap.add_argument("--use-orbits", action="store_true",
                    help="Use orbit representatives at depth 1")
    args = ap.parse_args()
    
    t0 = time.time()
    
    print(f"Loading Wang LUT from {LUT_PATH}...")
    lut, meta = load_lut(LUT_PATH)
    core = CoreQuotient(pivot=1)
    
    print(f"Building constraint table (max_cap={args.max_cap})...")
    rows, point_to_rows = build_constraints(lut, core, max_cap=args.max_cap)
    print(f"  Constraining rows: {len(rows)}")
    print(f"  Points with constraints: {len(point_to_rows)}")
    
    # Constraint cap distribution
    cap_dist = defaultdict(int)
    for cap, pts in rows:
        cap_dist[cap] += 1
    print(f"  Cap distribution: {dict(sorted(cap_dist.items()))}")
    
    # Average constraints per point
    avg_per_point = sum(len(v) for v in point_to_rows.values()) / max(len(point_to_rows), 1)
    print(f"  Avg constraints per point: {avg_per_point:.1f}")
    
    # Load orbit data for canonicity
    orbit_reps = list(range(1, 256))  # default: all points
    if args.use_orbits and ORBIT_PATH.exists():
        with open(ORBIT_PATH) as f:
            orbit_data = json.load(f)
        orbit_reps = [orb["rep"] for orb in orbit_data["point_orbits"]["orbits"]]
        print(f"  Using {len(orbit_reps)} orbit representatives at depth 1")
    
    # DFS
    print(f"\nStarting orderly DFS (max_depth={args.max_depth}, "
          f"time_limit={args.time_limit}s)...")
    
    inside_count = [0] * len(rows)  # current inside count for each row
    node_count = [0] * (args.max_depth + 1)
    solutions = []
    
    chosen = []  # current column list
    
    def dfs(min_col, depth):
        """Try extending the current column list by choosing the next column >= min_col."""
        if time.time() - t0 > args.time_limit:
            return True  # timeout
        
        if depth == args.max_depth:
            node_count[depth] += 1
            solutions.append(list(chosen))
            return False
        
        remaining = args.max_depth - depth
        
        for q in range(min_col, 256):
            if 255 - q + 1 < remaining:
                break  # not enough points left
            
            # Check: does adding q violate any constraint?
            violated = False
            updated_rows = []
            
            for row_idx in point_to_rows.get(q, []):
                inside_count[row_idx] += 1
                updated_rows.append(row_idx)
                if inside_count[row_idx] > rows[row_idx][0]:
                    violated = True
                    break
            
            if not violated:
                node_count[depth + 1] += 1
                chosen.append(q)
                timeout = dfs(q + 1, depth + 1)
                chosen.pop()
                if timeout:
                    # Undo and return
                    for ri in updated_rows:
                        inside_count[ri] -= 1
                    return True
            
            # Undo
            for ri in updated_rows:
                inside_count[ri] -= 1
        
        return False
    
    # Start DFS from depth 0
    node_count[0] = 1
    
    if args.use_orbits:
        # At depth 1, only try orbit representatives
        for rep in orbit_reps:
            for row_idx in point_to_rows.get(rep, []):
                inside_count[row_idx] += 1
            
            violated = any(inside_count[ri] > rows[ri][0] 
                          for ri in point_to_rows.get(rep, []))
            
            if not violated:
                node_count[1] += 1
                chosen.append(rep)
                timeout = dfs(rep + 1, 1)
                chosen.pop()
            
            for row_idx in point_to_rows.get(rep, []):
                inside_count[row_idx] -= 1
            
            if time.time() - t0 > args.time_limit:
                break
    else:
        timeout = dfs(1, 0)
    
    elapsed = time.time() - t0
    
    # Report
    print(f"\nDFS completed in {elapsed:.1f}s")
    print(f"\nNode count by depth:")
    for d in range(args.max_depth + 1):
        if node_count[d] > 0:
            print(f"  depth {d:>2}: {node_count[d]:>12,}")
    
    if solutions:
        print(f"\nFound {len(solutions)} complete 19-point supports!")
        for i, sol in enumerate(solutions[:5]):
            print(f"  Solution {i}: {sol}")
    else:
        max_depth_reached = max(d for d in range(len(node_count)) if node_count[d] > 0)
        print(f"\nNo complete support found. Max depth reached: {max_depth_reached}")
    
    # Save results
    output = {
        "status": "ok",
        "max_cap": args.max_cap,
        "max_depth": args.max_depth,
        "constraining_rows": len(rows),
        "cap_distribution": dict(sorted(cap_dist.items())),
        "node_count_by_depth": {str(d): node_count[d] for d in range(len(node_count)) if node_count[d] > 0},
        "solutions_found": len(solutions),
        "solutions_head": solutions[:10],
        "elapsed_sec": elapsed,
        "timeout": elapsed >= args.time_limit,
    }
    
    outpath = OUTDIR / f"dfs_pilot_cap{args.max_cap}.json"
    with open(outpath, "w") as f:
        json.dump(output, f, indent=2, sort_keys=True)
    print(f"\nSaved to {outpath}")


if __name__ == "__main__":
    main()
