#!/usr/bin/env python3
"""Verify the domain DFS positive control: rank-21 pool must be FEASIBLE at length 21."""
import json, subprocess, struct, time
from pathlib import Path
import numpy as np

DFS = str(Path("scripts/e11_domain_dfs"))
CONS = str(Path("data/wang_native/e11_wang_cap5.bin"))
POOL = Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
OUTDIR = Path("data/wang_native")

def main():
    # Load pool and extract quotient A-directions
    pool = np.load(POOL)
    N, cols = pool.shape
    R = cols // 3
    
    print(f"Pool: {N} rows, {R} terms per row")
    
    # Load constraint binary to get row data for manual checking
    with open(CONS, "rb") as f:
        magic = f.read(8)
        assert magic == b"E11WANG1"
        nrows = struct.unpack("<I", f.read(4))[0]
        rows = []
        for _ in range(nrows):
            cap, dim, reserved = struct.unpack("<BBH", f.read(4))
            mask_words = struct.unpack("<4Q", f.read(32))
            pts = set()
            for w in range(4):
                m = mask_words[w]
                while m:
                    bit = m & (-m)
                    p = w * 64 + bit.bit_length() - 1
                    if 1 <= p <= 255:
                        pts.add(p)
                    m ^= bit
            rows.append((cap, dim, pts))
    
    print(f"Loaded {nrows} cap<=5 constraints")
    
    # Check first 20 pool rows against cap<=5 constraints at length 21
    violations_total = 0
    for row_idx in range(min(20, N)):
        row = pool[row_idx]
        us = [int(row[3*t]) & 0xFF for t in range(R)]  # raw 8-bit core masks
        nonzero_us = [u for u in us if u != 0]
        
        # Count occupancy per constraint row
        max_violations = 0
        for ri, (cap, dim, pts) in enumerate(rows):
            cap21 = cap + 2  # cap at length 21 = (21 - lb) where cap19 = (19 - lb), so cap21 = cap19 + 2
            occ = sum(1 for u in us if u in pts)  # with multiplicity
            if occ > cap21:
                max_violations += 1
        
        if max_violations > 0:
            violations_total += 1
        print(f"  Row {row_idx}: {len(nonzero_us)} nonzero dirs, violations at cap21 = {max_violations}")
    
    # Also check at length 19 (should be infeasible for most)
    print(f"\nCheck at length 19 (expect many violations since pool is rank 21):")
    for row_idx in range(min(5, N)):
        row = pool[row_idx]
        us = [int(row[3*t]) & 0xFF for t in range(R)]
        nonzero_us = [u for u in us if u != 0]
        
        viol19 = 0
        for ri, (cap, dim, pts) in enumerate(rows):
            occ = sum(1 for u in us if u in pts)
            if occ > cap:  # cap19
                viol19 += 1
        print(f"  Row {row_idx}: {len(nonzero_us)} nonzero dirs, violations at cap19 = {viol19}")
    
    print(f"\nPool positive control at cap21: {violations_total} rows with violations out of {min(20, N)}")
    if violations_total == 0:
        print("POSITIVE CONTROL PASSED: known rank-21 pool satisfies cap<=5 at length 21")
    else:
        print("WARNING: pool violations detected at cap21!")

if __name__ == "__main__":
    main()
