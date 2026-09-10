#!/usr/bin/env python3
"""Generate orbit-branched Wang constraint binaries for quotient DFS.

For each orbit branch k, generates a constraint binary where:
  - All points from orbits 0,...,k-1 are removed from all masks
  - The orbit representative is available for forcing
  - Remaining points are from orbits k,...,num_orbits-1

This enables complete symmetry-aware DFS: the union of all branch searches
covers all Wang-admissible supports up to stabilizer equivalence.
"""
from __future__ import annotations

import json
import os
import struct
import sys
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent

ORBIT_PATH = SESSION / "workspace/data/quotient_orbits/quotient_stabilizer_orbits.json"
BIN_DIR = SESSION / "workspace/data/wang_native/quotient_binaries"
OUT_DIR = SESSION / "workspace/data/wang_native/orbit_branches"


def load_binary(path: str):
    """Load E11WANG1 format binary."""
    rows = []
    with open(path, 'rb') as f:
        magic = f.read(8)
        assert magic == b'E11WANG1', f"Bad magic: {magic}"
        nrows = struct.unpack('<I', f.read(4))[0]
        for _ in range(nrows):
            hdr = f.read(4)
            cap = hdr[0]
            dim = hdr[1]
            words = list(struct.unpack('<4Q', f.read(32)))
            rows.append((cap, dim, words))
    return rows


def remove_points_from_rows(rows, points_to_remove):
    """Remove specified points from all constraint masks."""
    new_rows = []
    for cap, dim, words in rows:
        new_words = list(words)
        for p in points_to_remove:
            w_idx = p >> 6
            bit = p & 63
            new_words[w_idx] &= ~(1 << bit)
        # Count remaining points
        npts = sum(bin(w).count('1') for w in new_words)
        if npts > 0 and cap > 0:  # keep non-trivial constraints
            new_rows.append((cap, dim, new_words))
    return new_rows


def write_binary(rows, path):
    """Write E11WANG1 format binary."""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'wb') as f:
        f.write(b'E11WANG1')
        f.write(struct.pack('<I', len(rows)))
        for cap, dim, words in rows:
            f.write(struct.pack('<BBHQQQQ', cap, dim, 0, *words))


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot-name", choices=["rank2", "rank3"], required=True)
    ap.add_argument("--target", type=int, default=19)
    args = ap.parse_args()
    
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    
    orbits_data = json.loads(ORBIT_PATH.read_text())
    pivot_data = orbits_data[args.pivot_name]
    all_orbits = pivot_data["orbits"]["orbits"]
    reps = pivot_data["orbits"]["representatives"]
    
    # Load the all-cap binary for this pivot at the target
    bin_name = f"{args.pivot_name}_all_n{args.target}.bin"
    bin_path = BIN_DIR / bin_name
    if not bin_path.exists():
        print(f"ERROR: {bin_path} not found")
        return
    
    print(f"Loading {bin_path}...")
    base_rows = load_binary(str(bin_path))
    print(f"  Loaded {len(base_rows)} rows")
    
    # Generate orbit-branched binaries
    summary = {
        "pivot_name": args.pivot_name,
        "pivot": pivot_data["pivot"],
        "target": args.target,
        "num_orbits": len(all_orbits),
        "stabilizer_size": pivot_data["stabilizer_size"],
        "branches": [],
    }
    
    forbidden_pts = set()
    
    for branch_idx in range(len(all_orbits)):
        orbit = all_orbits[branch_idx]
        rep = reps[branch_idx]
        orbit_size = len(orbit)
        
        # Points available in this branch
        available = 255 - len(forbidden_pts)
        
        branch_rows = remove_points_from_rows(base_rows, forbidden_pts)
        
        # Write branch binary
        branch_name = f"{args.pivot_name}_n{args.target}_branch{branch_idx}.bin"
        branch_path = OUT_DIR / branch_name
        write_binary(branch_rows, str(branch_path))
        
        # Count cap-1 rows in this branch
        cap1_count = sum(1 for cap, _, _ in branch_rows if cap == 1)
        
        branch_info = {
            "branch": branch_idx,
            "representative": rep,
            "orbit_size": orbit_size,
            "available_points": available,
            "rows": len(branch_rows),
            "cap1_rows": cap1_count,
            "binary": str(branch_path),
            "force_prefix": f"--force-prefix {rep}",
        }
        summary["branches"].append(branch_info)
        
        print(f"  Branch {branch_idx}: rep={rep}, orbit_size={orbit_size}, "
              f"available={available}, rows={len(branch_rows)}, cap1={cap1_count}")
        
        # Add this orbit's points to forbidden set for next branches
        forbidden_pts.update(orbit)
    
    summary_path = OUT_DIR / f"{args.pivot_name}_n{args.target}_orbit_branches.json"
    summary_path.write_text(json.dumps(summary, indent=2))
    print(f"\nSaved {summary_path}")


if __name__ == "__main__":
    main()
