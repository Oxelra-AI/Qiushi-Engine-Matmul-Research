#!/usr/bin/env python3
"""Compute stabilizer orbits for rank-2 and rank-3 quotient pivots.

For pivot p, the stabilizer is {(P,Q) in GL3(F2) x GL3(F2) : P^T p Q^{-T} = p}.
Its action on the quotient A-space F2^8 gives orbits that can be used for
symmetry breaking in SAT and DFS.

Also computes: how many quotient Wang rows are invariant under the stabilizer
(a consistency check on the LUT).
"""
from __future__ import annotations

import json
import os
import sys
from collections import Counter
from pathlib import Path
from typing import Dict, List, Set, Tuple

import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from quotient_line_caps_and_controls import (
    bits_to_mat, mat_to_bits, gf2_rank_mat, gf2_inv, gl3,
    quotient_project, quotient_tensor,
)

OUTDIR = SESSION / "workspace/data/quotient_orbits"


def compute_stabilizer(pivot: int) -> List[Tuple[np.ndarray, np.ndarray]]:
    """Find all (P, Q) in GL3(F2) x GL3(F2) such that P^T * A * Q^{-T} = A
    where A is the matrix corresponding to the pivot."""
    A = bits_to_mat(pivot)
    stabilizer = []
    all_gl3 = gl3()
    for P in all_gl3:
        for Q in all_gl3:
            QinvT = gf2_inv(Q).T % 2
            result = (P.T @ A @ QinvT) % 2
            if np.array_equal(result % 2, A):
                stabilizer.append((P.copy(), Q.copy()))
    return stabilizer


def quotient_action(P: np.ndarray, Q: np.ndarray, pivot: int, q_point: int) -> int:
    """Apply the stabilizer element (P,Q) to a quotient point.
    
    The action on the full A-space is A -> P^T A Q^{-T}.
    The quotient map is a -> quotient_project(a, pivot).
    We need: quotient_project(P^T * a_lift * Q^{-T}, pivot).
    """
    # Lift q_point to a 9-bit representative
    h = pivot.bit_length() - 1
    low = q_point & ((1 << h) - 1)
    high = (q_point >> h) << (h + 1)
    a_lift = low | high  # 9-bit representative with bit h = 0
    
    # Apply transformation
    A = bits_to_mat(a_lift)
    QinvT = gf2_inv(Q).T % 2
    B = (P.T @ A @ QinvT) % 2
    b = mat_to_bits(B)
    
    return quotient_project(b, pivot)


def compute_orbits(pivot: int, stabilizer: List[Tuple[np.ndarray, np.ndarray]]) -> Dict:
    """Compute orbits of the stabilizer action on quotient points 1..255."""
    visited = set()
    orbits = []
    
    for q in range(1, 256):
        if q in visited:
            continue
        orbit = set()
        for P, Q in stabilizer:
            img = quotient_action(P, Q, pivot, q)
            if img > 0:
                orbit.add(img)
        orbits.append(sorted(orbit))
        visited |= orbit
    
    return {
        "num_orbits": len(orbits),
        "orbit_sizes": sorted([len(o) for o in orbits]),
        "orbit_size_hist": dict(sorted(Counter(len(o) for o in orbits).items())),
        "representatives": [o[0] for o in orbits],
        "orbits": orbits[:20],  # save first 20 for inspection
    }


def main():
    OUTDIR.mkdir(parents=True, exist_ok=True)
    
    results = {}
    for name, pivot in [("rank2", 17), ("rank3", 273)]:
        print(f"\nComputing stabilizer for {name} (pivot {pivot})...")
        stab = compute_stabilizer(pivot)
        print(f"  Stabilizer size: {len(stab)}")
        
        print(f"  Computing orbits on quotient points...")
        orb = compute_orbits(pivot, stab)
        print(f"  Orbits: {orb['num_orbits']}, sizes: {orb['orbit_size_hist']}")
        
        results[name] = {
            "pivot": pivot,
            "pivot_matrix_rank": int(gf2_rank_mat(bits_to_mat(pivot))),
            "stabilizer_size": len(stab),
            "orbits": orb,
        }
    
    out_path = OUTDIR / "quotient_stabilizer_orbits.json"
    out_path.write_text(json.dumps(results, indent=2, sort_keys=True))
    print(f"\nSaved {out_path}")
    print(json.dumps({k: {
        "pivot": v["pivot"],
        "stabilizer_size": v["stabilizer_size"],
        "num_orbits": v["orbits"]["num_orbits"],
        "orbit_size_hist": v["orbits"]["orbit_size_hist"],
    } for k, v in results.items()}, indent=2))


if __name__ == "__main__":
    main()
