#!/usr/bin/env python3
"""Enhanced pivot-fixed occupation model with flattening cut.

The pivot-fixed n=20 full Wang occupation system with x_pivot=1 is equivalent
to Wang's own target-20 computation at his dimension-1 certificate nodes.
This script adds the independent flattening cut:
    sum_{a in support} rank_3x3(a) >= 27
which with x_pivot = 1 becomes:
    sum_{a != pivot} rank(a)*x_a >= 27 - rank(pivot)

Also computes cap sensitivity: for the CEGAR candidates, which dim/LB nodes
are most binding, and what happens if we tighten specific caps by 1.
"""
from __future__ import annotations
import json, os, pickle, struct, sys, time
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
LUT_PATH = SCRIPT_DIR / ".." / ".." / ".." / ".." / "data/wang_f2_lb20/wang_subspace_lut.pkl"
OUTDIR = SESSION / "workspace/data/wang_analysis"
OUTDIR.mkdir(parents=True, exist_ok=True)

def gf2_rank_3x3(a):
    """Rank of 3x3 GF(2) matrix encoded as 9-bit int."""
    m = np.zeros((3, 3), dtype=np.int32)
    for i in range(3):
        for j in range(3):
            m[i, j] = (a >> (3*i + j)) & 1
    # GF(2) Gaussian elimination
    r = 0
    for c in range(3):
        pivot = None
        for rr in range(r, 3):
            if m[rr, c] % 2:
                pivot = rr
                break
        if pivot is None:
            continue
        m[[r, pivot]] = m[[pivot, r]]
        for rr in range(3):
            if rr != r and m[rr, c] % 2:
                m[rr] = (m[rr] + m[r]) % 2
        r += 1
    return r

def unpack_basis(key):
    k = int(key)
    d = k & 0xF
    x = k >> 4
    basis = []
    for _ in range(d):
        basis.append(x & 0x1FF)
        x >>= 9
    return basis

def main():
    t0 = time.time()
    
    # Pre-compute rank of all 512 9-bit values
    rank_of = {}
    rank_hist = Counter()
    for a in range(512):
        r = gf2_rank_3x3(a)
        rank_of[a] = r
        if a > 0:
            rank_hist[r] += 1
    print(f"Rank distribution of nonzero 3x3 F2 matrices: {dict(sorted(rank_hist.items()))}")
    # Expected: {1: 49, 2: 294, 3: 168}
    
    # Load LUT
    with open(LUT_PATH, "rb") as f:
        data = pickle.load(f)
    lut = data['lut']
    
    for pivot, pivot_name in [(17, "rank2"), (273, "rank3")]:
        print(f"\n{'='*60}")
        print(f"Pivot {pivot} ({pivot_name}), rank={rank_of[pivot]}")
        print(f"{'='*60}")
        
        # Flattening cut: sum_{a != pivot} rank(a)*x_a >= 27 - rank(pivot)
        rhs_flat = 27 - rank_of[pivot]
        print(f"Flattening cut: sum rank(a)*x_a >= {rhs_flat} from 19 non-pivot terms")
        
        # Points available: all 511 nonzero a != pivot  
        points = [a for a in range(1, 512) if a != pivot]
        n_pts = len(points)
        print(f"Available points: {n_pts}")
        
        # Rank breakdown of available points
        r_breakdown = Counter()
        for a in points:
            r_breakdown[rank_of[a]] += 1
        print(f"Rank breakdown: {dict(sorted(r_breakdown.items()))}")
        
        # At n=19 (19 non-pivot terms from 510 points):
        # If all 19 were rank-1: sum = 19 < rhs_flat
        # Need k2 + 2*k3 >= rhs_flat - 19
        needed = rhs_flat - 19
        print(f"Need r2 + 2*r3 >= {needed} among 19 non-pivot terms")
        print(f"  => At least {needed} rank-2 terms (if no rank-3)")
        print(f"  => At least {(needed + 1)//2} rank-3 terms (if no rank-2)")
        
        # Check flattening cut against CEGAR candidates
        cegar_path = SESSION / f"workspace/data/pivot_fixed/bg_p{pivot}_n20_allbinding/{pivot_name}_n20_allbinding_cegar.json"
        if not cegar_path.exists():
            cegar_path = SESSION / f"workspace/data/pivot_fixed/bg_p{pivot}_n20_allbinding/pivot{pivot}_n20_allbinding_cegar.json"
        
        if cegar_path.exists():
            cegar = json.load(open(cegar_path))
            print(f"\nCEGAR analysis from {cegar_path.name}:")
            for i, it in enumerate(cegar.get('iterations', [])):
                cand = it.get('candidate_multiset', [])
                if not cand:
                    continue
                # Compute flattening sum
                flat_sum = sum(rank_of.get(a, 0) for a in cand)
                total_sum = flat_sum + rank_of[pivot]
                
                # Rank breakdown of candidate
                cr = Counter(rank_of.get(a, 0) for a in cand)
                
                scan = it.get('scan', {})
                v_count = scan.get('violation_count', '?')
                
                print(f"  Round {i}: |cand|={len(cand)}, flat_sum={flat_sum} (need>={rhs_flat}), "
                      f"total={total_sum} (need>=27), ranks={dict(cr)}, violations={v_count}")
                
                if flat_sum < rhs_flat:
                    print(f"    *** FLATTENING CUT WOULD REJECT THIS CANDIDATE ***")
        
        # Dimension/LB analysis of violated rows
        if cegar_path.exists():
            cegar = json.load(open(cegar_path))
            dim_viol = Counter()
            cap_viol = Counter()
            lb_viol = Counter()
            
            for it in cegar.get('iterations', []):
                scan = it.get('scan', {})
                for d, c in scan.get('dim_hist_violated', {}).items():
                    dim_viol[int(d)] += c
                for cap_val, c in scan.get('cap_hist_violated', {}).items():
                    cap_viol[int(cap_val)] += c
            
            if dim_viol:
                print(f"\n  Violated row dimension distribution:")
                for d in sorted(dim_viol.keys()):
                    print(f"    dim {d}: {dim_viol[d]}")
                print(f"\n  Violated row cap distribution:")
                for c in sorted(cap_viol.keys()):
                    print(f"    cap {c}: {cap_viol[c]}")
    
    elapsed = time.time() - t0
    print(f"\nElapsed: {elapsed:.1f}s")

if __name__ == "__main__":
    main()
