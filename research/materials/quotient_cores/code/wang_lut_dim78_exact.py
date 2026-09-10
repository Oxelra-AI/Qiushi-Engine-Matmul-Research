#!/usr/bin/env python3
"""Check dim-8 and dim-7 LUT exactness using the correct quotient interpretation.

The Wang LB value for a subspace W is a lower bound on the rank of T/W,
where T/W is the restriction of T to a COMPLEMENT of W in F2^9.

Dim-8 (codim 1): complement is 1-dimensional, T/W = single 9x9 matrix,
                  LB should equal its GF(2) matrix rank.
Dim-7 (codim 2): complement is 2-dimensional, T/W = matrix pencil,
                  LB <= tensor rank of the pencil.
"""
from __future__ import annotations
import json, os, pickle, sys, time
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
LUT_PATH = SCRIPT_DIR / ".." / ".." / ".." / ".." / "data/wang_f2_lb20/wang_subspace_lut.pkl"
OUTDIR = SESSION / "workspace/data/wang_analysis"
OUTDIR.mkdir(parents=True, exist_ok=True)

def gf2_rank(m):
    m = np.array(m, dtype=np.int32) % 2
    rows, cols = m.shape
    r = 0
    for c in range(cols):
        pivot = None
        for rr in range(r, rows):
            if m[rr, c] % 2:
                pivot = rr
                break
        if pivot is None:
            continue
        m[[r, pivot]] = m[[pivot, r]]
        for rr in range(rows):
            if rr != r and m[rr, c] % 2:
                m[rr] = (m[rr] + m[r]) % 2
        r += 1
    return r

def build_slice_table():
    """T[a] for each a in 0..511, as 9x9 GF(2) matrices."""
    slices = {}
    # Single-bit slices (basis)
    for bit in range(9):
        M = np.zeros((9, 9), dtype=np.int32)
        # bit = 3i+j, slice T[e_{ij}]
        i, j = divmod(bit, 3)
        for k in range(3):
            M[3*j+k, 3*i+k] = 1
        slices[1 << bit] = M
    slices[0] = np.zeros((9, 9), dtype=np.int32)
    # Multi-bit by linearity
    for a in range(512):
        if a in slices:
            continue
        M = np.zeros((9, 9), dtype=np.int32)
        for bit in range(9):
            if (a >> bit) & 1:
                M = (M + slices[1 << bit]) % 2
        slices[a] = M
    return slices

def unpack_basis(key):
    k = int(key)
    d = k & 0xF
    x = k >> 4
    basis = []
    for _ in range(d):
        basis.append(x & 0x1FF)
        x >>= 9
    return basis

def find_complement_vectors(basis, target_dim):
    """Find target_dim vectors outside span(basis) that extend it."""
    # Build span
    rref = []
    for b in basis:
        v = int(b)
        for rb in rref:
            top = rb.bit_length() - 1
            if (v >> top) & 1:
                v ^= rb
        if v == 0:
            continue
        # Insert maintaining pivot order
        inserted = False
        for idx in range(len(rref)):
            if v.bit_length() > rref[idx].bit_length():
                rref.insert(idx, v)
                inserted = True
                break
        if not inserted:
            rref.append(v)
    
    # Find vectors outside the span
    complement = []
    for candidate in range(1, 512):
        v = candidate
        for rb in rref:
            top = rb.bit_length() - 1
            if (v >> top) & 1:
                v ^= rb
        if v != 0:  # not in span
            # Check independence with existing complement vectors
            ok = True
            test_rref = list(rref) + complement[:]
            vv = candidate
            for rb in test_rref:
                top = rb.bit_length() - 1
                if (vv >> top) & 1:
                    vv ^= rb
            if vv != 0:
                complement.append(candidate)
                # Add to extended basis for future independence checks
                rref_ext = list(rref) + complement[:]
                if len(complement) >= target_dim:
                    break
    return complement

def main():
    t0 = time.time()
    
    with open(LUT_PATH, "rb") as f:
        data = pickle.load(f)
    lut = data['lut']
    meta = data['meta']
    
    slices = build_slice_table()
    
    # Build dim -> LB distribution from meta orbit_sizes
    dim_lb_dist = defaultdict(Counter)
    for orb in meta['orbit_sizes']:
        dim_lb_dist[orb['dim']][orb['lb']] += orb['orbit_size']
    
    print("=== LB distribution by dimension ===")
    for d in sorted(dim_lb_dist.keys()):
        total = sum(dim_lb_dist[d].values())
        print(f"  dim {d} ({total}): {dict(sorted(dim_lb_dist[d].items()))}")
    
    # --- DIM 8: single matrix ---
    print("\n=== Dim 8: codim-1 (single 9×9 matrix) ===")
    dim8_results = {"exact": 0, "loose": 0, "overclaim": 0, "total": 0}
    dim8_lb_rank_pairs = Counter()
    
    count = 0
    for key, lb_val in lut.items():
        basis = unpack_basis(key)
        if len(basis) != 8:
            continue
        dim8_results["total"] += 1
        
        # Find one complement vector
        comp = find_complement_vectors(basis, 1)
        if not comp:
            print(f"  WARNING: no complement for {key}")
            continue
        p = comp[0]
        
        # Quotient = single slice T[p]
        M = slices[p]
        true_rank = gf2_rank(M)
        
        dim8_lb_rank_pairs[(lb_val, true_rank)] += 1
        
        if lb_val == true_rank:
            dim8_results["exact"] += 1
        elif lb_val < true_rank:
            dim8_results["loose"] += 1
        else:
            dim8_results["overclaim"] += 1
        
        count += 1
        if count % 100 == 0:
            print(f"  ...processed {count}/511 dim-8 entries")
    
    print(f"\n  Results: {dim8_results}")
    print(f"  (LUT_LB, true_rank) pairs: {dict(sorted(dim8_lb_rank_pairs.items()))}")
    
    # --- DIM 7: matrix pencil ---
    print("\n=== Dim 7: codim-2 (matrix pencil) ===")
    dim7_results = {"lut_matches_pencil": 0, "lut_below_pencil": 0, "lut_above_pencil": 0, "total": 0}
    dim7_lb_pencil_pairs = Counter()
    dim7_loose_examples = []
    
    count = 0
    for key, lb_val in lut.items():
        basis = unpack_basis(key)
        if len(basis) != 7:
            continue
        dim7_results["total"] += 1
        
        comp = find_complement_vectors(basis, 2)
        if len(comp) < 2:
            continue
        p1, p2 = comp[0], comp[1]
        
        # Pencil: 3 nonzero combinations (p1, p2, p1^p2) 
        M1 = slices[p1]
        M2 = slices[p2]
        M3 = slices[p1 ^ p2]
        
        # Max slice rank
        pencil_lb = max(gf2_rank(M1), gf2_rank(M2), gf2_rank(M3))
        
        # Also: (12,3) flattening: stack 3 nonzero slices as 27x9
        flat = np.vstack([M1, M2, M3]) % 2
        flat_rank = gf2_rank(flat)
        pencil_lb = max(pencil_lb, flat_rank)
        
        dim7_lb_pencil_pairs[(lb_val, pencil_lb)] += 1
        
        if lb_val == pencil_lb:
            dim7_results["lut_matches_pencil"] += 1
        elif lb_val < pencil_lb:
            dim7_results["lut_below_pencil"] += 1
            if len(dim7_loose_examples) < 10:
                dim7_loose_examples.append({
                    "key": str(key), "lut_lb": lb_val, "pencil_lb": pencil_lb,
                    "comp": [p1, p2], "slice_ranks": [gf2_rank(M1), gf2_rank(M2), gf2_rank(M3)],
                    "flat_rank": flat_rank,
                })
        else:
            dim7_results["lut_above_pencil"] += 1
        
        count += 1
        if count % 5000 == 0:
            print(f"  ...processed {count}/43435 dim-7 entries")
    
    print(f"\n  Results: {dim7_results}")
    print(f"  (LUT_LB, pencil_LB) distribution: {dict(sorted(dim7_lb_pencil_pairs.items()))}")
    if dim7_loose_examples:
        print(f"  LOOSE examples: {json.dumps(dim7_loose_examples[:3], indent=2)}")
    
    elapsed = time.time() - t0
    
    result = {
        "dim_lb_dist": {str(d): dict(dim_lb_dist[d]) for d in sorted(dim_lb_dist.keys())},
        "dim8": dim8_results,
        "dim8_lb_rank_pairs": {str(k): v for k, v in sorted(dim8_lb_rank_pairs.items())},
        "dim7": dim7_results,
        "dim7_lb_pencil_pairs": {str(k): v for k, v in sorted(dim7_lb_pencil_pairs.items())},
        "dim7_loose_examples": dim7_loose_examples,
        "elapsed_sec": round(elapsed, 2),
    }
    
    out = OUTDIR / "dim78_exactness_v2.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"\nSaved {out}")

if __name__ == "__main__":
    main()
