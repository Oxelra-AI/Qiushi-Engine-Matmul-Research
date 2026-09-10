#!/usr/bin/env python3
"""Check whether Wang LUT dim-7 (pencil) and dim-8 (matrix) LB values are exact.

Dim-8: quotient = single 9x9 matrix, LB should equal matrix rank (exact).
Dim-7: quotient = matrix pencil (2 x 9 x 9), LB should equal at least
       max over nonzero alpha of rank(sum alpha_i M_i).

Also adds the flattening cut: sum_a rank(a)*x_a >= 27 at n=20.
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

def full_tensor():
    T = np.zeros((512, 9, 9), dtype=np.int32)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a = 3*i + j
                b = 3*j + k
                c = 3*i + k
                T[1 << a, b, c] = 1
    # Sum for all 9-bit a: T[a] = sum of T[1<<bit] for set bits
    for a in range(512):
        if bin(a).count('1') <= 1:
            continue
        T[a] = np.zeros((9, 9), dtype=np.int32)
        for bit in range(9):
            if (a >> bit) & 1:
                T[a] = (T[a] + T[1 << bit]) % 2
    return T

def unpack_basis_local(key):
    """Unpack basis from LUT key: bits 0-3 = dimension, then d 9-bit vectors."""
    k = int(key)
    d = k & 0xF
    x = k >> 4
    basis = []
    for _ in range(d):
        basis.append(x & 0x1FF)
        x >>= 9
    return basis

def quotient_project_basis(basis_ints):
    """Return RREF basis, pivot bits, and projection function."""
    rref = []
    pivot_bits = []
    for b in basis_ints:
        v = int(b)
        for pb, rb in zip(pivot_bits, rref):
            if (v >> pb) & 1:
                v ^= rb
        if v == 0:
            continue
        p = v.bit_length() - 1
        new_rref = []
        new_pivots = []
        for pb2, rb2 in zip(pivot_bits, rref):
            if (rb2 >> p) & 1:
                rb2 ^= v
            new_rref.append(rb2)
            new_pivots.append(pb2)
        new_rref.append(v)
        new_pivots.append(p)
        rref = new_rref
        pivot_bits = new_pivots
    
    pivot_set = set(pivot_bits)
    free_bits = sorted([i for i in range(9) if i not in pivot_set])
    q_dim = len(free_bits)
    
    def project(a):
        v = int(a)
        for pb, rb in zip(pivot_bits, rref):
            if (v >> pb) & 1:
                v ^= rb
        q = 0
        for qi, fi in enumerate(free_bits):
            if (v >> fi) & 1:
                q |= (1 << qi)
        return q
    
    return rref, pivot_bits, free_bits, q_dim, project

def build_quotient_tensor(T, basis_ints):
    """Build quotient tensor by summing projected slices."""
    _, _, _, q_dim, project = quotient_project_basis(basis_ints)
    n_q = 1 << q_dim
    Q = np.zeros((n_q, 9, 9), dtype=np.int32)
    for a in range(512):
        qa = project(a)
        Q[qa] = (Q[qa] + T[a]) % 2
    return Q, q_dim

def main():
    t0 = time.time()
    
    # Load LUT
    with open(LUT_PATH, "rb") as f:
        data = pickle.load(f)
    lut = data['lut']
    meta = data['meta']
    
    T = full_tensor()
    
    # Build dim -> LB distribution from meta orbit_sizes
    dim_lb_dist = defaultdict(Counter)
    for orb in meta['orbit_sizes']:
        dim_lb_dist[orb['dim']][orb['lb']] += orb['orbit_size']
    
    print("=== LB distribution by dimension (from certificate orbits) ===")
    for d in sorted(dim_lb_dist.keys()):
        total = sum(dim_lb_dist[d].values())
        print(f"  dim {d} ({total} subspaces): {dict(sorted(dim_lb_dist[d].items()))}")
    
    # --- DIM 8: verify matrix rank exactness ---
    print("\n=== Dim 8: codim-1 subspaces (single 9x9 matrix) ===")
    dim8_stats = {"exact": 0, "loose": 0, "overclaim": 0, "total": 0}
    dim8_loose_examples = []
    
    for key, entry in lut.items():
        basis = unpack_basis_local(key)
        if len(basis) != 8:
            continue
        dim8_stats["total"] += 1
        lb = entry if isinstance(entry, int) else entry.get('lb', entry)
        Q, q_dim = build_quotient_tensor(T, basis)
        assert q_dim == 1, f"Expected q_dim=1, got {q_dim}"
        # Single matrix: Q[1] is the nonzero slice (Q[0] is zero)
        true_rank = gf2_rank(Q[1])
        if lb == true_rank:
            dim8_stats["exact"] += 1
        elif lb < true_rank:
            dim8_stats["loose"] += 1
            dim8_loose_examples.append({"key": str(key), "lb": lb, "true_rank": true_rank})
        else:
            dim8_stats["overclaim"] += 1
    
    print(f"  Total: {dim8_stats['total']}, Exact: {dim8_stats['exact']}, "
          f"Loose: {dim8_stats['loose']}, Overclaim: {dim8_stats['overclaim']}")
    if dim8_loose_examples:
        print(f"  LOOSE EXAMPLES: {dim8_loose_examples[:5]}")
    
    # --- DIM 7: pencil rank check ---
    print("\n=== Dim 7: codim-2 subspaces (matrix pencil, 2×9×9) ===")
    dim7_stats = {"exact": 0, "loose": 0, "overclaim": 0, "total": 0}
    dim7_loose_examples = []
    dim7_lb_vs_pencil = Counter()
    
    for key, entry in lut.items():
        basis = unpack_basis_local(key)
        if len(basis) != 7:
            continue
        dim7_stats["total"] += 1
        lb = entry if isinstance(entry, int) else entry.get('lb', entry)
        Q, q_dim = build_quotient_tensor(T, basis)
        assert q_dim == 2, f"Expected q_dim=2, got {q_dim}"
        
        # Pencil: check all 3 nonzero combinations
        pencil_lb = 0
        for alpha in range(1, 4):  # 1,2,3 are nonzero in F2^2
            M = np.zeros((9, 9), dtype=np.int32)
            for bit in range(2):
                if (alpha >> bit) & 1:
                    M = (M + Q[1 << bit]) % 2
            pencil_lb = max(pencil_lb, gf2_rank(M))
        
        # Also check (12,3) flattening: stack slices vertically
        flat = np.vstack([Q[1], Q[2], Q[3]]) % 2  # 27 x 9
        flat_rank = gf2_rank(flat)
        pencil_lb = max(pencil_lb, flat_rank)
        
        dim7_lb_vs_pencil[(lb, pencil_lb)] += 1
        
        if lb < pencil_lb:
            dim7_stats["loose"] += 1
            if len(dim7_loose_examples) < 20:
                dim7_loose_examples.append({
                    "key": str(key), "lut_lb": lb, "pencil_lb": pencil_lb,
                    "slice_ranks": [gf2_rank(Q[alpha]) for alpha in range(4)]
                })
        elif lb == pencil_lb:
            dim7_stats["exact"] += 1
        else:
            # LUT LB exceeds our pencil bound — LUT uses deeper recursion
            dim7_stats["overclaim"] += 1  # actually not overclaim, just deeper
    
    print(f"  Total: {dim7_stats['total']}")
    print(f"  LUT LB == pencil max-slice/flat rank: {dim7_stats['exact']}")
    print(f"  LUT LB < pencil bound (LOOSE LUT): {dim7_stats['loose']}")
    print(f"  LUT LB > pencil bound (deeper recursion): {dim7_stats['overclaim']}")
    print(f"  (lb, pencil_lb) distribution: {dict(sorted(dim7_lb_vs_pencil.items()))}")
    if dim7_loose_examples:
        print(f"  LOOSE EXAMPLES: {json.dumps(dim7_loose_examples[:5], indent=2)}")
    
    # --- Dim-7 potential tightening ---
    # For nodes where LUT LB matches the flatten bound, check whether
    # Kronecker/pencil theory gives anything tighter
    print("\n=== Dim 7 nodes where LUT uses flatten ===")
    dim7_flatten_nodes = [orb for orb in meta['orbit_sizes'] if orb['dim'] == 7 and orb['proof_type'] == 'flatten']
    for orb in dim7_flatten_nodes:
        print(f"  index {orb['index']}: lb={orb['lb']}, size={orb['orbit_size']}")
    
    # --- A-rank distribution over F2^9 for flattening cut ---
    print("\n=== A-rank distribution for flattening cut ===")
    rank_hist = Counter()
    for a in range(512):
        m = np.zeros((3, 3), dtype=np.int32)
        for i in range(3):
            for j in range(3):
                m[i, j] = (a >> (3*i + j)) & 1
        r = gf2_rank(m)
        rank_hist[r] += 1
    print(f"  Rank distribution of 3x3 F2 matrices: {dict(sorted(rank_hist.items()))}")
    # rank 0: 1, rank 1: 49, rank 2: 294, rank 3: 168 = 512 total
    
    # The flattening cut says: sum_a rank(a)*x_a >= 27
    # At n=20 with x_p=1 (pivot of rank 2 or 3):
    # sum_{a != p} rank(a)*x_a >= 27 - rank(p)
    # For pivot 17 (rank 2): remaining 19 terms need sum >= 25
    #   If all 19 are rank-1: sum = 19 < 25. Need at least 6 rank-2 terms
    #   More precisely: if k terms have rank>=2, then sum >= 19-k + 2k = 19+k >= 25 => k >= 6
    #   Wait: rank-1 contributes 1, rank-2 contributes 2, rank-3 contributes 3
    #   With 19 terms: sum = sum(rank(a_t)) for t != pivot
    #   If r2 terms have rank 2 and r3 have rank 3: sum = (19-r2-r3) + 2*r2 + 3*r3 = 19 + r2 + 2*r3
    #   Need 19 + r2 + 2*r3 >= 25, so r2 + 2*r3 >= 6
    # For pivot 273 (rank 3): remaining 19 terms need sum >= 24
    #   19 + r2 + 2*r3 >= 24, so r2 + 2*r3 >= 5
    
    for pivot, rank_p, name in [(17, 2, "rank-2"), (273, 3, "rank-3")]:
        remaining = 27 - rank_p
        print(f"\n  Pivot {pivot} ({name}): remaining sum >= {remaining} from 19 terms")
        print(f"    Need r2 + 2*r3 >= {remaining - 19}")
        print(f"    Minimum higher-rank terms: {remaining - 19} (all rank-2) to {(remaining-19+1)//2} (all rank-3)")
    
    elapsed = time.time() - t0
    
    result = {
        "dim_lb_dist": {str(d): dict(dim_lb_dist[d]) for d in sorted(dim_lb_dist.keys())},
        "dim8": dim8_stats,
        "dim8_loose": dim8_loose_examples,
        "dim7": dim7_stats,
        "dim7_loose": dim7_loose_examples,
        "dim7_lb_vs_pencil": {str(k): v for k, v in sorted(dim7_lb_vs_pencil.items())},
        "a_rank_dist": dict(sorted(rank_hist.items())),
        "flattening_cut": {
            "full_sum_bound": 27,
            "pivot17_remaining": 25,
            "pivot273_remaining": 24,
        },
        "elapsed_sec": round(elapsed, 2),
    }
    
    out = OUTDIR / "dim78_exactness_check.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"\nSaved {out}")
    print(f"Elapsed: {elapsed:.1f}s")

if __name__ == "__main__":
    main()
