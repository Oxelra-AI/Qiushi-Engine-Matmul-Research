#!/usr/bin/env python3
"""Analyze Wang LUT by dimension: check whether dim 7-8 values are exact,
identify loose values, and compute the sensitivity of the pivot-fixed n=20
model to cap improvements at each dimension level.

At dim 8 (codim 1), T/W is a single 3x3 matrix over F2 and its rank is exact.
At dim 7 (codim 2), T/W is a matrix pencil of 3x3 matrices and its rank is 
exactly computable.
At dim 6 (codim 3), T/W is a 3x9x9 tensor with small orbit structure.

If any recorded LUT value is below the true quotient rank, tightening it
cascades upward through every ancestor row.
"""
from __future__ import annotations
import json, os, pickle, sys, time
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import unpack_basis  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = SESSION / "workspace/data/wang_analysis"
OUTDIR.mkdir(parents=True, exist_ok=True)

# --- GF(2) tensor and rank tools ---

def gf2_mat(a_int):
    """3x3 GF(2) matrix from 9-bit int (row-major)."""
    m = np.zeros((3, 3), dtype=np.int32)
    for i in range(3):
        for j in range(3):
            m[i, j] = (a_int >> (3*i + j)) & 1
    return m

def gf2_rank(m):
    """Rank of a matrix over GF(2)."""
    m = m.copy() % 2
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
    """Build T_{3,3,3} over F2 as 9x9x9 binary array."""
    T = np.zeros((9, 9, 9), dtype=np.int32)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T

def quotient_tensor(T, basis_ints):
    """Compute quotient tensor T / span(basis).
    
    For a subspace W with basis vectors b1,...,bd (as 9-bit ints),
    T/W is a tensor in F2^{(9-d) x 9 x 9} obtained by projecting
    the A-space by W.
    
    Returns: (Q, proj_map) where Q is the quotient tensor and
    proj_map maps original A-indices to quotient indices.
    """
    # Build quotient projection for A-space (F2^9 -> F2^{9-d})
    d = len(basis_ints)
    q_dim = 9 - d
    
    # RREF the basis
    basis = [int(b) for b in basis_ints]
    rref = []
    pivot_bits = []
    for b in basis:
        v = b
        for pb, rb in zip(pivot_bits, rref):
            if (v >> pb) & 1:
                v ^= rb
        if v == 0:
            continue
        p = v.bit_length() - 1
        # reduce existing by new
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
    # Non-pivot bits define quotient coordinates
    free_bits = [i for i in range(9) if i not in pivot_set]
    assert len(free_bits) == q_dim
    
    def project_a(a):
        """Project a 9-bit A-vector to quotient."""
        # First reduce modulo the basis
        v = a
        for pb, rb in zip(pivot_bits, rref):
            if (v >> pb) & 1:
                v ^= rb
        # Now v has zero in all pivot positions; read off free bits
        q = 0
        for qi, fi in enumerate(free_bits):
            if (v >> fi) & 1:
                q |= (1 << qi)
        return q
    
    Q = np.zeros((1 << q_dim, 9, 9), dtype=np.int32)
    for a in range(9 if d < 9 else 0):  # skip if quotient is trivial
        pass
    
    # Build quotient tensor by summing original slices
    for a_orig in range(512):
        qa = project_a(a_orig)
        Q[qa] = (Q[qa] + T[a_orig]) % 2
    
    return Q, project_a, free_bits

def tensor_rank_upper(Q):
    """Rough upper bound on tensor rank by slice rank sum."""
    total = 0
    for s in range(Q.shape[0]):
        total += gf2_rank(Q[s])
    return total

def exact_matrix_rank_as_tensor(Q):
    """If Q is 1 x 9 x 9, return rank of the single matrix."""
    if Q.shape[0] != 1:
        return None
    return gf2_rank(Q[0])

def pencil_rank_bounds(Q):
    """For 2-slice pencil Q (dim 2 x 9 x 9), compute bounds."""
    if Q.shape[0] < 2:
        return None
    # Individual slice ranks
    r0 = gf2_rank(Q[0])
    r1 = gf2_rank(Q[1])
    # Lower bound: max slice rank
    lb = max(r0, r1)
    # Check all linear combinations (only 3 nonzero for F2^2)
    for a in range(1, Q.shape[0]):
        M = Q[a].copy()
        rr = gf2_rank(M)
        lb = max(lb, rr)
    
    # For 2-slice: check XOR combination too
    if Q.shape[0] == 2:
        M_xor = (Q[0] + Q[1]) % 2
        lb = max(lb, gf2_rank(M_xor))
    
    # Upper bound: sum of slice ranks
    ub = sum(gf2_rank(Q[i]) for i in range(Q.shape[0]))
    
    return {"lb": lb, "ub": ub, "slice_ranks": [gf2_rank(Q[i]) for i in range(Q.shape[0])]}

def main():
    t0 = time.time()
    
    # Load LUT
    with open(LUT_PATH, "rb") as f:
        lut = pickle.load(f)
    
    T = full_tensor()
    
    # Analyze LB distribution by dimension
    dim_lb_hist = defaultdict(lambda: Counter())
    dim_count = Counter()
    
    for key, entry in lut.items():
        basis = list(unpack_basis(int(key)))
        dim = len(basis)
        lb = entry["lb"]
        dim_lb_hist[dim][lb] += 1
        dim_count[dim] += 1
    
    print("=== LUT LB distribution by dimension ===")
    for d in sorted(dim_lb_hist.keys()):
        print(f"  dim {d} ({dim_count[d]} subspaces):")
        for lb in sorted(dim_lb_hist[d].keys()):
            print(f"    LB={lb}: {dim_lb_hist[d][lb]}")
    
    # --- DIM 8: codim-1 subspaces, quotient is a single 3x3 matrix ---
    print("\n=== Dim 8 analysis: quotient = single 3x3 matrix ===")
    dim8_loose = []
    dim8_exact = 0
    dim8_total = 0
    for key, entry in lut.items():
        basis = list(unpack_basis(int(key)))
        if len(basis) != 8:
            continue
        dim8_total += 1
        lb = entry["lb"]
        Q, _, _ = quotient_tensor(T, basis)
        true_rank = gf2_rank(Q[0])  # 1-dim quotient: single matrix
        if lb < true_rank:
            dim8_loose.append({"key": int(key), "lut_lb": lb, "true_rank": true_rank})
        elif lb == true_rank:
            dim8_exact += 1
        else:
            # LB > true rank would be a certificate bug
            dim8_loose.append({"key": int(key), "lut_lb": lb, "true_rank": true_rank, "ERROR": "LB > true rank"})
    
    print(f"  Total dim-8 subspaces: {dim8_total}")
    print(f"  Exact (LB == true rank): {dim8_exact}")
    print(f"  Loose (LB < true rank): {len(dim8_loose)}")
    if dim8_loose:
        for x in dim8_loose[:10]:
            print(f"    key={x['key']}: LB={x['lut_lb']}, true_rank={x['true_rank']}")
    
    # --- DIM 7: codim-2 subspaces, quotient is a matrix pencil ---
    print("\n=== Dim 7 analysis: quotient = matrix pencil ===")
    dim7_loose = []
    dim7_exact = 0
    dim7_total = 0
    dim7_improved = 0
    for key, entry in lut.items():
        basis = list(unpack_basis(int(key)))
        if len(basis) != 7:
            continue
        dim7_total += 1
        lb = entry["lb"]
        Q, _, _ = quotient_tensor(T, basis)
        # For 2-dim quotient: check all 3 nonzero combinations
        bounds = pencil_rank_bounds(Q)
        pencil_lb = bounds["lb"]
        if lb < pencil_lb:
            dim7_loose.append({"key": int(key), "lut_lb": lb, "pencil_lb": pencil_lb,
                             "slice_ranks": bounds["slice_ranks"]})
            dim7_improved += 1
        elif lb == pencil_lb:
            dim7_exact += 1
    
    print(f"  Total dim-7 subspaces: {dim7_total}")
    print(f"  Exact (LB == pencil LB): {dim7_exact}")
    print(f"  Loose (LB < pencil LB): {len(dim7_loose)}")
    if dim7_loose:
        for x in dim7_loose[:10]:
            print(f"    key={x['key']}: LB={x['lut_lb']}, pencil_lb={x['pencil_lb']}, slices={x['slice_ranks']}")
    
    # --- DIM 9 (trivial: the zero subspace = full tensor) ---
    print("\n=== Dim 9 (root): full tensor ===")
    for key, entry in lut.items():
        basis = list(unpack_basis(int(key)))
        if len(basis) == 9:
            print(f"  LB = {entry['lb']}")
    
    # --- Dim 0 (trivial: just a point) ---
    for key, entry in lut.items():
        basis = list(unpack_basis(int(key)))
        if len(basis) == 0:
            print(f"\n=== Dim 0 (empty subspace): LB = {entry['lb']} ===")
    
    elapsed = time.time() - t0
    
    result = {
        "dim_lb_hist": {str(d): dict(dim_lb_hist[d]) for d in sorted(dim_lb_hist.keys())},
        "dim8": {
            "total": dim8_total,
            "exact": dim8_exact, 
            "loose_count": len(dim8_loose),
            "loose_head": dim8_loose[:20],
        },
        "dim7": {
            "total": dim7_total,
            "exact": dim7_exact,
            "loose_count": len(dim7_loose),
            "improved": dim7_improved,
            "loose_head": dim7_loose[:20],
        },
        "elapsed_sec": round(elapsed, 2),
    }
    
    out = OUTDIR / "lut_dim_analysis.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"\nSaved {out}")
    print(f"Elapsed: {elapsed:.1f}s")

if __name__ == "__main__":
    main()
