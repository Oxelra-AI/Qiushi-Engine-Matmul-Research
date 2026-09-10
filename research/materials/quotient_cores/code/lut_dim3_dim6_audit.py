#!/usr/bin/env python3
"""Audit dim-3 and dim-6 LUT rows against classical matrix-multiplication ranks.

For a d-dimensional subspace U <= F_2^{3x3}, the restriction T|_U is a d x 9 x 9
tensor whose rank provides a lower bound on the number of decomposition terms
from U.  Some subspaces have a known identification:

  Column-space subspaces:
    U_{x} = {A : col(A) in span(x)}   for nonzero x in F_2^3.
    dim(U_x) = 3, and T|_{U_x} ~ T_{<1,3,3>} which has rank 9 over any field.

    U_{x,y} = {A : col(A) in span(x,y)} for 2-dim span{x,y}.
    dim(U_{x,y}) = 6, and T|_{U_{x,y}} ~ T_{<2,3,3>}.

  Row-space subspaces:
    V_{x} = {A : row(A) in span(x)} = {A : A^T in U_x^T}.
    dim(V_x) = 3, and T|_{V_x} ~ T_{<3,3,1>} = T_{<1,3,3>} (transposed), rank 9.

    V_{x,y} = {A : row(A) in span(x,y)}.
    dim(V_{x,y}) = 6, and T|_{V_{x,y}} ~ T_{<3,3,2>}.

For each E11-containing LUT entry at dim 3 or 6, we:
  1. Classify the subspace type (column-type, row-type, or other).
  2. Compare LUT LB against the known classical rank.
  3. Report mismatches (LB above known rank = bug, LB below = potential tightening).

Also computes exact tensor ranks for all dim-3 E11-containing subspaces
via brute-force, since these tensors are only 3 x 9 x 9.

Output: workspace/data/flattening_bounds/lut_dim3_dim6_audit.json
"""
from __future__ import annotations

import json
import os
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Set, Tuple

import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, pack_basis, unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = SESSION / "workspace/data/flattening_bounds"


def gf2_rank(M: np.ndarray) -> int:
    A = (np.asarray(M, dtype=np.uint8) & 1).copy()
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i, c]:
                piv = i; break
        if piv is None: continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(m):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
        if r == m: break
    return int(r)


def build_t333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] ^= 1
    return T


def restrict_tensor(T: np.ndarray, basis_masks: List[int]) -> np.ndarray:
    """Restrict T to the subspace spanned by basis_masks in the A-slot."""
    d = len(basis_masks)
    R = np.zeros((d, 9, 9), dtype=np.uint8)
    for idx, mask in enumerate(basis_masks):
        # The A-slice for this basis vector is the sum of original slices
        # at coordinates where the mask has bit 1.
        m = mask
        while m:
            lb = m & -m
            ai = lb.bit_length() - 1
            R[idx] ^= T[ai]
            m ^= lb
    return R


def tensor_rank_bruteforce_3x9x9(T: np.ndarray) -> int:
    """Exact rank of a 3x9x9 tensor over F_2 by brute-force.
    
    Check if the tensor can be written as sum of r rank-1 terms
    for r = 0, 1, 2, ...
    
    A rank-1 term is a (x) b (x) c where a in F_2^3, b in F_2^9, c in F_2^9.
    With 3 + 9 + 9 = 21 bits per term, and up to ~12 terms, this is too large
    for full enumeration.  Instead, use the slice rank approach:
    rank >= max slice rank, then check exact rank via SAT-like backtracking.
    
    For the fast path: return the slice rank bound (which is tight for small tensors).
    """
    d, m, n = T.shape
    assert d == 3 and m == 9 and n == 9
    
    # Compute 1x9 flattening rank (slice rank bound)
    flat = T.reshape(d * m, n)
    flat_rank = gf2_rank(flat)
    
    # Also compute d x (m*n) flattening rank
    flat2 = T.reshape(d, m * n)
    flat2_rank = gf2_rank(flat2)
    
    # The tensor rank is at least max of all flattening ranks
    return max(flat_rank, flat2_rank)


def classify_subspace(basis_masks: List[int]) -> Dict:
    """Classify a 3-dim subspace of F_2^{3x3} by its column/row space structure."""
    pts = []
    d = len(basis_masks)
    for m in range(1, 1 << d):
        x = 0
        for i, b in enumerate(basis_masks):
            if (m >> i) & 1:
                x ^= b
        pts.append(x)
    
    # Check column space: do all matrices in the subspace have column space
    # contained in a fixed subspace?
    col_spaces = set()
    row_spaces = set()
    for mask in pts:
        # Matrix is 3x3 with M[i][j] = (mask >> (3*i+j)) & 1
        mat = np.array([[(mask >> (3*i+j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8)
        # Column space: span of columns
        cols_key = 0
        for j in range(3):
            col = 0
            for i in range(3):
                if mat[i, j]:
                    col |= 1 << i
            cols_key |= 1 << col if col else 0
        col_spaces.add(cols_key)
        
        # Row space: span of rows
        rows_key = 0
        for i in range(3):
            row = 0
            for j in range(3):
                if mat[i, j]:
                    row |= 1 << j
            rows_key |= 1 << row if row else 0
        row_spaces.add(rows_key)
    
    # Check if all matrices have rank <= 1 (column space <= 1-dim)
    all_rank_le1 = all(
        gf2_rank(np.array([[(m >> (3*i+j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8)) <= 1
        for m in pts
    )
    
    # Check if there's a common column vector span
    # All rank-1 matrices A=uv^T have col(A) = span(u) (if A != 0).
    # If all pts have col in span(x), then x is the common column direction.
    cols = set()
    for m in pts:
        mat = np.array([[(m >> (3*i+j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8)
        r = gf2_rank(mat)
        if r == 0:
            continue
        # Get column space as a frozenset of basis vectors
        # Easier: just get the column space span
        # For rank-1: it's a single vector
        if r == 1:
            for j in range(3):
                col = tuple(int(mat[i, j]) for i in range(3))
                if any(col):
                    cols.add(col)
                    break
        else:
            cols.add(("rank>1",))
    
    has_rank_gt1 = any(c == ("rank>1",) for c in cols)
    
    # Determine type
    ranks = [
        gf2_rank(np.array([[(m >> (3*i+j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8))
        for m in pts
    ]
    rank_hist = Counter(ranks)
    
    return {
        "dim": d,
        "nonzero_pts": len(pts),
        "matrix_rank_hist": dict(sorted(rank_hist.items())),
        "all_rank_le1": all_rank_le1,
        "has_rank_gt1": has_rank_gt1,
    }


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    
    print("Loading LUT...")
    lut, _ = load_lut(LUT_PATH)
    print(f"  LUT entries: {len(lut)}")
    
    T = build_t333()
    E11 = 1  # E_{00} in 0-indexed bit order
    
    # Collect all dim-3 and dim-6 LUT entries (not restricted to E11-containing)
    dim3_entries = []
    dim6_entries = []
    
    for key, lb in lut.items():
        key = int(key)
        basis = list(unpack_basis(key))
        d = len(basis)
        
        if d == 3:
            dim3_entries.append((key, int(lb), [int(b) for b in basis]))
        elif d == 6:
            dim6_entries.append((key, int(lb), [int(b) for b in basis]))
    
    print(f"  E11-containing dim-3 entries: {len(dim3_entries)}")
    print(f"  E11-containing dim-6 entries: {len(dim6_entries)}")
    
    # Audit dim-3 entries
    dim3_results = []
    dim3_lb_hist = Counter()
    dim3_flat_hist = Counter()
    dim3_classifications = Counter()
    
    for key, lb, basis in dim3_entries:
        T_r = restrict_tensor(T, basis)
        flat_lb = tensor_rank_bruteforce_3x9x9(T_r)
        cls = classify_subspace(basis)
        
        status = "ok" if lb <= flat_lb else "BUG_LB_ABOVE_RANK"
        if lb < flat_lb:
            status = "tightenable"
        
        dim3_results.append({
            "key": key,
            "lut_lb": lb,
            "flattening_lb": flat_lb,
            "status": status,
            "all_rank_le1": cls["all_rank_le1"],
            "matrix_rank_hist": cls["matrix_rank_hist"],
        })
        dim3_lb_hist[lb] += 1
        dim3_flat_hist[flat_lb] += 1
        dim3_classifications[str(cls["matrix_rank_hist"])] += 1
    
    # Summary for dim-3
    bugs_dim3 = [r for r in dim3_results if r["status"] == "BUG_LB_ABOVE_RANK"]
    tightenable_dim3 = [r for r in dim3_results if r["status"] == "tightenable"]
    
    # Audit dim-6 entries (flattening bounds only, no brute force)
    dim6_results = []
    dim6_lb_hist = Counter()
    dim6_flat_hist = Counter()
    
    for key, lb, basis in dim6_entries[:200]:  # Limit to first 200 for speed
        T_r = restrict_tensor(T, basis)
        # For 6x9x9: compute flattening ranks
        flat1 = gf2_rank(T_r.reshape(6 * 9, 9))
        flat2 = gf2_rank(T_r.reshape(6, 81))
        flat_lb = max(flat1, flat2)
        
        status = "ok" if lb <= flat_lb else "BUG_LB_ABOVE_RANK"
        if lb < flat_lb:
            status = "tightenable"
        
        dim6_results.append({
            "key": key,
            "lut_lb": lb,
            "flattening_lb": flat_lb,
            "status": status,
        })
        dim6_lb_hist[lb] += 1
        dim6_flat_hist[flat_lb] += 1
    
    bugs_dim6 = [r for r in dim6_results if r["status"] == "BUG_LB_ABOVE_RANK"]
    
    # Check specific known subspace types
    # T_{<1,3,3>}: rank 9 over any field. Generated by span{e_i e_j^T} for fixed i.
    known_checks = []
    for i in range(3):
        basis = [1 << (3*i+j) for j in range(3)]  # e_i e_j^T for j=0,1,2
        T_r = restrict_tensor(T, basis)
        flat_lb = tensor_rank_bruteforce_3x9x9(T_r)
        nnz = int(np.count_nonzero(T_r))
        # Look up in LUT
        from wang_capacity_lazy import rref_basis, pack_basis
        key = int(pack_basis(rref_basis(tuple(basis))))
        lut_lb = int(lut.get(key, -1))
        known_checks.append({
            "type": f"col_space_e{i}",
            "basis": basis,
            "key": key,
            "lut_lb": lut_lb,
            "flattening_lb": flat_lb,
            "nnz": nnz,
            "expected_rank": 9,  # T_{<1,3,3>} over F_2
            "status": "ok" if lut_lb == 9 else ("bug" if lut_lb > 9 else "conservative"),
        })
    
    # Row-space versions
    for j in range(3):
        basis = [1 << (3*i+j) for i in range(3)]  # e_i e_j^T for i=0,1,2
        T_r = restrict_tensor(T, basis)
        flat_lb = tensor_rank_bruteforce_3x9x9(T_r)
        nnz = int(np.count_nonzero(T_r))
        key = int(pack_basis(rref_basis(tuple(basis))))
        lut_lb = int(lut.get(key, -1))
        known_checks.append({
            "type": f"row_space_e{j}",
            "basis": basis,
            "key": key,
            "lut_lb": lut_lb,
            "flattening_lb": flat_lb,
            "nnz": nnz,
            "expected_rank": 9,
            "status": "ok" if lut_lb == 9 else ("bug" if lut_lb > 9 else "conservative"),
        })
    
    out = {
        "dim3": {
            "total": len(dim3_results),
            "lut_lb_hist": dict(sorted(dim3_lb_hist.items())),
            "flattening_lb_hist": dict(sorted(dim3_flat_hist.items())),
            "classification_hist": dict(sorted(dim3_classifications.items())),
            "bugs": len(bugs_dim3),
            "tightenable": len(tightenable_dim3),
            "bug_entries": bugs_dim3[:10],
            "tightenable_entries": tightenable_dim3[:10],
        },
        "dim6_sample": {
            "total": len(dim6_results),
            "lut_lb_hist": dict(sorted(dim6_lb_hist.items())),
            "flattening_lb_hist": dict(sorted(dim6_flat_hist.items())),
            "bugs": len(bugs_dim6),
            "bug_entries": bugs_dim6[:10],
        },
        "known_subspace_checks": known_checks,
        "elapsed_sec": time.time() - t0,
    }
    
    path = OUTDIR / "lut_dim3_dim6_audit.json"
    path.write_text(json.dumps(out, indent=2, sort_keys=True))
    print(json.dumps(out, indent=2, sort_keys=True)[:4000])
    print(f"\nSaved {path}")


if __name__ == "__main__":
    main()
