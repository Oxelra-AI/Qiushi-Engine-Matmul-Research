#!/usr/bin/env python3
r"""analysis (part 3): Verify N^2 behavior for all rank types with a rank-9 contraction.

For types where one contraction is rank 9 (invertible), we normalize:
  N = M_9^{-1} M_r,  where r is another contraction's rank.
  N = H_0 \otimes I_3,  H_0 = Q_9^{-1} Q_r.

We check:
  - H_0^2: nilpotent (=0) or idempotent (=H_0) or other
  - rank(I + H_0): determines whether H_0 is nilpotent vs idempotent
  - The pencil theorem only applies when N^2 = 0 (nilpotent)
"""
import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np

WDIR = Path("research/research_record/workspace")
SCRIPTS = WDIR / "scripts"
ODIR = WDIR / "data" / "pencil_wang_comparison"
ODIR.mkdir(parents=True, exist_ok=True)

if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))


def gf2_rank(M):
    A = np.array(M, dtype=np.uint8) % 2
    m, n = A.shape
    r = 0
    for col in range(n):
        piv = None
        for row in range(r, m):
            if A[row, col]:
                piv = row
                break
        if piv is None:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for row in range(m):
            if row != r and A[row, col]:
                A[row] ^= A[r]
        r += 1
    return r


def gf2_mat_mul(A, B):
    return np.array(A @ B % 2, dtype=np.uint8)


def gf2_inverse(M):
    n = M.shape[0]
    aug = np.hstack([M.copy(), np.eye(n, dtype=np.uint8)])
    for col in range(n):
        piv = None
        for row in range(col, n):
            if aug[row, col]:
                piv = row
                break
        assert piv is not None
        if piv != col:
            aug[[col, piv]] = aug[[piv, col]]
        for row in range(n):
            if row != col and aug[row, col]:
                aug[row] ^= aug[col]
    return aug[:, n:]


def build_e11_core():
    T = np.zeros((8, 9, 9), dtype=np.uint8)
    idx = 0
    for i in range(3):
        for j in range(3):
            if i == 0 and j == 0:
                continue
            for k in range(3):
                T[idx, 3*j+k, 3*i+k] = 1
            idx += 1
    return T


def contraction_matrix(T, q):
    na = T.shape[0]
    M = np.zeros((T.shape[1], T.shape[2]), dtype=np.uint8)
    for j in range(na):
        if (q >> j) & 1:
            M = (M + T[j]) % 2
    return M


def classify_N2(N):
    """Classify N^2: 'nilpotent' if N^2=0, 'idempotent' if N^2=N, else 'other'."""
    N2 = gf2_mat_mul(N, N)
    if np.all(N2 == 0):
        return 'nilpotent'
    if np.all(N2 == N):
        return 'idempotent'
    return 'other'


def main():
    t0 = time.time()
    T = build_e11_core()
    
    crank = {}
    cmat = {}
    for q in range(1, 256):
        M = contraction_matrix(T, q)
        crank[q] = gf2_rank(M)
        cmat[q] = M
    
    # Enumerate all dual lines
    lines = []
    seen = set()
    for q1 in range(1, 256):
        for q2 in range(q1+1, 256):
            q3 = q1 ^ q2
            if q3 == 0 or q3 <= q1:
                continue
            key = tuple(sorted([q1, q2, q3]))
            if key in seen:
                continue
            seen.add(key)
            lines.append((q1, q2, q3))
    
    # For each line with at least one rank-9 contraction, classify N^2
    type_n2 = defaultdict(lambda: Counter())
    
    for q1, q2, q3 in lines:
        r1, r2, r3 = crank[q1], crank[q2], crank[q3]
        rtype = tuple(sorted([r1, r2, r3]))
        
        # Check all rank-9 contractions as normalizers
        for q_inv, q_other in [(q1, q2), (q2, q1), (q1, q3), (q3, q1), (q2, q3), (q3, q2)]:
            if crank[q_inv] != 9:
                continue
            r_other = crank[q_other]
            
            M_inv = cmat[q_inv]
            M_other = cmat[q_other]
            M_inv_inv = gf2_inverse(M_inv)
            N = gf2_mat_mul(M_inv_inv, M_other)
            
            label = classify_N2(N)
            pair_key = f"r={r_other}_via_r9"
            type_n2[rtype][f"{pair_key}_{label}"] += 1
    
    print(f"{'Rank Type':>12s}  N^2 classifications (normalizing by rank-9)")
    print("-" * 80)
    for rtype in sorted(type_n2.keys()):
        counts = type_n2[rtype]
        parts = []
        for k in sorted(counts.keys()):
            parts.append(f"{k}: {counts[k]}")
        print(f"{str(rtype):>12s}  {', '.join(parts)}")
    
    # Focused analysis: for types with rank-9, what fraction have N^2=0?
    print("\n=== Pencil applicability by type ===")
    print(f"{'Type':>12s}  {'N²=0':>6s}  {'N²=N':>6s}  {'other':>6s}  {'Pencil theorem applies':>24s}")
    print("-" * 70)
    
    applicability = {}
    for rtype in sorted(type_n2.keys()):
        counts = type_n2[rtype]
        n2_zero = sum(v for k, v in counts.items() if 'nilpotent' in k)
        n2_self = sum(v for k, v in counts.items() if 'idempotent' in k)
        n2_other = sum(v for k, v in counts.items() if 'other' in k)
        total = n2_zero + n2_self + n2_other
        
        if total == 0:
            applies = "NO rank-9 contraction"
        elif n2_zero == total:
            applies = "ALL lines (N²=0)"
        elif n2_zero == 0:
            applies = "NO lines"
        else:
            applies = f"{n2_zero}/{total} lines"
        
        applicability[str(rtype)] = {
            'nilpotent_count': n2_zero,
            'idempotent_count': n2_self,
            'other_count': n2_other,
            'total_normalizations': total,
            'pencil_applies': applies,
        }
        
        print(f"{str(rtype):>12s}  {n2_zero:6d}  {n2_self:6d}  {n2_other:6d}  {applies:>24s}")
    
    # Types without rank-9 contraction
    non_inv_types = set()
    for q1, q2, q3 in lines:
        rtype = tuple(sorted([crank[q1], crank[q2], crank[q3]]))
        if 9 not in rtype:
            non_inv_types.add(rtype)
    
    print(f"\nTypes with NO rank-9 contraction (pencil normalization unavailable):")
    for rt in sorted(non_inv_types):
        count = sum(1 for q1, q2, q3 in lines
                    if tuple(sorted([crank[q1], crank[q2], crank[q3]])) == rt)
        print(f"  {rt}: {count} lines")
    
    results = {
        'applicability': applicability,
        'non_invertible_types': {str(rt): 'no rank-9 normalization' for rt in non_inv_types},
        'elapsed_sec': time.time() - t0,
    }
    
    out = ODIR / "n2_classification.json"
    with open(out, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nSaved: {out}")
    print(f"Elapsed: {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
