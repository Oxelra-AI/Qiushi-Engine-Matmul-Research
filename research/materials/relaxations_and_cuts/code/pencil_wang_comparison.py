#!/usr/bin/env python3
r"""analysis: Algebraic pencil proof for (3,9,9) lines and Wang comparison.

THEOREM (Nilpotent-Idempotent Rank Bound):
  Let N, W be n×n matrices over F_2 with N^2 = 0 and W^2 = W. Then
    rank(N + W) >= rank(N).

PROOF:
  W maps ker(N+W) into ker(N) \cap im(W), with kernel
  ker(W) \cap ker(N+W) \subseteq ker(W) \cap ker(N).
  Since W is idempotent, ker(W) \cap im(W) = {0}, so
    ker(W) \cap ker(N)  and  im(W) \cap ker(N)
  are disjoint subspaces of ker(N).
  Therefore dim ker(N+W) <= dim ker(N), i.e. rank(N+W) >= rank(N).  QED

APPLICATION to (3,9,9) pencil lines:
  For a dual line D = span(q_1, q_2) with contraction ranks (3, 9, 9),
  normalize by the invertible contraction M_2 = L(q_2):
    N = M_2^{-1} M_1,   W = M_2^{-1} Z,   Z = X_{11}.
  The Kronecker structure gives N = H_0 \otimes I_3 with rank(H_0) = 1
  and I_3 + H_0 invertible (rank 3).  Over F_2 this forces H_0^2 = 0,
  hence N^2 = 0.  When c_{11} + c_{01} <= 9, the rank constraints
  force W to be idempotent, so rank(N+W) >= 3 > c_{10} = 2.
  Budget (2, 7, 2) is therefore pencil-infeasible.

This script then compares against the Wang occupation table:
  For D^\perp (6D core subspace), L(D^\perp) from the Wang LUT
  gives  c_{00} <= 19 - L.   When w(q_2) = 9 (tight), the Wang bound
  alone gives c_{10} >= L - 9.  If L >= 12, Wang already implies c_{10} >= 3.
"""
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

WDIR = Path("research/research_record/workspace")
SCRIPTS = WDIR / "scripts"
ODIR = WDIR / "data" / "pencil_wang_comparison"
ODIR.mkdir(parents=True, exist_ok=True)

if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from wang_capacity_lazy import (
    rref_basis,
    pack_basis,
    unpack_basis,
    in_rowspace,
    subspace_points_from_basis,
)
from core_capacity_from_wang_lut import CoreQuotient, load_lut

# ---- GF(2) utilities ----

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

# ---- Core tensor ----

def build_e11_core():
    T = np.zeros((8, 9, 9), dtype=np.uint8)
    # 8 core A-slices: positions (i,j) != (0,0), ordered (0,1),(0,2),(1,0),...,(2,2)
    idx = 0
    for i in range(3):
        for j in range(3):
            if i == 0 and j == 0:
                continue
            for k in range(3):
                b = 3*j + k
                c = 3*i + k
                T[idx, b, c] = 1
            idx += 1
    return T

def contraction_matrix(T, q):
    na = T.shape[0]
    M = np.zeros((T.shape[1], T.shape[2]), dtype=np.uint8)
    for j in range(na):
        if (q >> j) & 1:
            M = (M + T[j]) % 2
    return M

def gf2_inner(a, b):
    return bin(a & b).count('1') % 2

# ---- Main ----

def main():
    t0 = time.time()
    T = build_e11_core()

    # All contraction ranks
    crank = {}
    cmat = {}
    for q in range(1, 256):
        M = contraction_matrix(T, q)
        crank[q] = gf2_rank(M)
        cmat[q] = M

    print(f"Contraction rank distribution: {dict(Counter(crank.values()))}")

    # Find all (3,9,9) dual lines
    # Canonical: q_lo has rank 3, q_hi1 and q_hi2 have rank 9
    lines_399 = []
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
            ranks = [crank[q1], crank[q2], crank[q3]]
            if sorted(ranks) == [3, 9, 9]:
                # Identify q_lo (rank 3)
                if crank[q1] == 3:
                    lines_399.append((q1, q2, q3))
                elif crank[q2] == 3:
                    lines_399.append((q2, q1, q3))
                else:
                    lines_399.append((q3, q1, q2))

    print(f"(3,9,9) dual lines: {len(lines_399)}")

    # ======== Part 1: Algebraic proof verification ========
    n2_zero = 0
    n2_fail = 0
    for q_lo, q_hi1, q_hi2 in lines_399:
        M_lo = cmat[q_lo]   # rank 3
        M_hi1 = cmat[q_hi1] # rank 9
        assert gf2_rank(M_hi1) == 9

        M_hi1_inv = gf2_inverse(M_hi1)
        N = gf2_mat_mul(M_hi1_inv, M_lo)
        assert gf2_rank(N) == 3

        N2 = gf2_mat_mul(N, N)
        if np.all(N2 == 0):
            n2_zero += 1
        else:
            n2_fail += 1

    print(f"\nAlgebraic proof: N^2 = 0 verified on {n2_zero}/{len(lines_399)} lines")
    if n2_fail > 0:
        print(f"  WARNING: {n2_fail} failures!")

    # Structural proof WHY N^2=0:
    # N = H_0 ⊗ I_3 where H_0 = Q_hi1^{-1} Q_lo has rank 1.
    # I_3 + H_0 = Q_hi1^{-1} Q_hi2 has rank 3 (invertible).
    # If H_0 were idempotent (H_0^2 = H_0), rank(I_3+H_0) = 3-1 = 2 ≠ 3.
    # So H_0 is NOT idempotent, hence H_0^2 = (b^T Q_hi1^{-1} a) H_0 with
    # the scalar = 0 (forced by rank(I+H_0)=3). Therefore H_0^2=0 and N^2=0.
    print("  Structural: rank(I_3 + H_0) = 3 forces H_0^2 = 0.")

    # ======== Part 2: Wang LUT comparison ========
    print("\nLoading Wang LUT...")
    lut_path = WDIR / "data" / "wang_f2_lb20" / "wang_subspace_lut.pkl"
    lut, meta = load_lut(lut_path)
    print(f"  LUT entries: {len(lut):,}")

    core = CoreQuotient(1)  # E11 pivot = mask 1 in 9-bit space

    # For each (3,9,9) line D = span(q_hi1, q_hi2):
    #   D⊥ = ker(q_hi1) ∩ ker(q_hi2) is a 6D core subspace
    #   Lifted to 9-bit: span(E11, lift(D⊥)) is a 7D full-tensor subspace
    #   LUT gives L for this 7D subspace
    #
    # Pencil constraint: c_10 >= 3 (when w(q_hi1) = 9, forcing idempotent W)
    # Wang constraint: c_00 <= 19 - L, so occupation >= L
    #   When w(q_hi1) = 9: c_10 = occupation - 9 >= L - 9
    #   If L >= 12: Wang gives c_10 >= 3 (matching pencil)
    #   If L >= 13: Wang gives c_10 >= 4 (stronger than pencil)

    line_wang = []
    for q_lo, q_hi1, q_hi2 in lines_399:
        # Compute basis of D⊥ = ker(q_hi1) ∩ ker(q_hi2) in 8-bit core space
        basis_perp = []
        for p in range(1, 256):
            if gf2_inner(p, q_hi1) == 0 and gf2_inner(p, q_hi2) == 0:
                # Check linear independence
                b = rref_basis(basis_perp + [p], n=8)
                if len(b) > len(basis_perp):
                    basis_perp = list(b)
                    if len(basis_perp) == 6:
                        break

        assert len(basis_perp) == 6, f"D⊥ has dimension {len(basis_perp)} != 6"

        key8 = pack_basis(rref_basis(basis_perp, n=8))
        dim8 = key8 & 0xF
        assert dim8 == 6

        key9 = core.key9_from_key8(key8)
        dim9 = key9 & 0xF
        assert dim9 == 7

        L = lut.get(key9, None)
        if L is None:
            print(f"  WARNING: key9 {key9} not in LUT for line ({q_lo},{q_hi1},{q_hi2})")
            L = -1

        # Also look up L for the 2D core subspace D itself
        key8_D = pack_basis(rref_basis([q_hi1, q_hi2], n=8))
        dim8_D = key8_D & 0xF
        key9_D = core.key9_from_key8(key8_D)
        L_D = lut.get(key9_D, -1)

        # Also look up L for each 7D subspace ker(q) (the 1D contraction capacity)
        kerhi1_basis = []
        for p in range(1, 256):
            if gf2_inner(p, q_hi1) == 0:
                kerhi1_basis = list(rref_basis(kerhi1_basis + [p], n=8))
                if len(kerhi1_basis) == 7:
                    break
        key8_khi1 = pack_basis(rref_basis(kerhi1_basis, n=8))
        key9_khi1 = core.key9_from_key8(key8_khi1)
        L_kerhi1 = lut.get(key9_khi1, -1)

        # Wang bound from D⊥: when w(q_hi1) = 9, c_10 >= L - 9
        wang_c10_lower = max(0, L - 9) if L >= 0 else -1
        pencil_c10_lower = 3
        pencil_redundant = wang_c10_lower >= pencil_c10_lower

        line_wang.append({
            'line': [q_lo, q_hi1, q_hi2],
            'L_Dperp': L,
            'dim_Dperp_lifted': dim9,
            'L_D': L_D,
            'dim_D_lifted': key9_D & 0xF,
            'L_ker_qhi1': L_kerhi1,
            'wang_c10_lower_at_tight_w': wang_c10_lower,
            'pencil_c10_lower': pencil_c10_lower,
            'pencil_redundant': pencil_redundant,
        })

    # Summarize
    L_dist = Counter(r['L_Dperp'] for r in line_wang)
    redundant_count = sum(1 for r in line_wang if r['pencil_redundant'])
    nonredundant_count = len(line_wang) - redundant_count

    print(f"\n=== Wang comparison for (3,9,9) pencil ===")
    print(f"Total (3,9,9) lines: {len(line_wang)}")
    print(f"L(D⊥_lifted) distribution: {dict(sorted(L_dist.items()))}")
    print(f"Pencil redundant (Wang c_10 >= 3 at tight w): {redundant_count}")
    print(f"Pencil potentially adds value: {nonredundant_count}")

    # ======== Part 3: Near-miss coloring analysis ========
    S = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]

    near_miss_pencil_fails = []
    for qi, (q_lo, q_hi1, q_hi2) in enumerate(lines_399):
        c = [0, 0, 0, 0]
        for p in S:
            v1 = gf2_inner(p, q_hi1)
            v2 = gf2_inner(p, q_hi2)
            c[v1*2 + v2] += 1
        c10, c01, c11, c00 = c[2], c[1], c[3], c[0]
        w_hi1 = c10 + c11
        w_hi2 = c01 + c11

        # Check if pencil would apply (w_hi1 = 9 forces idempotent W)
        # Actually M_2 = M_hi1 in my normalization; check both rank-9 contractions
        pencil_applies = (w_hi1 == 9)  # tight = idempotent forced
        pencil_fail = pencil_applies and c10 < 3

        # Also check Wang violation for D⊥
        L_Dp = line_wang[qi]['L_Dperp']
        wang_violated = c00 > (19 - L_Dp) if L_Dp >= 0 else False

        if pencil_fail or wang_violated:
            near_miss_pencil_fails.append({
                'line': [q_lo, q_hi1, q_hi2],
                'colors': [c10, c01, c11],
                'c00': c00,
                'w_hi1': w_hi1,
                'w_hi2': w_hi2,
                'pencil_applies': pencil_applies,
                'pencil_fail': pencil_fail,
                'L_Dperp': L_Dp,
                'wang_c00_cap': 19 - L_Dp if L_Dp >= 0 else None,
                'wang_violated': wang_violated,
            })

    # Count lines where near-miss has tight w AND c10 < 3
    tight_w_lines = sum(1 for qi, (q_lo, q_hi1, q_hi2) in enumerate(lines_399)
                        if sum(gf2_inner(p, q_hi1) for p in S) == 9)

    print(f"\n=== Near-miss coloring on (3,9,9) lines ===")
    print(f"Lines where w(q_hi1) = 9 (tight): {tight_w_lines}")
    print(f"Lines with pencil failure (tight w AND c10<3): {sum(1 for x in near_miss_pencil_fails if x['pencil_fail'])}")
    print(f"Lines with Wang D⊥ violation: {sum(1 for x in near_miss_pencil_fails if x['wang_violated'])}")
    print(f"Lines with BOTH pencil fail AND Wang violated: {sum(1 for x in near_miss_pencil_fails if x['pencil_fail'] and x['wang_violated'])}")

    if near_miss_pencil_fails:
        print(f"\nExamples (first 5):")
        for x in near_miss_pencil_fails[:5]:
            print(f"  line={x['line']} colors=({x['colors'][0]},{x['colors'][1]},{x['colors'][2]}) "
                  f"c00={x['c00']} w_hi1={x['w_hi1']} L(D⊥)={x['L_Dperp']} "
                  f"cap={x['wang_c00_cap']} wang_viol={x['wang_violated']} pencil={x['pencil_fail']}")

    # ======== Part 4: Global assessment ========
    # For ANY complete-Wang-admissible support:
    #   occupation(D) >= L(D⊥_lifted), so when w(q_2)=9: c_10 >= L - 9.
    #   Pencil gives c_10 >= 3 when w(q_2) = 9.
    #   Pencil is STRICTLY redundant iff L >= 12 for ALL (3,9,9) lines.

    min_L = min(r['L_Dperp'] for r in line_wang)
    max_L = max(r['L_Dperp'] for r in line_wang)
    all_redundant = all(r['pencil_redundant'] for r in line_wang)

    print(f"\n=== Global assessment ===")
    print(f"L(D⊥) range: [{min_L}, {max_L}]")
    print(f"Pencil completely redundant for (3,9,9): {all_redundant}")
    if all_redundant:
        print("  CONCLUSION: For any Wang-admissible support, the Wang 6D/7D row")
        print("  for D⊥ already implies c_10 >= 3 when w(q) = 9.")
        print("  The (3,9,9) pencil obstruction adds NO new support restriction.")
    else:
        print(f"  Some lines have L < 12; pencil adds value on {nonredundant_count} lines.")

    results = {
        'theorem': 'For N^2=0 and W^2=W over F_2, rank(N+W) >= rank(N)',
        'application': '(3,9,9) pencil: c_10 >= 3 when w(q_hi)=9 forces W idempotent',
        'lines_399_count': len(lines_399),
        'N2_zero_verified': n2_zero,
        'N2_failures': n2_fail,
        'L_Dperp_distribution': {str(k): v for k, v in sorted(L_dist.items())},
        'pencil_redundant_count': redundant_count,
        'pencil_nonredundant_count': nonredundant_count,
        'pencil_completely_redundant': all_redundant,
        'min_L_Dperp': min_L,
        'max_L_Dperp': max_L,
        'near_miss_tight_w_lines': tight_w_lines,
        'near_miss_pencil_fails': len([x for x in near_miss_pencil_fails if x['pencil_fail']]),
        'near_miss_wang_Dperp_violations': len([x for x in near_miss_pencil_fails if x['wang_violated']]),
        'examples_head': line_wang[:5],
        'near_miss_fail_examples': near_miss_pencil_fails[:10],
        'elapsed_sec': time.time() - t0,
    }

    out = ODIR / "pencil_wang_comparison.json"
    with open(out, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nSaved: {out}")
    print(f"Elapsed: {time.time()-t0:.1f}s")

if __name__ == "__main__":
    main()
