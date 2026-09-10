#!/usr/bin/env python3
"""Standalone self-contained verification of the A-slot flattening bound.

Theorem: For any decomposition T_{<3,3,3>} = sum_t a_t (x) b_t (x) c_t
over any field, sum_t rank(a_t) >= 27.

Proof: The A-slot split flattening Phi_A(T) is a 27x27 permutation matrix,
hence has rank 27. Each term contributes rank(a_t) to the flattening rank.

This script verifies the mathematical claim with no external dependencies
beyond numpy for GF(2) matrix rank.
"""
import numpy as np

def gf2_rank(M):
    A = np.array(M, dtype=np.uint8) % 2
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
    return r

# Build T_{<3,3,3>} in convention T[3i+j, 3j+k, 3i+k] = 1
T = np.zeros((9, 9, 9), dtype=np.uint8)
for i in range(3):
    for j in range(3):
        for k in range(3):
            T[3*i+j, 3*j+k, 3*i+k] = 1

# Build A-slot split flattening: Phi_A[(i, 3j+k), (j, 3i+k)]
Phi = np.zeros((27, 27), dtype=np.uint8)
for i in range(3):
    for j in range(3):
        for k in range(3):
            row = i * 9 + 3*j + k
            col = j * 9 + 3*i + k
            Phi[row, col] = 1

# Verify: permutation matrix
assert Phi.sum() == 27, f"Expected 27 nonzeros, got {Phi.sum()}"
assert all(Phi.sum(axis=1) == 1), "Not all row sums are 1"
assert all(Phi.sum(axis=0) == 1), "Not all col sums are 1"

# Verify: rank 27 over GF(2)
r = gf2_rank(Phi)
assert r == 27, f"Expected rank 27, got {r}"

# Verify: consistent with actual tensor
# The flattening should equal the A-split of T
Phi_check = np.zeros((27, 27), dtype=np.uint8)
for a in range(9):
    i, j = divmod(a, 3)
    for b in range(9):
        for c in range(9):
            if T[a, b, c]:
                Phi_check[i*9 + b, j*9 + c] ^= 1
assert np.array_equal(Phi, Phi_check), "Flattening doesn't match tensor"

# Verify: B-slot split also has rank 27
PhiB = np.zeros((27, 27), dtype=np.uint8)
for b_idx in range(9):
    j, k = divmod(b_idx, 3)
    for a in range(9):
        for c in range(9):
            if T[a, b_idx, c]:
                PhiB[j*9 + c, k*9 + a] ^= 1
rB = gf2_rank(PhiB)
assert rB == 27, f"B-slot rank {rB}, expected 27"

# Consequence: at n=20, at least 4 factors have rank >= 2
# Because sum >= 27, n = 20, excess = 7, ceil(7/2) = 4
excess_20 = 27 - 20
min_rank_ge2 = -(-excess_20 // 2)  # ceiling division
assert min_rank_ge2 == 4

print("ALL CHECKS PASSED")
print(f"  Phi_A: 27x27 permutation matrix, rank {r} over GF(2)")
print(f"  Phi_B: 27x27 permutation matrix, rank {rB} over GF(2)")
print(f"  Bound: sum rank(a_t) >= 27 for any decomposition")
print(f"  At n=20: at least {min_rank_ge2} factors have matrix rank >= 2")
print(f"  Consequence: rank-2 or rank-3 pivot always exists in rank-20 decomposition")
print(f"  Lower bound proof needs ONLY rank-2 and rank-3 quotients (not E11)")
