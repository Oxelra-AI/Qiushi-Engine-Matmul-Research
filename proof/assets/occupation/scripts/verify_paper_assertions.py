#!/usr/bin/env python3
"""Verify key mathematical assertions in the paper."""
import numpy as np
from itertools import combinations

def int_to_mat(v):
    m = np.zeros((3,3), dtype=int)
    for i in range(3):
        for j in range(3):
            m[i,j] = (v >> (3*i+j)) & 1
    return m

# 1. Verify rank(D)=2 coset structure
p = int_to_mat(272)
print("=== Coset structure ===")
print("p =", p.tolist())
D = p[1:,:]
print("D =", D.tolist(), "rank(D) =", np.linalg.matrix_rank(D))

rowspan = set()
for mask in range(4):
    v = np.zeros(3, dtype=int)
    for b in range(2):
        if mask & (1<<b):
            v = (v + D[b]) % 2
    rowspan.add(tuple(v))
print("Row span of D:", sorted(rowspan))

n_rank2 = n_rank3 = 0
for w_int in range(8):
    w = np.array([(w_int>>j)&1 for j in range(3)], dtype=int)
    mat = p.copy()
    mat[0] = w
    mat = mat % 2
    r = np.linalg.matrix_rank(mat)
    if r == 2: n_rank2 += 1
    if r == 3: n_rank3 += 1
    print(f"  w={w.tolist()}, rank={r}, in_rowspan={tuple(w) in rowspan}")

print(f"  rank-2: {n_rank2}, rank-3: {n_rank3}")
assert n_rank2 == 4 and n_rank3 == 4, "Coset structure wrong!"
print("  ✓ Confirmed: 4 rank-2 and 4 rank-3 elements")

# 2. Verify AG(3,2) cap number = 4
print("\n=== AG(3,2) cap bound ===")
F23 = [tuple((v>>j)&1 for j in range(3)) for v in range(8)]
planes = []
for pts in combinations(F23, 4):
    s = tuple((pts[0][j]+pts[1][j]+pts[2][j]+pts[3][j])%2 for j in range(3))
    if s == (0,0,0):
        planes.append(pts)
print(f"Total 4-point affine planes: {len(planes)}")

# Every 5-subset contains a plane
for pts5 in combinations(F23, 5):
    has_plane = False
    for sub4 in combinations(pts5, 4):
        s = tuple((sub4[0][j]+sub4[1][j]+sub4[2][j]+sub4[3][j])%2 for j in range(3))
        if s == (0,0,0):
            has_plane = True
            break
    assert has_plane, f"No plane in {pts5}"
print("Every 5-subset contains a plane. Cap number = 4. ✓")

# 3. Verify pigeonhole proof
print("\n=== Pigeonhole proof verification ===")
for pts5 in combinations(F23, 5):
    pair_sums = {}
    for p1, p2 in combinations(pts5, 2):
        s = tuple((p1[j]+p2[j])%2 for j in range(3))
        pair_sums.setdefault(s, []).append((p1, p2))
    found = False
    for s, pairs in pair_sums.items():
        if len(pairs) >= 2:
            p1, p2 = pairs[0]
            p3, p4 = pairs[1]
            if len(set([p1,p2,p3,p4])) == 4:
                total = tuple((p1[j]+p2[j]+p3[j]+p4[j])%2 for j in range(3))
                assert total == (0,0,0)
                found = True
                break
    assert found, f"Pigeonhole failed for {pts5}"
print("Pigeonhole argument verified for all 56 five-subsets. ✓")

# 4. Verify product identity on one example
print("\n=== Product identity spot check ===")
rng = np.random.RandomState(42)
for trial in range(100):
    At = rng.randint(0, 2, (3,3))
    Bt = rng.randint(0, 2, (3,3))
    Ct = rng.randint(0, 2, (3,3))
    As = rng.randint(0, 2, (3,3))
    Bs = rng.randint(0, 2, (3,3))
    Cs = rng.randint(0, 2, (3,3))
    
    # Build P and M_t, M_s
    P = np.zeros((27,27), dtype=int)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                P[3*i+j*1, 3*j+k*1] = 0  # wrong indexing
    # Actually build P correctly
    P = np.zeros((27,27), dtype=int)
    T = np.zeros((9,9,9), dtype=int)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    
    for row_i in range(3):
        for b in range(9):
            for col_j in range(3):
                for c in range(9):
                    P[row_i*9+b, col_j*9+c] = T[3*row_i+col_j, b, c]
    
    def make_M(A, B, C):
        M = np.zeros((27,27), dtype=int)
        bvec = B.flatten()
        cvec = C.flatten()
        for i in range(3):
            for b in range(9):
                for j in range(3):
                    for c in range(9):
                        M[i*9+b, j*9+c] = (A[i,j] * bvec[b] * cvec[c]) % 2
        return M
    
    Mt = make_M(At, Bt, Ct)
    Ms = make_M(As, Bs, Cs)
    
    Pinv = P.T  # over F2, permutation matrix
    
    lhs = (Mt @ Pinv @ Ms) % 2
    
    prod = (At @ Bs @ Ct.T @ As) % 2
    rhs = make_M(prod, Bt, Cs)
    
    assert np.array_equal(lhs, rhs), f"Product identity failed on trial {trial}"

print("Product identity verified on 100 random triples. ✓")
print("\nAll paper assertions verified. ✓✓✓")
