#!/usr/bin/env python3
"""Analyze the V-residual tensor rank for the quotient lift approach."""
import numpy as np

def gf2_rank_mat(M):
    M = M.copy().astype(np.uint8)
    m, n = M.shape
    r = 0
    for col in range(n):
        piv = None
        for row in range(r, m):
            if M[row, col] & 1:
                piv = row; break
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]
        for row in range(m):
            if row != r and M[row, col] & 1:
                M[row] ^= M[r]
        r += 1
    return r

# Build E11 core
T = np.zeros((9,9,9), dtype=np.uint8)
for i in range(3):
    for j in range(3):
        for k in range(3):
            T[3*i+j, 3*j+k, 3*i+k] = 1
core = T[1:,:,:]

prefix = [1, 2, 4, 8]
print(f"Prefix: {prefix}")

for k in range(4):
    sl = core[k]
    print(f"V-slice {k} (core[{k}]): rank={gf2_rank_mat(sl)}, "
          f"nz={[(b,c) for b in range(9) for c in range(9) if sl[b,c]]}")

V_res = core[:4, :, :]
print(f"\nV-residual shape={V_res.shape}, nnz={V_res.sum()}")

# B-unfolding: (9) x (4*9)
B_unfold = np.zeros((9, 36), dtype=np.uint8)
for k in range(4):
    B_unfold[:, k*9:(k+1)*9] = V_res[k]
B_rank = gf2_rank_mat(B_unfold)
print(f"B-unfolding rank: {B_rank}")

C_unfold = np.zeros((9, 36), dtype=np.uint8)
for k in range(4):
    C_unfold[:, k*9:(k+1)*9] = V_res[k].T
C_rank = gf2_rank_mat(C_unfold)
print(f"C-unfolding rank: {C_rank}")

lb = max(4, B_rank, C_rank)
print(f"\nTensor rank lower bound: {lb}")
print(f"Aligned lift with 4 prefix terms requires V-residual rank <= 4")
print(f"Result: {'INFEASIBLE' if lb > 4 else 'POSSIBLE'} for this prefix")

# Now scan ALL 33 rank-3 phi masks to find best prefix
print("\n--- Scanning all prefixes with rank-3 V-slices ---")
rank3_phis = []
for phi in range(1, 256):
    sl = np.zeros((9,9), dtype=np.uint8)
    for a in range(8):
        if (phi >> a) & 1:
            sl ^= core[a]
    if gf2_rank_mat(sl) == 3:
        rank3_phis.append(phi)

# Find all 4-element independent subsets of rank-3 phis
def parity(x): return int(x).bit_count() & 1
def gf2_indep(vecs):
    basis = {}
    for v in vecs:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if p in basis: x ^= basis[p]
            else: basis[p] = x; break
    return len(basis) == len(vecs)

best_lb = 99
best_prefix = None
count = 0
# Test a selection of 4-tuples of rank-3 phis
from itertools import combinations
for combo in combinations(rank3_phis, 4):
    if not gf2_indep(combo):
        continue
    count += 1
    # Find corresponding prefix: phi_k(u_i) = delta_{ki}
    # Build phi matrix
    P = np.zeros((4, 8), dtype=np.uint8)
    for k in range(4):
        for b in range(8):
            P[k, b] = (combo[k] >> b) & 1
    # For each u_i: solve P @ x = e_i over GF(2)
    u_masks = []
    ok = True
    for i in range(4):
        target = np.zeros(4, dtype=np.uint8)
        target[i] = 1
        aug = np.hstack([P.copy(), target.reshape(-1,1)])
        row = 0
        pivots = []
        for col in range(8):
            pv = None
            for r in range(row, 4):
                if aug[r,col]: pv = r; break
            if pv is None: continue
            aug[[row,pv]] = aug[[pv,row]]
            for r in range(4):
                if r!=row and aug[r,col]: aug[r]^=aug[row]
            pivots.append((row,col))
            row += 1
        x = np.zeros(8, dtype=np.uint8)
        for r,c in pivots: x[c] = aug[r,8]
        u_masks.append(sum(int(x[b])<<b for b in range(8)))
    
    if not gf2_indep(u_masks):
        continue
    
    # Compute V-residual
    V_res_test = np.zeros((4, 9, 9), dtype=np.uint8)
    for k in range(4):
        phi_vec = np.array([(combo[k]>>a)&1 for a in range(8)], dtype=np.uint8)
        for b in range(9):
            for c in range(9):
                V_res_test[k, b, c] = np.dot(phi_vec, core[:,b,c]) % 2
    
    # B-unfolding rank
    Bf = np.zeros((9, 36), dtype=np.uint8)
    for k in range(4):
        Bf[:, k*9:(k+1)*9] = V_res_test[k]
    br = gf2_rank_mat(Bf)
    
    Cf = np.zeros((9, 36), dtype=np.uint8)
    for k in range(4):
        Cf[:, k*9:(k+1)*9] = V_res_test[k].T
    cr = gf2_rank_mat(Cf)
    
    lb_test = max(4, br, cr)
    if lb_test < best_lb:
        best_lb = lb_test
        best_prefix = (u_masks, combo, lb_test, br, cr)
    
    if count >= 5000:
        break

print(f"Tested {count} valid 4-tuples of rank-3 phis")
print(f"Best tensor rank lower bound: {best_lb}")
if best_prefix:
    u, phis, lb, br, cr = best_prefix
    print(f"Best prefix: u={u}, phis={phis}, B-rank={br}, C-rank={cr}")
