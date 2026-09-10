#!/usr/bin/env python3
"""analysis: One-term deletion from Laderman rank-23 tau decomposition.

Laderman has tau-skeleton (f=7, m=8, rank=23) under Phi3*Phi4.
If we delete one FIXED term, we get (f=6, m=8, rank=22).
For this to give a valid rank-22 algorithm, the remaining 22 rank-1 
matrices must still satisfy L_1 ⊂ span{v_l w_l^T}.

This script checks all 7 possible fixed-term deletions.
"""
import numpy as np
from pathlib import Path
import json

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / "data" / "laderman_deletion"
DATA_DIR.mkdir(parents=True, exist_ok=True)

def E(i, j):
    M = np.zeros((3,3), dtype=int)
    M[i,j] = 1
    return M

# Build Laderman terms (from Burichenko tensor form)
terms = [
    (E(0,0)+E(0,1)+E(0,2)-E(1,0)-E(1,1)-E(2,1)-E(2,2), E(1,1), E(1,0)),
    (E(0,0)-E(1,0), -E(0,1)+E(1,1), E(0,1)+E(1,1)),
    (E(1,1), -E(0,0)+E(0,1)+E(1,0)-E(1,1)-E(1,2)-E(2,0)+E(2,2), E(0,1)),
    (-E(0,0)+E(1,0)+E(1,1), E(0,0)-E(0,1)+E(1,1), E(1,0)+E(0,1)+E(1,1)),
    (E(1,0)+E(1,1), -E(0,0)+E(0,1), E(1,0)+E(1,1)),
    (E(0,0), E(0,0), E(0,0)+E(1,0)+E(2,0)+E(0,1)+E(1,1)+E(0,2)+E(2,2)),
    (-E(0,0)+E(2,0)+E(2,1), E(0,0)-E(0,2)+E(1,2), E(2,0)+E(0,2)+E(2,2)),
    (-E(0,0)+E(2,0), E(0,2)-E(1,2), E(0,2)+E(2,2)),
    (E(2,0)+E(2,1), -E(0,0)+E(0,2), E(2,0)+E(2,2)),
    (E(0,0)+E(0,1)+E(0,2)-E(1,1)-E(1,2)-E(2,0)-E(2,1), E(1,2), E(2,0)),
    (E(2,1), -E(0,0)+E(0,2)+E(1,0)-E(1,1)-E(1,2)-E(2,0)+E(2,1), E(0,2)),
    (-E(0,2)+E(2,1)+E(2,2), E(1,1)+E(2,0)-E(2,1), E(1,0)+E(0,2)+E(1,2)),
    (E(0,2)-E(2,2), E(1,1)-E(2,1), E(0,2)+E(1,2)),
    (E(0,2), E(2,0), E(0,0)+E(1,0)+E(2,0)+E(0,1)+E(2,1)+E(0,2)+E(1,2)),
    (E(2,1)+E(2,2), -E(2,0)+E(2,1), E(1,0)+E(1,2)),
    (-E(0,2)+E(1,1)+E(1,2), E(1,2)+E(2,0)-E(2,2), E(2,0)+E(0,1)+E(2,1)),
    (E(0,2)-E(1,2), E(1,2)-E(2,2), E(0,1)+E(2,1)),
    (E(1,1)+E(1,2), -E(2,0)+E(2,2), E(2,0)+E(2,1)),
    (E(0,1), E(1,0), E(0,0)),
    (E(1,2), E(2,1), E(1,1)),
    (E(1,0), E(0,2), E(2,1)),
    (E(2,0), E(0,1), E(1,2)),
    (E(2,2), E(2,2), E(2,2)),
]

# Fixed point indices (0-based): 0, 3, 9, 11, 18, 20, 22
fixed_indices = [0, 3, 9, 11, 18, 20, 22]
# Two-cycle pairs (0-based): (1,4), (2,5), (6,15), (7,17), (8,16), (10,13), (12,14), (19,21)
two_cycles = [(1,4), (2,5), (6,15), (7,17), (8,16), (10,13), (12,14), (19,21)]

def extended_gcd(a, b):
    if a == 0: return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def mod_inv(a, m):
    g, x, _ = extended_gcd(a % m, m)
    if g != 1: return None
    return x % m

def modp_rank(M, mod):
    M = M.copy() % mod
    rows, cols = M.shape
    r = 0
    for col in range(cols):
        if r >= rows: break
        pivot = None
        for row in range(r, rows):
            if M[row, col] % mod != 0: pivot = row; break
        if pivot is None: continue
        M[[r, pivot]] = M[[pivot, r]]
        inv = mod_inv(int(M[r, col]), mod)
        if inv is None: continue
        M[r] = (M[r] * inv) % mod
        for row in range(rows):
            if row == r: continue
            if M[row, col] % mod != 0:
                M[row] = (M[row] - (M[row, col] % mod) * M[r]) % mod
        r += 1
    return r

def build_L_basis():
    """Correct L_1 basis: B_{ab} with entries at (3b+k, 3k+a)."""
    basis = []
    for a in range(3):
        for b in range(3):
            M = np.zeros((9, 9), dtype=int)
            for k in range(3):
                M[3*b + k, 3*k + a] = 1
            basis.append(M)
    return basis

# Build rank-1 matrices from Laderman terms
# Each term (a, b, c) contributes v w^T where v = b (flattened) and w = c (flattened)
# (since the tensor is u ⊗ v ⊗ w where u=a, v=b, w=c from our convention)
rank1_matrices = []
for a, b, c in terms:
    v = b.ravel()  # second factor (Y-linear form)
    w = c.ravel()  # third factor (Z-linear form, already transposed in Burichenko's convention)
    rank1_matrices.append(np.outer(v, w))

# Verify: full Laderman satisfies containment
L_basis = build_L_basis()
L_vecs = np.array([B.ravel() for B in L_basis], dtype=int)

p = 65521
all_vecs = np.array([M.ravel() for M in rank1_matrices], dtype=int) % p
AB = np.vstack([all_vecs, L_vecs]) % p
rA = modp_rank(all_vecs.copy(), p)
rAB = modp_rank(AB.copy(), p)
print(f"Full Laderman (23 terms): span rank={rA}, joint rank={rAB}, contained={rA==rAB}")

# Now test deletion of each fixed term
print(f"\n=== One-term deletion tests ===")
results = {"full_rank": int(rA), "full_contained": bool(rA == rAB), "deletions": {}}

for del_idx in fixed_indices:
    remaining = [i for i in range(23) if i != del_idx]
    remaining_vecs = np.array([rank1_matrices[i].ravel() for i in remaining], dtype=int) % p
    AB_del = np.vstack([remaining_vecs, L_vecs]) % p
    rA_del = modp_rank(remaining_vecs.copy(), p)
    rAB_del = modp_rank(AB_del.copy(), p)
    defect = rAB_del - rA_del
    contained = (defect == 0)
    
    a, b, c = terms[del_idx]
    term_name = f"t_{del_idx+1}"
    print(f"  Delete {term_name}: rank={rA_del}, defect={defect}, contained={contained}")
    
    results["deletions"][term_name] = {
        "index": del_idx,
        "rank_after": int(rA_del),
        "defect": int(defect),
        "contained": bool(contained)
    }

# Also test deletion of free orbits (removes 2 terms)
print(f"\n=== Free orbit deletion tests (rank 21) ===")
for l, l_prime in two_cycles:
    remaining = [i for i in range(23) if i != l and i != l_prime]
    remaining_vecs = np.array([rank1_matrices[i].ravel() for i in remaining], dtype=int) % p
    AB_del = np.vstack([remaining_vecs, L_vecs]) % p
    rA_del = modp_rank(remaining_vecs.copy(), p)
    rAB_del = modp_rank(AB_del.copy(), p)
    defect = rAB_del - rA_del
    print(f"  Delete orbit ({l+1},{l_prime+1}): rank={rA_del}, defect={defect}")

# Test: delete fixed + add general replacement
print(f"\n=== Delete fixed + replace with random rank-1 ===")
np.random.seed(0)
for del_idx in fixed_indices[:3]:  # test first 3
    remaining = [i for i in range(23) if i != del_idx]
    remaining_vecs = np.array([rank1_matrices[i].ravel() for i in remaining], dtype=int) % p
    
    n_trials = 10000
    successes = 0
    for _ in range(n_trials):
        v = np.random.randint(0, p, 9)
        w = np.random.randint(0, p, 9)
        new_vec = (np.outer(v, w).ravel()) % p
        test = np.vstack([remaining_vecs, new_vec.reshape(1,-1), L_vecs]) % p
        r_test = modp_rank(test.copy(), p)
        r_without = modp_rank(np.vstack([remaining_vecs, L_vecs]).copy(), p)
        # The defect should be 0 for the replacement to work
        # But we also need the new total rank to be ≤ 22 (already guaranteed)
        if r_test == modp_rank(np.vstack([remaining_vecs, new_vec.reshape(1,-1)]).copy(), p):
            successes += 1
    
    print(f"  Delete t_{del_idx+1}: {successes}/{n_trials} random replacements work")

out_path = DATA_DIR / "laderman_deletion_check.json"
with open(out_path, 'w') as f:
    json.dump(results, f, indent=2)
print(f"\nSAVED {out_path}")
