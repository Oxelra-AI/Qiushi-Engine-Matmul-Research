#!/usr/bin/env python3
"""analysis: Algebraic analysis of the projected containment condition.

Key insight: The containment L_1 ⊂ span{v_l w_l^T} projects to a 
27-dimensional "relevant subspace" where L_1 is 9-dimensional and 
rank-1 matrices have rank up to 3 (not 1).

This script:
1. Verifies the projected structure
2. Tests whether 22 random general pairs span L_1 in projection
3. Explores structured constructions
"""
import numpy as np
from pathlib import Path
import json

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / "data" / "projected_analysis"
DATA_DIR.mkdir(parents=True, exist_ok=True)

p = 65521

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
        for row2 in range(rows):
            if row2 == r: continue
            if M[row2, col] % mod != 0:
                M[row2] = (M[row2] - (M[row2, col] % mod) * M[r]) % mod
        r += 1
    return r

def project_rank1(v, w):
    """Project v w^T to the 27 relevant coordinates.
    Returns a 27-vector: for row r ∈ {0,...,8} and column a ∈ {0,1,2},
    the entry is v[r] * w[3*(r%3) + a]."""
    result = np.zeros(27, dtype=int)
    for r in range(9):
        k = r % 3  # block index
        for a in range(3):
            result[r * 3 + a] = (int(v[r]) * int(w[3*k + a])) % p
    return result % p

def build_L_projected():
    """Build projected L_1 basis in K^{27}.
    B_{ab} has entries: row 3b+k, col a, value 1 for k=0,1,2.
    In the 27-vector: index (3b+k)*3 + a."""
    basis = []
    for a in range(3):
        for b in range(3):
            vec = np.zeros(27, dtype=int)
            for k in range(3):
                vec[(3*b + k) * 3 + a] = 1
            basis.append(vec)
    return np.array(basis, dtype=int)

L_proj = build_L_projected()
print(f"Projected L_1 rank: {modp_rank(L_proj.copy(), p)} (should be 9)")

# ======================================================================
# 1. Verify naive_27 in projection
# ======================================================================
print("\n=== Naive 27-term projected containment ===")
naive_proj = []
for i in range(3):
    for j in range(3):
        for k in range(3):
            v = np.zeros(9, dtype=int); v[3*j+k] = 1
            w = np.zeros(9, dtype=int); w[3*k+i] = 1
            naive_proj.append(project_rank1(v, w))

A_naive = np.array(naive_proj, dtype=int) % p
AB = np.vstack([A_naive, L_proj]) % p
rA = modp_rank(A_naive.copy(), p)
rAB = modp_rank(AB.copy(), p)
print(f"  Projected span rank: {rA}, joint rank: {rAB}, contained: {rA==rAB}")

# Each naive projected vector has rank 1 in K^{27}: just one nonzero entry
print(f"  Nonzero entries per projected naive vector: "
      f"{[np.count_nonzero(v) for v in naive_proj[:5]]}...")

# ======================================================================
# 2. Random general pairs: projected containment test
# ======================================================================
print("\n=== Random general pairs in projection ===")
np.random.seed(42)

for N in [9, 12, 15, 18, 22, 27]:
    n_trials = 5000
    successes = 0
    for _ in range(n_trials):
        vecs = []
        for _ in range(N):
            v = np.random.randint(1, p, 9)
            w = np.random.randint(1, p, 9)
            vecs.append(project_rank1(v, w))
        A = np.array(vecs, dtype=int) % p
        AB = np.vstack([A, L_proj]) % p
        rA = modp_rank(A.copy(), p)
        rAB = modp_rank(AB.copy(), p)
        if rA == rAB:
            successes += 1
    print(f"  N={N:2d}: {successes}/{n_trials} ({successes/n_trials:.4f})")

# ======================================================================
# 3. Projected rank of one general pair
# ======================================================================
print("\n=== Projected rank per pair ===")
ranks = []
for _ in range(1000):
    v = np.random.randint(1, p, 9)
    w = np.random.randint(1, p, 9)
    pv = project_rank1(v, w)
    # Reshape to 9×3 and compute rank
    M = pv.reshape(9, 3)
    r = modp_rank(M.copy(), p)
    ranks.append(r)
from collections import Counter
print(f"  Rank distribution (9×3): {dict(Counter(ranks))}")

# ======================================================================
# 4. Tau-structured pairs in projection
# ======================================================================
print("\n=== Tau-structured pairs in projection (correct tau action) ===")

def transpose_3x3_vec(v):
    """Apply the 3×3 matrix transpose to a 9-vector (row-major)."""
    V = v.reshape(3, 3)
    return V.T.ravel()

# For tau: fixed term has w = T(v), free orbit has (v,w) and (T(w), T(v))
# Projected vectors:
# Fixed (v, T(v)): project_rank1(v, transpose(v))
# Free (v, w): project_rank1(v, w) and project_rank1(transpose(w), transpose(v))

for f, m in [(0,11), (2,10), (4,9), (6,8), (8,7)]:
    if f + 2*m != 22: continue
    n_trials = 10000
    successes = 0
    for _ in range(n_trials):
        vecs = []
        for _ in range(f):
            v = np.random.randint(1, p, 9)
            tv = transpose_3x3_vec(v) % p
            vecs.append(project_rank1(v, tv))
        for _ in range(m):
            v = np.random.randint(1, p, 9)
            w = np.random.randint(1, p, 9)
            tv = transpose_3x3_vec(v) % p
            tw = transpose_3x3_vec(w) % p
            vecs.append(project_rank1(v, w))
            vecs.append(project_rank1(tw, tv))
        A = np.array(vecs, dtype=int) % p
        AB = np.vstack([A, L_proj]) % p
        rA = modp_rank(A.copy(), p)
        rAB = modp_rank(AB.copy(), p)
        if rA == rAB:
            successes += 1
    rate = successes / n_trials
    print(f"  tau (f={f:2d},m={m:2d}): {successes}/{n_trials} ({rate:.4f})")

out_path = DATA_DIR / "projected_analysis.json"
with open(out_path, 'w') as f:
    json.dump({"note": "Projected containment analysis, see stdout"}, f)
print(f"\nSAVED {out_path}")
