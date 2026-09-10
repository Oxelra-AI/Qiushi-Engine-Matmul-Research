#!/usr/bin/env python3
"""analysis: Unified containment formulation for the transpose layer.

The key insight: the Gram and anti sectors are just the ±1
eigendecomposition of a single containment condition:

    span{v_i w_i^T : i=1,...,N} ⊇ L

where L = {X ⊗ I_3 : X ∈ K^{3×3}} is the 9-dimensional slice space.

For a tau-invariant rank-r decomposition with f fixed and m free orbits:
  - Fixed term i: contributes v_i v_i^T (symmetric rank-1)
  - Free orbit j: contributes v_j w_j^T and w_j v_j^T (a transpose pair)
  - Total rank: r = f + 2m, number of pairs: N = f + m

The containment span{vw^T} ⊇ L is equivalent to BOTH:
  - Gram sector: span{v⊙w} ⊇ L_sym (the symmetric part)  
  - Anti sector: span{v∧w} ⊇ L_anti (the antisymmetric part)

And once (v,w) pairs are fixed, u's symmetric part is determined linearly by Gram
and u's antisymmetric part is determined linearly by anti. So the full 729 Brent
identities reduce to this single containment test!

This script:
1. Verifies the unified formulation on naive_27 as positive control
2. Tests the containment condition as a practical feasibility oracle
3. Searches for rank-22 tau-invariant configurations
"""
import numpy as np
from pathlib import Path
import json
import itertools

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / "data" / "unified_containment"
DATA_DIR.mkdir(parents=True, exist_ok=True)

p = 65521  # large prime, p ≡ 1 mod 4 so sqrt(-1) exists

def mod_inv(a, m):
    """Modular inverse via extended Euclidean."""
    g, x, _ = extended_gcd(a % m, m)
    if g != 1: return None
    return x % m

def extended_gcd(a, b):
    if a == 0: return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def modp(x):
    return x % p

# Build the target slice space L = {X ⊗ I_3 : X ∈ K^{3×3}} in K^{9×9}
# L has dimension 9; basis elements are E_{ab} ⊗ I_3 for a,b ∈ {0,1,2}
def build_L_basis():
    """Build 9 basis matrices of L, each 9×9."""
    basis = []
    for a in range(3):
        for b in range(3):
            M = np.zeros((9, 9), dtype=int)
            # E_{ab} ⊗ I_3: entry (3a+c, 3b+c) = 1 for c=0,1,2
            for c in range(3):
                M[3*a + c, 3*b + c] = 1
            basis.append(M)
    return basis

def rank_one_matrix(v, w):
    """Outer product v w^T, mod p."""
    return np.outer(v, w) % p

def check_containment(pairs, L_basis, mod=None):
    """Check if span{v_i w_i^T} ⊇ L.
    pairs: list of (v, w) vectors in K^9.
    L_basis: list of 9x9 matrices forming a basis of L.
    Returns: True if L ⊆ span{vw^T}."""
    n = len(pairs)
    dim_L = len(L_basis)
    
    # Flatten all rank-1 matrices and L basis to vectors in K^81
    vw_vecs = []
    for v, w in pairs:
        M = np.outer(v, w)
        if mod: M = M % mod
        vw_vecs.append(M.ravel())
    
    L_vecs = [B.ravel() for B in L_basis]
    
    # Stack and check: L_vecs should be in row space of vw_vecs
    if mod:
        A = np.array(vw_vecs, dtype=int) % mod  # n × 81
        B = np.array(L_vecs, dtype=int) % mod    # dim_L × 81
        # Check rank of [A; B] vs rank of A
        AB = np.vstack([A, B]) % mod
        rA = modp_rank(A, mod)
        rAB = modp_rank(AB, mod)
        return rA == rAB
    else:
        A = np.array(vw_vecs, dtype=float)
        B = np.array(L_vecs, dtype=float)
        AB = np.vstack([A, B])
        rA = np.linalg.matrix_rank(A, tol=1e-8)
        rAB = np.linalg.matrix_rank(AB, tol=1e-8)
        return rA == rAB

def modp_rank(M, mod):
    """Rank of integer matrix mod prime."""
    M = M.copy() % mod
    rows, cols = M.shape
    r = 0
    for col in range(cols):
        if r >= rows: break
        # Find pivot
        pivot = None
        for row in range(r, rows):
            if M[row, col] % mod != 0:
                pivot = row
                break
        if pivot is None: continue
        M[[r, pivot]] = M[[pivot, r]]
        inv_val = mod_inv(int(M[r, col]), mod)
        if inv_val is None: continue
        M[r] = (M[r] * inv_val) % mod
        for row in range(rows):
            if row == r: continue
            if M[row, col] % mod != 0:
                factor = M[row, col] % mod
                M[row] = (M[row] - factor * M[r]) % mod
        r += 1
    return r

L_basis = build_L_basis()
print(f"L basis: {len(L_basis)} matrices, each 9x9")

# Verify L_basis are linearly independent mod p
L_vecs = np.array([B.ravel() for B in L_basis], dtype=int)
print(f"L rank mod {p}: {modp_rank(L_vecs, p)}")

# ======================================================================
# 1. Positive control: naive_27 tau decomposition
# ======================================================================
print("\n=== Naive 27-term scheme as positive control ===")

# naive_27: t_l = e_{ij} ⊗ e_{jk} ⊗ e_{ki} for i,j,k ∈ {0,1,2}
# In our u,v,w convention (using entrywise pairing):
#   u_l = e_{ij} (as 3×3 matrix = a_{l}), 
#   v_l = e_{jk}, w_l = e_{ki}
# In K^9 (flattening row-major): e_{ij} → unit vector e_{3i+j}

naive_pairs = []
fixed_indices = []
free_orbit_indices = []

for i in range(3):
    for j in range(3):
        for k in range(3):
            v = np.zeros(9, dtype=int); v[3*j + k] = 1  # e_{jk}
            w = np.zeros(9, dtype=int); w[3*k + i] = 1  # e_{ki}
            
            # Check if this is tau-fixed: v = w means e_{jk} = e_{ki}
            # i.e. j=k and k=i, so i=j=k
            is_fixed = (i == j == k)
            
            naive_pairs.append((v, w))
            if is_fixed:
                fixed_indices.append(len(naive_pairs)-1)
            else:
                # Group into orbits: (i,j,k) and (j,i,k) are a tau-pair
                # Actually: tau swaps factors 2,3, which means v↔w^T
                # The tau partner of term (i,j,k) is (i,k,j) [swapping j,k roles]
                # Wait - need to be more careful with the actual tau action
                pass

# For naive_27, the 27 rank-1 matrices are e_{jk} e_{ki}^T
# The tau-pair structure: the transpose of e_{jk} e_{ki}^T is e_{ki} e_{jk}^T
# So term (i,j,k) is tau-paired with term (j,i,k) [no, need to work this out]
# Actually for tau: (u,v,w) → (u^T, w^T, v^T), so the rank-1 contribution
# v w^T → (w^T)(v^T)^T = w^T v... no, let me think again.

# The unified view: each term contributes v_l w_l^T to the span.
# For naive_27, term (i,j,k): v = e_{jk}, w = e_{ki}, so v w^T = e_{jk} e_{ki}^T

# Check containment
contained = check_containment(naive_pairs, L_basis, mod=p)
print(f"  naive_27 pairs contain L: {contained}")

# Also check rank of the span
all_vecs = np.array([np.outer(v, w).ravel() for v, w in naive_pairs], dtype=int) % p
span_rank = modp_rank(all_vecs, p)
print(f"  Span rank of 27 pairs: {span_rank} (should be >= 9)")

# ======================================================================
# 2. Tau-orbit structure of naive_27
# ======================================================================
print("\n=== Tau-orbit structure ===")

# For tau-invariant decomposition:
# Fixed: v = w (i.e. e_{jk} = e_{ki} ↔ j=k=i), giving 3 terms
# Wait, that's not right. Let me use the correct tau action.

# tau acts on terms as: (u,v,w) → (u^T, w^T, v^T)
# So (e_{ij}, e_{jk}, e_{ki}) → (e_{ji}, e_{ik}, e_{kj})
# This is the term (j,i,k) → wait, we need (e_{ji}, e_{ik}, e_{kj})
# to be of the form (e_{ab}, e_{bc}, e_{ca}): a=j, b=i, c=k → yes, term (j,i,k)

# So tau maps term (i,j,k) to term (j,i,k).
# Fixed iff i=j, giving 9 fixed terms: (i,i,k) for i,k ∈ {0,1,2}
# Free orbits: {(i,j,k), (j,i,k)} for i≠j, giving 9 orbits

fixed = [(i,j,k) for i in range(3) for j in range(3) for k in range(3) if i==j]
free_pairs = []
seen = set()
for i in range(3):
    for j in range(3):
        for k in range(3):
            if i == j: continue
            trip = (i,j,k)
            partner = (j,i,k)
            key = tuple(sorted([trip, partner]))
            if key not in seen:
                seen.add(key)
                free_pairs.append((trip, partner))

print(f"  Fixed terms (i=j): {len(fixed)}")
print(f"  Free orbits (i≠j): {len(free_pairs)}")
print(f"  Total rank: {len(fixed)} + 2*{len(free_pairs)} = {len(fixed) + 2*len(free_pairs)}")

# For each free orbit, the v w^T matrix is:
# Term (i,j,k): e_{jk} e_{ki}^T 
# Partner (j,i,k): e_{ik} e_{kj}^T = (e_{jk} e_{ki}^T)^T
# So the pair contributes {M, M^T}, exactly a tau-pair.

# ======================================================================
# 3. Search for rank-22 tau configurations
# ======================================================================
print("\n=== Rank-22 search: unified containment ===")

# For rank-22 with f fixed + m free: f + 2m = 22, N = f + m
# Pairs: f symmetric (v,v) and m general (v,w)+(w,v)
# Need span{v_i v_i^T, v_j w_j^T, w_j v_j^T} ⊇ L

# The review says: don't optimize by m0 or N_G separately.
# Instead, search directly for (v,w) configurations passing containment.

# Key insight: once (v,w) are fixed, u is determined linearly.
# So we only need to search over 18 params per free orbit (9+9)
# and 9 params per fixed term.

# Random search over various skeletons
np.random.seed(2024)

results = {
    "naive27_control": {
        "contained": bool(contained),
        "span_rank": int(span_rank),
        "f": len(fixed),
        "m": len(free_pairs),
        "N": len(fixed) + len(free_pairs)
    },
    "searches": {}
}

for f, m in [(0,11), (2,10), (4,9), (6,8), (8,7), (10,6)]:
    N = f + m
    if f + 2*m != 22: continue
    
    n_trials = 2000
    successes = 0
    best_defect = 9  # worst case: L not contained at all
    
    for trial in range(n_trials):
        pairs = []
        
        # Fixed terms: random v, pair = (v, v)
        for _ in range(f):
            v = np.random.randint(0, p, 9) 
            pairs.append((v, v))
        
        # Free orbits: random (v, w) + (w, v)
        for _ in range(m):
            v = np.random.randint(0, p, 9)
            w = np.random.randint(0, p, 9)
            pairs.append((v, w))
            pairs.append((w, v))
        
        # Check containment
        all_vecs = np.array([np.outer(v, w).ravel() % p for v, w in pairs], dtype=int) % p
        L_vecs_int = np.array([B.ravel() for B in L_basis], dtype=int)
        AB = np.vstack([all_vecs, L_vecs_int]) % p
        rA = modp_rank(all_vecs, p)
        rAB = modp_rank(AB, p)
        defect = rAB - rA
        
        if defect < best_defect:
            best_defect = defect
        if defect == 0:
            successes += 1
    
    rate = successes / n_trials
    results["searches"][f"f{f}_m{m}"] = {
        "f": f, "m": m, "N": N, "trials": n_trials,
        "successes": successes, "rate": rate, 
        "best_defect": int(best_defect)
    }
    print(f"  (f={f:2d}, m={m:2d}): {successes}/{n_trials} ({rate:.4f}), best defect={best_defect}")

# ======================================================================
# 4. Targeted search: cross-direction products for anti + diagonal for Gram
# ======================================================================
print("\n=== Structured search: cross-direction products ===")

# The key structural insight: 
# Single-row-direction products (u_a ⊗ x)(u_b ⊗ y)^T = (u_a u_b^T) ⊗ (x y^T)
# These have v ∧ w component in Sym²U ⊗ Λ²C only (zero in Λ²U ⊗ Sym²C).
# But the anti target lies in Λ²U ⊗ Sym²C. So we MUST have cross-direction products.

# Strategy: use standard row vectors u_0=(1,0,0), u_1=(0,1,0), u_2=(0,0,1)
# and place products (u_a ⊗ x_j, u_b ⊗ y_j) with a ≠ b for anti coverage.

# For each cross-direction pair (a,b), the M_{ab} component of v∧w is
# v_a ⊙ w_b - v_b ⊙ w_a (using the row decomposition v = (v_0, v_1, v_2) etc.)

# The anti target requires spanning theta_01, theta_02, theta_12 where
# theta_{ab} = -sum_k e_{ak} ∧ e_{bk}
# In the (Λ²U ⊗ Sym²C) component, this becomes e_a ∧ e_b ⊗ q where q = sum_k e_k ⊗ e_k

# A cross-direction product with row indices (a,b), column vectors x, y:
# v = u_a ⊗ x, w = u_b ⊗ y
# v ∧ w has Λ²U⊗Sym²C component: (u_a ∧ u_b) ⊗ (x ⊙ y)
# And Sym²U⊗Λ²C component: (u_a ⊙ u_b) ⊗ (x ∧ y)

# To hit the anti target, we need x ⊙ y = q = sum e_k ⊗ e_k (the identity in Sym²C)
# This requires at least 2 products per (a,b) pair (since rank of single x⊙y ≤ 2 
# while q has rank 3).

# The cheapest anti construction: 6 cross-direction free orbits covering 3 pairs
# plus additional terms for Gram.

# Actually, with the identity q in 3D: the minimum number of decomposable symmetric
# matrices spanning a 3-dim containing q is... this connects to the literature.

# Let's test the "polarization + cross-direction" approach:
# 6 cross-direction free orbits (2 per pair) for anti
# 6 fixed terms for diagonal Gram
# Total: f=6, m=6, rank = 6 + 12 = 18 (too few for 22!)

# Need m ≥ 7 (from A-wedge bound) free orbits.
# For rank 22: f + 2m = 22 with m ≥ 7 → f ≤ 8.

# Let's try: 8 fixed + 7 free = rank 22
# 7 free orbits must cover L_anti, which needs m ≥ 7.
# And 8 fixed + Gram parts of 7 free must cover L_sym.

sqrti = None
for x in range(1, p):
    if (x * x) % p == p - 1:
        sqrti = x
        break

print(f"sqrt(-1) mod {p} = {sqrti}")

# Structured construction attempt
n_struct_trials = 5000
struct_successes = 0

for trial in range(n_struct_trials):
    pairs = []
    
    # Strategy: 8 fixed terms in "diagonal" positions
    for _ in range(8):
        v = np.random.randint(0, p, 9)
        pairs.append((v, v))
    
    # 7 free orbits: cross-direction for anti coverage
    for _ in range(7):
        # Random cross-direction: pick two row indices a, b
        a, b = sorted(np.random.choice(3, 2, replace=False))
        x = np.random.randint(0, p, 3)
        y = np.random.randint(0, p, 3)
        v = np.zeros(9, dtype=int)
        w = np.zeros(9, dtype=int)
        v[3*a:3*a+3] = x
        w[3*b:3*b+3] = y
        pairs.append((v % p, w % p))
        pairs.append((w % p, v % p))
    
    all_vecs = np.array([np.outer(v, w).ravel() % p for v, w in pairs], dtype=int) % p
    L_vecs_int = np.array([B.ravel() for B in L_basis], dtype=int)
    AB = np.vstack([all_vecs, L_vecs_int]) % p
    rA = modp_rank(all_vecs, p)
    rAB = modp_rank(AB, p)
    if rAB == rA:
        struct_successes += 1

rate = struct_successes / n_struct_trials
print(f"  (f=8, m=7, cross-direction free): {struct_successes}/{n_struct_trials} ({rate:.4f})")
results["searches"]["f8_m7_crossdir"] = {
    "f": 8, "m": 7, "trials": n_struct_trials,
    "successes": struct_successes, "rate": rate
}

# Also try general random for comparison
gen_successes = 0
for trial in range(n_struct_trials):
    pairs = []
    for _ in range(8):
        v = np.random.randint(0, p, 9)
        pairs.append((v, v))
    for _ in range(7):
        v = np.random.randint(0, p, 9)
        w = np.random.randint(0, p, 9)
        pairs.append((v, w))
        pairs.append((w, v))
    
    all_vecs = np.array([np.outer(v, w).ravel() % p for v, w in pairs], dtype=int) % p
    L_vecs_int = np.array([B.ravel() for B in L_basis], dtype=int)
    AB = np.vstack([all_vecs, L_vecs_int]) % p
    rA = modp_rank(all_vecs, p)
    rAB = modp_rank(AB, p)
    if rAB == rA:
        gen_successes += 1

rate2 = gen_successes / n_struct_trials
print(f"  (f=8, m=7, general random):       {gen_successes}/{n_struct_trials} ({rate2:.4f})")
results["searches"]["f8_m7_general"] = {
    "f": 8, "m": 7, "trials": n_struct_trials,
    "successes": gen_successes, "rate": rate2
}

out_path = DATA_DIR / "unified_containment_search.json"
with open(out_path, 'w') as f:
    json.dump(results, f, indent=2, default=lambda o: int(o) if isinstance(o, (np.integer,)) else float(o))
print(f"\nSAVED {out_path}")
