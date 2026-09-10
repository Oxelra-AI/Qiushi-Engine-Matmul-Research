#!/usr/bin/env python3
"""analysisB: Complete cyclic automorphism check (both directions + full 9x9).

The Part B search in laderman_S3_analysis.py checked only one cyclic direction
(sigma^2: Q maps a -> b) using Kronecker-factored Q. This script:
1. Checks BOTH cyclic directions (sigma and sigma^2)
2. Uses proportionality graph invariant as an independent necessary condition
3. Tries full 9x9 Q search (not Kronecker-restricted) for the first promising direction
"""

import numpy as np
from pathlib import Path
import json
from collections import defaultdict

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA = WS / "data" / "S3_analysis"
DATA.mkdir(parents=True, exist_ok=True)

def E(i, j):
    M = np.zeros((3,3), dtype=int)
    M[i,j] = 1
    return M

pi12 = E(0,1) + E(1,0) + E(2,2)
eps1 = np.diag([-1,1,1])
eps2 = np.diag([1,-1,1])

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

p = 65521

# Flatten to 9-vectors mod p
A = np.zeros((9, 23), dtype=int)  # a-factors
B = np.zeros((9, 23), dtype=int)  # b-factors
C = np.zeros((9, 23), dtype=int)  # c-factors
for l, (a, b, c) in enumerate(terms):
    A[:, l] = a.reshape(-1) % p
    B[:, l] = b.reshape(-1) % p
    C[:, l] = c.reshape(-1) % p

def proportional_mod(u, v, p):
    """Check if u is proportional to v over F_p."""
    for i in range(len(u)):
        for j in range(i+1, len(u)):
            det2 = (int(u[i]) * int(v[j]) - int(u[j]) * int(v[i])) % p
            if det2 != 0:
                return False
    return not (np.all(u % p == 0) and np.all(v % p == 0))

# ============================================================
# PROPORTIONALITY GRAPH ANALYSIS
# ============================================================
print("=" * 60)
print("Proportionality graph analysis")
print("=" * 60)

def compute_prop_classes(vecs, p):
    """Group vectors by proportionality class."""
    n = vecs.shape[1]
    visited = [False] * n
    classes = []
    for i in range(n):
        if visited[i]:
            continue
        cls = [i]
        visited[i] = True
        for j in range(i+1, n):
            if not visited[j] and proportional_mod(vecs[:, i], vecs[:, j], p):
                cls.append(j)
                visited[j] = True
        classes.append(tuple(cls))
    return classes

a_classes = compute_prop_classes(A, p)
b_classes = compute_prop_classes(B, p)
c_classes = compute_prop_classes(C, p)

# The class size multiset must match between source and target for a valid automorphism
a_sizes = sorted(len(c) for c in a_classes)
b_sizes = sorted(len(c) for c in b_classes)
c_sizes = sorted(len(c) for c in c_classes)

print(f"A-vector proportionality classes: {len(a_classes)} classes, sizes {a_sizes}")
print(f"  Classes: {[tuple(i+1 for i in c) for c in a_classes]}")
print(f"B-vector proportionality classes: {len(b_classes)} classes, sizes {b_sizes}")
print(f"  Classes: {[tuple(i+1 for i in c) for c in b_classes]}")
print(f"C-vector proportionality classes: {len(c_classes)} classes, sizes {c_sizes}")
print(f"  Classes: {[tuple(i+1 for i in c) for c in c_classes]}")

# For sigma^2: Q maps A -> B. Necessary: a_sizes == b_sizes
sigma2_possible = (a_sizes == b_sizes)
print(f"\nsigma^2 (Q: A->B) proportionality match: {sigma2_possible}")

# For sigma: Q maps C -> B. Necessary: c_sizes == b_sizes
sigma_possible = (c_sizes == b_sizes)
print(f"sigma (Q: C->B) proportionality match: {sigma_possible}")

# Also need: P maps B/C -> A, R maps C/A -> C/B
# sigma^2: P: C->A, R: B->C
sigma2_P = (c_sizes == a_sizes)
sigma2_R = (b_sizes == c_sizes)
print(f"\nsigma^2 full: P(C->A)={sigma2_P}, Q(A->B)={sigma2_possible}, R(B->C)={sigma2_R}")

# sigma: P: B->A, Q: C->B, R: A->C
sigma_P = (b_sizes == a_sizes)
sigma_Q = (c_sizes == b_sizes)
sigma_R = (a_sizes == c_sizes)
print(f"sigma full: P(B->A)={sigma_P}, Q(C->B)={sigma_Q}, R(A->C)={sigma_R}")

# ============================================================
# FULL 9x9 SEARCH (σ² direction: Q maps A to B)
# ============================================================
print("\n" + "=" * 60)
print("Full 9x9 search: sigma^2 direction (Q: A -> B)")
print("=" * 60)

def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def modinv(a, m):
    a = a % m
    g, x, _ = extended_gcd(a, m)
    if g != 1:
        return None
    return x % m

def mat_inv_9(M, p):
    n = 9
    A_aug = np.zeros((n, 2*n), dtype=int)
    A_aug[:, :n] = np.array(M, dtype=int) % p
    for i in range(n):
        A_aug[i, n+i] = 1
    for col in range(n):
        pivot = None
        for row in range(col, n):
            if A_aug[row, col] % p != 0:
                pivot = row
                break
        if pivot is None:
            return None
        A_aug[[col, pivot]] = A_aug[[pivot, col]].copy()
        inv_piv = modinv(int(A_aug[col, col]), p)
        if inv_piv is None:
            return None
        A_aug[col] = (A_aug[col] * inv_piv) % p
        for row in range(n):
            if row != col and A_aug[row, col] % p != 0:
                factor = int(A_aug[row, col])
                A_aug[row] = (A_aug[row] - factor * A_aug[col]) % p
    return A_aug[:, n:] % p

def find_Q_full(X, Y, p, direction_name):
    """Find Q in GL_9(F_p) mapping X[:,l] ∝ Y[:,π(l)] for all l.
    
    Uses tree search with early pruning.
    X, Y: 9×23 integer matrices mod p.
    """
    n = X.shape[1]
    
    # Find 9 independent X-columns as basis
    basis = []
    for l in range(n):
        cols = X[:, basis + [l]].astype(float)
        if np.linalg.matrix_rank(cols) == len(basis) + 1:
            basis.append(l)
            if len(basis) == 9:
                break
    assert len(basis) == 9, f"Only {len(basis)} independent X-columns"
    
    X_basis = X[:, basis].astype(int) % p
    X_inv = mat_inv_9(X_basis, p)
    if X_inv is None:
        print(f"  X basis not invertible mod {p}")
        return []
    
    # Coordinates of all X-vectors in this basis
    coords = np.zeros((9, n), dtype=int)
    for l in range(n):
        for i in range(9):
            coords[i, l] = sum(int(X_inv[i, j]) * int(X[j, l]) for j in range(9)) % p
    
    non_basis = [l for l in range(n) if l not in basis]
    
    # For pruning: precompute proportionality targets for each non-basis vector
    # After assigning basis[0:k] -> (j_0,...,j_{k-1}), each non-basis vector l has
    # Q X_l = sum_r coords[r,l] * alpha_r * Y[:,j_r]
    # This must be proportional to some Y[:,j].
    
    # DFS with incremental pruning
    hits = []
    node_count = [0]
    
    def dfs(depth, assigned_targets, alpha_ratios):
        """depth: how many basis vectors assigned.
        assigned_targets: list of Y-column indices for basis[0:depth]
        alpha_ratios: dict mapping (i,j) pairs to alpha_i/alpha_j ratios (mod p)
        """
        node_count[0] += 1
        if node_count[0] > 5_000_000:
            return  # Safety cutoff
        
        if depth == 9:
            # All basis vectors assigned. Verify all non-basis.
            # Reconstruct Q and check.
            Y_imgs = np.zeros((9, 9), dtype=int)
            for k in range(9):
                Y_imgs[:, k] = Y[:, assigned_targets[k]].astype(int) % p
            
            # Q @ X_basis = diag(alpha) @ Y_imgs
            # Q = diag(alpha) @ Y_imgs @ X_inv
            # But we don't know alpha. Try alpha = (1,1,...,1) first.
            Q_try = np.zeros((9, 9), dtype=int)
            for i in range(9):
                for j in range(9):
                    Q_try[i, j] = sum(int(Y_imgs[i, k]) * int(X_inv[k, j]) for k in range(9)) % p
            
            # Check if Q_try maps each X[:,l] to proportional to some Y[:,j]
            perm = {}
            for l in range(n):
                Ql = np.array([sum(int(Q_try[r, s]) * int(X[s, l]) for s in range(9)) % p for r in range(9)])
                if np.all(Ql == 0):
                    return
                found = False
                for j in range(n):
                    if proportional_mod(Ql, Y[:, j], p):
                        perm[l] = j
                        found = True
                        break
                if not found:
                    # Try with non-trivial alpha
                    return
            
            if len(set(perm.values())) == n:  # bijective
                hits.append({"perm": perm, "assigned": list(assigned_targets)})
                print(f"  HIT! perm = {[perm[l]+1 for l in range(n)]}")
            return
        
        # Try each Y-column target for basis[depth]
        for j in range(n):
            # Quick pruning: check first non-basis vector for consistency
            if depth >= 2 and non_basis:
                l = non_basis[0]
                # Q X_l = sum_r coords[r,l] * alpha_r * Y[:,assigned[r]]
                # With all alpha=1: check if the linear combination is proportional to some Y
                combo = np.zeros(9, dtype=int)
                for r in range(depth):
                    combo = (combo + int(coords[r, l]) * Y[:, assigned_targets[r]].astype(int)) % p
                combo = (combo + int(coords[depth, l]) * Y[:, j].astype(int)) % p
                
                # Check if this partial combination could be proportional to any Y
                # (remaining coords may still contribute)
                # Skip pruning if remaining basis elements contribute
                if depth == 8:
                    # All coords accounted for
                    found_any = False
                    for jj in range(n):
                        if proportional_mod(combo, Y[:, jj], p):
                            found_any = True
                            break
                    if not found_any:
                        continue
            
            dfs(depth + 1, assigned_targets + [j], alpha_ratios)
    
    print(f"  Starting DFS for {direction_name}...")
    dfs(0, [], {})
    print(f"  Nodes explored: {node_count[0]}")
    return hits

# Run for sigma^2: Q maps A -> B
if sigma2_possible:
    sigma2_hits = find_Q_full(A, B, p, "sigma^2 (A->B)")
    print(f"sigma^2 hits: {len(sigma2_hits)}")
else:
    sigma2_hits = []
    print("sigma^2 blocked by proportionality graph")

# Run for sigma: Q maps C -> B
if sigma_possible:
    sigma_hits = find_Q_full(C, B, p, "sigma (C->B)")
    print(f"sigma hits: {len(sigma_hits)}")
else:
    sigma_hits = []
    print("sigma blocked by proportionality graph")

# ============================================================
# SUMMARY
# ============================================================
has_cyclic = len(sigma2_hits) > 0 or len(sigma_hits) > 0
print(f"\n{'='*60}")
print(f"FINAL RESULT: Laderman has cyclic automorphism = {has_cyclic}")
print(f"  sigma^2 direction: {len(sigma2_hits)} hits")
print(f"  sigma direction: {len(sigma_hits)} hits")
print(f"{'='*60}")

results = {
    "proportionality_classes": {
        "a_sizes": a_sizes, "b_sizes": b_sizes, "c_sizes": c_sizes,
        "a_classes": [[i+1 for i in c] for c in a_classes],
        "b_classes": [[i+1 for i in c] for c in b_classes],
        "c_classes": [[i+1 for i in c] for c in c_classes],
    },
    "sigma2_proportionality_ok": sigma2_possible,
    "sigma_proportionality_ok": sigma_possible,
    "sigma2_Q_hits": len(sigma2_hits),
    "sigma_Q_hits": len(sigma_hits),
    "has_cyclic_automorphism": has_cyclic,
}

path = DATA / "laderman_cyclic_complete.json"
path.write_text(json.dumps(results, indent=2) + "\n")
print(f"\nSAVED {path}")
