#!/usr/bin/env python3
"""analysisC: Correct L_sym projection of fixed terms at Laderman witness.

Key insight from quotient_structure: free symmetric products have zero 
L_sym quotient (they lie entirely in F). So the 6-dimensional L_sym must be 
covered entirely by the 7 fixed terms' projections. This script computes the 
PROJECTION onto L_sym (not membership test) for each fixed term and free 
symmetric product.
"""
import numpy as np
import json
from pathlib import Path

P = 65521; IROOT = 41224
WS = Path(__file__).resolve().parent.parent
DATA = WS / "data" / "two_sector"

def mod(x): return np.asarray(x, dtype=object) % P
def inv_mod(a): return pow(int(a) % P, -1, P)

def rref_mod(M):
    M = mod(M).copy(); m, n = M.shape; r = 0; pivs = []
    for c in range(n):
        piv = next((i for i in range(r, m) if int(M[i,c]) % P), None)
        if piv is None: continue
        if piv != r: M[[r, piv]] = M[[piv, r]]
        M[r,:] = (M[r,:] * inv_mod(M[r,c])) % P
        for i in range(m):
            if i != r and int(M[i,c]) % P:
                M[i,:] = (M[i,:] - M[i,c] * M[r,:]) % P
        pivs.append(c); r += 1
    return M, r, pivs

def rank_mod(M): return rref_mod(M)[1]
def nullspace_mod(M):
    R, r, pivs = rref_mod(M)
    n = M.shape[1]; pset = set(pivs)
    free = [c for c in range(n) if c not in pset]
    out = []
    for f in free:
        x = np.zeros(n, dtype=object); x[f] = 1
        for ri, pc in enumerate(pivs): x[pc] = (-R[ri, f]) % P
        out.append(x % P)
    return np.vstack(out) % P if out else np.zeros((0, n), dtype=object)

# Build L_1, L_sym, L_anti
L1_vecs = []
for a in range(3):
    for b in range(3):
        row = np.zeros(81, dtype=object)
        for k in range(3):
            row[9*(3*b+k) + (3*k+a)] = 1
        L1_vecs.append(row)
L1 = np.vstack(L1_vecs)

sym_vecs, anti_vecs = [], []
for a in range(3):
    sym_vecs.append(L1_vecs[3*a+a])
for a in range(3):
    for b in range(a+1, 3):
        sym_vecs.append((L1_vecs[3*a+b] + L1_vecs[3*b+a]) % P)
        anti_vecs.append((L1_vecs[3*a+b] - L1_vecs[3*b+a]) % P)
L_sym = mod(np.vstack(sym_vecs)); L_anti = mod(np.vstack(anti_vecs))

# Transport Laderman
src = (WS/"scripts"/"laderman_tau_decomp.py").read_text()
prefix = src.split('print(f"Sum matches T333')[0]
ns = {"__file__": str(WS/"scripts"/"laderman_tau_decomp.py"), "__name__": "defs_only"}
exec(compile(prefix, str(WS/"scripts"/"laderman_tau_decomp.py"), "exec"), ns)
terms = [(mod(a), mod(b), mod(c)) for a, b, c in ns['terms']]
eps1, pi12 = mod(ns['eps1']), mod(ns['pi12'])
def mat_inv(A):
    A = mod(A); n = A.shape[0]
    aug = np.concatenate([A, np.eye(n, dtype=object)], axis=1) % P
    for c in range(n):
        piv = next(i for i in range(c, n) if int(aug[i,c]) % P)
        if piv != c: aug[[c, piv]] = aug[[piv, c]]
        aug[c,:] = (aug[c,:] * inv_mod(aug[c,c])) % P
        for i in range(n):
            if i != c and int(aug[i,c]) % P:
                aug[i,:] = (aug[i,:] - aug[i,c]*aug[c,:]) % P
    return aug[:, n:] % P
Q_mat = (eps1 @ pi12) % P; R_mat = np.diag([IROOT, 1, 1]).astype(object) % P
Qinv = mat_inv(Q_mat); Rinv = mat_inv(R_mat)
transported = [(a @ Qinv % P, Q_mat @ b @ Rinv % P, R_mat @ c % P) for a, b, c in terms]

free_pairs = [(1,4),(2,5),(6,15),(7,17),(8,16),(10,13),(12,14),(19,21)]
free_indices = [i for p in free_pairs for i in p]
fixed_indices = [i for i in range(23) if i not in free_indices]

def vec9(M): return mod(M).reshape(9)

# Build F and fixed/sym-prod matrices
F_vecs = []
for idx in free_indices:
    _, b, c = transported[idx]
    F_vecs.append(np.outer(vec9(b), vec9(c)).reshape(81) % P)
F = mod(np.vstack(F_vecs))

fixed_vecs = []
for idx in fixed_indices:
    _, b, c = transported[idx]
    fixed_vecs.append(np.outer(vec9(b), vec9(c)).reshape(81) % P)

sym_prods = []
for i1, i2 in free_pairs:
    _, b1, c1 = transported[i1]
    _, b2, c2 = transported[i2]
    s = (np.outer(vec9(b1), vec9(c1)).reshape(81) + np.outer(vec9(b2), vec9(c2)).reshape(81)) % P
    sym_prods.append(s)

# Quotient via F nullspace
N_F = nullspace_mod(F)  # 65 x 81
L_sym_q = mod(L_sym @ N_F.T)  # 6 x 65 (L_sym in quotient)
fixed_q = mod(np.vstack(fixed_vecs) @ N_F.T)  # 7 x 65
sym_q = mod(np.vstack(sym_prods) @ N_F.T)     # 8 x 65

# RREF of L_sym in quotient to get pivot positions
Lsq_rref, rk_Lsq, Lsq_pivs = rref_mod(L_sym_q)
print(f"L_sym quotient rank = {rk_Lsq}, pivots at columns {Lsq_pivs}")

# PROJECT each vector onto L_sym using RREF pivot extraction
# For RREF R with pivots c_1,...,c_6: projection alpha = (v[c_1], ..., v[c_6])
def project_onto_Lsym(v):
    """Return 6-vector of L_sym coordinates via RREF pivot extraction."""
    return np.array([int(v[c]) % P for c in Lsq_pivs], dtype=object) % P

print("\n=== Fixed terms' L_sym projections ===")
fixed_Lsym = []
for fi, fv in enumerate(fixed_vecs):
    fq = fixed_q[fi]
    alpha = project_onto_Lsym(fq)
    fixed_Lsym.append(alpha)
    print(f"  Fixed {fixed_indices[fi]+1}: L_sym proj = {[int(x) for x in alpha]}")

fixed_Lsym_mat = mod(np.vstack(fixed_Lsym))  # 7 x 6
rk_fixed_Lsym = rank_mod(fixed_Lsym_mat)
print(f"\nFixed L_sym projection rank = {rk_fixed_Lsym}")

print("\n=== Free sym products' L_sym projections ===")
sym_Lsym = []
for si, sv in enumerate(sym_prods):
    sq = sym_q[si]
    alpha = project_onto_Lsym(sq)
    sym_Lsym.append(alpha)
    if any(int(x) % P for x in alpha):
        print(f"  Free pair {free_pairs[si]}: L_sym proj = {[int(x) for x in alpha]} (NONZERO!)")
sym_Lsym_mat = mod(np.vstack(sym_Lsym))
rk_sym_Lsym = rank_mod(sym_Lsym_mat)
print(f"Free sym L_sym projection rank = {rk_sym_Lsym}")

# Combined
all_Lsym = mod(np.vstack([fixed_Lsym_mat, sym_Lsym_mat]))
rk_all = rank_mod(all_Lsym)
print(f"\nCombined (fixed + free_sym) L_sym projection rank = {rk_all}")

# Relation among fixed L_sym projections
if rk_fixed_Lsym < 7:
    null_rel = nullspace_mod(fixed_Lsym_mat)
    print(f"\nRelations among fixed L_sym projections: {null_rel.shape[0]}")
    for ni in range(null_rel.shape[0]):
        nv = null_rel[ni]
        print(f"  Relation {ni}: {[int(x) for x in nv]}")
        nz = sum(1 for x in nv if int(x) % P)
        print(f"    Nonzero coefficients: {nz}/7")
        terms_rel = [(fixed_indices[j]+1, int(nv[j])) for j in range(7) if int(nv[j]) % P]
        print(f"    Support: {terms_rel}")

# Deletion analysis with CORRECT projections
print("\n=== Deletion analysis (correct projection) ===")
for fi in range(7):
    remaining = [fixed_Lsym[j] for j in range(7) if j != fi]
    # Also add free_sym contributions (should be zero, but include for completeness)
    remaining_mat = mod(np.vstack(remaining + [a for a in sym_Lsym]))
    rk = rank_mod(remaining_mat)
    deficit = 6 - rk
    print(f"  Delete fixed {fixed_indices[fi]+1}: L_sym rank = {rk}, deficit = {deficit}")

# Verify total coverage
print(f"\n=== Verification ===")
# F + all terms should contain L_1
all_terms = mod(np.vstack(F_vecs + fixed_vecs + [sp for sp in sym_prods]))
FL1 = mod(np.vstack([all_terms, L1]))
print(f"dim(all terms + L_1) = {rank_mod(FL1)} (should be 23)")

# Check: does fixed_Lsym_mat span all of R^6?
print(f"Fixed L_sym projection spans all L_sym: {rk_fixed_Lsym == 6}")

out = {
    "fixed_Lsym_rank": int(rk_fixed_Lsym),
    "free_sym_Lsym_rank": int(rk_sym_Lsym),
    "combined_Lsym_rank": int(rk_all),
    "fixed_Lsym_coords": [[int(x) for x in row] for row in fixed_Lsym],
    "fixed_Lsym_pivots": Lsq_pivs,
}
out_path = DATA / "correct_Lsym_projection.json"
out_path.write_text(json.dumps(out, indent=2) + "\n")
print(f"\nSAVED {out_path}")
