#!/usr/bin/env python3
"""analysisB: Laderman two-sector decomposition — quotient structure analysis.

Computes at the transported Laderman (7,8) witness:
1. Free symmetric quotient rank (how much of L_sym the 8 free orbits already cover)
2. Fixed quotient images in L_sym and their relation
3. Whether the one-dimensional relation has full support (all 7 coefficients nonzero)
4. Deformation direction: does a generic anti-containment-preserving perturbation
   of the free pairs change the symmetric coverage?
"""
import numpy as np
import json
from pathlib import Path

P = 65521; IROOT = 41224
WS = Path(__file__).resolve().parent.parent
DATA = WS / "data" / "two_sector"
DATA.mkdir(parents=True, exist_ok=True)

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

# ================================================================
# Build L_1, L_sym, L_anti
# ================================================================
L1_vecs = []
for a in range(3):
    for b in range(3):
        row = np.zeros(81, dtype=object)
        for k in range(3):
            row[9*(3*b+k) + (3*k+a)] = 1
        L1_vecs.append(row)
L1 = np.vstack(L1_vecs)

# L_sym basis: B_{aa} for a=0,1,2 and (B_{ab}+B_{ba})/2 for a<b
# L_anti basis: (B_{ab}-B_{ba})/2 for a<b
sym_vecs, anti_vecs = [], []
for a in range(3):
    sym_vecs.append(L1_vecs[3*a+a])
for a in range(3):
    for b in range(a+1, 3):
        sym_vecs.append((L1_vecs[3*a+b] + L1_vecs[3*b+a]) % P)
        anti_vecs.append((L1_vecs[3*a+b] - L1_vecs[3*b+a]) % P)
L_sym = mod(np.vstack(sym_vecs))   # 6 x 81
L_anti = mod(np.vstack(anti_vecs)) # 3 x 81

# ================================================================
# Load and transport Laderman
# ================================================================
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
def transport(a, b, c): return (a @ Qinv % P, Q_mat @ b @ Rinv % P, R_mat @ c % P)
transported = [transport(a, b, c) for a, b, c in terms]

free_pairs = [(1,4),(2,5),(6,15),(7,17),(8,16),(10,13),(12,14),(19,21)]
free_indices = [i for p in free_pairs for i in p]
fixed_indices = [i for i in range(23) if i not in free_indices]

def vec9(M): return mod(M).reshape(9)

# ================================================================
# Build free span F, fixed span, symmetric/antisymmetric products
# ================================================================
F_vecs = []
for idx in free_indices:
    _, b, c = transported[idx]
    F_vecs.append(np.outer(vec9(b), vec9(c)).reshape(81) % P)
F = mod(np.vstack(F_vecs))  # 16 x 81

fixed_vecs = []
for idx in fixed_indices:
    _, b, c = transported[idx]
    fixed_vecs.append(np.outer(vec9(b), vec9(c)).reshape(81) % P)
fixed_mat = mod(np.vstack(fixed_vecs))  # 7 x 81

# Free symmetric products: for each pair (i1,i2), sym = vec(b1)vec(c1)^T + vec(b2)vec(c2)^T
sym_prods = []
for i1, i2 in free_pairs:
    _, b1, c1 = transported[i1]
    _, b2, c2 = transported[i2]
    s = (np.outer(vec9(b1), vec9(c1)).reshape(81) + np.outer(vec9(b2), vec9(c2)).reshape(81)) % P
    sym_prods.append(s)
sym_prods_mat = mod(np.vstack(sym_prods))  # 8 x 81

# ================================================================
# Quotient analysis: project everything modulo F
# ================================================================
rk_F = rank_mod(F)
print(f"dim F = {rk_F}")

# Free symmetric quotient rank
rk_F_sym = rank_mod(mod(np.vstack([F, sym_prods_mat])))
free_sym_quotient_rank = rk_F_sym - rk_F
print(f"dim(F + free_sym_prods) = {rk_F_sym}")
print(f"Free symmetric quotient rank = {free_sym_quotient_rank}")

# Fixed quotient rank
rk_F_fixed = rank_mod(mod(np.vstack([F, fixed_mat])))
fixed_quotient_rank = rk_F_fixed - rk_F
print(f"dim(F + fixed) = {rk_F_fixed}")
print(f"Fixed quotient rank = {fixed_quotient_rank}")

# Total coverage of L_sym
rk_all_sym = rank_mod(mod(np.vstack([F, sym_prods_mat, fixed_mat, L_sym])))
print(f"dim(F + free_sym + fixed + L_sym) = {rk_all_sym}")

# Verify: does F + fixed + free_sym cover all of L_1?
rk_cover = rank_mod(mod(np.vstack([F, sym_prods_mat, fixed_mat, L1])))
print(f"dim(F + free_sym + fixed + L_1) = {rk_cover} (should be 23 if full coverage)")

# ================================================================
# Fixed term deletion analysis (in quotient)
# ================================================================
print("\n=== Fixed term quotient analysis ===")
# Compute quotient images of fixed terms
# Use the nullspace of F^T to project: x mod F is Q^T x where Q is a basis of F^perp cap (F+L_1)
# Simpler: compute rank(F + fixed_i) - rank(F) for each fixed term i
# And rank(F + all_fixed_except_i) - rank(F) for each deletion

# First, compute the 7 fixed quotient images explicitly via row reduction
# Stack [F; L_sym] and compute a basis for (F+L_1)/F
# Actually, let's compute the quotient representation matrix

# Row reduce F to find a complement basis
F_rref, rk_F, F_pivs = rref_mod(F)
# The quotient (K^81)/F has dimension 81-16=65
# But we only care about the 6-dim quotient (F+L_1)/F = L_sym

# Project L_sym basis onto complement of F
# Stack [F; L_sym] and reduce to find the 6 independent quotient directions
FL_sym = mod(np.vstack([F, L_sym]))  # 22 x 81
rk_FL_sym = rank_mod(FL_sym)
print(f"dim(F + L_sym) = {rk_FL_sym} (should be 22)")

# Project fixed terms onto quotient F+L_sym space
# For each fixed term, compute its image in (F+L_sym)/F
# = unique representation in L_sym modulo F ∩ L_sym = 0

# Represent each fixed term's quotient image as a vector in R^6 (L_sym coords)
# Method: solve fixed_vec = F_part + L_sym_part, where F_part ∈ F and L_sym_part ∈ span(L_sym basis)
# Stack [F^T; L_sym^T] and solve for coefficients

# Actually, simpler: use the fact that F ∩ L_1 = L_anti
# Each fixed term's slice matrix is in the full 23-dim span.
# Its L_sym component is the projection onto L_sym.
# Since L_1 = L_sym ⊕ L_anti and F ∩ L_1 = L_anti,
# the quotient (F+L_1)/F ≅ L_1/(F∩L_1) = L_1/L_anti ≅ L_sym

# For a concrete computation, solve: fixed_vec ≡ sum_j alpha_j * L_sym_basis[j] (mod F)
# This means: fixed_vec - sum_j alpha_j * L_sym_basis[j] ∈ F
# Equivalently: nullspace of [F^T | L_sym^T | fixed_vec] has a specific structure

# Easiest: compute coefficients by augmented row reduction
# [F; L_sym | I_6] -> rref -> read off the L_sym coordinates of the projection

# Let me use a different approach: row-reduce [F; L_sym_basis] to get pivot+free structure,
# then express each fixed_vec in these coordinates

# Actually, the simplest approach: for each fixed_vec, find its coordinates in L_sym
# by computing rank([F; L_sym; fixed_vec]) and solving
# fixed_vec = c_1 F_row_1 + ... + c_16 F_row_16 + d_1 L_sym_1 + ... + d_6 L_sym_6

# Build the system: [F; L_sym]^T x = fixed_vec^T
# This is 81 equations in 22 unknowns

basis_22 = mod(np.vstack([F, L_sym]))  # rows form a basis of F+L_sym (22-dim)
# For each fixed vector, solve basis_22^T x = fixed_vec
# Equivalently: find x such that x . basis_22 = fixed_vec
# Transpose: basis_22^T . x = fixed_vec^T (solving 81 x 22 system for x in R^22)

# Easier: augment [basis_22 | fixed_vec^T] and row reduce
fixed_quotient_coords = []  # each is a 6-vector (the L_sym part)
for fi, fv in enumerate(fixed_vecs):
    aug = mod(np.vstack([basis_22, fv.reshape(1, 81)]))  # 23 x 81
    R, rk, pivs = rref_mod(aug)
    if rk == 22:
        # The last row (fixed_vec) is in span(basis_22)
        # Read off the L_sym coefficients from the back-substitution
        # The coefficients are in the representation of fv in terms of basis_22 rows
        # After rref, the 23rd row should be zero (since rk=22)
        # But we need the actual coefficients...
        pass
    # Alternative: solve the system [F; L_sym] . alpha = fv using left-inverse
    # Since [F; L_sym] has full row rank 22, we need alpha in R^22
    pass

# Simplest: just compute the quotient image coordinates
# For L_sym representation: project fixed_vec onto L_sym modulo F
# This is equivalent to: in the rref of [F; L_sym], the L_sym basis vectors have
# specific pivot positions. The coefficient of each L_sym basis vector in the
# representation of fixed_vec modulo F gives the quotient coordinate.

# Let me use a concrete method: row-reduce [F; L_sym_1; ... ; L_sym_6] to echelon form,
# recording which rows correspond to L_sym directions.
# Then for each fixed_vec, express it in this basis.

# Build [F; L_sym_1; ...; L_sym_6; fixed_1; ...; fixed_7] and track rows
full_system = mod(np.vstack([F, L_sym, fixed_mat]))  # 29 x 81
R_full, rk_full, pivs_full = rref_mod(full_system)
print(f"rank([F; L_sym; fixed]) = {rk_full}")

# After rref, the first 22 rows should span F+L_sym, and the 7 fixed rows
# should have specific relations. Let me check which of the 29 rows survive.
# Track original row origins
origins = ['F']*16 + ['Lsym']*6 + ['fixed']*7
surviving = []
for i in range(min(rk_full, 29)):
    surviving.append((i, origins[i] if i < 29 else '?'))

# Actually, rref permutes rows, so tracking is harder.
# Let me use a different approach: explicit quotient coordinates.

# Method: compute the left null of F (81 x 65 matrix), restrict to L_sym,
# and project fixed terms through this.

# Null space of F: vectors n such that F . n = 0 (as 16 equations in 81 unknowns)
N_F = nullspace_mod(F)  # (81-16) x 81 = 65 x 81
print(f"dim null(F) = {N_F.shape[0]}")

# Project L_sym basis onto null(F): L_sym_proj[i] = N_F @ L_sym[i]
L_sym_proj = mod(L_sym @ N_F.T)  # 6 x 65
rk_Lsym_proj = rank_mod(L_sym_proj)
print(f"rank of L_sym projected to F-quotient = {rk_Lsym_proj}")

# Project fixed terms onto null(F)
fixed_proj = mod(fixed_mat @ N_F.T)  # 7 x 65
rk_fixed_proj = rank_mod(fixed_proj)
print(f"rank of fixed projected to F-quotient = {rk_fixed_proj}")

# Project free symmetric products onto null(F)
sym_proj = mod(sym_prods_mat @ N_F.T)  # 8 x 65
rk_sym_proj = rank_mod(sym_proj)
print(f"rank of free_sym projected to F-quotient = {rk_sym_proj}")

# Combined: fixed + free_sym in quotient
combined_proj = mod(np.vstack([fixed_proj, sym_proj]))
rk_combined = rank_mod(combined_proj)
print(f"rank of (fixed + free_sym) in F-quotient = {rk_combined}")

# L_sym coordinates: express quotient projections in L_sym_proj basis
# Solve: for each fixed_proj[i], find alpha such that fixed_proj[i] = sum_j alpha_j L_sym_proj[j]
# Since L_sym_proj has rank 6, this determines alpha uniquely (if fixed_proj[i] is in the span)

# Row-reduce [L_sym_proj; fixed_proj_i] to find alpha
print("\n=== Fixed terms' L_sym coordinates ===")
fixed_lsym_coords = []
for fi in range(7):
    aug = mod(np.vstack([L_sym_proj, fixed_proj[fi:fi+1]]))
    R, rk, pivs = rref_mod(aug)
    if rk == 6:
        # fixed_proj[fi] is in span(L_sym_proj)
        # The 7th row should be zero after rref
        # Coefficient vector is in the representation
        # Actually, need to solve L_sym_proj^T . alpha = fixed_proj[fi]^T
        # Do it via augmented matrix [L_sym_proj | identity]
        pass
    print(f"  Fixed {fixed_indices[fi]+1}: augmented rank = {rk}")
    if rk == 6:
        print(f"    -> in span(L_sym), consistent")
    else:
        print(f"    -> NOT in span(L_sym)")

# Express each fixed in L_sym coordinates using pseudoinverse
# [L_sym_proj^T | fixed_proj^T] -> rref to find coefficients
Ls_aug = mod(np.vstack([L_sym_proj, np.eye(6, L_sym_proj.shape[1], dtype=object)[:6]]))
# Actually this is getting complicated. Let me use a direct solve.

# Method: build [L_sym_proj.T] and solve for each fixed_proj[i]
# L_sym_proj is 6 x 65. Transpose is 65 x 6.
# For each fixed_proj[i] (length 65), solve L_sym_proj.T . alpha = fixed_proj[i]

def solve_lsq(A, b):
    """Solve A.T x = b over F_p where A is m x n, b is n-vector, x is m-vector."""
    m, n = A.shape
    aug = mod(np.column_stack([A.T, b.reshape(-1, 1)]))  # n x (m+1)
    R, rk, pivs = rref_mod(aug)
    if m in pivs:
        return None  # inconsistent
    x = np.zeros(m, dtype=object)
    for ri, pc in enumerate(pivs):
        if pc < m:
            x[pc] = R[ri, m]
    return x % P

coords = []
for fi in range(7):
    alpha = solve_lsq(L_sym_proj, fixed_proj[fi])
    if alpha is not None:
        coords.append(alpha)
        print(f"  Fixed {fixed_indices[fi]+1}: L_sym coords = {[int(x) for x in alpha]}")
    else:
        coords.append(None)
        print(f"  Fixed {fixed_indices[fi]+1}: NOT in L_sym span (inconsistent)")

# Free symmetric L_sym coordinates
print("\n=== Free symmetric products' L_sym coordinates ===")
sym_coords = []
for si in range(8):
    alpha = solve_lsq(L_sym_proj, sym_proj[si])
    if alpha is not None:
        sym_coords.append(alpha)
        print(f"  Free pair {free_pairs[si]}: L_sym coords = {[int(x) for x in alpha]}")
    else:
        sym_coords.append(None)
        print(f"  Free pair {free_pairs[si]}: NOT in L_sym span")

# ================================================================
# Relation analysis: the 7 fixed + 8 free_sym in L_sym (R^6)
# ================================================================
print("\n=== Relation structure in L_sym ===")
valid_fixed = [c for c in coords if c is not None]
valid_sym = [c for c in sym_coords if c is not None]

if valid_fixed:
    fixed_coord_mat = mod(np.vstack(valid_fixed))  # 7 x 6
    rk_fixed_coord = rank_mod(fixed_coord_mat)
    print(f"Fixed terms span rank in L_sym = {rk_fixed_coord}")
    
    if rk_fixed_coord < len(valid_fixed):
        # There's a relation
        null_fixed = nullspace_mod(fixed_coord_mat)
        print(f"Number of relations among fixed: {null_fixed.shape[0]}")
        for ni, nv in enumerate(null_fixed):
            print(f"  Relation {ni}: {[int(x) for x in nv]}")
            nonzero = sum(1 for x in nv if int(x) % P != 0)
            print(f"    Nonzero coefficients: {nonzero}/{len(nv)}")

if valid_sym:
    sym_coord_mat = mod(np.vstack(valid_sym))  # 8 x 6
    rk_sym_coord = rank_mod(sym_coord_mat)
    print(f"Free sym products span rank in L_sym = {rk_sym_coord}")

# Combined analysis
all_coords = valid_fixed + valid_sym
if all_coords:
    all_coord_mat = mod(np.vstack(all_coords))  # 15 x 6
    rk_all_coord = rank_mod(all_coord_mat)
    print(f"All (fixed + free_sym) span rank in L_sym = {rk_all_coord}")

# ================================================================
# Deletion analysis: for each fixed, check if remaining 6+8 still span L_sym
# ================================================================
print("\n=== Fixed deletion analysis (L_sym coverage) ===")
deletion_results = []
for fi in range(7):
    remaining_fixed = [coords[j] for j in range(7) if j != fi and coords[j] is not None]
    remaining = remaining_fixed + valid_sym
    if remaining:
        rem_mat = mod(np.vstack(remaining))
        rk_rem = rank_mod(rem_mat)
        deficit = 6 - rk_rem
        print(f"  Delete fixed {fixed_indices[fi]+1}: remaining rank = {rk_rem}, deficit = {deficit}")
        deletion_results.append({"fixed_1based": fixed_indices[fi]+1, "remaining_rank": int(rk_rem), "deficit": int(deficit)})

# ================================================================
# Summary
# ================================================================
out = {
    "field": f"F_{P}",
    "dim_F": int(rk_F),
    "free_sym_quotient_rank": int(free_sym_quotient_rank),
    "fixed_quotient_rank": int(fixed_quotient_rank),
    "rk_sym_proj_in_Lsym": int(rk_sym_coord) if valid_sym else None,
    "rk_fixed_proj_in_Lsym": int(rk_fixed_coord) if valid_fixed else None,
    "rk_combined_in_Lsym": int(rk_all_coord) if all_coords else None,
    "deletion_results": deletion_results,
    "interpretation": (
        "At the transported Laderman (7,8) witness, the free symmetric products "
        "and fixed terms together span L_sym. Deletion analysis shows which fixed "
        "terms are individually essential. If free_sym alone covers d dimensions, "
        "then 7-d fixed terms suffice, and the remaining d-1 are redundant for "
        "a (6,8) approach. The deformation parameter is the anti-containment "
        "family at the 8-bivector witness."
    )
}
out_path = DATA / "quotient_structure.json"
out_path.write_text(json.dumps(out, indent=2) + "\n")
print(f"\nSAVED {out_path}")
print(json.dumps(out, indent=2))
