#!/usr/bin/env python3
"""analysis: Two-sector τ-containment, Q(i) frozen-span compatibility, f-parity.

Three structural results:
A. L_1 = L_sym(6) ⊕ L_anti(3); two-sector containment conditions
B. Over Q(i), frozen-Laderman-free-span compatibility variety for tau-fixed generators
   → Singular input for projective degree computation
C. f mod 2 invariant under free-free flips / orbit reductions
   → rank 22 from odd-f seeds requires parity-changing moves

Also: modular F_65521 sanity checks throughout.
"""
from fractions import Fraction
import numpy as np
import json, sys
from pathlib import Path

WS = Path(__file__).resolve().parent.parent
DATA = WS / "data" / "two_sector"
DATA.mkdir(parents=True, exist_ok=True)
P = 65521; IROOT = 41224

# ================================================================
# Modular helpers
# ================================================================
def mod(x): return np.asarray(x, dtype=object) % P
def inv_mod(a): return pow(int(a) % P, -1, P)
def rank_mod(M):
    M = mod(M).copy(); m, n = M.shape; r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if int(M[i,c]) % P), None)
        if piv is None: continue
        if piv != r: M[[r, piv]] = M[[piv, r]]
        M[r,:] = (M[r,:] * inv_mod(M[r,c])) % P
        for i in range(m):
            if i != r and int(M[i,c]) % P:
                M[i,:] = (M[i,:] - M[i,c] * M[r,:]) % P
        r += 1
    return r

def nullspace_mod(M):
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
    free = [c for c in range(n) if c not in set(pivs)]
    out = []
    for f in free:
        x = np.zeros(n, dtype=object); x[f] = 1
        for row, col in enumerate(pivs):
            x[col] = (-M[row, f]) % P
        out.append(x % P)
    return np.vstack(out) % P if out else np.zeros((0, n), dtype=object)

# ================================================================
# Gaussian rational Q(i) arithmetic
# ================================================================
Z = Fraction(0); O = Fraction(1)
GZ = (Z, Z); GO = (O, Z); GI = (Z, O)

def ga(a, b): return (a[0]+b[0], a[1]+b[1])
def gs(a, b): return (a[0]-b[0], a[1]-b[1])
def gm(a, b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def gn(a): return (-a[0], -a[1])
def ginv(a):
    d = a[0]*a[0]+a[1]*a[1]
    return (a[0]/d, -a[1]/d)
def gz(a): return a[0]==0 and a[1]==0

def gfrom(s):
    s = s.strip()
    if s == '0': return GZ
    if s == '1': return GO
    if s == '-1': return (Fraction(-1), Z)
    if s == 'I': return GI
    if s == '-I': return (Z, Fraction(-1))
    raise ValueError(f"Unknown: {s}")

def grref(M, nr, nc):
    r = 0; pivs = []
    for c in range(nc):
        piv = next((i for i in range(r, nr) if not gz(M[i][c])), None)
        if piv is None: continue
        if piv != r: M[r], M[piv] = M[piv], M[r]
        sc = ginv(M[r][c])
        for j in range(nc): M[r][j] = gm(M[r][j], sc)
        for i in range(nr):
            if i != r and not gz(M[i][c]):
                fac = M[i][c]
                for j in range(nc): M[i][j] = gs(M[i][j], gm(fac, M[r][j]))
        pivs.append(c); r += 1
    return r, pivs

def gnull(M, nr, nc):
    R = [[M[i][j] for j in range(nc)] for i in range(nr)]
    rk, pivs = grref(R, nr, nc)
    pset = set(pivs)
    free = [c for c in range(nc) if c not in pset]
    vecs = []
    for f in free:
        v = [GZ]*nc; v[f] = GO
        for ri, pc in enumerate(pivs): v[pc] = gn(R[ri][f])
        vecs.append(v)
    return rk, vecs

# ================================================================
# Part A: Two-sector decomposition (modular)
# ================================================================
print("="*60)
print("PART A: Two-sector decomposition of L_1 under tau")
print("="*60)

# L_1 basis: B_{ab} has 1 at positions (3b+k, 3k+a) for k=0,1,2
L1_81 = []
for a in range(3):
    for b in range(3):
        row = np.zeros(81, dtype=object)
        for k in range(3):
            row[9*(3*b+k) + (3*k+a)] = 1
        L1_81.append(row)
L1_81 = np.vstack(L1_81)  # 9 x 81

# P9 perm: transpose of 3x3 matrix, P9[3j+i] = position of entry (j,i)
# In vector indexing: position 3i+j maps to 3j+i
P9p = [3*(k%3)+k//3 for k in range(9)]

# tau on 81-vectors: tau(vec(M))[9*a+b] = vec(M)[9*P9p[b]+P9p[a]]
tau_perm = [9*P9p[b]+P9p[a] for a in range(9) for b in range(9)]

# tau acts on L_1: B_{ab} -> B_{ba} (swap a,b indices in the first factor)
# Build tau|_{L_1} as a 9x9 matrix
tau_L1 = np.zeros((9, 9), dtype=int)
for ab in range(9):
    a, b = divmod(ab, 3)
    ba = 3*b + a
    tau_L1[ab, ba] = 1
# Eigenvalues: +1 for a<=b (sym), -1 for a<b (anti)
# +1 eigenspace: span{B_{aa}, (B_{ab}+B_{ba})/2 for a<b} dim=6
# -1 eigenspace: span{(B_{ab}-B_{ba})/2 for a<b} dim=3

sym_vecs, anti_vecs = [], []
for a in range(3):
    sym_vecs.append(L1_81[3*a+a])  # B_{aa}
for a in range(3):
    for b in range(a+1, 3):
        sym_vecs.append((L1_81[3*a+b] + L1_81[3*b+a]) % P)
        anti_vecs.append((L1_81[3*a+b] - L1_81[3*b+a]) % P)

L_sym = mod(np.vstack(sym_vecs))   # 6 x 81
L_anti = mod(np.vstack(anti_vecs)) # 3 x 81
dim_sym = rank_mod(L_sym)
dim_anti = rank_mod(L_anti)
dim_total = rank_mod(np.vstack([L_sym, L_anti]))
print(f"dim L_sym = {dim_sym}")
print(f"dim L_anti = {dim_anti}")
print(f"dim(L_sym + L_anti) = {dim_total} (should be 9)")
print(f"Direct sum: {dim_total == dim_sym + dim_anti}")

# ================================================================
# Load transported Laderman (modular p=65521)
# ================================================================
src = (WS / "scripts" / "laderman_tau_decomp.py").read_text()
prefix = src.split('print(f"Sum matches T333')[0]
ns = {"__file__": str(WS/"scripts"/"laderman_tau_decomp.py"), "__name__": "defs_only"}
exec(compile(prefix, str(WS/"scripts"/"laderman_tau_decomp.py"), "exec"), ns)
terms = [(mod(a), mod(b), mod(c)) for a, b, c in ns['terms']]
eps1, pi12 = mod(ns['eps1']), mod(ns['pi12'])

def mat_inv_mod(A):
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

Q_mat = (eps1 @ pi12) % P
R_mat = np.diag([IROOT, 1, 1]).astype(object) % P
Qinv = mat_inv_mod(Q_mat); Rinv = mat_inv_mod(R_mat)
def transport(a, b, c):
    return (a @ Qinv % P, Q_mat @ b @ Rinv % P, R_mat @ c % P)
transported = [transport(a, b, c) for a, b, c in terms]

free_pairs_1 = [(1,4),(2,5),(6,15),(7,17),(8,16),(10,13),(12,14),(19,21)]
free_indices = [i for p in free_pairs_1 for i in p]
fixed_indices = [i for i in range(23) if i not in free_indices]

def vec9(M): return mod(M).reshape(9)

# Free span F
F_mod = []
for idx in free_indices:
    _, b, c = transported[idx]
    F_mod.append(np.outer(vec9(b), vec9(c)).reshape(81) % P)
F_mod = mod(np.vstack(F_mod))  # 16 x 81

# Verify dimensions
FL = mod(np.vstack([F_mod, L1_81]))
rk_FL = rank_mod(FL)
rk_F = rank_mod(F_mod)
print(f"\nTransported Laderman:")
print(f"  dim F (free span) = {rk_F}")
print(f"  dim(F + L_1) = {rk_FL}")
print(f"  dim(F ∩ L_1) = {rk_F + 9 - rk_FL}")

# Check F ∩ L_1 = L_anti
F_anti = mod(np.vstack([F_mod, L_anti]))
rk_F_anti = rank_mod(F_anti)
print(f"  dim(F + L_anti) = {rk_F_anti} (should be {rk_F} if L_anti ⊆ F)")
print(f"  L_anti ⊆ F: {rk_F_anti == rk_F}")

# Free symmetric products in L_sym quotient
sym_products = []
for j, (i1, i2) in enumerate(free_pairs_1):
    _, b1, c1 = transported[i1]
    _, b2, c2 = transported[i2]
    v1, w1 = vec9(b1), vec9(c1)
    v2, w2 = vec9(b2), vec9(c2)
    # symmetric combination: v1⊗w1 + v2⊗w2 (partner is tau-swapped)
    sp = (np.outer(v1, w1).reshape(81) + np.outer(v2, w2).reshape(81)) % P
    sym_products.append(sp)
sym_prods_mat = mod(np.vstack(sym_products))  # 8 x 81
# Project onto L_sym quotient
sym_F_L = mod(np.vstack([F_mod, L_sym]))
rk_sym_FL = rank_mod(sym_F_L)
print(f"  dim(F + L_sym) = {rk_sym_FL} (should be {rk_F + dim_sym} = {rk_F+6})")

# Fixed terms' contribution
fixed_slices = []
for idx in fixed_indices:
    _, b, c = transported[idx]
    fixed_slices.append(np.outer(vec9(b), vec9(c)).reshape(81) % P)
fixed_mat = mod(np.vstack(fixed_slices))  # 7 x 81
all_gens = mod(np.vstack([F_mod, fixed_mat]))
rk_all = rank_mod(mod(np.vstack([all_gens, L1_81])))
print(f"  dim(F + fixed + L_1) with all terms = {rk_all}")

# Quotient images: project fixed terms modulo F
# Number of fixed quotient directions contributing to L_sym
fixed_plus_F_plus_Lsym = mod(np.vstack([F_mod, fixed_mat, L_sym]))
rk_fFLs = rank_mod(fixed_plus_F_plus_Lsym)
print(f"  dim(F + fixed + L_sym) = {rk_fFLs}")

# ================================================================
# Part B: f-parity theorem
# ================================================================
print("\n" + "="*60)
print("PART B: f-parity invariance")
print("="*60)
print("""
Theorem: Under the currently implemented tau-walk moves, f mod 2 is invariant.

Proof: 
- Free-free orbit flip: replaces one free orbit with another. (f,m) unchanged. f invariant.
- Free-orbit reduction: removes a free orbit. (f,m) -> (f,m-1). f invariant.
- Free-orbit rewrite (free pairs contribute same b,c sums): (f,m) unchanged.

Since rank = f + 2m, rank mod 2 = f mod 2.

Consequence:
- naive_27: f=9 (odd), rank=27. All reachable schemes have odd rank.
- Laderman_tau: f=7 (odd), rank=23. All reachable schemes have odd rank.
- Rank 22 requires even f. UNREACHABLE by current moves.

Parity-changing moves needed:
1. Orbit collapse: free pair (v,w) with w -> alpha*v, two terms merge to one fixed.
   (f,m) -> (f+1,m-1), rank -> rank-1. Changes f parity.
2. Fixed-term addition: add a new tau-fixed term.
   (f,m) -> (f+1,m), rank -> rank+1. Changes f parity.
3. Fixed-term removal: delete a tau-fixed term.
   (f,m) -> (f-1,m), rank -> rank-1. Changes f parity.

Cross-check with walk results:
- analysis: 72 clean free-free flips from naive_27, all stay at (9,9) rank 27. 
  This is structurally necessary, not a search failure.
- The only rank-23 reachable from naive_27 by current moves is (9,7)=23.
  (9,7) exists only if m_0 <= 7 (need 7 bivectors to span L_anti).
  m_0 is currently in [7,8], so (9,7) existence is the same as m_0=7.
""")

# ================================================================
# Part C: Q(i) frozen-span compatibility ideal
# ================================================================
print("="*60)
print("PART C: Q(i) frozen-span compatibility ideal")
print("="*60)

qi_path = WS/"data"/"transport_laderman_tau"/"transported_laderman_standard_tau_Qi.json"
with open(qi_path) as f:
    qi_data = json.load(f)

# Parse terms
terms_qi = []
for t in qi_data["transported_terms_Qi"]:
    a = [[gfrom(t["a"][i][j]) for j in range(3)] for i in range(3)]
    b = [[gfrom(t["b"][i][j]) for j in range(3)] for i in range(3)]
    c = [[gfrom(t["c"][i][j]) for j in range(3)] for i in range(3)]
    terms_qi.append((a, b, c))

# Build free span over Q(i)
def qvec9(mat):
    return [mat[i][j] for i in range(3) for j in range(3)]
def qouter81(v, w):
    return [gm(v[i], w[j]) for i in range(9) for j in range(9)]

fp_qi = [(p[0]-1, p[1]-1) for p in qi_data["free_pairs"]]
fi_qi = [i for p in fp_qi for i in p]

F_qi = []  # list of 81-element Q(i) vectors
for idx in fi_qi:
    _, b, c = terms_qi[idx]
    F_qi.append(qouter81(qvec9(b), qvec9(c)))
# L_1 over Z (as Q(i) elements)
L1_qi = []
for a in range(3):
    for b in range(3):
        row = [GZ]*81
        for k in range(3):
            row[9*(3*b+k)+(3*k+a)] = GO
        L1_qi.append(row)
# Combined S = [F; L1], 25 x 81
S_qi = F_qi + L1_qi
print(f"Building {len(S_qi)} x 81 matrix over Q(i)...")
sys.stdout.flush()

rk_qi, null_qi = gnull(S_qi, len(S_qi), 81)
print(f"rank over Q(i) = {rk_qi}")
print(f"nullspace dim = {len(null_qi)}")
assert rk_qi == 22, f"Expected rank 22, got {rk_qi}"
assert len(null_qi) == 59, f"Expected 59 null vectors, got {len(null_qi)}"

# Generate quadrics: for each null vector n, form
# Q(x) = sum_{i,j} n[9i+j] * x_i * x_{P9p[j]}
quadrics_qi = []
for nv in null_qi:
    # Bilinear form B[i,k] = n[9*i + sigma(k)] where sigma = P9p
    # Symmetrized: coeff of x_a*x_b (a<=b) = B[a,b] + B[b,a] for a<b, B[a,a] for a=b
    mono = {}
    for a in range(9):
        for b in range(a, 9):
            if a == b:
                c = nv[9*a + P9p[a]]
            else:
                c = ga(nv[9*a + P9p[b]], nv[9*b + P9p[a]])
            if not gz(c):
                mono[(a, b)] = c
    if mono:
        quadrics_qi.append(mono)

print(f"Nonzero quadrics: {len(quadrics_qi)}")

# ================================================================
# Generate Singular input
# ================================================================
def gi_to_singular(v):
    """Convert Q(i) element to Singular Q(a) string."""
    re, im = v
    parts = []
    if re != 0:
        if re.denominator == 1:
            parts.append(str(re.numerator))
        else:
            parts.append(f"({re})")
    if im != 0:
        if im == 1:
            parts.append("a")
        elif im == -1:
            parts.append("(-a)")
        else:
            if im.denominator == 1:
                parts.append(f"({im.numerator}*a)")
            else:
                parts.append(f"({im}*a)")
    if not parts: return "0"
    return "+".join(parts).replace("+-", "-")

vs = ",".join(f"x{i}" for i in range(9))
lines = [
    "// analysis: tau-fixed compatibility ideal over Q(i)",
    "// Frozen Laderman free span; generated by two_sector_Qi_compat.py",
    f"ring r = (0,a),({vs}),dp;",
    "minpoly = a2+1;",
    "ideal I ="
]
for idx, qd in enumerate(quadrics_qi):
    terms = []
    for (a, b), c in sorted(qd.items()):
        cs = gi_to_singular(c)
        mono = f"x{a}^2" if a == b else f"x{a}*x{b}"
        terms.append(f"({cs})*{mono}")
    poly = "+".join(terms) if terms else "0"
    sep = "," if idx < len(quadrics_qi)-1 else ";"
    lines.append(f"  {poly}{sep}")
lines += [
    "ideal J = std(I);",
    'print("num_gens"); size(I);',
    'print("affine_dim"); dim(J);',
    'print("degree");',
    "degree(J);",
    'print("std_size"); size(J);',
    "// Chart enumeration for projective points",
    "int k;",
    "for (k=0; k<9; k=k+1) {",
    '  print("chart"); k;',
    "  ideal C = I, x(k+1)-1;",
    "  ideal JC = std(C);",
    "  dim(JC); degree(JC); size(JC);",
    "  kill C; kill JC;",
    "}",
    "quit;"
]
sing_path = DATA / "compatibility_Qi.sing"
sing_path.write_text("\n".join(lines) + "\n")
print(f"Singular input: {sing_path}")

# Also generate the GENERAL (non-tau-fixed) bilinear compatibility
# For general rank-one: vec(v w^T) = v ⊗ w, compatibility is N @ (v ⊗ w) = 0
# This gives bilinear equations in (v_0,...,v_8, w_0,...,w_8)
lines2 = [
    "// analysis: general rank-one compatibility ideal over Q(i)",
    "// Bilinear: N @ (v tensor w) = 0",
    f"ring r2 = (0,a),(v0,v1,v2,v3,v4,v5,v6,v7,v8,w0,w1,w2,w3,w4,w5,w6,w7,w8),dp;",
    "minpoly = a2+1;",
    "ideal I2 ="
]
bilinear_qi = []
for nv in null_qi:
    mono = {}
    for i in range(9):
        for j in range(9):
            c = nv[9*i + j]
            if not gz(c):
                mono[(i, j)] = c
    if mono:
        bilinear_qi.append(mono)

for idx, bl in enumerate(bilinear_qi):
    terms = []
    for (i, j), c in sorted(bl.items()):
        cs = gi_to_singular(c)
        terms.append(f"({cs})*v{i}*w{j}")
    poly = "+".join(terms) if terms else "0"
    sep = "," if idx < len(bilinear_qi)-1 else ";"
    lines2.append(f"  {poly}{sep}")
lines2 += [
    "ideal J2 = std(I2);",
    'print("bilinear_num_gens"); size(I2);',
    'print("bilinear_affine_dim"); dim(J2);',
    'print("bilinear_degree");',
    "degree(J2);",
    "quit;"
]
bilin_path = DATA / "compatibility_Qi_bilinear.sing"
bilin_path.write_text("\n".join(lines2) + "\n")
print(f"Bilinear Singular input: {bilin_path}")

# ================================================================
# Summary
# ================================================================
out = {
    "two_sector": {
        "dim_L_sym": dim_sym,
        "dim_L_anti": dim_anti,
        "direct_sum": dim_total == dim_sym + dim_anti,
        "F_contains_L_anti": rk_F_anti == rk_F,
        "dim_F_cap_L1": rk_F + 9 - rk_FL,
        "dim_quotient": rk_FL - rk_F,
    },
    "Qi_compatibility": {
        "rank_over_Qi": rk_qi,
        "nullspace_dim": len(null_qi),
        "num_quadrics": len(quadrics_qi),
        "num_bilinear": len(bilinear_qi),
        "singular_fixed_path": str(sing_path),
        "singular_bilinear_path": str(bilin_path),
    },
    "f_parity": {
        "naive_27_f": 9,
        "naive_27_rank": 27,
        "laderman_tau_f": 7,
        "laderman_tau_rank": 23,
        "both_odd": True,
        "rank22_needs_even_f": True,
        "current_moves_preserve_f_parity": True,
        "parity_changing_moves": ["orbit_collapse", "fixed_term_addition", "fixed_term_removal"],
    },
    "skeleton_variables": {
        "(8,7) r=22": {"f": 8, "m": 7, "vars_fixed": 72, "vars_free": 126, "total": 198},
        "(6,8) r=22": {"f": 6, "m": 8, "vars_fixed": 54, "vars_free": 144, "total": 198},
        "(4,9) r=22": {"f": 4, "m": 9, "vars_fixed": 36, "vars_free": 162, "total": 198},
        "(2,10) r=22": {"f": 2, "m": 10, "vars_fixed": 18, "vars_free": 180, "total": 198},
        "(0,11) r=22": {"f": 0, "m": 11, "vars_fixed": 0, "vars_free": 198, "total": 198},
        "note": "All skeletons have 9*(f+2m) = 9*22 = 198 unknowns before symmetry reduction"
    }
}

out_path = DATA / "two_sector_results.json"
out_path.write_text(json.dumps(out, indent=2) + "\n")
print(f"\nSAVED {out_path}")
print(json.dumps(out, indent=2))
