#!/usr/bin/env python3
"""analysisC: Correct cyclic automorphism search with proper matmul symmetry structure.

The automorphism group of T_{333} is {(A⊗B^{-T}, B⊗C^{-T}, C⊗A^{-T}) : A,B,C in GL_3} x S_3.

For sigma^2 cyclic direction (a,b,c) -> (c,a,b):
  Factor 1: (A⊗B^{-T}) c_l ∝ a_{π(l)}  -> A c_L ∝ a_L_π, B^{-T} c_R ∝ a_R_π
  Factor 2: (B⊗C^{-T}) a_l ∝ b_{π(l)}  -> B a_L ∝ b_L_π, C^{-T} a_R ∝ b_R_π
  Factor 3: (C⊗A^{-T}) b_l ∝ c_{π(l)}  -> C b_L ∝ c_L_π, A^{-T} b_R ∝ c_R_π

So B maps a_L -> b_L, AND A maps c_L -> a_L, AND C maps b_L -> c_L.
And B^{-T} maps c_R -> a_R, C^{-T} maps a_R -> b_R, A^{-T} maps b_R -> c_R.

The left maps (A,B,C) and right maps (B^{-T},C^{-T},A^{-T}) are COUPLED.
B: a_L -> b_L  and  B^{-T}: c_R -> a_R  =>  B^T a_R ∝ c_R => CORRECT RIGHT CHECK.

My earlier search found B=Q_L candidates (a_L -> b_L) but checked Q_R independently.
The correct check: for each B candidate, verify B^T maps a_R -> c_R (not b_R!).
"""

import numpy as np
from pathlib import Path
import json, itertools

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA = WS / "data" / "S3_analysis"
DATA.mkdir(parents=True, exist_ok=True)

def E(i, j):
    M = np.zeros((3,3), dtype=int)
    M[i,j] = 1
    return M

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

def extended_gcd(a, b):
    if a == 0: return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def modinv(a, m):
    a = a % m
    g, x, _ = extended_gcd(a, m)
    return x % m if g == 1 else None

def mat_inv_3(M, p):
    M = np.array(M, dtype=int) % p
    d = (int(M[0,0])*(int(M[1,1])*int(M[2,2])-int(M[1,2])*int(M[2,1]))
        -int(M[0,1])*(int(M[1,0])*int(M[2,2])-int(M[1,2])*int(M[2,0]))
        +int(M[0,2])*(int(M[1,0])*int(M[2,1])-int(M[1,1])*int(M[2,0]))) % p
    if d == 0: return None
    di = modinv(d, p)
    if di is None: return None
    adj = np.zeros((3,3), dtype=int)
    for i in range(3):
        for j in range(3):
            mn = np.delete(np.delete(M, i, 0), j, 1)
            cof = (int(mn[0,0])*int(mn[1,1]) - int(mn[0,1])*int(mn[1,0])) % p
            adj[j,i] = ((-1)**(i+j) * cof * di) % p
    return adj % p

def rank1_factor(M):
    """Factor rank-1 3x3 M = u v^T. Return (u, v) or None."""
    M = np.array(M, dtype=int)
    for i in range(3):
        for j in range(3):
            if M[i,j] != 0:
                u = M[:, j].copy()
                v = M[i, :].copy()
                if np.array_equal(np.outer(u, v), M * M[i,j]):
                    return u, v
    return None

def cross_zero(u, v, p):
    """Check u ∝ v in F_p^3."""
    for i in range(3):
        for j in range(i+1,3):
            if (int(u[i])*int(v[j]) - int(u[j])*int(v[i])) % p != 0:
                return False
    return True

# Extract rank-1 factorizations
r1 = {}  # index -> (a_L, a_R, b_L, b_R, c_L, c_R) for rank-1 factors
for l, (a, b, c) in enumerate(terms):
    fa = rank1_factor(a)
    fb = rank1_factor(b)
    fc = rank1_factor(c)
    r1[l] = {
        'a': fa, 'b': fb, 'c': fc,
        'a_rank': int(np.linalg.matrix_rank(a)),
        'b_rank': int(np.linalg.matrix_rank(b)),
        'c_rank': int(np.linalg.matrix_rank(c)),
    }

r1_a = {l: r1[l]['a'] for l in r1 if r1[l]['a'] is not None}
r1_b = {l: r1[l]['b'] for l in r1 if r1[l]['b'] is not None}
r1_c = {l: r1[l]['c'] for l in r1 if r1[l]['c'] is not None}

print(f"Rank-1 factors: a={len(r1_a)}, b={len(r1_b)}, c={len(r1_c)}")

# Find independent triples for left and right factors
def find_indep(factors, comp, n=3):
    idx = sorted(factors.keys())
    for combo in itertools.combinations(idx, n):
        vecs = [np.array(factors[i][comp], dtype=int) for i in combo]
        M = np.column_stack(vecs)
        if abs(np.linalg.det(M)) > 0.5:
            return combo
    return None

# ============================================================
# SIGMA^2 direction: B maps a_L -> b_L, B^T maps a_R -> c_R
# ============================================================
print("\n" + "=" * 60)
print("SIGMA^2 direction: B maps a_L -> b_L, B^T maps a_R -> c_R")
print("=" * 60)

# analysis: Find B candidates from a_L -> b_L (3 independent left factors)
aL_basis = find_indep(r1_a, 0)
print(f"a_L basis: terms {tuple(l+1 for l in aL_basis)}")
aL_vecs = [np.array(r1_a[l][0], dtype=int) for l in aL_basis]
M_aL = np.column_stack(aL_vecs)
M_aL_inv = mat_inv_3(M_aL, p)

B_candidates = []
r1_b_idx = sorted(r1_b.keys())

for j0, j1, j2 in itertools.permutations(r1_b_idx, 3):
    bL_vecs = [np.array(r1_b[j][0], dtype=int) % p for j in (j0, j1, j2)]
    M_bL = np.column_stack(bL_vecs) % p
    d = (int(M_bL[0,0])*(int(M_bL[1,1])*int(M_bL[2,2])-int(M_bL[1,2])*int(M_bL[2,1]))
        -int(M_bL[0,1])*(int(M_bL[1,0])*int(M_bL[2,2])-int(M_bL[1,2])*int(M_bL[2,0]))
        +int(M_bL[0,2])*(int(M_bL[1,0])*int(M_bL[2,1])-int(M_bL[1,1])*int(M_bL[2,0]))) % p
    if d == 0: continue
    
    B_mat = np.zeros((3,3), dtype=int)
    for i in range(3):
        for j in range(3):
            B_mat[i,j] = sum(int(M_bL[i,k]) * int(M_aL_inv[k,j]) for k in range(3)) % p
    
    # Check B on ALL rank-1 a-factors (left component)
    perm_L = {aL_basis[0]: j0, aL_basis[1]: j1, aL_basis[2]: j2}
    valid = True
    for l in r1_a:
        if l in aL_basis: continue
        aL = np.array(r1_a[l][0], dtype=int) % p
        BaL = np.array([sum(int(B_mat[r,s]) * int(aL[s]) for s in range(3)) % p for r in range(3)])
        found = False
        for j in r1_b_idx:
            bL = np.array(r1_b[j][0], dtype=int) % p
            if cross_zero(BaL, bL, p):
                perm_L[l] = j
                found = True
                break
        if not found:
            valid = False
            break
    
    if valid:
        # Now check B^T on a_R -> c_R (the CORRECT coupling)
        BT = B_mat.T % p
        perm_R = {}
        valid_R = True
        for l in r1_a:
            aR = np.array(r1_a[l][1], dtype=int) % p
            BTaR = np.array([sum(int(BT[r,s]) * int(aR[s]) for s in range(3)) % p for r in range(3)])
            found = False
            r1_c_idx = sorted(r1_c.keys())
            for j in r1_c_idx:
                cR = np.array(r1_c[j][1], dtype=int) % p
                if cross_zero(BTaR, cR, p):
                    perm_R[l] = j
                    found = True
                    break
            if not found:
                valid_R = False
                break
        
        if valid_R:
            # Check permutation consistency: perm_L and perm_R should define same π
            # perm_L[l] = π(l) (a_l -> b_{π(l)} left)
            # perm_R[l] maps a_R_l -> c_R_{π^{-1}(l)} ... need to check
            B_candidates.append({
                "B": B_mat.tolist(),
                "perm_L": {str(k):v for k,v in perm_L.items()},
                "perm_R": {str(k):v for k,v in perm_R.items()},
            })
            pi_L = [perm_L.get(l, '?') for l in range(23)]
            pi_R = [perm_R.get(l, '?') for l in range(23)]
            print(f"  HIT: B left perm (partial): ...{len(perm_L)} entries matched")
            print(f"         B^T right perm (partial): ...{len(perm_R)} entries matched")

print(f"\nSigma^2 B candidates (both L and R): {len(B_candidates)}")

# ============================================================
# SIGMA direction: B maps c_L -> b_L, B^T maps a_R -> b_R
# ============================================================
print("\n" + "=" * 60)
print("SIGMA direction: B maps c_L -> b_L, B^T maps a_R -> b_R")
print("=" * 60)

cL_basis = find_indep(r1_c, 0)
if cL_basis:
    print(f"c_L basis: terms {tuple(l+1 for l in cL_basis)}")
    cL_vecs = [np.array(r1_c[l][0], dtype=int) for l in cL_basis]
    M_cL = np.column_stack(cL_vecs)
    M_cL_inv = mat_inv_3(M_cL, p)
    
    B_sigma = []
    for j0, j1, j2 in itertools.permutations(r1_b_idx, 3):
        bL_vecs = [np.array(r1_b[j][0], dtype=int) % p for j in (j0, j1, j2)]
        M_bL = np.column_stack(bL_vecs) % p
        d = (int(M_bL[0,0])*(int(M_bL[1,1])*int(M_bL[2,2])-int(M_bL[1,2])*int(M_bL[2,1]))
            -int(M_bL[0,1])*(int(M_bL[1,0])*int(M_bL[2,2])-int(M_bL[1,2])*int(M_bL[2,0]))
            +int(M_bL[0,2])*(int(M_bL[1,0])*int(M_bL[2,1])-int(M_bL[1,1])*int(M_bL[2,0]))) % p
        if d == 0: continue
        
        B_mat = np.zeros((3,3), dtype=int)
        for i in range(3):
            for j in range(3):
                B_mat[i,j] = sum(int(M_bL[i,k]) * int(M_cL_inv[k,j]) for k in range(3)) % p
        
        perm_L = {cL_basis[0]: j0, cL_basis[1]: j1, cL_basis[2]: j2}
        valid = True
        for l in r1_c:
            if l in cL_basis: continue
            cL = np.array(r1_c[l][0], dtype=int) % p
            BcL = np.array([sum(int(B_mat[r,s]) * int(cL[s]) for s in range(3)) % p for r in range(3)])
            found = False
            for j in r1_b_idx:
                bL = np.array(r1_b[j][0], dtype=int) % p
                if cross_zero(BcL, bL, p):
                    perm_L[l] = j
                    found = True
                    break
            if not found:
                valid = False
                break
        
        if valid:
            BT = B_mat.T % p
            perm_R = {}
            valid_R = True
            aR_basis = find_indep(r1_a, 1)
            for l in r1_a:
                aR = np.array(r1_a[l][1], dtype=int) % p
                BTaR = np.array([sum(int(BT[r,s]) * int(aR[s]) for s in range(3)) % p for r in range(3)])
                found = False
                for j in r1_b_idx:
                    bR = np.array(r1_b[j][1], dtype=int) % p
                    if cross_zero(BTaR, bR, p):
                        perm_R[l] = j
                        found = True
                        break
                if not found:
                    valid_R = False
                    break
            
            if valid_R:
                B_sigma.append({
                    "B": B_mat.tolist(),
                    "perm_L_size": len(perm_L),
                    "perm_R_size": len(perm_R),
                })
                print(f"  HIT: B left={len(perm_L)}, B^T right={len(perm_R)} entries")
    
    print(f"\nSigma B candidates (both L and R): {len(B_sigma)}")
else:
    print("Cannot find independent c_L basis")
    B_sigma = []

# ============================================================
# ALSO: check the wrong-search from Part B with correct coupling
# Part B found 68 Q_L hits for sigma^2 (a_L -> b_L).
# How many survive when we check Q_L^T on a_R -> c_R instead of Q_R on a_R -> b_R?
# ============================================================
print("\n" + "=" * 60)
print("Corrected check of Part B Q_L candidates")
print("=" * 60)

count_L_only = 0
count_LR_both = 0
for j0, j1, j2 in itertools.permutations(r1_b_idx, 3):
    bL_vecs = [np.array(r1_b[j][0], dtype=int) % p for j in (j0, j1, j2)]
    M_bL = np.column_stack(bL_vecs) % p
    d = (int(M_bL[0,0])*(int(M_bL[1,1])*int(M_bL[2,2])-int(M_bL[1,2])*int(M_bL[2,1]))
        -int(M_bL[0,1])*(int(M_bL[1,0])*int(M_bL[2,2])-int(M_bL[1,2])*int(M_bL[2,0]))
        +int(M_bL[0,2])*(int(M_bL[1,0])*int(M_bL[2,1])-int(M_bL[1,1])*int(M_bL[2,0]))) % p
    if d == 0: continue
    
    B_mat = np.zeros((3,3), dtype=int)
    for i in range(3):
        for j in range(3):
            B_mat[i,j] = sum(int(M_bL[i,k]) * int(M_aL_inv[k,j]) for k in range(3)) % p
    
    # Check LEFT: B a_L -> b_L
    perm_L = {aL_basis[0]: j0, aL_basis[1]: j1, aL_basis[2]: j2}
    valid_L = True
    for l in r1_a:
        if l in aL_basis: continue
        aL = np.array(r1_a[l][0], dtype=int) % p
        BaL = np.array([sum(int(B_mat[r,s]) * int(aL[s]) for s in range(3)) % p for r in range(3)])
        found = False
        for j in r1_b_idx:
            bL = np.array(r1_b[j][0], dtype=int) % p
            if cross_zero(BaL, bL, p):
                perm_L[l] = j; found = True; break
        if not found:
            valid_L = False; break
    
    if not valid_L: continue
    count_L_only += 1
    
    # Check RIGHT: B^T a_R -> c_R (CORRECT COUPLING)
    BT = B_mat.T % p
    valid_R = True
    for l in r1_a:
        aR = np.array(r1_a[l][1], dtype=int) % p
        BTaR = np.array([sum(int(BT[r,s]) * int(aR[s]) for s in range(3)) % p for r in range(3)])
        found = False
        r1_c_idx = sorted(r1_c.keys())
        for j in r1_c_idx:
            cR = np.array(r1_c[j][1], dtype=int) % p
            if cross_zero(BTaR, cR, p):
                found = True; break
        if not found:
            valid_R = False; break
    
    if valid_R:
        count_LR_both += 1
        print(f"  Sigma^2 HIT: B basis ({j0+1},{j1+1},{j2+1})")

print(f"\nSigma^2 corrected: L-only={count_L_only}, L+R both={count_LR_both}")

# ============================================================
# SUMMARY
# ============================================================
total = len(B_candidates) + len(B_sigma) + count_LR_both
print(f"\n{'='*60}")
print(f"FINAL: Laderman cyclic automorphism candidates = {total}")
if total == 0:
    print("Laderman does NOT have S3 symmetry.")
    print("The S3 route requires a different seed or a non-Laderman approach.")
print(f"{'='*60}")

results = {
    "sigma2_candidates": len(B_candidates),
    "sigma_candidates": len(B_sigma),
    "sigma2_corrected_LR": count_LR_both,
    "has_cyclic": total > 0,
    "note": "Checked both cyclic directions with correct Aut(T_333) Kronecker coupling"
}
path = DATA / "laderman_cyclic_correct.json"
path.write_text(json.dumps(results, indent=2) + "\n")
print(f"SAVED {path}")
