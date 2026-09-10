#!/usr/bin/env python3
"""analysisD: Full verification of Laderman cyclic automorphism candidates.

From earlier analysisC: 10 sigma^2 candidates with B passing both L and R on rank-1 factors.
Now verify on ALL 23 terms by determining C and checking B a_l C^{-1} ∝ b_{π(l)}.
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
n = 23

def extended_gcd(a, b):
    if a == 0: return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def modinv(a, m):
    a = a % m
    g, x, _ = extended_gcd(a, m)
    return x % m if g == 1 else None

def det3(M, p):
    M = np.array(M, dtype=int) % p
    return (int(M[0,0])*(int(M[1,1])*int(M[2,2])-int(M[1,2])*int(M[2,1]))
           -int(M[0,1])*(int(M[1,0])*int(M[2,2])-int(M[1,2])*int(M[2,0]))
           +int(M[0,2])*(int(M[1,0])*int(M[2,1])-int(M[1,1])*int(M[2,0]))) % p

def mat_inv_3(M, p):
    d = det3(M, p)
    if d == 0: return None
    di = modinv(d, p)
    if di is None: return None
    M = np.array(M, dtype=int) % p
    adj = np.zeros((3,3), dtype=int)
    for i in range(3):
        for j in range(3):
            mn = np.delete(np.delete(M, i, 0), j, 1)
            cof = (int(mn[0,0])*int(mn[1,1]) - int(mn[0,1])*int(mn[1,0])) % p
            adj[j,i] = ((-1)**(i+j) * cof * di) % p
    return adj % p

def matmul3(A, B, p):
    C = np.zeros((3,3), dtype=int)
    for i in range(3):
        for j in range(3):
            C[i,j] = sum(int(A[i,k]) * int(B[k,j]) for k in range(3)) % p
    return C

def mat_prop(X, Y, p):
    """Check if 3x3 matrices X and Y are proportional mod p."""
    # Flatten and check
    x = X.reshape(-1).astype(int) % p
    y = Y.reshape(-1).astype(int) % p
    for i in range(9):
        for j in range(i+1, 9):
            if (int(x[i])*int(y[j]) - int(x[j])*int(y[i])) % p != 0:
                return False
    return not (np.all(x == 0))

def rank1_factor(M):
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
    for i in range(3):
        for j in range(i+1,3):
            if (int(u[i])*int(v[j]) - int(u[j])*int(v[i])) % p != 0:
                return False
    return True

# Extract rank-1 factorizations
r1_a, r1_b, r1_c = {}, {}, {}
for l, (a, b, c) in enumerate(terms):
    fa = rank1_factor(a)
    if fa: r1_a[l] = fa
    fb = rank1_factor(b)
    if fb: r1_b[l] = fb
    fc = rank1_factor(c)
    if fc: r1_c[l] = fc

# Convert terms to mod p matrices
a_mats = [np.array(t[0], dtype=int) % p for t in terms]
b_mats = [np.array(t[1], dtype=int) % p for t in terms]
c_mats = [np.array(t[2], dtype=int) % p for t in terms]

# Reconstruct the 10 sigma^2 B candidates from earlier analysisC
def find_indep(factors, comp):
    idx = sorted(factors.keys())
    for combo in itertools.combinations(idx, 3):
        vecs = [np.array(factors[i][comp], dtype=int) for i in combo]
        M = np.column_stack(vecs)
        if abs(np.linalg.det(M)) > 0.5:
            return combo
    return None

aL_basis = find_indep(r1_a, 0)
aL_vecs = [np.array(r1_a[l][0], dtype=int) for l in aL_basis]
M_aL = np.column_stack(aL_vecs)
M_aL_inv = mat_inv_3(M_aL, p)

r1_b_idx = sorted(r1_b.keys())
r1_c_idx = sorted(r1_c.keys())

print("Reconstructing and fully verifying sigma^2 B candidates...")
print("=" * 60)

verified_autos = []

for j0, j1, j2 in itertools.permutations(r1_b_idx, 3):
    bL_vecs = [np.array(r1_b[j][0], dtype=int) % p for j in (j0, j1, j2)]
    M_bL = np.column_stack(bL_vecs) % p
    if det3(M_bL, p) == 0: continue
    
    B = matmul3(M_bL, M_aL_inv, p)
    
    # Check LEFT: B a_L -> b_L for all rank-1 a-factors
    perm = {}
    perm[aL_basis[0]] = j0
    perm[aL_basis[1]] = j1
    perm[aL_basis[2]] = j2
    valid_L = True
    for l in r1_a:
        if l in aL_basis: continue
        aL = np.array(r1_a[l][0], dtype=int) % p
        BaL = np.array([sum(int(B[r,s]) * int(aL[s]) for s in range(3)) % p for r in range(3)])
        found = False
        for j in r1_b_idx:
            bL = np.array(r1_b[j][0], dtype=int) % p
            if cross_zero(BaL, bL, p):
                perm[l] = j; found = True; break
        if not found:
            valid_L = False; break
    if not valid_L: continue
    
    # Check RIGHT: B^T a_R -> c_R
    BT = B.T % p
    valid_R = True
    perm_R = {}
    for l in r1_a:
        aR = np.array(r1_a[l][1], dtype=int) % p
        BTaR = np.array([sum(int(BT[r,s]) * int(aR[s]) for s in range(3)) % p for r in range(3)])
        found = False
        for j in r1_c_idx:
            cR = np.array(r1_c[j][1], dtype=int) % p
            if cross_zero(BTaR, cR, p):
                perm_R[l] = j; found = True; break
        if not found:
            valid_R = False; break
    if not valid_R: continue
    
    # Now determine C from factor 2 right: C^{-T} a_R ∝ b_R_{π}
    # i.e., C^{-T} maps a_R_l -> b_R_{π(l)}
    # Need 3 independent a_R vectors
    aR_basis = find_indep(r1_a, 1)
    aR_vecs = [np.array(r1_a[l][1], dtype=int) % p for l in aR_basis]
    M_aR = np.column_stack(aR_vecs) % p
    M_aR_inv = mat_inv_3(M_aR, p)
    if M_aR_inv is None: continue
    
    bR_targets = [np.array(r1_b[perm[l]][1], dtype=int) % p for l in aR_basis]
    M_bR = np.column_stack(bR_targets) % p
    if det3(M_bR, p) == 0: continue
    
    # C^{-T} = M_bR @ M_aR_inv, so C^{-T} = M_bR M_aR^{-1}
    C_inv_T = matmul3(M_bR, M_aR_inv, p)
    # C^T = (C^{-T})^{-1}
    CT = mat_inv_3(C_inv_T, p)
    if CT is None: continue
    C = CT.T % p
    C_inv = mat_inv_3(C, p)
    if C_inv is None: continue
    
    # FULL VERIFICATION: B a_l C^{-1} ∝ b_{π(l)} for all 23 terms
    # For rank-1 terms, we already know the permutation. Extend to all terms.
    full_valid = True
    full_perm = dict(perm)  # Start with rank-1 permutation
    
    for l in range(n):
        result = matmul3(matmul3(B, a_mats[l], p), C_inv, p)
        if l in full_perm:
            j = full_perm[l]
            if not mat_prop(result, b_mats[j], p):
                full_valid = False
                break
        else:
            # Find which b-term this matches
            found = False
            for j in range(n):
                if mat_prop(result, b_mats[j], p):
                    full_perm[l] = j
                    found = True
                    break
            if not found:
                full_valid = False
                break
    
    if not full_valid: continue
    
    # Check permutation is a bijection
    if len(set(full_perm.values())) != n: continue
    
    # Determine A from factor 1: A c_l B^{-1} ∝ a_{π(l)}
    B_inv = mat_inv_3(B, p)
    if B_inv is None: continue
    
    # Use 3 independent c_L vectors
    cL_basis_idx = find_indep(r1_c, 0)
    cL_vecs = [np.array(r1_c[l][0], dtype=int) % p for l in cL_basis_idx]
    M_cL = np.column_stack(cL_vecs) % p
    M_cL_inv = mat_inv_3(M_cL, p)
    if M_cL_inv is None: continue
    
    aL_targets = [np.array(r1_a[full_perm[l]][0], dtype=int) % p for l in cL_basis_idx]
    M_aL_tgt = np.column_stack(aL_targets) % p
    if det3(M_aL_tgt, p) == 0: continue
    
    A = matmul3(M_aL_tgt, M_cL_inv, p)
    
    # Verify A c_l B^{-1} ∝ a_{π(l)} for all l
    A_valid = True
    for l in range(n):
        result = matmul3(matmul3(A, c_mats[l], p), B_inv, p)
        j = full_perm[l]
        if not mat_prop(result, a_mats[j], p):
            A_valid = False
            break
    
    # Also verify factor 3: C b_l A^{-1} ∝ c_{π(l)}
    A_inv = mat_inv_3(A, p)
    if A_inv is None: continue
    
    C3_valid = True
    for l in range(n):
        result = matmul3(matmul3(C, b_mats[l], p), A_inv, p)
        j = full_perm[l]
        if not mat_prop(result, c_mats[j], p):
            C3_valid = False
            break
    
    if full_valid and A_valid and C3_valid:
        pi = [full_perm[l]+1 for l in range(n)]
        # Orbit structure
        visited = [False]*n
        fixed = []; three_cyc = []; other = []
        for l in range(n):
            if visited[l]: continue
            orb = [l]
            visited[l] = True
            nxt = full_perm[l]
            while nxt != l:
                orb.append(nxt)
                visited[nxt] = True
                nxt = full_perm[nxt]
            if len(orb) == 1: fixed.append(l+1)
            elif len(orb) == 3: three_cyc.append(tuple(o+1 for o in orb))
            else: other.append(tuple(o+1 for o in orb))
        
        auto = {
            "permutation": pi,
            "A": A.tolist(), "B": B.tolist(), "C": C.tolist(),
            "fixed_points": fixed,
            "three_cycles": three_cyc,
            "other_orbits": other,
            "f_sigma": len(fixed),
            "m_sigma": len(three_cyc),
            "factor_2_verified": True,
            "factor_1_verified": A_valid,
            "factor_3_verified": C3_valid,
        }
        verified_autos.append(auto)
        print(f"\n*** VERIFIED CYCLIC AUTOMORPHISM ***")
        print(f"  Permutation: {pi}")
        print(f"  Fixed points (f_σ={len(fixed)}): {fixed}")
        print(f"  3-cycles (m_σ={len(three_cyc)}): {three_cyc}")
        if other: print(f"  Other orbits: {other}")
        print(f"  B = {B.tolist()}")

print(f"\n{'='*60}")
print(f"TOTAL VERIFIED CYCLIC AUTOMORPHISMS: {len(verified_autos)}")

if verified_autos:
    print("\nLaderman IS S3-invariant (has cyclic Z3 automorphism)!")
    
    # S3 orbit structure for the first automorphism
    auto = verified_autos[0]
    pi = auto["permutation"]
    tau_perm = [1,5,6,4,2,3,16,18,17,10,14,12,15,11,13,7,9,8,19,22,21,20,23]
    
    sigma_fixed = set(auto["fixed_points"])
    tau_fixed = {i for i in range(1,24) if tau_perm[i-1] == i}
    
    print(f"\n  σ-fixed (cyclic): {sorted(sigma_fixed)}")
    print(f"  τ-fixed (transpose): {sorted(tau_fixed)}")
    print(f"  Both (S3 size-1 orbits): {sorted(sigma_fixed & tau_fixed)}")
    
    # Full S3 orbit computation
    def sigma_act(i): return pi[i-1]  # 1-indexed
    def tau_act(i): return tau_perm[i-1]  # 1-indexed
    
    visited = set()
    s3_orbits = {1: [], 2: [], 3: [], 6: []}
    for start in range(1, 24):
        if start in visited: continue
        orbit = set()
        queue = [start]
        while queue:
            cur = queue.pop()
            if cur in orbit: continue
            orbit.add(cur)
            queue.append(sigma_act(cur))
            queue.append(tau_act(cur))
        for o in orbit: visited.add(o)
        s3_orbits[len(orbit)].append(sorted(orbit))
    
    print(f"\n  S3 orbit structure:")
    for size in [1, 2, 3, 6]:
        if s3_orbits[size]:
            print(f"    Size {size}: {len(s3_orbits[size])} orbits: {s3_orbits[size]}")
    
    a = len(s3_orbits[1])
    b = len(s3_orbits[2])
    c = len(s3_orbits[3])
    d = len(s3_orbits[6])
    print(f"\n  S3 decomposition: (a,b,c,d) = ({a},{b},{c},{d})")
    print(f"  a + 2b + 3c + 6d = {a + 2*b + 3*c + 6*d} (should be 23)")
    print(f"  f_σ = a + 2b = {a + 2*b}")
    print(f"  m_σ = c + 2d = {c + 2*d}")
    print(f"  f_τ = a + c = {a + c}")
    print(f"  m_τ = b + c + 3d = {b + c + 3*d}")
else:
    print("\nLaderman does NOT have a cyclic automorphism.")

# Save results
results = {
    "num_verified": len(verified_autos),
    "has_cyclic": len(verified_autos) > 0,
    "automorphisms": verified_autos,
}
path = DATA / "laderman_cyclic_full_verification.json"
path.write_text(json.dumps(results, indent=2) + "\n")
print(f"\nSAVED {path}")
