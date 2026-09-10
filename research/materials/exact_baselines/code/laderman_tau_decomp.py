#!/usr/bin/env python3
"""analysis: Extract the Laderman algorithm's tau decomposition.

From Burichenko (1508.01110), the Laderman algorithm has 23 terms:
t_1,...,t_23 where each t_l = a_l ⊗ b_l ⊗ c_l^T (third factor transposed).

The tau-type automorphism Phi3*Phi4 permutes these 23 terms.
We compute:
1. The permutation of terms under Phi3*Phi4
2. The number of fixed points (f) and 2-cycles (m)  
3. The tau skeleton (f, m) for this rank-23 positive control
"""
import numpy as np
from pathlib import Path
import json

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / "data" / "laderman_tau"
DATA_DIR.mkdir(parents=True, exist_ok=True)

# 3x3 matrix unit
def E(i, j):
    M = np.zeros((3,3), dtype=int)
    M[i,j] = 1
    return M

# Special matrices from Burichenko
pi12 = E(0,1) + E(1,0) + E(2,2)
pi13 = E(0,2) + E(1,1) + E(2,0)
pi23 = E(0,0) + E(1,2) + E(2,1)
eps1 = np.diag([-1,1,1])
eps2 = np.diag([1,-1,1])
I3 = np.eye(3, dtype=int)

# Define the 23 Laderman terms from Burichenko's tensor form
# Each term is (a, b, c_transposed) where the tensor is a ⊗ b ⊗ c^T
terms = []

# t1: (e11+e12+e13-e21-e22-e32-e33) ⊗ e22 ⊗ e21
terms.append((E(0,0)+E(0,1)+E(0,2)-E(1,0)-E(1,1)-E(2,1)-E(2,2), E(1,1), E(1,0)))
# t2: (e11-e21) ⊗ (-e12+e22) ⊗ (e12+e22)  
terms.append((E(0,0)-E(1,0), -E(0,1)+E(1,1), E(0,1)+E(1,1)))
# t3: e22 ⊗ (-e11+e12+e21-e22-e23-e31+e33) ⊗ e12
terms.append((E(1,1), -E(0,0)+E(0,1)+E(1,0)-E(1,1)-E(1,2)-E(2,0)+E(2,2), E(0,1)))
# t4: (-e11+e21+e22) ⊗ (e11-e12+e22) ⊗ (e21+e12+e22)
terms.append((-E(0,0)+E(1,0)+E(1,1), E(0,0)-E(0,1)+E(1,1), E(1,0)+E(0,1)+E(1,1)))
# t5: (e21+e22) ⊗ (-e11+e12) ⊗ (e21+e22)
terms.append((E(1,0)+E(1,1), -E(0,0)+E(0,1), E(1,0)+E(1,1)))
# t6: e11 ⊗ e11 ⊗ (e11+e21+e31+e12+e22+e13+e33)
terms.append((E(0,0), E(0,0), E(0,0)+E(1,0)+E(2,0)+E(0,1)+E(1,1)+E(0,2)+E(2,2)))
# t7: (-e11+e31+e32) ⊗ (e11-e13+e23) ⊗ (e31+e13+e33)
terms.append((-E(0,0)+E(2,0)+E(2,1), E(0,0)-E(0,2)+E(1,2), E(2,0)+E(0,2)+E(2,2)))
# t8: (-e11+e31) ⊗ (e13-e23) ⊗ (e13+e33)
terms.append((-E(0,0)+E(2,0), E(0,2)-E(1,2), E(0,2)+E(2,2)))
# t9: (e31+e32) ⊗ (-e11+e13) ⊗ (e31+e33)
terms.append((E(2,0)+E(2,1), -E(0,0)+E(0,2), E(2,0)+E(2,2)))
# t10: (e11+e12+e13-e22-e23-e31-e32) ⊗ e23 ⊗ e31
terms.append((E(0,0)+E(0,1)+E(0,2)-E(1,1)-E(1,2)-E(2,0)-E(2,1), E(1,2), E(2,0)))
# t11: e32 ⊗ (-e11+e13+e21-e22-e23-e31+e32) ⊗ e13
terms.append((E(2,1), -E(0,0)+E(0,2)+E(1,0)-E(1,1)-E(1,2)-E(2,0)+E(2,1), E(0,2)))
# t12: (-e13+e32+e33) ⊗ (e22+e31-e32) ⊗ (e21+e13+e23)  
terms.append((-E(0,2)+E(2,1)+E(2,2), E(1,1)+E(2,0)-E(2,1), E(1,0)+E(0,2)+E(1,2)))
# t13: (e13-e33) ⊗ (e22-e32) ⊗ (e13+e23)
terms.append((E(0,2)-E(2,2), E(1,1)-E(2,1), E(0,2)+E(1,2)))
# t14: e13 ⊗ e31 ⊗ (e11+e21+e31+e12+e32+e13+e23)
terms.append((E(0,2), E(2,0), E(0,0)+E(1,0)+E(2,0)+E(0,1)+E(2,1)+E(0,2)+E(1,2)))
# t15: (e32+e33) ⊗ (-e31+e32) ⊗ (e21+e23)
terms.append((E(2,1)+E(2,2), -E(2,0)+E(2,1), E(1,0)+E(1,2)))
# t16: (-e13+e22+e23) ⊗ (e23+e31-e33) ⊗ (e31+e12+e32)
terms.append((-E(0,2)+E(1,1)+E(1,2), E(1,2)+E(2,0)-E(2,2), E(2,0)+E(0,1)+E(2,1)))
# t17: (e13-e23) ⊗ (e23-e33) ⊗ (e12+e32)
terms.append((E(0,2)-E(1,2), E(1,2)-E(2,2), E(0,1)+E(2,1)))
# t18: (e22+e23) ⊗ (-e31+e33) ⊗ (e31+e32)
terms.append((E(1,1)+E(1,2), -E(2,0)+E(2,2), E(2,0)+E(2,1)))
# t19: e12 ⊗ e21 ⊗ e11
terms.append((E(0,1), E(1,0), E(0,0)))
# t20: e23 ⊗ e32 ⊗ e22
terms.append((E(1,2), E(2,1), E(1,1)))
# t21: e21 ⊗ e13 ⊗ e32
terms.append((E(1,0), E(0,2), E(2,1)))
# t22: e31 ⊗ e12 ⊗ e23
terms.append((E(2,0), E(0,1), E(1,2)))
# t23: e33 ⊗ e33 ⊗ e33
terms.append((E(2,2), E(2,2), E(2,2)))

print(f"Loaded {len(terms)} Laderman terms")

# Verify: sum of terms should be <3,3,3>
T333 = np.zeros((9,9,9), dtype=int)
for i in range(3):
    for j in range(3):
        for k in range(3):
            T333[3*i+j, 3*j+k, 3*k+i] = 1

T_sum = np.zeros((9,9,9), dtype=int)
for a, b, c in terms:
    # In tensor form: a ⊗ b ⊗ c^T
    # But Burichenko writes the third factor already as c^T
    # Check: t19 = e12 ⊗ e21 ⊗ e11, and the contribution to z11 = x12*y21
    # means c_{11,19} = 1, i.e., c_19 = e_11, c_19^T = e_11.
    # So the third factor in the tensor product IS c^T = e_11 for t19.
    # But e_{ki} in T333 at (i,j,k)=(0,1,0): e_{ki}=e_{01}.
    # And t19 at e12 ⊗ e21 ⊗ e11: i=0,j=1 for first, j=1,k=0 for second, 
    # k=0,i=0 for third. Check: e_{ki} = e_{00} = e11. Yes.
    for r1 in range(3):
        for c1 in range(3):
            for r2 in range(3):
                for c2 in range(3):
                    for r3 in range(3):
                        for c3 in range(3):
                            T_sum[3*r1+c1, 3*r2+c2, 3*r3+c3] += a[r1,c1]*b[r2,c2]*c[r3,c3]

print(f"Sum matches T333: {np.array_equal(T_sum, T333)}")

# Define Phi3 and Phi4
def Phi3(a, b, c):
    """Phi3(x⊗y⊗z) = y^T eps2 ⊗ eps2 x^T ⊗ z^T"""
    return (b.T @ eps2, eps2 @ a.T, c.T)

def Phi4(a, b, c):
    """Phi4(x⊗y⊗z) = eps1 z pi12 ⊗ pi12 x pi12 eps1 ⊗ eps1 pi12 y eps1"""
    return (eps1 @ c @ pi12, pi12 @ a @ pi12 @ eps1, eps1 @ pi12 @ b @ eps1)

def compose_phi(f, g, a, b, c):
    a1, b1, c1 = g(a, b, c)
    return f(a1, b1, c1)

# Apply Phi3*Phi4 to each term and find the permutation
print("\n=== Permutation of terms under Phi3*Phi4 ===")

phi_terms = []
for a, b, c in terms:
    a1, b1, c1 = compose_phi(Phi3, Phi4, a, b, c)
    phi_terms.append((a1, b1, c1))

# Match each transformed term to an original term (up to scaling)
permutation = [None] * 23
for i, (a1, b1, c1) in enumerate(phi_terms):
    for j, (a2, b2, c2) in enumerate(terms):
        # Check proportionality: a1 = lambda * a2, b1 = mu * b2, c1 = nu * c2
        # with lambda * mu * nu = 1
        # Find lambda from first nonzero entry
        lam = None
        for r in range(3):
            for c in range(3):
                if a2[r,c] != 0:
                    lam = a1[r,c] / a2[r,c]
                    break
            if lam is not None: break
        
        if lam is None or lam == 0:
            if np.allclose(a1, 0) and np.allclose(a2, 0):
                lam = 1  # both zero, check other factors
            else:
                continue
        
        if not np.allclose(a1, lam * a2): continue
        
        mu = None
        for r in range(3):
            for cc in range(3):
                if b2[r,cc] != 0:
                    mu = b1[r,cc] / b2[r,cc]
                    break
            if mu is not None: break
        
        if mu is None or mu == 0: continue
        if not np.allclose(b1, mu * b2): continue
        
        nu = None
        for r in range(3):
            for cc in range(3):
                if c2[r,cc] != 0:
                    nu = c1[r,cc] / c2[r,cc]
                    break
            if nu is not None: break
        
        if nu is None or nu == 0: continue
        if not np.allclose(c1, nu * c2): continue
        
        # Check lambda * mu * nu ≈ 1 (may be ±1 due to scaling freedom)
        product = lam * mu * nu
        if abs(abs(product) - 1) < 1e-10:
            permutation[i] = j
            break
    
    if permutation[i] is not None:
        j = permutation[i]
        print(f"  t_{i+1:2d} -> t_{j+1:2d} (scale: {lam:.0f},{mu:.0f},{nu:.0f})")
    else:
        print(f"  t_{i+1:2d} -> ??? (NOT FOUND)")

# Compute fixed points and 2-cycles
fixed_points = [i for i in range(23) if permutation[i] == i]
two_cycles = []
seen = set()
for i in range(23):
    j = permutation[i]
    if j is not None and j != i and i not in seen:
        if permutation[j] == i:
            two_cycles.append((i, j))
            seen.add(i)
            seen.add(j)

f = len(fixed_points)
m = len(two_cycles)

print(f"\nFixed points (f): {f} -> terms {[i+1 for i in fixed_points]}")
print(f"2-cycles (m): {m} -> {[(i+1,j+1) for i,j in two_cycles]}")
print(f"Tau skeleton: (f={f}, m={m}), rank = {f + 2*m}")
print(f"N = f + m = {f + m}")

results = {
    "permutation": [int(p+1) if p is not None else None for p in permutation],
    "fixed_points": [int(i+1) for i in fixed_points],
    "two_cycles": [(int(i+1), int(j+1)) for i, j in two_cycles],
    "f": f, "m": m, "N": f + m, "rank": f + 2*m,
    "note": "Laderman algorithm tau decomposition under Phi3*Phi4"
}

# Verify the tau-type action on these terms
# For each fixed point i, check: a_i^T = lambda * a_i (symmetric or antisymmetric?)
print("\n=== Fixed term analysis ===")
for i in fixed_points:
    a, b, c = terms[i]
    a1, b1, c1 = phi_terms[i]
    print(f"  t_{i+1}: a symmetric: {np.allclose(a, a.T)}, "
          f"b=c^T: {np.allclose(b, c.T)}")

out_path = DATA_DIR / "laderman_tau_decomposition.json"
with open(out_path, 'w') as f:
    json.dump(results, f, indent=2)
print(f"\nSAVED {out_path}")
