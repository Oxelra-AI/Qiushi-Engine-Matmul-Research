#!/usr/bin/env python3
"""
analysis: Exact integer Jennrich certificate on gl_3.
Find integer directions where the BILR commutator has a nonzero 3x3 minor.
"""

import numpy as np
import json
from pathlib import Path
from itertools import combinations

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "hessian_commutator"
OUT.mkdir(parents=True, exist_ok=True)

p = 65521

def modinv(a, m):
    a = a % m
    g, x, _ = extended_gcd(a, m)
    if g != 1: return None
    return x % m

def extended_gcd(a, b):
    if a == 0: return b, 0, 1
    g, x1, y1 = extended_gcd(b % a, a)
    return g, y1 - (b // a) * x1, x1

def rank_mod_p(M, p):
    M = M.copy() % p
    n, m = M.shape
    r = 0
    for col in range(m):
        pivot = -1
        for row in range(r, n):
            if M[row, col] % p != 0:
                pivot = row; break
        if pivot < 0: continue
        M[[r, pivot]] = M[[pivot, r]]
        inv_d = modinv(int(M[r, col]), p)
        if inv_d is None: continue
        M[r] = (M[r] * inv_d) % p
        for row in range(n):
            if row != r and M[row, col] % p != 0:
                M[row] = (M[row] - int(M[row, col]) * M[r]) % p
        r += 1
    return r

# gl_3 setup
basis_gl3 = []
for i in range(3):
    for j in range(3):
        M = np.zeros((3,3), dtype=int); M[i,j] = 1
        basis_gl3.append(M)
names_gl3 = [f"E{i}{j}" for i in range(3) for j in range(3)]

K = np.zeros((9,9), dtype=int)
for a in range(9):
    for b in range(9):
        K[a,b] = int(np.trace(basis_gl3[a] @ basis_gl3[b]))

# K = K^{-1} (involution)
assert np.all(K @ K == np.eye(9, dtype=int)), "K not involution"

# Load BILR
with open(WS / "data/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json") as f:
    bilr = json.load(f)
cubes_mat = [np.array(c, dtype=int) for c in bilr["cubes"]]
cube_forms = np.array([[int(np.trace(L.T @ basis_gl3[k])) for k in range(9)] for L in cubes_mat])
cube_traces = np.array([int(np.trace(L)) for L in cubes_mat])
w = cube_traces**3
mu = np.array([cube_traces[i] * cube_forms[i] for i in range(11)], dtype=np.int64)

# Verify moment: sum w_i mu_i mu_i^T = K
M2 = np.zeros((9,9), dtype=np.int64)
for i in range(11):
    M2 += w[i] * np.outer(mu[i], mu[i])
assert np.all(M2 == K), "Moment check failed"
print("gl_3 moment verified: sum w_i mu_i mu_i^T = K")

# Check mu rank on gl_3
for pp in [65521, 100003]:
    r = rank_mod_p(mu.astype(int) % pp, pp)
    print(f"mu matrix rank mod {pp}: {r}")

# Integer Hessian computation
# H(X) = 6 * sum_i w_i (mu_i.x) mu_i mu_i^T K^{-1}
# Since K^{-1} = K:
# H(X) = 6 * sum_i w_i (mu_i.x) mu_i mu_i^T K
# = 6 * [sum_i w_i (mu_i.x) mu_i mu_i^T] K

def hessian_K_int(x, mu, w, K):
    """H(X) = 6 * sum w_i (mu_i.x) mu_i mu_i^T K over integers."""
    n = mu.shape[1]
    H = np.zeros((n,n), dtype=np.int64)
    for i in range(len(w)):
        c = 6 * int(w[i]) * int(np.dot(mu[i], x))
        H += c * np.outer(mu[i], mu[i])
    return H @ K

# Test with small integer directions
rng = np.random.RandomState(42)
print("\nSearching for integer direction pair with nonzero commutator...")

found = False
for trial in range(200):
    # Use small integers to keep numbers manageable
    x1 = rng.randint(-3, 4, size=9).astype(np.int64)
    x2 = rng.randint(-3, 4, size=9).astype(np.int64)
    
    H1 = hessian_K_int(x1, mu, w, K)
    H2 = hessian_K_int(x2, mu, w, K)
    comm = H1 @ H2 - H2 @ H1
    
    if np.any(comm != 0):
        # Check rank mod p
        r = rank_mod_p(comm.astype(int) % p, p)
        if r >= 3:
            print(f"  trial {trial}: x1={x1.tolist()}, x2={x2.tolist()}")
            print(f"  comm rank mod {p} = {r}")
            print(f"  comm max abs entry = {np.max(np.abs(comm))}")
            
            # Find nonzero 3x3 minor
            for rows in combinations(range(9), 3):
                for cols in combinations(range(9), 3):
                    sub = comm[np.ix_(list(rows), list(cols))]
                    d = int(sub[0,0]*(sub[1,1]*sub[2,2]-sub[1,2]*sub[2,1])
                           -sub[0,1]*(sub[1,0]*sub[2,2]-sub[1,2]*sub[2,0])
                           +sub[0,2]*(sub[1,0]*sub[2,1]-sub[1,1]*sub[2,0]))
                    if d != 0:
                        print(f"  3x3 minor: rows={rows}, cols={cols}, det={d}")
                        found = True
                        cert_x1 = x1.tolist()
                        cert_x2 = x2.tolist()
                        cert_rows = list(rows)
                        cert_cols = list(cols)
                        cert_det = d
                        cert_sub = sub.tolist()
                        cert_rank = r
                        break
                if found: break
            break

if not found:
    # Try with pure sum-of-basis directions
    for a in range(9):
        for b in range(a+1, 9):
            x1 = np.zeros(9, dtype=np.int64)
            x2 = np.zeros(9, dtype=np.int64)
            # x1 = e_a + e_b, x2 = e_a - e_b
            x1[a] = 1; x1[b] = 1
            x2[a] = 1; x2[b] = -1
            H1 = hessian_K_int(x1, mu, w, K)
            H2 = hessian_K_int(x2, mu, w, K)
            comm = H1 @ H2 - H2 @ H1
            if np.any(comm != 0):
                r = rank_mod_p(comm.astype(int) % p, p)
                if r >= 3:
                    print(f"  sum-of-basis: a={a}({names_gl3[a]}), b={b}({names_gl3[b]})")
                    print(f"  x1={x1.tolist()}, x2={x2.tolist()}, rank={r}")
                    # Find minor
                    for rows in combinations(range(9), 3):
                        for cols in combinations(range(9), 3):
                            sub = comm[np.ix_(list(rows), list(cols))]
                            d = int(sub[0,0]*(sub[1,1]*sub[2,2]-sub[1,2]*sub[2,1])
                                   -sub[0,1]*(sub[1,0]*sub[2,2]-sub[1,2]*sub[2,0])
                                   +sub[0,2]*(sub[1,0]*sub[2,1]-sub[1,1]*sub[2,0]))
                            if d != 0:
                                found = True
                                cert_x1 = x1.tolist()
                                cert_x2 = x2.tolist()
                                cert_rows = list(rows)
                                cert_cols = list(cols)
                                cert_det = d
                                cert_sub = sub.tolist()
                                cert_rank = r
                                print(f"  3x3 minor: rows={rows}, cols={cols}, det={d}")
                                break
                        if found: break
                if found: break
        if found: break

if found:
    # Multi-prime verification
    primes = [65521, 100003, 1000003, 32003]
    x1_arr = np.array(cert_x1, dtype=np.int64)
    x2_arr = np.array(cert_x2, dtype=np.int64)
    H1 = hessian_K_int(x1_arr, mu, w, K)
    H2 = hessian_K_int(x2_arr, mu, w, K)
    comm = H1 @ H2 - H2 @ H1
    
    multi_prime = []
    for pp in primes:
        r = rank_mod_p(comm.astype(int) % pp, pp)
        d_mod = cert_det % pp
        multi_prime.append({"prime": pp, "rank": r, "det_mod_p": int(d_mod)})
        print(f"  p={pp}: rank={r}, det mod p = {d_mod}")
    
    result = {
        "scope": "Exact integer Jennrich commutator certificate for BILR on gl_3.",
        "theorem": (
            "For k cubes in gl_3 (dim 9) with sum w_i mu_i^2 = K (trace form), "
            "rank([H(X),H(Y)]) <= 2*max(0, k-9). "
            "Proof: for k = n+1 = 10, in any 9-vector basis, H(X) = diag(Mx) + u(y)v^T "
            "(diagonal + rank-1). The key identity "
            "y∘u(z) - z∘u(y) = -(α·z)u(y) + (α·y)u(z) "
            "shows the commutator column space ⊆ span(u(y),u(z)), hence rank ≤ 2."
        ),
        "bilr_cube_count": 11,
        "gl3_dimension": 9,
        "expected_max_comm_rank_for_10_cubes": 2,
        "bilr_comm_rank": cert_rank,
        "bilr_rank_exceeds_10cube_bound": cert_rank > 2,
        "certificate": {
            "x1": cert_x1,
            "x2": cert_x2,
            "minor_rows": cert_rows,
            "minor_cols": cert_cols,
            "exact_integer_determinant": cert_det,
            "sub_matrix_integer": cert_sub
        },
        "multi_prime_verification": multi_prime,
        "conclusion": (
            "The BILR residual cubic on gl_3 has Waring rank ≥ 11 > 10, "
            "proved by the nonzero 3×3 minor of the Hessian commutator. "
            "Any (10,4) decomposition on the BILR exterior component is excluded: "
            "the 10 cubes would give commutator rank ≤ 2, contradicting rank ≥ 3."
        )
    }
    
    out_path = OUT / "jennrich_integer_certificate.json"
    with open(out_path, 'w') as f:
        json.dump(result, f, indent=2)
    print(f"\nCertificate saved to {out_path}")
else:
    print("\nNo nonzero 3x3 minor found! Checking all commutator ranks...")
    for trial in range(20):
        x1 = rng.randint(-5, 6, size=9).astype(np.int64)
        x2 = rng.randint(-5, 6, size=9).astype(np.int64)
        H1 = hessian_K_int(x1, mu, w, K)
        H2 = hessian_K_int(x2, mu, w, K)
        comm = H1 @ H2 - H2 @ H1
        r = rank_mod_p(comm.astype(int) % p, p)
        print(f"  trial {trial}: rank = {r}, max entry = {np.max(np.abs(comm))}")
    
    # Also check if the modular rank was correct
    print("\nDirect modular computation (reproducing earlier result):")
    from functools import reduce
    def mat_inv_mod(M, p):
        n = M.shape[0]
        A = M.copy() % p
        I_n = np.eye(n, dtype=int)
        aug = np.hstack([A, I_n])
        for col in range(n):
            pivot = -1
            for row in range(col, n):
                if aug[row, col] % p != 0:
                    pivot = row; break
            if pivot < 0: return None
            aug[[col, pivot]] = aug[[pivot, col]]
            inv_d = modinv(int(aug[col, col]), p)
            if inv_d is None: return None
            aug[col] = (aug[col] * inv_d) % p
            for row in range(n):
                if row != col and aug[row, col] % p != 0:
                    aug[row] = (aug[row] - int(aug[row, col]) * aug[col]) % p
        return aug[:, n:] % p
    
    Kinv_mod = mat_inv_mod(K % p, p)
    # Verify K @ Kinv = I mod p
    check = (K @ Kinv_mod) % p
    print(f"K @ Kinv mod p = I? {np.all(check == np.eye(9, dtype=int) % p)}")
    print(f"K = Kinv mod p? {np.all(K % p == Kinv_mod)}")
    
    for trial in range(5):
        x1 = rng.randint(0, p, size=9).astype(int)
        x2 = rng.randint(0, p, size=9).astype(int)
        # Using Kinv_mod
        H1_mod = np.zeros((9,9), dtype=int)
        H2_mod = np.zeros((9,9), dtype=int)
        for i in range(11):
            c1 = int(6 * w[i] * np.dot(mu[i] % p, x1)) % p
            c2 = int(6 * w[i] * np.dot(mu[i] % p, x2)) % p
            ou = np.outer(mu[i] % p, mu[i] % p) % p
            H1_mod = (H1_mod + c1 * ou) % p
            H2_mod = (H2_mod + c2 * ou) % p
        H1_mod = H1_mod @ Kinv_mod % p
        H2_mod = H2_mod @ Kinv_mod % p
        comm_mod = (H1_mod @ H2_mod - H2_mod @ H1_mod) % p
        r = rank_mod_p(comm_mod, p)
        print(f"  Modular trial {trial}: rank = {r}")
