#!/usr/bin/env python3
"""analysis: Tangent space to {KY rank <= 722} at BILR frame.

For the BILR residual cubic R, the Koszul-Young flattening M has rank 722 and
corank 412. For each of 32 internal frame directions (4 planes × 8 sl_3 basis),
compute the first-order change delta_R and test whether V^T KY(delta_R) U = 0,
where U = ker(M), V = ker(M^T).

The 8 torus directions (H1,H2 per plane) fix R exactly and are trivially tangent.
The question: are any of the 24 non-torus directions also tangent?

If the tangent equals the 8 torus directions, BILR is first-order isolated in
the low-rank stratum.
"""
import numpy as np, itertools, json, sys, time
from pathlib import Path

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'ky_tangent'
OUT.mkdir(parents=True, exist_ok=True)

sys.path.insert(0, str(WS / 'scripts'))
import ballard_z4_cyclic_scheme as bilr

P = 65521  # good prime: 1134 * P^2 < 2^63
N = 9

# ---- Koszul-Young flattening ----
SUB4 = list(itertools.combinations(range(N), 4))
SUB5 = list(itertools.combinations(range(N), 5))
SUB5_IDX = {s: i for i, s in enumerate(SUB5)}
NROWS = len(SUB5) * N  # 1134
NCOLS = len(SUB4) * N  # 1134

def poly_to_tensor(coeff, p):
    """Polynomial coeffs {sorted triple: int} -> symmetric 9x9x9 mod p."""
    T = np.zeros((N,N,N), dtype=np.int64)
    for key, c in coeff.items():
        perms = list(set(itertools.permutations(key)))
        inv_n = pow(len(perms), -1, p)
        val = (int(c) % p * inv_n) % p
        for perm in perms:
            T[perm] = val
    return T

def ky_from_tensor(T, p):
    """Build KY matrix from symmetric 3-tensor mod p."""
    M = np.zeros((NROWS, NCOLS), dtype=np.int64)
    for a in range(N):
        for sidx, S in enumerate(SUB4):
            Sset = set(S)
            col = a * len(SUB4) + sidx
            for i in range(N):
                if i in Sset: continue
                U5 = tuple(sorted((i,) + S))
                sgn = 1 if sum(1 for z in S if z < i) % 2 == 0 else p-1
                row0 = SUB5_IDX[U5] * N
                M[row0:row0+N, col] = (M[row0:row0+N, col] + sgn * T[a,i,:]) % p
    return M

def rref_kernel(M, p, side='right'):
    """Compute kernel basis. side='right' for ker(M), 'left' for ker(M^T)."""
    if side == 'left':
        M = M.T.copy() % p
    else:
        M = M.copy() % p
    m, n = M.shape
    pivots = []
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if M[i, c] % p:
                piv = i; break
        if piv is None: continue
        if piv != r:
            M[[r, piv]] = M[[piv, r]]
        inv = pow(int(M[r, c] % p), -1, p)
        M[r] = (M[r] * inv) % p
        nzr = np.nonzero(M[:, c] % p)[0]
        for i in nzr:
            if i != r:
                M[i] = (M[i] - (M[i,c] % p) * M[r]) % p
        pivots.append((r, c))
        r += 1
    
    rank = r
    pivot_set = set(pc for _, pc in pivots)
    free_cols = [c for c in range(n) if c not in pivot_set]
    
    vecs = []
    for fc in free_cols:
        v = np.zeros(n, dtype=np.int64)
        v[fc] = 1
        for pr, pc in pivots:
            v[pc] = (-M[pr, fc]) % p
        vecs.append(v)
    
    if not vecs:
        return rank, np.zeros((0, n), dtype=np.int64)
    return rank, np.array(vecs, dtype=np.int64) % p

# ---- BILR scheme ----
print("Loading BILR scheme...", flush=True)
terms, cubes, free_orbits, powers, a0 = bilr.build_scheme()

# Residual cubic = cube polynomial (this is what's left after removing free orbits from target)
res_coeff = {}
for C in cubes:
    u = [int(x) for x in bilr.flatten(C)]
    for i,j,k in itertools.product(range(N), repeat=3):
        val = (u[i]*u[j]*u[k]) % P
        if val:
            key = tuple(sorted([i,j,k]))
            res_coeff[key] = (res_coeff.get(key,0)+val) % P
res_coeff = {k: v%P for k,v in res_coeff.items() if v%P}

res_tensor = poly_to_tensor(res_coeff, P)
print(f"Residual has {len(res_coeff)} nonzero polynomial coefficients", flush=True)

# ---- Build KY matrix ----
print("Building KY matrix...", flush=True)
t0 = time.time()
M0 = ky_from_tensor(res_tensor, P)
print(f"  Built in {time.time()-t0:.1f}s, shape {M0.shape}", flush=True)

# ---- Extract kernels ----
print("Extracting right kernel (ker M)...", flush=True)
t0 = time.time()
rank0, U_ker = rref_kernel(M0, P, side='right')
print(f"  Rank={rank0}, ker dim={U_ker.shape[0]}, time={time.time()-t0:.1f}s", flush=True)

print("Extracting left kernel (ker M^T)...", flush=True)
t0 = time.time()
rank0T, V_ker = rref_kernel(M0, P, side='left')
assert rank0 == rank0T, f"rank mismatch: {rank0} vs {rank0T}"
print(f"  Coker dim={V_ker.shape[0]}, time={time.time()-t0:.1f}s", flush=True)

# Verify V @ M0 = 0 using float64 BLAS
VT = V_ker.astype(np.float64)
M0f = M0.astype(np.float64)
check = (VT @ M0f) % P
check = np.round(check).astype(np.int64) % P
assert np.all(check == 0), f"V@M0 not zero! max={np.max(np.abs(check))}"
print("  Verified V @ M0 = 0 mod P", flush=True)

UT = U_ker.T.astype(np.float64)  # NCOLS × ker_dim

# ---- Frame directions ----
# For each orbit j and sl_3 basis A_k, compute δR and build KY(δR).
# The 4 free orbits have frames F_j = [flat(U_j), flat(V_j), flat(W_j)] (9-vectors).
# Right-multiplying by I + ε A_k gives:
#   δU = A_{00} U + A_{10} V + A_{20} W  (for column 0 of F @ A)
#   δV = A_{01} U + A_{11} V + A_{21} W  (for column 1)
#   δW = A_{02} U + A_{12} V + A_{22} W  (for column 2)
# The orbit j polynomial changes by:
#   δ(orbit_j) = 3*(δU·V·W + U·δV·W + U·V·δW) as polynomial coefficients

SL3_BASIS = [
    ("E12", [[0,1,0],[0,0,0],[0,0,0]]),  # A[0,1]=1
    ("E13", [[0,0,1],[0,0,0],[0,0,0]]),  # A[0,2]=1
    ("E21", [[0,0,0],[1,0,0],[0,0,0]]),  # A[1,0]=1
    ("E23", [[0,0,0],[0,0,1],[0,0,0]]),  # A[1,2]=1
    ("E31", [[0,0,0],[0,0,0],[1,0,0]]),  # A[2,0]=1
    ("E32", [[0,0,0],[0,0,0],[0,1,0]]),  # A[2,1]=1
    ("H1",  [[1,0,0],[0,-1,0],[0,0,0]]), # diag(1,-1,0)
    ("H2",  [[0,0,0],[0,1,0],[0,0,-1]]), # diag(0,1,-1)
]

def orbit_delta_coeffs(orbit_j, A_mat, p):
    """First-order polynomial coefficient change for orbit j under A_mat."""
    Uj, Vj, Wj = orbit_j
    u = np.array(bilr.flatten(Uj), dtype=np.int64) % p
    v = np.array(bilr.flatten(Vj), dtype=np.int64) % p
    w = np.array(bilr.flatten(Wj), dtype=np.int64) % p
    A = np.array(A_mat, dtype=np.int64)
    
    du = (A[0,0]*u + A[1,0]*v + A[2,0]*w) % p
    dv = (A[0,1]*u + A[1,1]*v + A[2,1]*w) % p
    dw = (A[0,2]*u + A[1,2]*v + A[2,2]*w) % p
    
    # δ(orbit) = 3*(du·v·w + u·dv·w + u·v·dw) summed over all index permutations
    coeff = {}
    for ii,jj,kk in itertools.product(range(N), repeat=3):
        val = (3 * (du[ii]*v[jj]*w[kk] + u[ii]*dv[jj]*w[kk] + u[ii]*v[jj]*dw[kk])) % p
        if val:
            key = tuple(sorted([ii,jj,kk]))
            coeff[key] = (coeff.get(key,0) + val) % p
    return {k: v%p for k,v in coeff.items() if v%p}

# ---- Run tangent test ----
print("\n=== Testing 32 frame tangent directions ===", flush=True)
results = []

for j in range(4):
    for ki, (name, Amat) in enumerate(SL3_BASIS):
        # δR = -(δ orbit_j poly)
        dc = orbit_delta_coeffs(free_orbits[j], Amat, P)
        # Negate: δR = -δ(orbit)
        dc_neg = {k: (P - v) % P for k, v in dc.items()}
        
        if not dc_neg:
            # δR = 0 means the direction fixes R exactly
            results.append({
                'orbit': j, 'basis': name, 'dR_zero': True,
                'VdMU_rank': 0, 'tangent': True
            })
            print(f"  orbit={j} basis={name}: δR=0 (fixes R), trivially tangent", flush=True)
            continue
        
        # Build KY(δR)
        dT = poly_to_tensor(dc_neg, P)
        dM = ky_from_tensor(dT, P)
        
        # Compute V^T @ dM @ U using float64 BLAS
        dMf = dM.astype(np.float64)
        VdM = (VT @ dMf)  # coker_dim × NCOLS
        VdM = np.round(VdM).astype(np.int64) % P
        VdMU = (VdM.astype(np.float64) @ UT)  # coker_dim × ker_dim
        VdMU = np.round(VdMU).astype(np.int64) % P
        
        rk = 0
        if VdMU.size > 0:
            # Compute rank of VdMU
            flat = VdMU.copy()
            m2, n2 = flat.shape
            r2 = 0
            for c2 in range(n2):
                piv2 = None
                for i2 in range(r2, m2):
                    if flat[i2, c2] % P:
                        piv2 = i2; break
                if piv2 is None: continue
                if piv2 != r2:
                    flat[[r2, piv2]] = flat[[piv2, r2]]
                inv2 = pow(int(flat[r2, c2] % P), -1, P)
                flat[r2] = (flat[r2] * inv2) % P
                nz2 = np.nonzero(flat[:, c2] % P)[0]
                for i2 in nz2:
                    if i2 != r2:
                        flat[i2] = (flat[i2] - (flat[i2, c2] % P) * flat[r2]) % P
                r2 += 1
            rk = r2
        
        is_tangent = (rk == 0)
        results.append({
            'orbit': j, 'basis': name, 'dR_zero': False,
            'VdMU_rank': int(rk), 'tangent': is_tangent
        })
        print(f"  orbit={j} basis={name}: δR nonzero ({len(dc_neg)} terms), "
              f"rank(V^T dM U)={rk}, tangent={is_tangent}", flush=True)

# ---- Summary ----
tangent_dirs = [r for r in results if r['tangent']]
nontorus_tangent = [r for r in tangent_dirs if r['basis'] not in ('H1','H2')]
torus_tangent = [r for r in tangent_dirs if r['basis'] in ('H1','H2')]

summary = {
    'prime': P,
    'ky_rank': rank0,
    'ky_corank': NROWS - rank0,
    'ker_dim': int(U_ker.shape[0]),
    'coker_dim': int(V_ker.shape[0]),
    'total_directions': 32,
    'tangent_directions': len(tangent_dirs),
    'torus_tangent': len(torus_tangent),
    'nontorus_tangent': len(nontorus_tangent),
    'nontorus_tangent_list': [f"orbit{r['orbit']}_{r['basis']}" for r in nontorus_tangent],
    'first_order_isolated': len(nontorus_tangent) == 0,
    'interpretation': (
        "If first_order_isolated=True, the BILR frame is first-order isolated "
        "in the KY-low-rank stratum. The rank-≤10 locus cannot be reached by "
        "internal frame deformation."
    ),
}

print(f"\n=== Summary ===\n{json.dumps(summary, indent=2)}")

out_path = OUT / 'ky_tangent_at_bilr.json'
out_path.write_text(json.dumps({
    'summary': summary,
    'directions': results,
}, indent=2) + '\n')
print(f"\nSAVED {out_path}")
