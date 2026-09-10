#!/usr/bin/env python3
"""
analysis: Check if the numerical rank-4 exterior decomposition from analysis
is in the same PGL_3(= Stab(omega)) orbit as the BILR (11,4) exterior decomposition.

If yes: the rank-4 fiber is a single orbit, and semicontinuity + Koszul rank 722
closes the m=4 cyclic rank-22 case.

Method: Stab(omega) = ad(SL_3) acts on sl_3 by conjugation. We need to find
g in GL_3 such that ad(g) maps the four BILR three-planes to the four numerical
three-planes (up to permutation and internal GL_3 within each plane).
"""
import numpy as np, itertools, json, sys
from pathlib import Path
from scipy.optimize import minimize

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = ROOT / 'data' / 'fiber_orbit'
OUT.mkdir(parents=True, exist_ok=True)

# ── sl_3 basis (traceless 3x3 matrices, row-major vectorized to R^8) ──
def sl3_basis_mats():
    """Return 8 basis matrices for sl_3 as 3x3 arrays."""
    basis = []
    for i in range(3):
        for j in range(3):
            if i != j:
                M = np.zeros((3,3)); M[i,j] = 1; basis.append(M)
    M = np.zeros((3,3)); M[0,0]=1; M[1,1]=-1; basis.append(M)
    M = np.zeros((3,3)); M[1,1]=1; M[2,2]=-1; basis.append(M)
    return basis

SL3_BASIS = sl3_basis_mats()

def vec9_to_sl3(v):
    """Project a 9-vector (row-major gl_3) to sl_3 coordinates (8-dim)."""
    M = v.reshape(3,3)
    M_tf = M - np.trace(M)/3 * np.eye(3)  # trace-free part
    coords = np.array([np.sum(B * M_tf) for B in SL3_BASIS])
    return coords

def sl3_to_mat(coords):
    """Convert sl_3 coordinates to a 3x3 traceless matrix."""
    return sum(c * B for c, B in zip(coords, SL3_BASIS))

def adjoint_action(g, M):
    """ad(g)(M) = g M g^{-1}."""
    return g @ M @ np.linalg.inv(g)

def wedge_3(u, v, w):
    """Compute u ∧ v ∧ w in Lambda^3(R^8) from sl_3 coordinate vectors."""
    n = len(u)
    result = {}
    for i in range(n):
        for j in range(i+1, n):
            for k in range(j+1, n):
                val = (u[i]*(v[j]*w[k] - v[k]*w[j])
                     - u[j]*(v[i]*w[k] - v[k]*w[i])
                     + u[k]*(v[i]*w[j] - v[j]*w[i]))
                if abs(val) > 1e-14:
                    result[(i,j,k)] = val
    return result

# ── Load BILR (11,4) scheme ───────────────────────────────────────────
def load_bilr_114():
    """Load the BILR rank-23 (11,4) scheme and extract the 4 free orbit three-planes in sl_3."""
    scheme_path = ROOT / 'data' / 'ballard_z4_cyclic' / 'ballard_z4_cyclic_scheme.json'
    with open(scheme_path) as f:
        data = json.load(f)

    # Extract free orbit vectors (already verified zero trace in analysis)
    orbit_vecs = data['free_orbit_vectors']  # list of [U, V, W] each 9-element
    planes = []
    for U, V, W in orbit_vecs:
        U8 = vec9_to_sl3(np.array(U, dtype=float))
        V8 = vec9_to_sl3(np.array(V, dtype=float))
        W8 = vec9_to_sl3(np.array(W, dtype=float))
        planes.append((U8, V8, W8))
    return planes

# ── Load numerical rank-4 decomposition from analysis ──────────────────
def load_numerical_decomp():
    """Load the numerical rank-4 exterior decomposition from analysis."""
    path = ROOT / 'data' / 'exterior_rank4' / 'exterior_rank4_decomposition.json'
    with open(path) as f:
        data = json.load(f)

    planes = []
    for term in data['decomposition']:
        u = np.array(term['u'])
        v = np.array(term['v'])
        w = np.array(term['w'])
        planes.append((u, v, w))
    return planes

# ── Check orbit equivalence ──────────────────────────────────────────
def planes_to_grassmannian(planes):
    """Convert 4 three-planes to their Grassmannian representations (3x8 basis matrices)."""
    result = []
    for U, V, W in planes:
        basis = np.vstack([U, V, W])  # 3 x 8
        result.append(basis)
    return result

def cost_function(params, bilr_planes, num_planes):
    """
    Cost: sum of distances from ad(g)(bilr_planes[sigma(i)]) to num_planes[i]
    for the best permutation sigma.

    params: 9 entries of a 3x3 matrix g (not necessarily in SL_3, but we'll
    use det normalization).
    """
    g = params.reshape(3, 3)
    det_g = np.linalg.det(g)
    if abs(det_g) < 1e-10:
        return 1e10

    # Normalize to det = 1
    g = g / (abs(det_g) ** (1.0/3))
    g_inv = np.linalg.inv(g)

    # Transform all BILR planes
    transformed = []
    for U, V, W in bilr_planes:
        U_mat = sl3_to_mat(U)
        V_mat = sl3_to_mat(V)
        W_mat = sl3_to_mat(W)
        tU = vec9_to_sl3((g @ U_mat @ g_inv).flatten())
        tV = vec9_to_sl3((g @ V_mat @ g_inv).flatten())
        tW = vec9_to_sl3((g @ W_mat @ g_inv).flatten())
        transformed.append((tU, tV, tW))

    # Find best permutation (4! = 24 permutations)
    best_cost = 1e20
    for perm in itertools.permutations(range(4)):
        cost = 0
        for i in range(4):
            j = perm[i]
            # Distance between three-planes:
            # Project transformed[j] to subspace of num_planes[i]
            B_num = np.vstack(num_planes[i])  # 3 x 8
            B_tr = np.vstack(transformed[j])   # 3 x 8
            # Subspace distance: use principal angles
            # or: minimize over internal GL_3 the Frobenius distance
            # Simple: project B_tr rows onto span(B_num) and measure residual
            if np.linalg.matrix_rank(B_num, tol=1e-6) < 3:
                cost += 100
                continue
            # Projection: P = B_num^T (B_num B_num^T)^{-1} B_num
            G_mat = B_num @ B_num.T
            try:
                proj = B_num.T @ np.linalg.solve(G_mat, B_num)  # 8x8 projector
            except:
                cost += 100
                continue
            residual = B_tr - B_tr @ proj
            cost += np.linalg.norm(residual) ** 2
        best_cost = min(best_cost, cost)
    return best_cost

def main():
    # Load both decompositions
    try:
        bilr_planes = load_bilr_114()
        print(f"BILR planes loaded: {len(bilr_planes)} three-planes in sl_3(R^8)")
    except Exception as e:
        print(f"Cannot load BILR: {e}")
        # Try to compute from the scheme directly
        bilr_planes = compute_bilr_planes_from_scheme()

    try:
        num_planes = load_numerical_decomp()
        print(f"Numerical planes loaded: {len(num_planes)} three-planes in sl_3(R^8)")
    except Exception as e:
        print(f"Cannot load numerical: {e}")
        return

    # Check that both give the same omega
    omega_bilr = {}
    for U, V, W in bilr_planes:
        w = wedge_3(U, V, W)
        for k, v in w.items():
            omega_bilr[k] = omega_bilr.get(k, 0) + v

    omega_num = {}
    for U, V, W in num_planes:
        w = wedge_3(U, V, W)
        for k, v in w.items():
            omega_num[k] = omega_num.get(k, 0) + v

    # Compare
    all_keys = set(omega_bilr.keys()) | set(omega_num.keys())
    max_diff = max(abs(omega_bilr.get(k,0) - omega_num.get(k,0)) for k in all_keys)
    print(f"Omega comparison: max diff = {max_diff:.2e}")

    # Also check the omega/3 normalization
    # BILR has sum wedge = omega/3 (from analysis analysis)
    # Numerical has sum wedge = omega/3 (from analysis search targeting omega)
    # But the omega in analysis was in the gl_3 basis, not sl_3

    # Optimization: find g ∈ GL_3 mapping BILR to numerical via ad(g)
    print("\nSearching for PGL_3 orbit equivalence...")
    best_result = None
    best_cost = 1e20

    for trial in range(100):
        np.random.seed(trial * 137 + 42)
        g0 = np.random.randn(3, 3)
        g0 /= abs(np.linalg.det(g0)) ** (1/3)  # normalize

        res = minimize(cost_function, g0.flatten(),
                      args=(bilr_planes, num_planes),
                      method='Nelder-Mead',
                      options={'maxiter': 5000, 'xatol': 1e-12, 'fatol': 1e-15})
        if res.fun < best_cost:
            best_cost = res.fun
            best_result = res
            if best_cost < 1e-10:
                break

    print(f"Best cost after {trial+1} trials: {best_cost:.6e}")
    if best_cost < 1e-6:
        print("*** DECOMPOSITIONS ARE IN THE SAME PGL_3 ORBIT ***")
        g = best_result.x.reshape(3,3)
        g /= abs(np.linalg.det(g)) ** (1/3)
        print(f"Transformation g:\n{g}")
    else:
        print("*** Decompositions appear to be in DIFFERENT orbits ***")
        print("(or optimization did not converge)")

    results = {
        'omega_max_diff': float(max_diff),
        'best_cost': float(best_cost),
        'n_trials': trial + 1,
        'same_orbit': bool(best_cost < 1e-6),
    }
    (OUT / 'fiber_orbit_check.json').write_text(json.dumps(results, indent=2) + '\n')
    print(f"\nSaved {OUT}/fiber_orbit_check.json")

def compute_bilr_planes_from_scheme():
    """Fallback: compute directly from the scheme."""
    sys.path.insert(0, str(ROOT / 'scripts'))
    from ballard_z4_cyclic_scheme import build_bilr_z4_scheme
    cubes, orbit_vecs = build_bilr_z4_scheme()
    planes = []
    for U, V, W in orbit_vecs:
        U8 = vec9_to_sl3(np.array(U, dtype=float))
        V8 = vec9_to_sl3(np.array(V, dtype=float))
        W8 = vec9_to_sl3(np.array(W, dtype=float))
        planes.append((U8, V8, W8))
    return planes

if __name__ == '__main__':
    main()
