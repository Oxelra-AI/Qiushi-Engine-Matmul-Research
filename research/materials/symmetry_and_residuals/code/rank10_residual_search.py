#!/usr/bin/env python3
r"""
analysis: Constructive search for rank-≤10 residual in the (10,4) cyclic family.

The BILR exterior 4-plane configuration is rigid up to PGL_3.  For each choice
of internal SL_3 frames within the 4 planes, the residual cubic changes.  BILR's
residual has Waring rank 11 (certified by Koszul rank 722 and Pfaffian Φ=-80000).

We search for frames where the Strassen/Hessian commutator has rank ≤ 2,
which would give a residual with Waring rank ≤ 10, hence a 22-term cyclic
scheme (10 cubes + 4 free orbits = 22).

OBJECTIVE: For test direction pairs (X_a, Y_a), compute the K-antisymmetrized
commutator Ω_a = K [H_{X_a}, H_{Y_a}].  Rank(Ω_a) ≤ 2 requires all
C(9,4)=126 four-by-four Pfaffians to vanish.  We minimize Σ_a Σ_I Pf_I(Ω_a)^2.

If zero is found: a candidate rank-22 scheme exists; reconstruct and verify.
If robustly nonzero: the (10,4) branch is locally excluded for this configuration.
"""

import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize
from itertools import combinations
import json, time, sys
from pathlib import Path

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "rank10_search"
OUT.mkdir(parents=True, exist_ok=True)

# ═══════════════════════════════════════════════════════════════
# Constants
# ═══════════════════════════════════════════════════════════════
I3 = np.eye(3)

# K = tr(XY) Gram matrix on gl_3, row-major basis E_{ij} = e_{3i+j}.
# K[3i+j, 3k+l] = δ_{il}δ_{jk}, i.e. the transpose permutation.
K9 = np.zeros((9, 9))
for a in range(9):
    i, j = divmod(a, 3)
    K9[a, 3*j+i] = 1.0

# sl_3 Lie algebra basis (8 generators)
SL3_GEN = []
for i in range(3):
    for j in range(3):
        if i != j:
            E = np.zeros((3, 3))
            E[i, j] = 1.0
            SL3_GEN.append(E)
SL3_GEN.append(np.diag([1., -1., 0.]))
SL3_GEN.append(np.diag([0., 1., -1.]))
assert len(SL3_GEN) == 8

# Precompute 4-element subsets of [9] for Pfaffian evaluation
SUBSETS4 = np.array(list(combinations(range(9), 4)), dtype=int)  # 126 × 4
I1, I2, I3_idx, I4 = SUBSETS4[:,0], SUBSETS4[:,1], SUBSETS4[:,2], SUBSETS4[:,3]

# ═══════════════════════════════════════════════════════════════
# Load and preprocess BILR data
# ═══════════════════════════════════════════════════════════════
def load_bilr_planes():
    """Load BILR free orbit planes with transpose convention: l_A(X) = tr(AX)."""
    p = WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json"
    with open(p) as f:
        scheme = json.load(f)
    planes = []
    for rep in scheme["free_orbit_representatives"]:
        U = np.array(rep["U"], dtype=float).T
        V = np.array(rep["V"], dtype=float).T
        W = np.array(rep["W"], dtype=float).T
        planes.append((U, V, W))
    return planes

def precompute_plane_data(planes):
    """Precompute correction outer-product matrices for each plane."""
    pdata = []
    for A, B, C in planes:
        a, b, c = A.ravel(), B.ravel(), C.ravel()
        # Transposed vectors: at[3r+c] = A[c,r] = A^T ravel
        at, bt, ct = A.T.ravel(), B.T.ravel(), C.T.ravel()
        # Correction matrices: M_XY = outer(x, yt) + outer(y, xt)
        M_AB = np.outer(a, bt) + np.outer(b, at)
        M_AC = np.outer(a, ct) + np.outer(c, at)
        M_BC = np.outer(b, ct) + np.outer(c, bt)
        pdata.append((at, bt, ct, M_AB, M_AC, M_BC))
    return pdata

# ═══════════════════════════════════════════════════════════════
# Core algebra
# ═══════════════════════════════════════════════════════════════
def params_to_frames(theta, n_free=4):
    """Map parameter vector to SL_3 matrices via exponential map.
    theta has 8*n_free entries."""
    frames = []
    for j in range(n_free):
        t = theta[8*j : 8*j + 8]
        A = np.zeros((3, 3))
        for k in range(8):
            A += t[k] * SL3_GEN[k]
        frames.append(expm(A))
    return frames

def apply_frame_to_plane(plane, M):
    """Apply GL_3 frame change M to a plane triple (A, B, C)."""
    A, B, C = plane
    new = []
    for row in range(3):
        new.append(M[row, 0]*A + M[row, 1]*B + M[row, 2]*C)
    return tuple(new)

def compute_6SX(X, pdata):
    """6 S_X as a 9×9 matrix.
    
    Jordan part: 3(X ⊗ I₃ + I₃ ⊗ X^T) acting on vec(Y).
    Correction: -3 Σ_j (cX M_AB + bX M_AC + aX M_BC).
    """
    J = np.kron(X, I3) + np.kron(I3, X.T)
    x = X.ravel()
    corr = np.zeros((9, 9))
    for at, bt, ct, M_AB, M_AC, M_BC in pdata:
        aX = at @ x
        bX = bt @ x
        cX = ct @ x
        corr += cX * M_AB + bX * M_AC + aX * M_BC
    return 3.0 * (J - corr)

def pfaffian_sum_sq(Omega):
    """Sum of squared 4×4 Pfaffians of a 9×9 antisymmetric matrix.
    Vectorized over all C(9,4)=126 index subsets."""
    pf = (Omega[I1, I2] * Omega[I3_idx, I4]
        - Omega[I1, I3_idx] * Omega[I2, I4]
        + Omega[I1, I4] * Omega[I2, I3_idx])
    return np.sum(pf * pf)

def commutator_rank(Omega, tol=1e-10):
    """Numerical rank of antisymmetric matrix via SVD."""
    sv = np.linalg.svd(Omega, compute_uv=False)
    return int(np.sum(sv > tol * sv[0]))

# ═══════════════════════════════════════════════════════════════
# Objective function
# ═══════════════════════════════════════════════════════════════
def objective(theta, base_planes, dir_pairs, fix_first=False):
    """Sum of squared 4×4 Pfaffians of K[H_X, H_Y] over direction pairs."""
    if fix_first:
        frames = [I3.copy()] + params_to_frames(theta, n_free=3)
    else:
        frames = params_to_frames(theta, n_free=4)
    new_planes = [apply_frame_to_plane(base_planes[j], frames[j]) for j in range(4)]
    pdata = precompute_plane_data(new_planes)
    
    total = 0.0
    for X, Y in dir_pairs:
        S_X = compute_6SX(X, pdata)
        S_Y = compute_6SX(Y, pdata)
        C = S_X @ S_Y - S_Y @ S_X
        Omega = K9 @ C
        total += pfaffian_sum_sq(Omega)
    return total

def detailed_eval(theta, base_planes, dir_pairs, fix_first=False):
    """Evaluate objective and return per-direction diagnostics."""
    if fix_first:
        frames = [I3.copy()] + params_to_frames(theta, n_free=3)
    else:
        frames = params_to_frames(theta, n_free=4)
    new_planes = [apply_frame_to_plane(base_planes[j], frames[j]) for j in range(4)]
    pdata = precompute_plane_data(new_planes)
    
    details = []
    total = 0.0
    for X, Y in dir_pairs:
        S_X = compute_6SX(X, pdata)
        S_Y = compute_6SX(Y, pdata)
        C = S_X @ S_Y - S_Y @ S_X
        Omega = K9 @ C
        pf_ss = pfaffian_sum_sq(Omega)
        total += pf_ss
        # Also compute Phi = 2tr(C^4) - tr(C^2)^2
        C2 = C @ C
        t2 = np.trace(C2)
        t4 = np.trace(C2 @ C2)
        phi = 2*t4 - t2*t2
        r = commutator_rank(Omega)
        details.append({"pf_sum_sq": float(pf_ss), "phi": float(phi),
                        "omega_rank": int(r), "frob_C": float(np.linalg.norm(C))})
    return total, details

# ═══════════════════════════════════════════════════════════════
# Test direction pairs
# ═══════════════════════════════════════════════════════════════
def make_test_directions(seed=42, n_random=8):
    """Generate test direction pairs. Include the analysis certificate pair."""
    pairs = []
    # analysis integer certificate directions
    X49 = np.array([[3, 0, 1], [3, -1, 1], [1, 3, -2]], dtype=float)
    Y49 = np.array([[-1, 3, -1], [-1, 1, 0], [-1, 2, 1]], dtype=float)
    pairs.append((X49, Y49))
    # Random integer directions
    rng = np.random.RandomState(seed)
    for _ in range(n_random):
        X = rng.randint(-5, 6, size=(3, 3)).astype(float)
        Y = rng.randint(-5, 6, size=(3, 3)).astype(float)
        pairs.append((X, Y))
    return pairs

# ═══════════════════════════════════════════════════════════════
# Main optimization
# ═══════════════════════════════════════════════════════════════
def main():
    planes = load_bilr_planes()
    dir_pairs = make_test_directions(seed=42, n_random=8)
    
    # Baseline: BILR (identity frames)
    t0 = time.time()
    f0, d0 = detailed_eval(np.zeros(32), planes, dir_pairs)
    print(f"BILR baseline: f = {f0:.6e}, time = {time.time()-t0:.3f}s")
    for i, d in enumerate(d0):
        print(f"  dir {i}: pf_sum_sq={d['pf_sum_sq']:.4e}, phi={d['phi']:.4e}, rank={d['omega_rank']}")
    
    # Verify Phi at analysis directions matches known -80000
    # (C = 36[S_X, S_Y], so Phi(C) = 36^4 * Phi([S,S]))
    # Our C = [6S_X, 6S_Y] = 36[S_X, S_Y], so matching
    phi_bilr = d0[0]["phi"]
    print(f"  analysis Phi = {phi_bilr:.0f} (expected: -80000 * 36^4 / 36^4 ??? check convention)")
    
    # ── Multi-restart optimization ──
    N_RESTARTS = 200
    rng = np.random.RandomState(12345)
    
    results = []
    best_f = f0
    best_theta = np.zeros(32)
    t_start = time.time()
    
    for trial in range(N_RESTARTS):
        # Random starting point
        if trial < 100:
            sigma = 1.5  # moderate perturbation
        elif trial < 150:
            sigma = 0.3  # local search near identity
        else:
            sigma = 3.0  # wide search
        
        theta_init = rng.randn(32) * sigma
        
        try:
            res = minimize(objective, theta_init, args=(planes, dir_pairs, False),
                          method='Powell',
                          options={'maxiter': 500, 'maxfev': 10000, 'ftol': 1e-25})
            fval = res.fun
        except Exception as e:
            fval = float('inf')
            res = None
        
        if fval < best_f:
            best_f = fval
            best_theta = res.x.copy() if res else theta_init
        
        results.append({
            "trial": trial,
            "fun": float(fval),
            "nfev": res.nfev if res else 0,
            "sigma": sigma,
        })
        
        if fval < 1e-10:
            print(f"*** CANDIDATE *** Trial {trial}: f = {fval:.6e}")
        elif trial % 25 == 0:
            elapsed = time.time() - t_start
            print(f"Trial {trial}/{N_RESTARTS}: f = {fval:.6e}, best = {best_f:.6e}, "
                  f"elapsed = {elapsed:.1f}s")
    
    elapsed = time.time() - t_start
    print(f"\nTotal time: {elapsed:.1f}s for {N_RESTARTS} restarts")
    
    # ── Also try with M1=I fixed (24 params) ──
    print("\n=== Fixed M1=I search (24 params) ===")
    best_f_fix = float('inf')
    best_theta_fix = np.zeros(24)
    for trial in range(100):
        sigma = 1.5 if trial < 50 else 0.5
        theta_init = rng.randn(24) * sigma
        try:
            res = minimize(objective, theta_init, args=(planes, dir_pairs, True),
                          method='Powell',
                          options={'maxiter': 500, 'maxfev': 10000, 'ftol': 1e-25})
            fval = res.fun
        except Exception:
            fval = float('inf')
            res = None
        if fval < best_f_fix:
            best_f_fix = fval
            best_theta_fix = res.x.copy() if res else theta_init
        if fval < 1e-10:
            print(f"*** CANDIDATE *** Trial {trial}: f = {fval:.6e}")
        elif trial % 25 == 0:
            print(f"Trial {trial}/100: f = {fval:.6e}, best = {best_f_fix:.6e}")
    
    # ── Analyze best result ──
    print("\n=== Best result analysis ===")
    f_best, d_best = detailed_eval(best_theta, planes, dir_pairs)
    print(f"Best (32 params): f = {f_best:.6e}")
    for i, d in enumerate(d_best):
        print(f"  dir {i}: pf_ss={d['pf_sum_sq']:.4e}, phi={d['phi']:.4e}, rank={d['omega_rank']}")
    
    f_best_fix, d_best_fix = detailed_eval(best_theta_fix, planes, dir_pairs, fix_first=True)
    print(f"Best (24 params, M1=I): f = {f_best_fix:.6e}")
    for i, d in enumerate(d_best_fix):
        print(f"  dir {i}: pf_ss={d['pf_sum_sq']:.4e}, phi={d['phi']:.4e}, rank={d['omega_rank']}")
    
    # ── Statistics ──
    fvals = sorted([r["fun"] for r in results if r["fun"] < float('inf')])
    print(f"\n=== Statistics (32-param search) ===")
    print(f"Restarts: {N_RESTARTS}")
    print(f"Finite results: {len(fvals)}")
    if fvals:
        print(f"Min: {fvals[0]:.6e}")
        print(f"Median: {fvals[len(fvals)//2]:.6e}")
        print(f"Max: {fvals[-1]:.6e}")
        n_small = sum(1 for f in fvals if f < 1e-5)
        print(f"Below 1e-5: {n_small}")
        n_tiny = sum(1 for f in fvals if f < 1e-10)
        print(f"Below 1e-10: {n_tiny}")
    
    # Histogram of log10(f)
    log_f = [np.log10(max(f, 1e-300)) for f in fvals if f > 0]
    if log_f:
        bins = np.arange(int(min(log_f))-1, int(max(log_f))+2)
        hist, edges = np.histogram(log_f, bins=bins)
        print(f"log10(f) histogram:")
        for i in range(len(hist)):
            if hist[i] > 0:
                print(f"  [{edges[i]:.0f}, {edges[i+1]:.0f}): {hist[i]}")
    
    # ── Save results ──
    output = {
        "scope": "Constructive search for rank-≤10 BILR residual via 4×4 Pfaffian minimization",
        "baseline_bilr": {"f": f0, "details": d0},
        "search_32param": {
            "n_restarts": N_RESTARTS,
            "best_f": float(best_f),
            "best_theta": best_theta.tolist(),
            "best_details": d_best,
            "elapsed_sec": elapsed,
            "min_f_values": fvals[:20] if fvals else [],
        },
        "search_24param": {
            "n_restarts": 100,
            "best_f": float(best_f_fix),
            "best_theta": best_theta_fix.tolist(),
            "best_details": d_best_fix,
        },
        "direction_pairs": [{"X": X.tolist(), "Y": Y.tolist()} for X, Y in dir_pairs],
        "interpretation": (
            "If min > 0 robustly across hundreds of restarts, the (10,4) BILR-exterior "
            "family likely has no rank-≤10 residual, localizing the obstruction for exact "
            "elimination. If min ≈ 0, the candidate frame gives a 10-cube residual; "
            "reconstruct over a number field and verify 729 Brent identities. "
            "Border rank ≤ 20 guarantees arbitrarily good approximations with divergent "
            "amplitudes; only a finite, bounded-norm minimum near zero is meaningful."
        ),
    }
    
    outpath = OUT / "rank10_search_results.json"
    with open(outpath, "w") as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\nSaved to {outpath}")

if __name__ == "__main__":
    main()
