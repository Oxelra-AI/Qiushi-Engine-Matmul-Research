#!/usr/bin/env python3
"""analysis: Extract Laderman's free-orbit bivectors and test anti-sector containment.

Central question: Laderman has tau-skeleton (7,8) under Phi3*Phi4.
Do its 8 free-orbit decomposable bivectors span L_anti?

If yes: m_0 <= 8 is directly witnessed, killing any m_0=9 program.
If no: the Phi3*Phi4-anti sector and standard-tau anti sector differ structurally.

We also verify that the full 23-term Laderman scheme exactly reproduces
the standard anti-target A_TARGET, and measure the bivector ranks.
"""
from __future__ import annotations
import numpy as np
import json
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "laderman_anti"
OUT.mkdir(parents=True, exist_ok=True)

# ---------- load Laderman terms ----------
src_path = SCRIPT_DIR / "laderman_tau_decomp.py"
src = src_path.read_text()
# Execute definitions + T333, stop before the verification loop (which writes output)
prefix = src.split('print(f"Sum matches T333')[0]
ns = {"__file__": str(src_path), "__name__": "defs_only"}
exec(compile(prefix, str(src_path), "exec"), ns)
terms = ns["terms"]       # list of (a, b, c) as 3x3 int arrays
T333 = ns["T333"]
print(f"Loaded {len(terms)} Laderman terms")

# Verify sum = T333
T_sum = np.zeros((9,9,9), dtype=int)
for a, b, c in terms:
    for r1 in range(3):
        for c1 in range(3):
            for r2 in range(3):
                for c2 in range(3):
                    for r3 in range(3):
                        for c3 in range(3):
                            T_sum[3*r1+c1, 3*r2+c2, 3*r3+c3] += a[r1,c1]*b[r2,c2]*c[r3,c3]
assert np.array_equal(T_sum, T333), "Sum mismatch"

# ---------- Phi3*Phi4 orbit data ----------
# From laderman_tau_decomposition.json (1-indexed)
fixed_1idx = [1, 4, 10, 12, 19, 21, 23]
two_cycles_1idx = [(2,5), (3,6), (7,16), (8,18), (9,17), (11,14), (13,15), (20,22)]
fixed_0idx = [i-1 for i in fixed_1idx]
orbit_reps = [(i-1, j-1) for i,j in two_cycles_1idx]

# ---------- Wedge computation ----------
WEDGE_PAIRS = [(a, b) for a in range(9) for b in range(a+1, 9)]
assert len(WEDGE_PAIRS) == 36

def wedge_vec(a, b):
    """a ^ b in Lambda^2(K^9), length 36."""
    v = np.zeros(36, dtype=float)
    for t, (i, j) in enumerate(WEDGE_PAIRS):
        v[t] = a[i]*b[j] - a[j]*b[i]
    return v

def vec9(M):
    """Flatten 3x3 matrix to 9-vector, row-major."""
    return M.reshape(9).astype(float)

# ---------- Anti target (from analysis) ----------
SKEW_PAIRS = [(0,1), (0,2), (1,2)]
def anti_target():
    """3 x 36 target for tr(A Y Z) with A skew, under tau identification."""
    def idx(i, k): return 3*i + k
    T = np.zeros((3, 36), dtype=float)
    for r, (a, b) in enumerate(SKEW_PAIRS):
        # A = E_ab - E_ba
        M = np.zeros((9, 9), dtype=float)
        for i in range(3):
            for j in range(3):
                A_ij = 0
                if (i,j) == (a,b): A_ij = 1
                elif (i,j) == (b,a): A_ij = -1
                if A_ij == 0: continue
                for k in range(3):
                    y = idx(j, k)
                    z = idx(i, k)
                    M[y, z] += A_ij
        # M should be skew
        assert np.max(np.abs(M + M.T)) == 0, "not skew"
        for t, (i, j) in enumerate(WEDGE_PAIRS):
            T[r, t] = M[i, j]
    return T

A_TARGET = anti_target()
print(f"Anti target shape: {A_TARGET.shape}, rank: {np.linalg.matrix_rank(A_TARGET)}")

# ---------- Compute all 23 bivectors ----------
all_bivectors = []
for l, (a, b, c) in enumerate(terms):
    v = vec9(b)        # vec(b_l)
    w = vec9(c.T)      # vec(c_l^T)
    eta = wedge_vec(v, w)
    all_bivectors.append(eta)
all_bivectors = np.array(all_bivectors)  # 23 x 36
print(f"All bivectors shape: {all_bivectors.shape}")

# Coefficient matrix C: C[r, l] = <a_l, A_r>
SKEW_BASIS = []
for a, b in SKEW_PAIRS:
    M = np.zeros((3,3), dtype=float)
    M[a,b] = 1; M[b,a] = -1
    SKEW_BASIS.append(M)

C = np.zeros((3, 23), dtype=float)
for l, (a, b, c) in enumerate(terms):
    for r, A in enumerate(SKEW_BASIS):
        C[r, l] = np.sum(a.astype(float) * A)
print(f"Coefficient matrix C shape: {C.shape}")

# Verify: C @ all_bivectors should = 2*A_TARGET
# The factor 2 arises because wedge_vec(b,c)[t] = b[i]c[j]-b[j]c[i] is twice the
# skew part b[i]c[j] stored in A_TARGET, and the total M_r is skew.
# For tau-invariant naive_27, summing orbit reps gives A_TARGET; summing all 27 gives 2*A_TARGET.
# For Laderman (not tau-invariant), summing all 23 should give 2*A_TARGET.
reconstructed = C @ all_bivectors
recon_error_2x = np.max(np.abs(reconstructed - 2*A_TARGET))
recon_error_1x = np.max(np.abs(reconstructed - A_TARGET))
print(f"Reconstruction vs 2*A_TARGET: error = {recon_error_2x}")
print(f"Reconstruction vs 1*A_TARGET: error = {recon_error_1x}")
# Also check direct bilinear form: M_r[y,z] = sum_l <a_l,A_r> b_l[y] c_l^sigma[z]
for r in range(3):
    M_direct = np.zeros((9,9), dtype=float)
    for l, (a, b, c) in enumerate(terms):
        coeff = float(np.sum(a.astype(float) * SKEW_BASIS[r]))
        bv = vec9(b)
        cv_sigma = vec9(c.T)  # sigma-permuted = transpose of 3x3 matrix
        M_direct += coeff * np.outer(bv, cv_sigma)
    # This should be skew
    skew_err = np.max(np.abs(M_direct + M_direct.T))
    # Upper triangle should match A_TARGET[r]
    target_err = 0
    for t, (i,j) in enumerate(WEDGE_PAIRS):
        target_err = max(target_err, abs(M_direct[i,j] - A_TARGET[r,t]))
    print(f"  M_{r} skew error: {skew_err}, target match error: {target_err}")
recon_error = min(recon_error_2x, recon_error_1x)
use_factor = 2.0 if recon_error_2x < recon_error_1x else 1.0
assert recon_error < 1e-10, f"Reconstruction failed: error = {recon_error}"

# ---------- Analysis of bivector structure ----------
# Rank of full 23 bivector matrix
full_rank = np.linalg.matrix_rank(all_bivectors)
print(f"\nFull 23-bivector rank: {full_rank}")

# Fixed term bivectors: should they be zero?
fixed_bivecs = all_bivectors[fixed_0idx]
fixed_norms = [float(np.linalg.norm(all_bivectors[i])) for i in fixed_0idx]
print(f"Fixed term bivector norms: {fixed_norms}")
any_fixed_zero = [n < 1e-10 for n in fixed_norms]
print(f"Fixed bivectors zero: {any_fixed_zero}")

# Free orbit representative bivectors
orbit_rep_bivecs = np.array([all_bivectors[i] for i, j in orbit_reps])  # 8 x 36
orbit_rep_rank = np.linalg.matrix_rank(orbit_rep_bivecs)
print(f"\n8 orbit-rep bivector rank: {orbit_rep_rank}")

# Check: do 8 orbit rep bivectors span L_anti?
augmented = np.vstack([orbit_rep_bivecs, A_TARGET])
aug_rank = np.linalg.matrix_rank(augmented)
orbit_reps_contain = (orbit_rep_rank == aug_rank)
print(f"Augmented rank (8 reps + target): {aug_rank}")
print(f"8 orbit-rep bivectors span L_anti: {orbit_reps_contain}")

# Free orbit partner bivectors
orbit_partner_bivecs = np.array([all_bivectors[j] for i, j in orbit_reps])
partner_rank = np.linalg.matrix_rank(orbit_partner_bivecs)
aug_partner = np.vstack([orbit_partner_bivecs, A_TARGET])
aug_partner_rank = np.linalg.matrix_rank(aug_partner)
print(f"8 orbit-partner bivec rank: {partner_rank}")
print(f"Partners span L_anti: {partner_rank == aug_partner_rank}")

# All 16 free-orbit bivectors
free_all = np.vstack([orbit_rep_bivecs, orbit_partner_bivecs])
free_all_rank = np.linalg.matrix_rank(free_all)
aug_free_all = np.vstack([free_all, A_TARGET])
aug_free_all_rank = np.linalg.matrix_rank(aug_free_all)
print(f"16 free bivec rank: {free_all_rank}")
print(f"16 free span L_anti: {free_all_rank == aug_free_all_rank}")

# Orbit-antisymmetric bivectors: (eta_i - eta_j)/2 for each free orbit
orbit_anti_bivecs = np.array([(all_bivectors[i] - all_bivectors[j])/2 
                               for i, j in orbit_reps])
orbit_anti_rank = np.linalg.matrix_rank(orbit_anti_bivecs)
aug_anti = np.vstack([orbit_anti_bivecs, A_TARGET])
aug_anti_rank = np.linalg.matrix_rank(aug_anti)
print(f"\n8 orbit-anti bivecs rank: {orbit_anti_rank}")
print(f"Orbit-anti span L_anti: {orbit_anti_rank == aug_anti_rank}")

# Search for minimum spanning subset among all 23
print("\n--- Minimum spanning subset search ---")
# First check how many of the 23 are needed
target_rows = A_TARGET
from itertools import combinations

def spans_target(indices, bivecs, target, tol=1e-8):
    """Check if bivecs[indices] span the target rows."""
    if len(indices) == 0: return False
    sub = bivecs[list(indices)]
    aug = np.vstack([sub, target])
    return np.linalg.matrix_rank(sub, tol=tol) == np.linalg.matrix_rank(aug, tol=tol)

# Try small subsets
min_m = None
for m in range(3, 10):
    found = False
    # Try specific structured subsets first
    if m <= 8:
        # Try orbit reps
        if m == 8 and orbit_reps_contain:
            min_m = 8
            print(f"m={m}: orbit reps span L_anti")
            found = True
        else:
            # Exhaustive among small subsets of the 23
            count = 0
            for subset in combinations(range(23), m):
                if spans_target(subset, all_bivectors, A_TARGET):
                    print(f"m={m}: found spanning subset {[s+1 for s in subset]}")
                    min_m = m
                    found = True
                    break
                count += 1
                if count > 200000:  # budget
                    break
            if not found and count > 200000:
                print(f"m={m}: exhausted budget ({count} subsets tested)")
    if found:
        break

# Also check: for each pair (a,b) in [(0,1),(0,2),(1,2)], which bivectors have 
# nonzero coefficient?
print("\n--- Coefficient support analysis ---")
for r, (a, b) in enumerate(SKEW_PAIRS):
    support = [l for l in range(23) if abs(C[r, l]) > 1e-10]
    print(f"  A_{a}{b}: {len(support)} terms with nonzero coeff: {[l+1 for l in support]}")

# Check rank of supported bivectors for each target row
print("\n--- Per-target-row analysis ---")
for r in range(3):
    support = [l for l in range(23) if abs(C[r, l]) > 1e-10]
    if support:
        sub_bvecs = all_bivectors[support]
        rk = np.linalg.matrix_rank(sub_bvecs)
        print(f"  Target row {r}: support size {len(support)}, bivec rank {rk}")

# ---------- Canonical comparison ----------
# The canonical 9 column bivectors
print("\n--- Canonical 9-column comparison ---")
def idx(i, k): return 3*i + k
canonical_bivecs = []
for r, (a, b) in enumerate(SKEW_PAIRS):
    for k in range(3):
        va = np.zeros(9); vb = np.zeros(9)
        va[idx(a, k)] = 1; vb[idx(b, k)] = 1
        canonical_bivecs.append(wedge_vec(va, vb))
canonical_bivecs = np.array(canonical_bivecs)
can_rank = np.linalg.matrix_rank(canonical_bivecs)
aug_can = np.vstack([canonical_bivecs, A_TARGET])
can_contains = can_rank == np.linalg.matrix_rank(aug_can)
print(f"Canonical 9 bivecs rank: {can_rank}, contains target: {can_contains}")

# Check if 8 of canonical 9 span target
for skip in range(9):
    sub = np.delete(canonical_bivecs, skip, axis=0)
    aug = np.vstack([sub, A_TARGET])
    if np.linalg.matrix_rank(sub) == np.linalg.matrix_rank(aug):
        print(f"  Canonical without #{skip}: still spans (rank {np.linalg.matrix_rank(sub)})")
    else:
        print(f"  Canonical without #{skip}: DOES NOT span (defect {np.linalg.matrix_rank(aug) - np.linalg.matrix_rank(sub)})")

# ---------- Save results ----------
out = {
    "num_terms": 23,
    "fixed_count": len(fixed_0idx),
    "free_orbit_count": len(orbit_reps),
    "reconstruction_error": float(recon_error),
    "full_23_bivector_rank": int(full_rank),
    "fixed_bivec_norms": fixed_norms,
    "fixed_bivecs_all_zero": all(n < 1e-10 for n in fixed_norms),
    "orbit_rep_8_bivec_rank": int(orbit_rep_rank),
    "orbit_rep_8_span_L_anti": bool(orbit_reps_contain),
    "orbit_partner_8_bivec_rank": int(partner_rank),
    "orbit_partner_8_span_L_anti": bool(partner_rank == aug_partner_rank),
    "all_16_free_bivec_rank": int(free_all_rank),
    "all_16_free_span_L_anti": bool(free_all_rank == aug_free_all_rank),
    "orbit_anti_8_rank": int(orbit_anti_rank),
    "orbit_anti_span_L_anti": bool(orbit_anti_rank == aug_anti_rank),
    "minimum_spanning_size_found": min_m,
    "canonical_9_rank": int(can_rank),
    "interpretation": (
        "Tests whether Laderman's 8 Phi3*Phi4 free-orbit bivectors span the "
        "standard tau anti-target L_anti. If yes, m_0 <= 8 directly. "
        "If no, the two tau-type anti-sectors differ structurally."
    )
}
path = OUT / "laderman_anti_witness.json"
path.write_text(json.dumps(out, indent=2) + "\n")
print(f"\nSAVED {path}")
print(json.dumps(out, indent=2))
