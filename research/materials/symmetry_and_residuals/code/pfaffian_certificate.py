#!/usr/bin/env python3
"""
analysis: Pfaffian scalar certificate and frame elimination pilot.

The scalar Phi(X,Y) = 2 tr(C^4) - tr(C^2)^2 for C=[H_X,H_Y]
is a one-directional certificate: rank(C)<=2 implies Phi=0, hence Phi!=0
implies rank(C)>=4.  Because the trace form is indefinite, Phi=0 need not imply
rank(C)<=2.  The exact rank<=2 equations are the 4x4 Pfaffians of the ordinary
skew matrix Omega=K C.

Strassen/Hessian bound: for k cubes on V (dim n) with K=(1/6)Hess_R(p) nondegenerate,
  rank([H_X, H_Y]) <= 2(k - n).
For Waring rank <= 10 on gl_3 (n=9): rank <= 2, hence Phi = 0 for all X,Y.
Therefore Phi(X_0, Y_0) != 0 proves Waring rank >= 11.

IMPORTANT: tr(C^3) = 0 is automatic for K-skew-symmetric C and carries
no information. Do not treat it as a discriminant.

This script:
1. Computes exact integer Phi at BILR (permanent certificate)
2. Scans internal frames over F_p (heuristic evidence for elimination)
"""

import json, random, sys, math
from pathlib import Path

OUT = Path("data/pfaffian_certificate")
OUT.mkdir(parents=True, exist_ok=True)

# ============================================================
# Load BILR scheme
# ============================================================
with open("data/ballard_z4_cyclic/"
          "ballard_z4_cyclic_scheme.json") as f:
    scheme = json.load(f)

# Transpose for trace convention: stored L satisfies l_L(X) = tr(L^T X),
# so A = L^T for the pairing l_A(X) = tr(AX).
free_reps = scheme["free_orbit_representatives"]
PLANES = []
for rep in free_reps:
    U = [[rep["U"][j][i] for j in range(3)] for i in range(3)]
    V = [[rep["V"][j][i] for j in range(3)] for i in range(3)]
    W = [[rep["W"][j][i] for j in range(3)] for i in range(3)]
    PLANES.append((U, V, W))

# ============================================================
# Core algebra (exact integers)
# ============================================================
def tr3(A, B):
    """tr(A @ B) for 3x3 integer matrices."""
    return sum(A[i][j] * B[j][i] for i in range(3) for j in range(3))

def compute_6SX(X, planes):
    """
    6 * S_X as a 9x9 integer matrix on gl_3.
    6 S_X(Y) = 3(XY + YX) - 3 sum_j correction_j(X, Y)
    """
    # Precompute form values a_j(X), b_j(X), c_j(X)
    fv = [(tr3(A, X), tr3(B, X), tr3(C, X)) for A, B, C in planes]

    S = [[0] * 9 for _ in range(9)]
    for idx in range(9):
        r, c = divmod(idx, 3)
        # Build column idx: 6 S_X(E_{r,c})
        col = [0] * 9
        for i in range(3):
            for j in range(3):
                # Jordan: 2(X @ E_{r,c} + E_{r,c} @ X)_{i,j}
                v = 0
                if j == c:
                    v += X[i][r]
                if i == r:
                    v += X[c][j]
                col[3 * i + j] = 3 * v  # 3 not 2: (1/6)Hess_{tr(X^3)} = (XY+YX)/2

        # Corrections from each plane
        for pidx, (A, B, C) in enumerate(planes):
            aX, bX, cX = fv[pidx]
            # a_j(E_{r,c}) = tr(A_j @ E_{r,c}) = A_j[c][r]
            aY = A[c][r]
            bY = B[c][r]
            cY = C[c][r]
            for i in range(3):
                for j in range(3):
                    corr = ((bY * cX + bX * cY) * A[i][j] +
                            (aY * cX + aX * cY) * B[i][j] +
                            (aY * bX + aX * bY) * C[i][j])
                    col[3 * i + j] -= 3 * corr

        for k in range(9):
            S[k][idx] = col[k]
    return S

def mul9(A, B):
    """9x9 exact integer matrix multiply."""
    return [[sum(A[i][k] * B[k][j] for k in range(9))
             for j in range(9)] for i in range(9)]

def tr9(A):
    return sum(A[i][i] for i in range(9))

def comm9(A, B):
    AB = mul9(A, B)
    BA = mul9(B, A)
    return [[AB[i][j] - BA[i][j] for j in range(9)] for i in range(9)]

def pfaff(C):
    """Phi = 2 tr(C^4)-tr(C^2)^2; nonzero certifies rank(C)>=4."""
    C2 = mul9(C, C)
    C4 = mul9(C2, C2)
    t2 = tr9(C2)
    t4 = tr9(C4)
    return 2 * t4 - t2 * t2, t2, t4

def rank_mod(M, p):
    """Rank of M modulo p via Gaussian elimination."""
    mat = [[M[i][j] % p for j in range(9)] for i in range(9)]
    rank = 0
    for col in range(9):
        pivot = -1
        for row in range(rank, 9):
            if mat[row][col] % p != 0:
                pivot = row
                break
        if pivot < 0:
            continue
        mat[rank], mat[pivot] = mat[pivot], mat[rank]
        inv_p = pow(mat[rank][col], p - 2, p)
        for row in range(9):
            if row != rank and mat[row][col] % p != 0:
                f = (mat[row][col] * inv_p) % p
                for c2 in range(9):
                    mat[row][c2] = (mat[row][c2] - f * mat[rank][c2]) % p
        rank += 1
    return rank

# ============================================================
# BILR exact integer Pfaffian certificate
# ============================================================
print("=" * 60)
print("BILR Pfaffian certificate (exact integers on gl_3)")
print("=" * 60)

# analysis integer directions
X1 = [[3, 0, 1], [3, -1, 1], [1, 3, -2]]
X2 = [[-1, 3, -1], [-1, 1, 0], [-1, 2, 1]]

S1 = compute_6SX(X1, PLANES)
S2 = compute_6SX(X2, PLANES)
C = comm9(S1, S2)  # = 36 [S_X1, S_X2]

phi, t2, t4 = pfaff(C)
C3 = mul9(mul9(C, C), C)
t3 = tr9(C3)

print(f"tr(C^2) = {t2}")
print(f"tr(C^3) = {t3}  (automatic 0 for K-skew-symmetric)")
print(f"tr(C^4) = {t4}")
print(f"Phi = 2 tr(C^4) - tr(C^2)^2 = {phi}")
print(f"Phi != 0: {phi != 0}")
if phi < 0:
    print("Phi < 0 for this certificate; nonzero is the invariant fact used")

# Factor |Phi|
if phi != 0:
    n = abs(phi)
    facs = {}
    for p in range(2, 300):
        while n % p == 0:
            facs[p] = facs.get(p, 0) + 1
            n //= p
    if n > 1:
        facs[n] = 1
    print(f"|Phi| = {abs(phi)}")
    print(f"|Phi| factorization: {dict(sorted(facs.items()))}")

# Rank mod primes
for p in [65521, 100003, 32003]:
    r = rank_mod(C, p)
    print(f"rank(C) mod {p} = {r}")

# ============================================================
# Random direction trials (still exact integers)
# ============================================================
print("\n--- Random direction trials (exact) ---")
random.seed(42)
n_nonzero = 0
for trial in range(10):
    x1 = [[random.randint(-5, 5) for _ in range(3)] for _ in range(3)]
    x2 = [[random.randint(-5, 5) for _ in range(3)] for _ in range(3)]
    s1 = compute_6SX(x1, PLANES)
    s2 = compute_6SX(x2, PLANES)
    c = comm9(s1, s2)
    ph, _, _ = pfaff(c)
    if ph != 0:
        n_nonzero += 1
    print(f"  trial {trial}: Phi = {ph}, nonzero = {ph != 0}")
print(f"  {n_nonzero}/10 trials had Phi != 0")

# ============================================================
# Calibration: R = tr(X^3) (no free orbits)
# ============================================================
print("\n--- Calibration: tr(X^3), no corrections ---")
s1_0 = compute_6SX(X1, [])  # empty planes = pure Jordan
s2_0 = compute_6SX(X2, [])
c_0 = comm9(s1_0, s2_0)
phi_0, t2_0, t4_0 = pfaff(c_0)
t3_0 = tr9(mul9(mul9(c_0, c_0), c_0))
print(f"tr(X^3): tr(C^3) = {t3_0}, Phi = {phi_0}")
print(f"rank(C) mod 65521 = {rank_mod(c_0, 65521)}")

# ============================================================
# Frame scan over F_p
# ============================================================
print("\n" + "=" * 60)
print("Internal frame scan over F_p")
print("=" * 60)

P = 65521

def inv_mod(x, p=P):
    return pow(x % p, p - 2, p)

def det3m(M, p=P):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0])) % p

def rand_sl3(p=P):
    while True:
        M = [[random.randint(0, p - 1) for _ in range(3)] for _ in range(3)]
        d = det3m(M, p)
        if d != 0:
            di = inv_mod(d, p)
            for i in range(3):
                M[i][2] = (M[i][2] * di) % p
            return M

def apply_frame(plane, M, p=P):
    A, B, C = plane
    def combo(row):
        return [[(M[row][0] * A[i][j] + M[row][1] * B[i][j] + M[row][2] * C[i][j]) % p
                 for j in range(3)] for i in range(3)]
    return combo(0), combo(1), combo(2)

def compute_6SX_mod(X, planes, p=P):
    fv = [(sum(A[i][j] * X[j][i] for i in range(3) for j in range(3)) % p,
           sum(B[i][j] * X[j][i] for i in range(3) for j in range(3)) % p,
           sum(Cm[i][j] * X[j][i] for i in range(3) for j in range(3)) % p)
          for A, B, Cm in planes]
    S = [[0] * 9 for _ in range(9)]
    for idx in range(9):
        r, c = divmod(idx, 3)
        col = [0] * 9
        for i in range(3):
            for j in range(3):
                v = 0
                if j == c: v += X[i][r]
                if i == r: v += X[c][j]
                col[3 * i + j] = (3 * v) % p  # coefficient 3, not 2
        for pidx, (A, B, Cm) in enumerate(planes):
            aX, bX, cX = fv[pidx]
            aY, bY, cY = A[c][r] % p, B[c][r] % p, Cm[c][r] % p
            for i in range(3):
                for j in range(3):
                    corr = ((bY * cX + bX * cY) % p * A[i][j] +
                            (aY * cX + aX * cY) % p * B[i][j] +
                            (aY * bX + aX * bY) % p * Cm[i][j]) % p
                    col[3 * i + j] = (col[3 * i + j] - 3 * corr) % p
        for k in range(9):
            S[k][idx] = col[k] % p
    return S

def mul9m(A, B, p=P):
    return [[(sum(A[i][k] * B[k][j] for k in range(9))) % p
             for j in range(9)] for i in range(9)]

def pfaff_mod(C, p=P):
    C2 = mul9m(C, C, p)
    C4 = mul9m(C2, C2, p)
    t2 = sum(C2[i][i] for i in range(9)) % p
    t4 = sum(C4[i][i] for i in range(9)) % p
    return (2 * t4 - t2 * t2) % p

# Reduce BILR planes mod p
bilr_p = [([[A[i][j] % P for j in range(3)] for i in range(3)],
            [[B[i][j] % P for j in range(3)] for i in range(3)],
            [[Cm[i][j] % P for j in range(3)] for i in range(3)])
           for A, B, Cm in PLANES]

X1p = [[v % P for v in row] for row in X1]
X2p = [[v % P for v in row] for row in X2]

# Baseline verification
s1b = compute_6SX_mod(X1p, bilr_p)
s2b = compute_6SX_mod(X2p, bilr_p)
cb = [[0] * 9 for _ in range(9)]
for i in range(9):
    for j in range(9):
        cb[i][j] = (sum(s1b[i][k] * s2b[k][j] - s2b[i][k] * s1b[k][j]
                        for k in range(9))) % P
phi_base = pfaff_mod(cb)
phi_exact_mod = phi % P
print(f"BILR baseline Phi mod {P} = {phi_base}")
print(f"Exact Phi mod {P} = {phi_exact_mod}")
assert phi_base == phi_exact_mod, "MODULAR MISMATCH!"
print("Modular check passed.")

# Generate multiple direction pairs for the scan
random.seed(777)
DIR_PAIRS = []
for _ in range(8):
    x1 = [[random.randint(-10, 10) % P for _ in range(3)] for _ in range(3)]
    x2 = [[random.randint(-10, 10) % P for _ in range(3)] for _ in range(3)]
    DIR_PAIRS.append((x1, x2))
# Also include the analysis certificate pair
DIR_PAIRS.insert(0, (X1p, X2p))

# Single-direction scan: 1000 random frames, check Phi at first direction
print(f"\n--- Single-direction frame scan (1000 trials, dir pair 0) ---")
random.seed(12345)
N_SCAN = 1000
zero_single = 0
for trial in range(N_SCAN):
    Ms = [rand_sl3() for _ in range(4)]
    new_planes = [apply_frame(bilr_p[j], Ms[j]) for j in range(4)]
    s1 = compute_6SX_mod(DIR_PAIRS[0][0], new_planes)
    s2 = compute_6SX_mod(DIR_PAIRS[0][1], new_planes)
    c = [[0] * 9 for _ in range(9)]
    for i in range(9):
        for j in range(9):
            c[i][j] = (sum(s1[i][k] * s2[k][j] - s2[i][k] * s1[k][j]
                           for k in range(9))) % P
    ph = pfaff_mod(c)
    if ph == 0:
        zero_single += 1
        if zero_single <= 3:
            print(f"  Trial {trial}: Phi = 0 mod {P}! Recording frame.")
print(f"Single-dir scan: {N_SCAN} trials, {zero_single} zeros")

# Multi-direction scan: all 9 pairs
print(f"\n--- Multi-direction frame scan (500 trials, {len(DIR_PAIRS)} dir pairs) ---")
random.seed(54321)
N_MULTI = 500
zero_all = 0
zero_counts = [0] * len(DIR_PAIRS)
for trial in range(N_MULTI):
    Ms = [rand_sl3() for _ in range(4)]
    new_planes = [apply_frame(bilr_p[j], Ms[j]) for j in range(4)]
    all_zero = True
    for didx, (x1, x2) in enumerate(DIR_PAIRS):
        s1 = compute_6SX_mod(x1, new_planes)
        s2 = compute_6SX_mod(x2, new_planes)
        c = [[0] * 9 for _ in range(9)]
        for i in range(9):
            for j in range(9):
                c[i][j] = (sum(s1[i][k] * s2[k][j] - s2[i][k] * s1[k][j]
                               for k in range(9))) % P
        ph = pfaff_mod(c)
        if ph == 0:
            zero_counts[didx] += 1
        else:
            all_zero = False
    if all_zero:
        zero_all += 1
        print(f"  Trial {trial}: ALL {len(DIR_PAIRS)} Phi = 0!")
print(f"Multi-dir scan: {N_MULTI} trials, {zero_all} with ALL Phi=0")
print(f"Per-direction zero rates: {[f'{z}/{N_MULTI}' for z in zero_counts]}")

# Schwartz-Zippel estimate
if zero_single > 0:
    frac = zero_single / N_SCAN
    est_deg = frac * P
    print(f"\nSchwartz-Zippel: Phi_0 zero fraction {frac:.6f}, estimated degree {est_deg:.1f}")
    print("(If Phi_0 is a nonzero polynomial of degree d, zero fraction <= d/p)")
else:
    print(f"\nNo zeros in {N_SCAN} single-dir trials; this is sampling calibration only, not a nonexistence result")

# ============================================================
# Save certificate
# ============================================================
cert = {
    "scope": "Exact Pfaffian certificate for BILR residual Waring rank >= 11 on gl_3 (dim 9).",
    "directions": {
        "X1": [3, 0, 1, 3, -1, 1, 1, 3, -2],
        "X2": [-1, 3, -1, -1, 1, 0, -1, 2, 1],
    },
    "traces": {
        "tr_C2": str(t2),
        "tr_C3": str(t3),
        "tr_C4": str(t4),
        "tr_C3_automatic_zero": t3 == 0,
    },
    "Phi_exact": str(phi),
    "Phi_nonzero": phi != 0,
    "Phi_negative": phi < 0,
    "commutator_rank_mod_65521": rank_mod(C, 65521),
    "theorem": (
        "Strassen/Hessian bound: for k cubes on V (dim n) with nondegenerate "
        "K=(1/6)Hess_R(p), the K-skew commutator [H_X,H_Y] has even rank at most "
        "2(k-n). Thus Waring rank <=10 on gl_3 forces rank<=2 and Phi=0 for all X,Y. "
        "BILR has Phi!=0, proving Waring rank>=11. The converse Phi=0=>rank<=2 can fail "
        "for indefinite K; exact rank<=2 is characterized by the 4x4 Pfaffians of Omega=KC. "
        "Also tr(C^3)=0 is automatic and carries no information."
    ),
    "scaling_note": (
        "C = [6S_{X1}, 6S_{X2}] = 36[S_{X1},S_{X2}]. "
        "Phi(C) = 36^4 Phi([S,S]), so Phi(C) != 0 iff true Phi != 0."
    ),
    "frame_scan": {
        "prime": P,
        "single_dir_trials": N_SCAN,
        "single_dir_zeros": zero_single,
        "multi_dir_trials": N_MULTI,
        "multi_dir_num_pairs": len(DIR_PAIRS),
        "multi_dir_all_zeros": zero_all,
        "per_direction_zeros": zero_counts,
    },
}

with open(OUT / "pfaffian_certificate_and_scan.json", "w") as f:
    json.dump(cert, f, indent=2)

print(f"\nCertificate saved to {OUT / 'pfaffian_certificate_and_scan.json'}")
print("Done.")
