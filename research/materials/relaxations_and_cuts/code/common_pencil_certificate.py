#!/usr/bin/env python3
"""
analysis: common-pencil associator certificate for the BILR residual.

For a Waring decomposition with k=n+1 and nondegenerate K, the Hessian
commutator 2-form Omega(X,Y)=K[H_X,H_Y] has the normal form
    Omega(X,Y) = -c * G(X) wedge G(Y),
so for every fixed X,
    Omega(X,Y) wedge Omega(X,Z) = 0        for all Y,Z.
This condition is quadratic in the skew 2-form entries and is stronger than
checking a finite list of scalar trace identities.  It is valid over char != 2
as a necessary condition for Waring rank <= n+1.

This script calibrates the condition on the fixed BILR residual cubic.  It finds
an exact integer triple X,Y,Z for which the mixed wedge is nonzero, giving a
low-degree certificate that the BILR residual is not a 10-cube residual.
"""

import json, random, math
from pathlib import Path
from itertools import combinations
from functools import reduce
import sympy as sp

SESSION = Path("research/research_record")
SCHEME_PATH = SESSION / "workspace/data/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json"
OUT_DIR = SESSION / "workspace/data/reduced_pair_associator"
OUT_DIR.mkdir(parents=True, exist_ok=True)
OUT_PATH = OUT_DIR / "bilr_common_pencil_certificate.json"


def transpose3(M):
    return [[M[j][i] for j in range(3)] for i in range(3)]


def tr3(A, B):
    return sum(A[i][j] * B[j][i] for i in range(3) for j in range(3))


def mat_from_vec(v):
    return [[v[3*i+j] for j in range(3)] for i in range(3)]


with open(SCHEME_PATH) as f:
    scheme = json.load(f)

PLANES = []
for rep in scheme["free_orbit_representatives"]:
    PLANES.append((transpose3(rep["U"]), transpose3(rep["V"]), transpose3(rep["W"])))

K = sp.zeros(9, 9)
for i in range(3):
    for j in range(3):
        K[3*i+j, 3*j+i] = 1

# A fixed integer basis for sl_3 in row-major coordinates.
SL3_BASIS_MATS = [
    [[0,1,0],[0,0,0],[0,0,0]],
    [[0,0,1],[0,0,0],[0,0,0]],
    [[0,0,0],[1,0,0],[0,0,0]],
    [[0,0,0],[0,0,1],[0,0,0]],
    [[0,0,0],[0,0,0],[1,0,0]],
    [[0,0,0],[0,0,0],[0,1,0]],
    [[1,0,0],[0,-1,0],[0,0,0]],
    [[0,0,0],[0,1,0],[0,0,-1]],
]
B = sp.zeros(9, 8)
for col, M in enumerate(SL3_BASIS_MATS):
    for i in range(3):
        for j in range(3):
            B[3*i+j, col] = M[i][j]


def compute_6H(X, planes):
    fv = [(tr3(A, X), tr3(BB, X), tr3(C, X)) for A, BB, C in planes]
    S = sp.zeros(9, 9)
    for idx in range(9):
        r, c = divmod(idx, 3)
        col = [0] * 9
        for i in range(3):
            for j in range(3):
                v = 0
                if j == c:
                    v += X[i][r]
                if i == r:
                    v += X[c][j]
                col[3*i+j] = 3 * v
        for pidx, (A, BB, C) in enumerate(planes):
            aX, bX, cX = fv[pidx]
            aY = A[c][r]
            bY = BB[c][r]
            cY = C[c][r]
            for i in range(3):
                for j in range(3):
                    corr = ((bY*cX + bX*cY) * A[i][j]
                            + (aY*cX + aX*cY) * BB[i][j]
                            + (aY*bX + aX*bY) * C[i][j])
                    col[3*i+j] -= 3 * corr
        for a in range(9):
            S[a, idx] = col[a]
    return S


def omega_sl3(X, Y):
    Sx = compute_6H(X, PLANES)
    Sy = compute_6H(Y, PLANES)
    C = Sx * Sy - Sy * Sx  # scaled by 36; scale irrelevant for nonvanishing
    Omega9 = K * C
    Omega8 = B.T * Omega9 * B
    skew_error = Omega8 + Omega8.T
    assert skew_error == sp.zeros(8, 8)
    return Omega8, C


def wedge2_mixed(A, BB):
    """Coefficients of A wedge BB in Lambda^4 for skew 8x8 matrices."""
    coeffs = {}
    for inds in combinations(range(8), 4):
        i, j, k, l = inds
        val = (A[i,j]*BB[k,l] - A[i,k]*BB[j,l] + A[i,l]*BB[j,k]
               + BB[i,j]*A[k,l] - BB[i,k]*A[j,l] + BB[i,l]*A[j,k])
        if val != 0:
            coeffs[inds] = sp.simplify(val)
    return coeffs


def rank_mod(M, p):
    rows = [[int(M[i, j]) % p for j in range(M.cols)] for i in range(M.rows)]
    rank = 0
    nrows, ncols = len(rows), len(rows[0])
    for col in range(ncols):
        piv = None
        for r in range(rank, nrows):
            if rows[r][col] % p:
                piv = r
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], p-2, p)
        for r in range(nrows):
            if r != rank and rows[r][col] % p:
                fac = rows[r][col] * inv % p
                for cc in range(col, ncols):
                    rows[r][cc] = (rows[r][cc] - fac * rows[rank][cc]) % p
        rank += 1
    return rank


X = [[3, 0, 1], [3, -1, 1], [1, 3, -2]]
Y = [[-1, 3, -1], [-1, 1, 0], [-1, 2, 1]]

# Search for a small Z with nonzero mixed wedge.
random.seed(20260906)
found = None
for trial in range(500):
    if trial == 0:
        Z = [[1,0,0],[0,-1,0],[0,0,0]]
    elif trial == 1:
        Z = [[0,1,0],[0,0,1],[1,0,0]]
    else:
        Z = [[random.randint(-2, 2) for _ in range(3)] for _ in range(3)]
    OmXY, Cxy = omega_sl3(X, Y)
    OmXZ, Cxz = omega_sl3(X, Z)
    coeffs = wedge2_mixed(OmXY, OmXZ)
    if coeffs:
        found = (trial, Z, OmXY, OmXZ, Cxy, Cxz, coeffs)
        break

if found is None:
    raise RuntimeError("No nonzero common-pencil wedge found in search")

trial, Z, OmXY, OmXZ, Cxy, Cxz, coeffs = found
first_inds, first_val = next(iter(coeffs.items()))

# Also compute ordinary rank/Pfaffian-square counts for the two individual 2-forms.
def nonzero_4pf_count(A):
    count = 0
    first = None
    for inds in combinations(range(8), 4):
        i, j, k, l = inds
        val = A[i,j]*A[k,l] - A[i,k]*A[j,l] + A[i,l]*A[j,k]
        if val != 0:
            count += 1
            if first is None:
                first = (inds, sp.simplify(val))
    return count, first

pf_count_xy, first_pf_xy = nonzero_4pf_count(OmXY)
pf_count_xz, first_pf_xz = nonzero_4pf_count(OmXZ)

record = {
    "schema": "common_pencil_certificate_v1",
    "scope": "Exact integer common-pencil wedge certificate for the fixed BILR residual cubic on sl_3/gl_3.",
    "necessary_condition": "If a cubic on n variables has Waring rank <= n+1 and nondegenerate Hessian at p, then for every fixed X, Omega(X,Y) wedge Omega(X,Z)=0 for all Y,Z, where Omega=K[H_X,H_Y].",
    "convention": "Stored BILR free representatives are transposed to A=L^T for l_A(X)=tr(A X).  Operators use 6H scaling; nonzero wedge is scale-independent.",
    "X": X,
    "Y": Y,
    "Z": Z,
    "Z_search_trial": trial,
    "rank_Cxy_mod_primes": {str(p): rank_mod(Cxy, p) for p in [101, 1009, 65521]},
    "rank_Cxz_mod_primes": {str(p): rank_mod(Cxz, p) for p in [101, 1009, 65521]},
    "rank_OmegaXY_sl3_Q": int(OmXY.rank()),
    "rank_OmegaXZ_sl3_Q": int(OmXZ.rank()),
    "individual_OmegaXY_nonzero_4pf_count": pf_count_xy,
    "individual_OmegaXY_first_nonzero_4pf": {"indices": list(first_pf_xy[0]), "value": str(first_pf_xy[1])} if first_pf_xy else None,
    "individual_OmegaXZ_nonzero_4pf_count": pf_count_xz,
    "individual_OmegaXZ_first_nonzero_4pf": {"indices": list(first_pf_xz[0]), "value": str(first_pf_xz[1])} if first_pf_xz else None,
    "mixed_wedge_nonzero_coeff_count": len(coeffs),
    "mixed_wedge_first_nonzero_coeff": {"indices": list(first_inds), "value": str(first_val)},
    "mixed_wedge_gcd_abs_coeffs": str(reduce(math.gcd, [abs(int(v)) for v in coeffs.values()])),
    "interpretation": "The fixed BILR residual violates the k=n+1 common-pencil condition.  This is another exact certificate that the BILR residual has Waring rank at least 11.  For variable cyclic frames the same wedge equations, especially in reduced split choices, are necessary filters; surviving zeros are candidate loci, not algorithms.",
}

with open(OUT_PATH, "w") as f:
    json.dump(record, f, indent=2)

print(json.dumps({
    "out": str(OUT_PATH),
    "Z_search_trial": trial,
    "rank_OmegaXY_sl3_Q": record["rank_OmegaXY_sl3_Q"],
    "rank_OmegaXZ_sl3_Q": record["rank_OmegaXZ_sl3_Q"],
    "individual_OmegaXY_nonzero_4pf_count": pf_count_xy,
    "individual_OmegaXZ_nonzero_4pf_count": pf_count_xz,
    "mixed_wedge_nonzero_coeff_count": len(coeffs),
    "mixed_wedge_first_nonzero_coeff": record["mixed_wedge_first_nonzero_coeff"],
}, indent=2))
