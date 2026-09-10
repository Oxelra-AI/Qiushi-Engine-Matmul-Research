#!/usr/bin/env python3
r"""
analysis: reduced-pair associator/Pfaffian calibration for the traceless (10,4)
cyclic branch on the BILR exterior component.

For a splitting {i,j}|{k,l}, choose X,Y spanning
    (P_i + P_j)^perp \cap sl_3
with respect to tr(A X).  The plane corrections for P_i and P_j vanish on
both X and Y, so the associator commutator depends only on the two remaining
internal frames P_k,P_l.  Before doing any elimination, this script checks at
the BILR identity frame whether rank([H_X,H_Y]) is already 4 for some splitting.
If so, the reduced two-frame Pfaffian equations are active; if all ranks are <=2,
this reduction is inactive at BILR.

Important convention: stored representatives L give l_L(X)=tr(L^T X), so we use
A=L^T as coefficient matrices in l_A(X)=tr(A X).
"""

import json
from pathlib import Path
from itertools import combinations
from math import gcd
from functools import reduce
import sympy as sp

SESSION = Path("research/research_record")
SCHEME_PATH = SESSION / "workspace/data/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json"
OUT_DIR = SESSION / "workspace/data/reduced_pair_associator"
OUT_DIR.mkdir(parents=True, exist_ok=True)
OUT_PATH = OUT_DIR / "bilr_reduced_pair_calibration.json"


def transpose3(M):
    return [[M[j][i] for j in range(3)] for i in range(3)]


def flatten(M):
    return [M[i][j] for i in range(3) for j in range(3)]


def mat_from_vec(v):
    return [[v[3*i+j] for j in range(3)] for i in range(3)]


def tr3(A, B):
    return sum(A[i][j] * B[j][i] for i in range(3) for j in range(3))


def linear_form_row(A):
    """Row r with r dot vec(X) = tr(A X)."""
    return [A[c][r] for r in range(3) for c in range(3)]


with open(SCHEME_PATH) as f:
    scheme = json.load(f)

PLANES = []
for rep in scheme["free_orbit_representatives"]:
    # Transpose stored representatives for l_A(X)=tr(A X).
    PLANES.append((transpose3(rep["U"]), transpose3(rep["V"]), transpose3(rep["W"])))

# Trace pairing matrix K on row-major gl_3: vec(X)^T K vec(Y)=tr(XY).
K = sp.zeros(9, 9)
for i in range(3):
    for j in range(3):
        K[3*i+j, 3*j+i] = 1

TRACE_ROW = [1 if idx in (0,4,8) else 0 for idx in range(9)]


def integer_nullspace_basis(rows):
    M = sp.Matrix(rows)
    ns = M.nullspace()
    out = []
    for v in ns:
        denoms = [sp.denom(x) for x in v]
        lcm = 1
        for d in denoms:
            lcm = sp.ilcm(lcm, int(d))
        ints = [int(x * lcm) for x in v]
        g = 0
        for a in ints:
            g = gcd(g, abs(a))
        if g > 1:
            ints = [a // g for a in ints]
        # Normalize sign for reproducibility.
        for a in ints:
            if a != 0:
                if a < 0:
                    ints = [-b for b in ints]
                break
        out.append(ints)
    return out, M.rank()


def compute_6H(X, planes, active_corrections=None):
    """
    Return the 9x9 matrix of 6 H_X on gl_3, where H_X(Y)=X*Y for the
    residual product.  The coefficient 3 in the Jordan term is essential:
        6 * ((XY+YX)/2) = 3(XY+YX).
    If active_corrections is supplied, only those plane corrections are included.
    """
    active = set(range(len(planes))) if active_corrections is None else set(active_corrections)
    fv = [(tr3(A, X), tr3(B, X), tr3(C, X)) for A, B, C in planes]
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
        for pidx, (A, B, C) in enumerate(planes):
            if pidx not in active:
                continue
            aX, bX, cX = fv[pidx]
            aY = A[c][r]
            bY = B[c][r]
            cY = C[c][r]
            for i in range(3):
                for j in range(3):
                    corr = ((bY*cX + bX*cY) * A[i][j]
                            + (aY*cX + aX*cY) * B[i][j]
                            + (aY*bX + aX*bY) * C[i][j])
                    col[3*i+j] -= 3 * corr
        for a in range(9):
            S[a, idx] = col[a]
    return S


def pfaffian4_skew(M, inds):
    a, b, c, d = inds
    return M[a, b] * M[c, d] - M[a, c] * M[b, d] + M[a, d] * M[b, c]


def rank_mod_int_matrix(M, p):
    rows = [[int(M[i, j]) % p for j in range(M.cols)] for i in range(M.rows)]
    rank = 0
    nrows, ncols = len(rows), len(rows[0])
    for col in range(ncols):
        pivot = None
        for r in range(rank, nrows):
            if rows[r][col] % p:
                pivot = r
                break
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inv = pow(rows[rank][col] % p, p - 2, p)
        for r in range(nrows):
            if r != rank and rows[r][col] % p:
                fac = rows[r][col] * inv % p
                for cc in range(col, ncols):
                    rows[r][cc] = (rows[r][cc] - fac * rows[rank][cc]) % p
        rank += 1
        if rank == nrows:
            break
    return rank


results = {
    "schema": "reduced_pair_associator_calibration_v1",
    "scope": "BILR exterior component identity frame; exact Q/integer calibration of reduced two-frame associator tests.",
    "scheme_path": str(SCHEME_PATH),
    "convention": "Stored L are transposed to A=L^T so l_A(X)=tr(A X).  Matrix K is the trace-pairing permutation vec(X)^T K vec(Y)=tr(XY).",
    "plane_traces": [],
    "splittings": [],
}

for j, plane in enumerate(PLANES):
    results["plane_traces"].append([[tr3(A, [[1,0,0],[0,1,0],[0,0,1]]) for A in plane]])

print("Reduced-pair associator/Pfaffian calibration at BILR")
print("=" * 72)

for pair in combinations(range(4), 2):
    rows = []
    for idx in pair:
        for A in PLANES[idx]:
            rows.append(linear_form_row(A))
    rows.append(TRACE_ROW)
    ns, row_rank = integer_nullspace_basis(rows)
    assert len(ns) >= 2, (pair, len(ns), row_rank)
    # In the BILR transverse case this should be exactly 2-dimensional.
    Xv, Yv = ns[0], ns[1]
    X = mat_from_vec(Xv)
    Y = mat_from_vec(Yv)
    remaining = [idx for idx in range(4) if idx not in pair]

    Sx_full = compute_6H(X, PLANES)
    Sy_full = compute_6H(Y, PLANES)
    Sx_remaining = compute_6H(X, PLANES, active_corrections=remaining)
    Sy_remaining = compute_6H(Y, PLANES, active_corrections=remaining)
    Sx_none = compute_6H(X, PLANES, active_corrections=[])
    Sy_none = compute_6H(Y, PLANES, active_corrections=[])

    full_equals_remaining = (Sx_full == Sx_remaining and Sy_full == Sy_remaining)
    C = Sx_full * Sy_full - Sy_full * Sx_full
    C_jordan = Sx_none * Sy_none - Sy_none * Sx_none
    Omega = K * C
    skew_error = Omega + Omega.T
    omega_rank = Omega.rank()
    c_rank = C.rank()
    jordan_rank = C_jordan.rank()

    nonzero_pfaffians = []
    first_pf = None
    for inds in combinations(range(9), 4):
        pf = sp.simplify(pfaffian4_skew(Omega, inds))
        if pf != 0:
            nonzero_pfaffians.append(inds)
            if first_pf is None:
                first_pf = {"indices": list(inds), "value": str(pf)}
    # Forms from killed planes should vanish on X and Y.
    killed_form_values = {}
    for idx in pair:
        vals = []
        for A in PLANES[idx]:
            vals.append({"on_X": tr3(A, X), "on_Y": tr3(A, Y)})
        killed_form_values[str(idx)] = vals

    # Does C annihilate I and land in sl3, as it should for traceless residuals?
    Ivec = sp.Matrix([1,0,0,0,1,0,0,0,1])
    CI = C * Ivec
    image_trace_violations = []
    for col in range(9):
        image_trace_violations.append(sum(C[3*d+d, col] for d in range(3)))

    rec = {
        "killed_pair": list(pair),
        "remaining_pair": remaining,
        "constraint_row_rank": row_rank,
        "complement_dim_in_sl3": len(ns),
        "basis_X": X,
        "basis_Y": Y,
        "killed_plane_form_values": killed_form_values,
        "full_equals_remaining_corrections": full_equals_remaining,
        "rank_C_over_Q": c_rank,
        "rank_Omega_over_Q": omega_rank,
        "rank_Jordan_only_C_over_Q": jordan_rank,
        "rank_C_mod_primes": {str(p): rank_mod_int_matrix(C, p) for p in [101, 1009, 65521]},
        "Omega_skew_max_abs_entry": max(abs(int(x)) for x in list(skew_error)) if skew_error.shape != (0,0) else 0,
        "Omega_nonzero_4x4_pfaffian_count": len(nonzero_pfaffians),
        "Omega_first_nonzero_4x4_pfaffian": first_pf,
        "C_annihilates_identity": all(v == 0 for v in CI),
        "C_identity_image": [int(v) for v in CI],
        "C_image_trace_violations": [int(v) for v in image_trace_violations],
    }
    results["splittings"].append(rec)

    print(f"split {pair}|{tuple(remaining)}: dim={len(ns)}, rank C={c_rank}, rank Omega={omega_rank}, "
          f"nonzero 4pf={len(nonzero_pfaffians)}, killed_ok={full_equals_remaining}")
    if first_pf:
        print(f"  first 4x4 Pfaffian {first_pf['indices']} = {first_pf['value']}")

active = [rec for rec in results["splittings"] if rec["rank_C_over_Q"] >= 4]
results["summary"] = {
    "num_splittings": len(results["splittings"]),
    "active_rank_ge4_splittings": [rec["killed_pair"] for rec in active],
    "all_complements_dim_2": all(rec["complement_dim_in_sl3"] == 2 for rec in results["splittings"]),
    "all_killed_corrections_verified": all(rec["full_equals_remaining_corrections"] for rec in results["splittings"]),
    "all_Omega_skew": all(rec["Omega_skew_max_abs_entry"] == 0 for rec in results["splittings"]),
    "all_C_kills_identity": all(rec["C_annihilates_identity"] for rec in results["splittings"]),
    "all_C_image_in_sl3": all(all(v == 0 for v in rec["C_image_trace_violations"]) for rec in results["splittings"]),
    "interpretation": (
        "At the BILR identity frame the reduced pair tests are active exactly when some splitting has rank_C_over_Q >= 4. "
        "A rank-4 split provides a two-remaining-frame polynomial system: all 4x4 Pfaffians of Omega=K[H_X,H_Y] must vanish for a rank-10 residual."
    ),
}

with open(OUT_PATH, "w") as f:
    json.dump(results, f, indent=2)

print("=" * 72)
print(json.dumps(results["summary"], indent=2))
print(f"wrote {OUT_PATH}")
