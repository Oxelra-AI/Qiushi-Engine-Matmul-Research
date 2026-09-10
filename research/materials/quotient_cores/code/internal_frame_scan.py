#!/usr/bin/env python3
"""
analysis: finite-field probes for the product-commutator obstruction under
internal SL_3 frame changes of the four BILR exterior planes.

This is not a proof of the characteristic-zero (10,4) branch.  It is an exact,
scoped experimental instrument for the double-edged Jennrich condition:
if a traceless (10,4) rank-22 cyclic decomposition exists, the linear space

    L = span{ [H(X), H(Y)] : X,Y in gl_3 }

for its residual must have upper rank <= 2.  Over characteristic zero, bounded
rank-2 matrix-space theory says such an L is either compressed (common image of
dimension <=2 or common kernel of dimension >=7, up to transpose) or belongs to a
small primitive rank-2 family (the 3-dimensional skew 3x3 model).  Thus the cheap
screen recorded here is:

    span_dim(L) <= 3  OR common_image_dim(L) <= 2 OR common_kernel_dim(L) >= 7.

The script samples random internal SL_3 frames and exhausts elementary one-
parameter slices over a good prime.  It also records scalar identities required
by rank<=2 for fixed (X,Y) pairs: tr(C^3)=0 and 2tr(C^4)=tr(C^2)^2.
"""

from pathlib import Path
import json
import random
import numpy as np

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "product_commutator"
OUT.mkdir(parents=True, exist_ok=True)

P = 31
rng = random.Random(20260904)

# -----------------------------------------------------------------------------
# Finite-field helpers
# -----------------------------------------------------------------------------

def inv(a):
    return pow(int(a) % P, P-2, P)

def rank_mod(M):
    A = np.array(M, dtype=np.int64) % P
    n, m = A.shape
    r = 0
    for c in range(m):
        piv = None
        for i in range(r, n):
            if A[i, c] % P:
                piv = i
                break
        if piv is None:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        A[r] = (A[r] * inv(A[r, c])) % P
        for i in range(n):
            if i != r and A[i, c] % P:
                A[i] = (A[i] - A[i, c] * A[r]) % P
        r += 1
        if r == n:
            break
    return r

def det3(M):
    A = np.array(M, dtype=np.int64) % P
    return int((A[0,0]*(A[1,1]*A[2,2]-A[1,2]*A[2,1])
              - A[0,1]*(A[1,0]*A[2,2]-A[1,2]*A[2,0])
              + A[0,2]*(A[1,0]*A[2,1]-A[1,1]*A[2,0])) % P)

def matmul(A, B):
    return (A @ B) % P

def tr3(A):
    """Trace of a 3x3 matrix over F_P."""
    return int((A[0,0] + A[1,1] + A[2,2]) % P)

def trace_mat(A):
    """Trace of an arbitrary square matrix over F_P."""
    return int(np.trace(A) % P)

def tracefree(A):
    A = np.array(A, dtype=np.int64) % P
    return (A - tr3(A) * inv(3) * np.eye(3, dtype=np.int64)) % P

def mat_from_json(M):
    return np.array(M, dtype=np.int64) % P

basis = []
basis_names = []
for i in range(3):
    for j in range(3):
        M = np.zeros((3,3), dtype=np.int64)
        M[i,j] = 1
        basis.append(M)
        basis_names.append(f"E{i}{j}")

def vec_to_mat(x):
    M = np.zeros((3,3), dtype=np.int64)
    for a, xa in enumerate(x):
        M = (M + int(xa) * basis[a]) % P
    return M

def mat_to_vec(M):
    return np.array([M[i,j] % P for i in range(3) for j in range(3)], dtype=np.int64)

def ell(A, X):
    return tr3(matmul(A, X))

# -----------------------------------------------------------------------------
# Load BILR trace-pairing free triples, stored matrices transposed.
# -----------------------------------------------------------------------------
with open(WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json") as f:
    scheme = json.load(f)

base_triples = []
for rep in scheme["free_orbit_representatives"]:
    triple = []
    for key in ["U", "V", "W"]:
        L = tracefree(mat_from_json(rep[key]))
        triple.append(L.T % P)
    base_triples.append(triple)

# -----------------------------------------------------------------------------
# Internal frame action and product Hessian.
# -----------------------------------------------------------------------------

def apply_frames(frames):
    """frames[j] is a 3x3 det-1 coordinate matrix; new columns = old columns * frame."""
    triples = []
    for tri, M in zip(base_triples, frames):
        new = []
        for col in range(3):
            A = np.zeros((3,3), dtype=np.int64)
            for row in range(3):
                A = (A + int(M[row, col]) * tri[row]) % P
            new.append(A % P)
        triples.append(new)
    return triples

def H2_product(x, triples):
    X = vec_to_mat(x)
    cols = []
    for Y in basis:
        out = (matmul(X,Y) + matmul(Y,X)) % P
        for U,V,W in triples:
            uX, vX, wX = ell(U,X), ell(V,X), ell(W,X)
            uY, vY, wY = ell(U,Y), ell(V,Y), ell(W,Y)
            out = (out - (vX*wY + wX*vY) * U) % P
            out = (out - (uX*wY + wX*uY) * V) % P
            out = (out - (uX*vY + vX*uY) * W) % P
        cols.append(mat_to_vec(out))
    return np.stack(cols, axis=1) % P

def comm(A, B):
    return (A @ B - B @ A) % P

def H_basis(triples):
    return [H2_product([1 if i == a else 0 for i in range(9)], triples) for a in range(9)]

def L_data_from_H(Hs, random_combo_trials=40):
    comms = []
    basis_ranks = []
    for a in range(9):
        for b in range(a+1,9):
            C = comm(Hs[a], Hs[b])
            comms.append(C)
            basis_ranks.append(rank_mod(C))
    span_dim = rank_mod(np.stack([C.reshape(-1) for C in comms], axis=0))
    common_image_dim = rank_mod(np.concatenate(comms, axis=1))
    common_kernel_dim = 9 - rank_mod(np.concatenate(comms, axis=0))
    max_random_rank = max(basis_ranks) if basis_ranks else 0
    for _ in range(random_combo_trials):
        C = np.zeros((9,9), dtype=np.int64)
        for Cj in comms:
            c = rng.randrange(P)
            if c:
                C = (C + c*Cj) % P
        max_random_rank = max(max_random_rank, rank_mod(C))
    screen = (span_dim <= 3) or (common_image_dim <= 2) or (common_kernel_dim >= 7)
    return {
        "span_dim": int(span_dim),
        "common_image_dim": int(common_image_dim),
        "common_kernel_dim": int(common_kernel_dim),
        "max_basis_rank": int(max(basis_ranks)),
        "max_rank_seen_random_combos": int(max_random_rank),
        "bounded_rank2_classification_screen_passes": bool(screen),
        "basis_rank_hist": {str(r): basis_ranks.count(r) for r in sorted(set(basis_ranks))},
        "comms": comms,
    }

rank2_pairs = [
    ([3,0,1,3,-1,1,1,3,-2], [-1,3,-1,-1,1,0,-1,2,1]),
    ([1,0,0,0,0,0,0,0,-1], [0,1,2,0,-1,0,3,0,1]),
    ([0,1,0,2,0,1,-1,0,3], [2,0,-1,1,1,0,0,3,-2]),
    ([1,2,3,4,5,6,7,8,9], [2,-1,0,3,-2,1,4,0,-3]),
    ([0,0,1,0,1,0,1,0,0], [1,1,0,-1,0,2,0,-2,1]),
]
rank2_pairs = [([v % P for v in x], [v % P for v in y]) for x,y in rank2_pairs]

def scalar_filter_values(Hs):
    vals = []
    for x,y in rank2_pairs:
        Hx = sum((x[a] * Hs[a] for a in range(9)), np.zeros((9,9), dtype=np.int64)) % P
        Hy = sum((y[a] * Hs[a] for a in range(9)), np.zeros((9,9), dtype=np.int64)) % P
        C = comm(Hx, Hy)
        C2 = C @ C % P
        C3 = C2 @ C % P
        C4 = C2 @ C2 % P
        tr2, tr3val, tr4 = trace_mat(C2), trace_mat(C3), trace_mat(C4)
        q4 = (2*tr4 - tr2*tr2) % P
        vals.append({"rank": rank_mod(C), "trC3": tr3val, "rank2_quartic": q4})
    passes = all(v["trC3"] == 0 and v["rank2_quartic"] == 0 for v in vals)
    return passes, vals

# -----------------------------------------------------------------------------
# Frame generation.
# -----------------------------------------------------------------------------
I3 = np.eye(3, dtype=np.int64) % P

def det_mod(M):
    return det3(M)

def random_sl3():
    while True:
        M = np.array([[rng.randrange(P) for _ in range(3)] for _ in range(3)], dtype=np.int64)
        d = det_mod(M)
        if d:
            M[0,:] = (M[0,:] * inv(d)) % P
            assert det_mod(M) == 1
            return M

def elementary_unipotent(a, b, t):
    M = I3.copy()
    M[a,b] = (M[a,b] + t) % P
    return M

def diagonal_frame(t, s):
    M = np.zeros((3,3), dtype=np.int64)
    M[0,0] = t % P
    M[1,1] = s % P
    M[2,2] = inv((t*s) % P)
    return M

# -----------------------------------------------------------------------------
# Baseline and scans.
# -----------------------------------------------------------------------------
base_frames = [I3.copy() for _ in range(4)]
base_H = H_basis(apply_frames(base_frames))
base_D = L_data_from_H(base_H, random_combo_trials=100)
base_pass, base_scalar = scalar_filter_values(base_H)

random_records = []
random_summary = {
    "samples": 300,
    "classification_screen_pass_count": 0,
    "scalar_filter_pass_count": 0,
    "both_filters_pass_count": 0,
    "span_dim_hist": {},
    "common_image_dim_hist": {},
    "common_kernel_dim_hist": {},
    "max_rank_seen_hist": {},
}
for idx in range(random_summary["samples"]):
    frames = [random_sl3() for _ in range(4)]
    Hs = H_basis(apply_frames(frames))
    D = L_data_from_H(Hs, random_combo_trials=20)
    scalar_pass, scalar_vals = scalar_filter_values(Hs)
    for key, val in [("span_dim_hist", D["span_dim"]), ("common_image_dim_hist", D["common_image_dim"]), ("common_kernel_dim_hist", D["common_kernel_dim"]), ("max_rank_seen_hist", D["max_rank_seen_random_combos"] )]:
        random_summary[key][str(val)] = random_summary[key].get(str(val), 0) + 1
    if D["bounded_rank2_classification_screen_passes"]:
        random_summary["classification_screen_pass_count"] += 1
    if scalar_pass:
        random_summary["scalar_filter_pass_count"] += 1
    if D["bounded_rank2_classification_screen_passes"] and scalar_pass:
        random_summary["both_filters_pass_count"] += 1
        if len(random_records) < 5:
            random_records.append({
                "sample_index": idx,
                "D": {k:v for k,v in D.items() if k != "comms"},
                "scalar_values": scalar_vals,
                "frames": [F.tolist() for F in frames],
            })

# Exhaust elementary one-parameter slices: one elementary SL3 move in one plane.
elementary_summary = []
for plane in range(4):
    for a in range(3):
        for b in range(3):
            if a == b:
                continue
            scalar_pass_values = []
            class_pass_values = []
            both_values = []
            min_max_rank = 9
            min_span_dim = 81
            for t in range(P):
                frames = [I3.copy() for _ in range(4)]
                frames[plane] = elementary_unipotent(a,b,t)
                Hs = H_basis(apply_frames(frames))
                D = L_data_from_H(Hs, random_combo_trials=10)
                scalar_pass, _vals = scalar_filter_values(Hs)
                min_max_rank = min(min_max_rank, D["max_rank_seen_random_combos"])
                min_span_dim = min(min_span_dim, D["span_dim"])
                if scalar_pass:
                    scalar_pass_values.append(t)
                if D["bounded_rank2_classification_screen_passes"]:
                    class_pass_values.append(t)
                if scalar_pass and D["bounded_rank2_classification_screen_passes"]:
                    both_values.append(t)
            elementary_summary.append({
                "plane": plane,
                "generator": [a,b],
                "values_tested": P,
                "scalar_filter_pass_count": len(scalar_pass_values),
                "classification_screen_pass_count": len(class_pass_values),
                "both_filters_pass_count": len(both_values),
                "scalar_filter_pass_values_first20": scalar_pass_values[:20],
                "classification_screen_pass_values_first20": class_pass_values[:20],
                "both_values_first20": both_values[:20],
                "min_max_rank_seen_random_combos": int(min_max_rank),
                "min_span_dim": int(min_span_dim),
            })

# Exhaust diagonal two-parameter slices for each plane over the same small good prime.
# This is a pilot-sized exact modular scan; larger primes can be run later if the pilot reveals structure.
diagonal_summary = []
for plane in range(4):
    scalar_count = class_count = both_count = 0
    examples = []
    min_max_rank = 9
    min_span_dim = 81
    for t in range(1, P):
        for s in range(1, P):
            frames = [I3.copy() for _ in range(4)]
            frames[plane] = diagonal_frame(t,s)
            Hs = H_basis(apply_frames(frames))
            D = L_data_from_H(Hs, random_combo_trials=5)
            scalar_pass, scalar_vals = scalar_filter_values(Hs)
            class_pass = D["bounded_rank2_classification_screen_passes"]
            min_max_rank = min(min_max_rank, D["max_rank_seen_random_combos"])
            min_span_dim = min(min_span_dim, D["span_dim"])
            if scalar_pass:
                scalar_count += 1
            if class_pass:
                class_count += 1
            if scalar_pass and class_pass:
                both_count += 1
                if len(examples) < 5:
                    examples.append({"t": t, "s": s, "D": {k:v for k,v in D.items() if k != "comms"}, "scalar_values": scalar_vals})
    diagonal_summary.append({
        "plane": plane,
        "values_tested": (P-1)*(P-1),
        "scalar_filter_pass_count": scalar_count,
        "classification_screen_pass_count": class_count,
        "both_filters_pass_count": both_count,
        "both_examples_first5": examples,
        "min_max_rank_seen_random_combos": int(min_max_rank),
        "min_span_dim": int(min_span_dim),
    })

result = {
    "scope": "Exact F_31 pilot probes of internal SL3 frame changes in the BILR four exterior planes for the Jennrich rank<=2 commutator condition.",
    "prime": P,
    "rank2_screen_explanation": "A valid <=10-cube residual must have upper rank <=2 for L=span[H(X),H(Y)]. The direct experimental rejection used here is max_rank_seen_random_combos>2 (or an explicit rank>2 basis/random combination). Bounded-rank classification over characteristic zero then says an actually upper-rank-2 L is built from rank-2 compression spaces R(2,0), R(1,1), R(0,2) and the primitive 3x3 skew-symmetric model; the simple common-image/common-kernel/span-dim screen recorded here is not a complete compression classifier because it does not detect R(1,1). Scalar filters are necessary identities for fixed X,Y, not sufficient.",
    "basis_order": basis_names,
    "fixed_rank2_scalar_test_pairs": [{"x": x, "y": y} for x,y in rank2_pairs],
    "base_bilr": {"D": {k:v for k,v in base_D.items() if k != "comms"}, "scalar_filter_passes": base_pass, "scalar_values": base_scalar},
    "random_internal_sl3_summary": random_summary,
    "random_both_filter_examples_first5": random_records,
    "elementary_one_parameter_slices": elementary_summary,
    "diagonal_two_parameter_slices": diagonal_summary,
    "interpretation": "No sampled random internal frame and no scanned elementary/diagonal slice point had upper-rank behavior compatible with rank<=2 in the tested linear combinations: random internal frames reached rank 8, while elementary and diagonal one-plane slices always had a rank-4 combination. This is not a proof: special rank-22 frames could lie outside these slices or require imposing all X,Y identities. The simple compression screen is intentionally only a coarse summary and does not implement the full R(1,1) compression alternative. The script provides a cheap exact modular instrument for locating or excluding candidate frame loci before any heavy elimination.",
}

out = OUT / "internal_frame_scan_f31.json"
with open(out, "w") as f:
    json.dump(result, f, indent=2)

# Print compact summary.
print(json.dumps({
    "out": str(out),
    "base": result["base_bilr"],
    "random_summary": random_summary,
    "elementary_total_both_pass": sum(s["both_filters_pass_count"] for s in elementary_summary),
    "elementary_total_scalar_pass": sum(s["scalar_filter_pass_count"] for s in elementary_summary),
    "elementary_total_class_pass": sum(s["classification_screen_pass_count"] for s in elementary_summary),
    "diagonal_total_both_pass": sum(s["both_filters_pass_count"] for s in diagonal_summary),
    "diagonal_total_scalar_pass": sum(s["scalar_filter_pass_count"] for s in diagonal_summary),
    "diagonal_total_class_pass": sum(s["classification_screen_pass_count"] for s in diagonal_summary),
}, indent=2))
