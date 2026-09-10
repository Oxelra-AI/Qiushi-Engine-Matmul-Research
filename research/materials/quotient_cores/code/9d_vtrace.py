#!/usr/bin/env python3
r"""analysis: 9D V_trace basis analysis — the definitive compact representation.

Key result: all tensor functionals F(p) live in the 9D V_trace space.
This script:
1) Finds an explicit 9D basis for V_trace
2) Expresses all 255 F(p) and all 72 phi_q in this basis
3) Computes the "determined parity" for each support direction when hitting
   contractions span all of V_trace
4) Characterizes the 9 rank-deficient directions structurally
5) Checks how many independent parity constraints the certificate collection gives
"""
from __future__ import annotations
import json, sys, time
from collections import Counter
from pathlib import Path
import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    build_matmul_tensor_f2, contraction_matrix, mat_rank_f2,
)
from dual_basis_instrument import gf2_mat_inv

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/family_consequence"
CERT_PATH = ROOT / "workspace/data/corrected_independent-verification-record"
NEAR_MISS = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]


def build_e11_core_tensor():
    return build_matmul_tensor_f2()[1:,:,:].astype(np.uint8) % 2

def popcount(x): return bin(x).count('1')

def gf2_rref_basis(vecs):
    basis = []
    for v in vecs:
        for b in basis: v = min(v, v^b)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    return basis

def gf2_rank(vecs): return len(gf2_rref_basis(vecs))

def gf2_coords(v, basis):
    """Express v in terms of basis over GF(2). Returns coefficient list or None."""
    n = len(basis)
    work_basis = []
    for i, b in enumerate(basis):
        vv, mm = b, 1 << i
        for bv, bm in work_basis:
            vv2 = vv ^ bv
            if vv2 < vv: vv, mm = vv2, mm ^ bm
        if vv: work_basis.append((vv, mm))
    vv, mm = v, 0
    for bv, bm in work_basis:
        vv2 = vv ^ bv
        if vv2 < vv: vv, mm = vv2, mm ^ bm
    if vv != 0:
        return None
    return [(mm >> i) & 1 for i in range(n)]

def compute_phi_q(M_inv):
    result = 0
    for b in range(9):
        for c in range(9):
            if int(M_inv[c,b]) & 1: result |= 1<<(b*9+c)
    return result


def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    T_core = build_e11_core_tensor()
    na, nb, nc = T_core.shape

    # Build all rank-9 contractions and phis
    rank9_qs = []
    phi_vectors = {}
    for q in range(1, 1 << na):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) != 9: continue
        rank9_qs.append(q)
        M_inv = gf2_mat_inv(M)
        phi_vectors[q] = compute_phi_q(M_inv)

    # Build V_trace basis
    all_phis = [phi_vectors[q] for q in rank9_qs]
    vtrace_basis = gf2_rref_basis(all_phis)
    print(f"V_trace dim = {len(vtrace_basis)}")

    # Load certificate to get tensor masks
    with open(CERT_PATH) as f:
        cert_data = json.load(f)
    labels = cert_data["full_greedy_row_shrink"]["labels"]
    tensor_masks = {}
    for lbl in labels:
        if lbl[0] == "tensor":
            i, b, c = int(lbl[1]), int(lbl[2]), int(lbl[3])
            tensor_masks[(b,c)] = tensor_masks.get((b,c), 0) ^ (1<<i)

    def compute_F(p):
        result = 0
        for b in range(nb):
            for c in range(nc):
                mask = tensor_masks.get((b,c), 0)
                if popcount(p & mask) & 1: result |= 1 << (b*nc+c)
        return result

    # Express all F(p) and phi_q in 9D coordinates
    print("\n=== 9D V_trace coordinate analysis ===")
    F_coords = {}
    F_in_vtrace = 0
    for p in range(1, 256):
        F_p = compute_F(p)
        coords = gf2_coords(F_p, vtrace_basis)
        if coords is not None:
            F_coords[p] = tuple(coords)
            F_in_vtrace += 1
    print(f"Directions in V_trace: {F_in_vtrace}/255")

    phi_coords = {}
    for q in rank9_qs:
        coords = gf2_coords(phi_vectors[q], vtrace_basis)
        assert coords is not None, f"phi_{q} not in V_trace!"
        phi_coords[q] = tuple(coords)

    # For each direction p, compute the "full-determined parity"
    # i.e., the forced value when ALL hitting rank-9 contractions are saturated
    # This is: find alpha such that F(p) = sum alpha_q phi_q for hitting q's
    # Then v(p) = sum alpha_q (mod 2)
    print("\n=== Full-determined parity computation ===")
    full_det_parity = {}
    rank_deficient = []
    for p in range(1, 256):
        F_p = compute_F(p)
        if F_p == 0:
            full_det_parity[p] = 0
            continue
        hitting = [phi_vectors[q] for q in rank9_qs if popcount(q & p) & 1]
        # Check if F(p) is in hitting span
        hbasis = []
        for i, h in enumerate(hitting):
            v, m = h, 1 << i
            for bv, bm in hbasis:
                v2 = v ^ bv
                if v2 < v: v, m = v2, m ^ bm
            if v: hbasis.append((v, m))
        v, m = F_p, 0
        for bv, bm in hbasis:
            v2 = v ^ bv
            if v2 < v: v, m = v2, m ^ bm
        if v == 0:
            full_det_parity[p] = popcount(m) % 2
        else:
            rank_deficient.append(p)

    print(f"Full-determined: {len(full_det_parity)}/255")
    print(f"Rank-deficient: {len(rank_deficient)}")

    parity_hist = Counter(full_det_parity.values())
    print(f"Parity distribution: {dict(parity_hist)}")

    # For a 19-point support from full-determined directions:
    # sum v(p_i) must satisfy the tensor functional constraint
    # T_rhs depends on the certificate, so it's cert-specific
    tensor_rhs = 0
    for lbl in labels:
        if lbl[0] == "tensor":
            i,b,c = int(lbl[1]),int(lbl[2]),int(lbl[3])
            tensor_rhs ^= int(T_core[i,b,c]) & 1
    print(f"\nTensor RHS parity: {tensor_rhs}")

    # Near-miss under full-72 guard
    nm_parity = sum(full_det_parity.get(p, 0) for p in NEAR_MISS) % 2
    print(f"Near-miss parity (full-72): {nm_parity} vs tensor_rhs={tensor_rhs}")
    print(f"  Contradiction: {nm_parity != tensor_rhs}")

    # The 9 rank-deficient directions
    print(f"\n=== Rank-deficient directions ===")
    mapping = ["E12","E13","E21","E22","E23","E31","E32","E33"]
    for p in rank_deficient:
        bits = "+".join(mapping[i] for i in range(8) if (p>>i)&1)
        F_p = compute_F(p)
        F_coords_p = gf2_coords(F_p, vtrace_basis)
        hitting_count = sum(1 for q in rank9_qs if popcount(q&p)&1)
        hit_phis = [phi_vectors[q] for q in rank9_qs if popcount(q&p)&1]
        hit_rank = gf2_rank(hit_phis)
        # Which dimension is missing?
        hit_basis = gf2_rref_basis(hit_phis)
        missing_dim = None
        for j, bv in enumerate(vtrace_basis):
            if not any(bv == hb for hb in hit_basis):
                if not all(bv == min(bv, bv^hb) for hb in hit_basis if bv != min(bv, bv^hb)):
                    pass
            vv = bv
            for hb in hit_basis: vv = min(vv, vv^hb)
            if vv != 0:
                missing_dim = j
                break
        print(f"  p={p} ({bits}): F_coords={F_coords_p}, hit_rank={hit_rank}, "
              f"hitting={hitting_count}, missing_dim={missing_dim}")

    # Key structural observation: the 9 rank-deficient directions
    # Check if they form a subspace
    rd_spans = gf2_rank([p for p in rank_deficient])
    print(f"\nRank-deficient directions span: {rd_spans} dimensions")
    print(f"Rank-deficient directions: {rank_deficient}")

    # Are they closed under XOR?
    rd_set = set(rank_deficient)
    closed = True
    for i, a in enumerate(rank_deficient):
        for b in rank_deficient[i+1:]:
            if (a^b) != 0 and (a^b) not in rd_set:
                closed = False
                break
    print(f"Closed under XOR: {closed}")

    # Summary: what fraction of 19-element subsets of full-determined directions
    # satisfy the parity constraint?
    n0, n1 = parity_hist.get(0, 0), parity_hist.get(1, 0)
    print(f"\nFull-determined: {n0} with v=0, {n1} with v=1")
    print(f"Any 19-point support from these needs odd count of v=1 for parity=1")
    print(f"Or even count of v=1 for parity=0")
    print(f"Tensor RHS={tensor_rhs}, so need {'odd' if tensor_rhs else 'even'} count of v=1")

    elapsed = time.time() - t0
    result = {
        "schema": "9d_vtrace_analysis_v1",
        "elapsed_sec": round(elapsed, 3),
        "vtrace_dim": len(vtrace_basis),
        "all_F_in_vtrace": F_in_vtrace == 255,
        "full_determined_count": len(full_det_parity),
        "rank_deficient_count": len(rank_deficient),
        "rank_deficient_directions": rank_deficient,
        "parity_distribution": dict(parity_hist),
        "tensor_rhs": tensor_rhs,
        "near_miss_full72_parity": nm_parity,
        "near_miss_contradiction_full72": nm_parity != tensor_rhs,
    }
    out = OUTDIR / "9d_vtrace_analysis.json"
    with open(out, 'w') as f:
        json.dump(result, f, indent=2)
    print(f"\nSaved {out}")

if __name__ == '__main__':
    main()
