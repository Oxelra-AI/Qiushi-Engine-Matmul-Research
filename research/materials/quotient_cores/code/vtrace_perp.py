#!/usr/bin/env python3
r"""analysis: V_trace perpendicular structure and family parity enumeration.

Investigates the 4 perpendicular escape directions {5,7,33,35} — why F(p) for
these directions has components outside the 9D trace functional space V_trace.

Also:
- Compute the full V_trace basis and its dual in F_2^81
- Characterize F(p) decomposition into V_trace and V_trace^perp components
- Enumerate how many 19-point forced-only supports give parity contradiction
- Check whether multiple certificates can cover different supports
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    build_matmul_tensor_f2,
    contraction_matrix,
    mat_rank_f2,
)
from dual_basis_instrument import gf2_mat_inv

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/family_consequence"
CERT_PATH = ROOT / "workspace/data/corrected_independent-verification-record"
NEAR_MISS = [1, 2, 3, 4, 8, 20, 24, 31, 32, 64, 73, 109, 127, 128, 141, 160, 182, 192, 219]
ESCAPE_FULL = [5, 7, 33, 35]


def build_e11_core_tensor():
    return build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2


def popcount(x):
    return bin(x).count('1')


def gf2_rref_basis(vecs):
    """Return a reduced basis in descending pivot order."""
    basis = []
    for v in vecs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    return basis


def gf2_in_span(target, generators):
    basis = gf2_rref_basis(generators)
    v = target
    for b in basis:
        v = min(v, v ^ b)
    return v == 0


def compute_phi_q(M_inv):
    result = 0
    for b in range(9):
        for c in range(9):
            if int(M_inv[c, b]) & 1:
                result |= 1 << (b * 9 + c)
    return result


def describe_direction(p):
    """Convert 8-bit E11-core direction to matrix entry names."""
    names = ["E12", "E13", "E21", "E22", "E23", "E31", "E32", "E33"]
    bits = [names[i] for i in range(8) if (p >> i) & 1]
    return "+".join(bits) if bits else "0"


def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)

    with open(CERT_PATH) as f:
        cert_data = json.load(f)
    labels = cert_data["full_greedy_row_shrink"]["labels"]

    # Build tensor masks
    tensor_masks = {}
    for lbl in labels:
        if lbl[0] == "tensor":
            i, b, c = int(lbl[1]), int(lbl[2]), int(lbl[3])
            tensor_masks[(b, c)] = tensor_masks.get((b, c), 0) ^ (1 << i)

    T_core = build_e11_core_tensor()
    na, nb, nc = T_core.shape

    # Compute all rank-9 phi vectors
    rank9_qs = []
    phi_vectors = {}
    for q in range(1, 1 << na):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) != 9:
            continue
        rank9_qs.append(q)
        M_inv = gf2_mat_inv(M)
        phi_vectors[q] = compute_phi_q(M_inv)

    # Compute V_trace basis
    all_phis = [phi_vectors[q] for q in rank9_qs]
    vtrace_basis = gf2_rref_basis(all_phis)
    vtrace_dim = len(vtrace_basis)
    print(f"V_trace dimension: {vtrace_dim}")
    print(f"V_trace basis pivots: {[v.bit_length()-1 for v in vtrace_basis]}")

    # Analyze the 4 perpendicular escape directions
    print("\n=== Perpendicular escape directions ===")
    escape_details = []
    for p in ESCAPE_FULL:
        F_p = 0
        for b in range(nb):
            for c in range(nc):
                mask = tensor_masks.get((b, c), 0)
                if popcount(p & mask) & 1:
                    F_p |= 1 << (b * nc + c)

        F_weight = popcount(F_p)
        in_vtrace = gf2_in_span(F_p, vtrace_basis)

        # Decompose F_p into trace and perp components
        F_trace = F_p
        for bv in vtrace_basis:
            F_trace = min(F_trace, F_trace ^ bv)
        F_perp = F_p ^ F_trace  # Wait, this is wrong. Let me redo.
        
        # Project F_p onto V_trace: find the V_trace component
        F_proj = 0
        residual = F_p
        for bv in vtrace_basis:
            residual2 = residual ^ bv
            if residual2 < residual:
                residual = residual2
                F_proj ^= bv
        # F_proj is the V_trace component, residual is the V_trace^perp component
        # F_p = F_proj ^ residual
        F_perp = residual
        assert F_p == (F_proj ^ F_perp)

        # Which rank-9 contractions hit this direction?
        hitting_qs = [q for q in rank9_qs if popcount(q & p) & 1]

        # Analyze the perp component: which (b,c) coordinates?
        perp_coords = [(b, c) for b in range(9) for c in range(9) if (F_perp >> (b*9+c)) & 1]
        perp_block = [(b//3, b%3, c//3, c%3) for b, c in perp_coords]

        desc = describe_direction(p)
        print(f"\np={p} ({desc}):")
        print(f"  F(p) weight: {F_weight}, in V_trace: {in_vtrace}")
        print(f"  V_trace projection weight: {popcount(F_proj)}")
        print(f"  V_perp component weight: {popcount(F_perp)}")
        print(f"  Rank-9 contractions hitting p: {len(hitting_qs)}/72")
        print(f"  Perp coordinates (b_row,b_col,c_row,c_col): {perp_block[:10]}")
        
        # Check: are perp coords all off-diagonal (b_col != c_col)?
        off_diag = [(br, bc, cr, cc) for br, bc, cr, cc in perp_block if bc != cc]
        on_diag = [(br, bc, cr, cc) for br, bc, cr, cc in perp_block if bc == cc]
        print(f"  Perp on block-diagonal: {len(on_diag)}, off block-diagonal: {len(off_diag)}")

        escape_details.append({
            "p": p,
            "description": desc,
            "F_weight": F_weight,
            "F_perp_weight": popcount(F_perp),
            "F_proj_weight": popcount(F_proj),
            "hitting_rk9_count": len(hitting_qs),
            "perp_on_diagonal": len(on_diag),
            "perp_off_diagonal": len(off_diag),
        })

    # Check: why are ONLY these 4 directions perpendicular?
    # The tensor functional F(p)[b,c] = popcount(p AND tensor_mask(b,c)) mod 2
    # The trace span V_trace consists of vectors nonzero only on block-diagonal (b%3 == c%3)
    # So F(p) is in V_trace iff F(p) is zero on all off-diagonal positions
    
    print("\n=== Block-diagonal analysis of V_trace ===")
    # V_trace lives in the block-diagonal subspace
    # Check: does every phi_q have zero off-diagonal entries?
    off_diag_phis = 0
    for q in rank9_qs:
        phi = phi_vectors[q]
        for b in range(9):
            for c in range(9):
                if b % 3 != c % 3:
                    if (phi >> (b*9+c)) & 1:
                        off_diag_phis += 1
                        break
    print(f"Phi vectors with off-diagonal entries: {off_diag_phis}/72")

    # For which (b,c) positions does the tensor_mask exist?
    print("\nTensor mask positions by block structure:")
    for b in range(9):
        for c in range(9):
            mask = tensor_masks.get((b, c), 0)
            if mask:
                block_type = "diag" if b % 3 == c % 3 else "off"
                print(f"  ({b},{c}) b_block=({b//3},{b%3}) c_block=({c//3},{c%3}) mask={mask:08b} [{block_type}]")

    # For F(p) to be in V_trace, we need F(p)[b,c] = 0 for all off-diagonal (b,c)
    # i.e., popcount(p AND tensor_mask(b,c)) must be even for all off-diag (b,c)
    print("\n=== Direction-by-direction check for V_trace membership ===")
    off_diag_masks = {}
    for b in range(9):
        for c in range(9):
            if b % 3 != c % 3:
                mask = tensor_masks.get((b, c), 0)
                if mask:
                    off_diag_masks[(b, c)] = mask

    print(f"Off-diagonal positions with nonzero tensor mask: {len(off_diag_masks)}")
    for (b, c), mask in sorted(off_diag_masks.items()):
        print(f"  ({b},{c}): mask = {mask} = {bin(mask)}")

    # A direction p escapes iff popcount(p AND mask) is odd for SOME off-diagonal mask
    # The escape condition is: p has odd inner product with some off-diagonal tensor_mask
    escape_check = []
    for p in range(1, 256):
        escapes = False
        for (b, c), mask in off_diag_masks.items():
            if popcount(p & mask) & 1:
                escapes = True
                break
        if escapes:
            escape_check.append(p)
    
    print(f"\nDirections with F(p) outside V_trace: {len(escape_check)}")
    print(f"These should match ESCAPE_FULL: {sorted(escape_check) == sorted(ESCAPE_FULL)}")

    # Now: family parity analysis for the CERT guard
    # Under cert guard, 111 forced directions with forced values
    # Any 19-point support from these 111 with forced parity sum != 1 is contradicted
    
    # Load the previous analysis to get forced values
    prev = json.load(open(OUTDIR / "family_consequence_analysis.json"))
    # Reconstruct forced values for cert guard
    cert_trace_qs = prev["certificate_contractions"]
    
    # Recompute forced values
    forced_cert = {}
    for p in range(1, 256):
        F_p = 0
        for b in range(nb):
            for c in range(nc):
                mask = tensor_masks.get((b, c), 0)
                if popcount(p & mask) & 1:
                    F_p |= 1 << (b * nc + c)
        
        if F_p == 0:
            forced_cert[p] = 0
            continue
        
        cert_phis = [phi_vectors[q] for q in cert_trace_qs if popcount(q & p) & 1]
        if gf2_in_span(F_p, cert_phis):
            # Find the decomposition
            basis_track = []
            for i, phi in enumerate(cert_phis):
                mask_i = 1 << i
                v = phi
                m = mask_i
                skip = False
                for bv, bm in basis_track:
                    v2 = v ^ bv
                    if v2 < v:
                        v = v2
                        m ^= bm
                if v:
                    basis_track.append((v, m))
            
            # Reduce F_p
            v = F_p
            m = 0
            for bv, bm in basis_track:
                v2 = v ^ bv
                if v2 < v:
                    v = v2
                    m ^= bm
            
            if v == 0:
                forced_cert[p] = popcount(m) % 2
    
    forced_0 = [p for p in forced_cert if forced_cert[p] == 0]
    forced_1 = [p for p in forced_cert if forced_cert[p] == 1]
    print(f"\nCert guard: {len(forced_0)} forced-0, {len(forced_1)} forced-1")
    print(f"Need 19-point support with odd count of forced-1 for parity to equal 1")
    print(f"Near-miss forced-1 count: {sum(1 for p in NEAR_MISS if forced_cert.get(p) == 1)}")

    # Check: among the 12-violation directions that PASS Wang, how many are forced?
    # analysis best support violates 12 Wang rows. Let's check parity for other near-misses.
    
    # The key structural result: the 4 V_trace-perpendicular directions
    # Let me verify their E11-core matrix structure
    print("\n=== E11-core matrix interpretation of escape directions ===")
    for p in ESCAPE_FULL:
        # In E11-deleted coordinates: bit i corresponds to position (i//3+delta, i%3)
        # where delta accounts for deleting row 0, col 0 (E11)
        # Actually the core uses bits 0-7 for the 8 positions:
        # Full 3x3 matrix has entries indexed as:
        # (0,0)=E11, (0,1)=E12, (0,2)=E13
        # (1,0)=E21, (1,1)=E22, (1,2)=E23
        # (2,0)=E31, (2,1)=E32, (2,2)=E33
        # Core removes E11, so bits 0-7 map to:
        # bit 0 = E12, bit 1 = E13, bit 2 = E21, bit 3 = E22,
        # bit 4 = E23, bit 5 = E31, bit 6 = E32, bit 7 = E33
        desc = describe_direction(p)
        # Express as 3x3 matrix (with E11=0)
        mat = np.zeros((3, 3), dtype=int)
        mapping = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
        for bit_idx in range(8):
            if (p >> bit_idx) & 1:
                r, c_idx = mapping[bit_idx]
                mat[r, c_idx] = 1
        print(f"p={p} ({desc}): rank={np.linalg.matrix_rank(mat)}")
        print(f"  {mat.tolist()}")

    elapsed = time.time() - t0
    result = {
        "schema": "vtrace_perp_analysis_v1",
        "elapsed_sec": round(elapsed, 3),
        "vtrace_dim": vtrace_dim,
        "escape_full_72": ESCAPE_FULL,
        "escape_descriptions": [describe_direction(p) for p in ESCAPE_FULL],
        "escape_details": escape_details,
        "off_diagonal_tensor_masks": {f"({b},{c})": mask for (b,c), mask in off_diag_masks.items()},
        "cert_forced_0_count": len(forced_0),
        "cert_forced_1_count": len(forced_1),
    }
    
    out = OUTDIR / "vtrace_perp_analysis.json"
    with open(out, 'w') as f:
        json.dump(result, f, indent=2, default=str)
    print(f"\nSaved {out}")

if __name__ == '__main__':
    main()
