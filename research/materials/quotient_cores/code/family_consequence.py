#!/usr/bin/env python3
r"""analysis: support-family parity consequence from corrected trace certificate.

The analysis certificate is an XOR of 90 tensor rows + 32 trace rows that gives
0 = 1 for the near-miss support.  This script extracts a FAMILY-level consequence:

For each possible A-direction p in F_2^8\{0}:
  1) Compute F(p) in F_2^81: the tensor-functional vector from certificate tensor rows
  2) Compute available trace functionals phi_q for cert contractions q with q(p)=1
  3) Check if F(p) is in span(phi_q's)
  4) If yes, determine the forced value v(p) = sum of decomposition coefficients

Under the saturation guard (cert contractions are saturated), any distinct 19-point
support using only "forced" directions must satisfy:
   sum_{p in S} v(p) = T_rhs_parity (mod 2)

A direction p where F(p) is NOT in the trace span is an "escape direction" whose
contribution depends on the specific B/C factors.

We also compare with the full 72 rank-9 contraction set for maximal span analysis.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (  # noqa: E402
    build_matmul_tensor_f2,
    contraction_matrix,
    mat_rank_f2,
)
from dual_basis_instrument import gf2_mat_inv  # noqa: E402

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/family_consequence"
CERT_PATH = ROOT / "workspace/data/corrected_independent-verification-record"
NEAR_MISS = [1, 2, 3, 4, 8, 20, 24, 31, 32, 64, 73, 109, 127, 128, 141, 160, 182, 192, 219]


def build_e11_core_tensor() -> np.ndarray:
    return build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2


def popcount(x: int) -> int:
    return bin(x).count('1')


def gf2_rank(vecs: List[int], nbits: int) -> int:
    """Rank of a list of GF(2) vectors (each an int bitmask)."""
    basis = []
    for v in vecs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


def gf2_in_span(target: int, generators: List[int]) -> Tuple[bool, Optional[int]]:
    """Check if target is in span of generators over GF(2).
    Returns (in_span, decomposition_mask) where decomposition_mask has bit i set
    if generator[i] is used."""
    n = len(generators)
    # Augmented system: track which generators are used
    # Use Gaussian elimination with tracking
    basis = []  # (reduced_vec, gen_mask)
    for i, g in enumerate(generators):
        mask = 1 << i
        v = g
        m = mask
        for bv, bm in basis:
            v2 = v ^ bv
            if v2 < v:
                v = v2
                m ^= bm
        if v:
            basis.append((v, m))
    
    # Now reduce target
    v = target
    m = 0
    for bv, bm in basis:
        v2 = v ^ bv
        if v2 < v:
            v = v2
            m ^= bm
    
    if v == 0:
        return True, m
    return False, None


def compute_phi_q(M_inv: np.ndarray) -> int:
    """Compute phi_q as an 81-bit vector: phi_q[b*9+c] = M_inv[c,b]."""
    result = 0
    for b in range(9):
        for c in range(9):
            if int(M_inv[c, b]) & 1:
                result |= 1 << (b * 9 + c)
    return result


def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    
    # Load certificate
    with open(CERT_PATH) as f:
        cert_data = json.load(f)
    
    # Extract certificate labels from the greedy shrink section
    labels = cert_data["full_greedy_row_shrink"]["labels"]
    
    # Build tensor_mask(b,c): for each (b,c), which i-coordinates are in certificate
    tensor_masks: Dict[Tuple[int,int], int] = {}
    cert_tensor_count = 0
    cert_trace_labels = []
    for lbl in labels:
        if lbl[0] == "tensor":
            i, b, c = int(lbl[1]), int(lbl[2]), int(lbl[3])
            key = (b, c)
            tensor_masks[key] = tensor_masks.get(key, 0) ^ (1 << i)
            cert_tensor_count += 1
        elif lbl[0] == "trace":
            cert_trace_labels.append((int(lbl[1]), int(lbl[2])))
    
    # Identify certificate trace contractions and per-term trace sets
    cert_trace_qs = sorted(set(q for q, s in cert_trace_labels))
    cert_trace_by_term = defaultdict(list)
    for q, s in cert_trace_labels:
        cert_trace_by_term[s].append(q)
    
    print(f"Certificate: {cert_tensor_count} tensor rows, {len(cert_trace_labels)} trace rows")
    print(f"Certificate contractions: {cert_trace_qs}")
    print(f"Tensor masks cover {len(tensor_masks)} (b,c) positions")
    
    # Compute RHS parity from tensor rows
    T_core = build_e11_core_tensor()
    na, nb, nc = T_core.shape
    assert na == 8 and nb == 9 and nc == 9
    
    tensor_rhs_parity = 0
    for lbl in labels:
        if lbl[0] == "tensor":
            i, b, c = int(lbl[1]), int(lbl[2]), int(lbl[3])
            tensor_rhs_parity ^= int(T_core[i, b, c]) & 1
    trace_rhs_parity = len(cert_trace_labels) % 2  # each trace row has RHS = 1
    total_rhs = tensor_rhs_parity ^ trace_rhs_parity
    print(f"Tensor RHS parity: {tensor_rhs_parity}, Trace RHS parity: {trace_rhs_parity}")
    print(f"Total RHS parity: {total_rhs} (must be 1 for valid certificate)")
    assert total_rhs == 1, "Certificate RHS parity must be 1"
    
    # Compute F(p) for each direction p in {1,...,255}
    def compute_F(p: int) -> int:
        """81-bit vector: F(p)[b*9+c] = popcount(p AND tensor_mask(b,c)) mod 2."""
        result = 0
        for b in range(nb):
            for c in range(nc):
                mask = tensor_masks.get((b, c), 0)
                if popcount(p & mask) & 1:
                    result |= 1 << (b * nc + c)
        return result
    
    # Compute phi_q for all 72 rank-9 contractions
    rank9_qs = []
    phi_vectors: Dict[int, int] = {}  # q -> 81-bit phi_q
    for q in range(1, 1 << na):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) != 9:
            continue
        rank9_qs.append(q)
        M_inv = gf2_mat_inv(M)
        assert M_inv is not None
        phi_vectors[q] = compute_phi_q(M_inv)
    
    print(f"\nRank-9 contractions: {len(rank9_qs)}")
    
    # Compute full trace span
    all_phi = [phi_vectors[q] for q in rank9_qs]
    full_trace_rank = gf2_rank(all_phi, 81)
    print(f"Full trace functional span: dimension {full_trace_rank} in F_2^81")
    
    # Verify near-miss certificate: for each near-miss direction, F(p_s) should equal
    # sum of phi_q for the cert trace rows of that term
    print("\n--- Near-miss verification ---")
    nm_forced_values = []
    for s, p in enumerate(NEAR_MISS):
        F_p = compute_F(p)
        trace_sum = 0
        for q in cert_trace_by_term.get(s, []):
            trace_sum ^= phi_vectors[q]
        match = (F_p == trace_sum)
        n_trace = len(cert_trace_by_term.get(s, []))
        forced_val = n_trace % 2
        nm_forced_values.append(forced_val)
        if not match:
            print(f"  MISMATCH: term {s}, direction {p}, F(p)!=sum_phi")
    
    parity_sum = sum(nm_forced_values) % 2
    print(f"Near-miss forced values parity: {parity_sum} vs tensor_rhs_parity={tensor_rhs_parity}")
    # The CONTRADICTION is exactly that parity_sum != tensor_rhs_parity
    # Tensor equations require sum F(p_s)^T X_s = 1
    # Trace equations force each F(p_s)^T X_s = |Q_cert_s| mod 2
    # But sum of forced values = 0 ≠ 1: this is the certificate's 0=1 contradiction
    is_contradiction = (parity_sum != tensor_rhs_parity)
    print(f"  Parity contradiction: {is_contradiction} (expected True for valid cert)")
    assert is_contradiction, "Certificate parity should contradict for near-miss"
    print("  Near-miss certificate structure verified ✓")
    
    # --- Family consequence analysis ---
    print("\n--- Family consequence: cert contractions guard ---")
    cert_q_set = set(cert_trace_qs)
    
    forced_directions = {}   # p -> forced_value
    escape_directions = []   # p values
    forced_in_full = {}      # p -> forced_value using ALL 72 rank-9 contractions
    escape_from_full = []
    
    for p in range(1, 256):
        F_p = compute_F(p)
        
        if F_p == 0:
            # Zero tensor functional: forced to 0 regardless
            forced_directions[p] = 0
            forced_in_full[p] = 0
            continue
        
        # Available cert trace functionals for direction p
        cert_phis_for_p = [phi_vectors[q] for q in cert_trace_qs if popcount(q & p) & 1]
        in_cert_span, decomp = gf2_in_span(F_p, cert_phis_for_p)
        
        if in_cert_span:
            # Forced value = number of generators used mod 2
            forced_val = popcount(decomp) % 2
            forced_directions[p] = forced_val
        else:
            escape_directions.append(p)
        
        # Also check with ALL 72 rank-9 contractions
        all_phis_for_p = [phi_vectors[q] for q in rank9_qs if popcount(q & p) & 1]
        in_full_span, full_decomp = gf2_in_span(F_p, all_phis_for_p)
        
        if in_full_span:
            forced_val_full = popcount(full_decomp) % 2
            forced_in_full[p] = forced_val_full
        else:
            escape_from_full.append(p)
    
    print(f"Forced directions (cert guard): {len(forced_directions)} / 255")
    print(f"Escape directions (cert guard): {len(escape_directions)} / 255")
    print(f"Forced directions (full 72 guard): {len(forced_in_full)} / 255")
    print(f"Escape directions (full 72 guard): {len(escape_from_full)} / 255")
    
    # Check near-miss directions
    nm_in_forced = sum(1 for p in NEAR_MISS if p in forced_directions)
    nm_in_escape = sum(1 for p in NEAR_MISS if p in escape_directions)
    print(f"\nNear-miss: {nm_in_forced} forced, {nm_in_escape} escape (cert guard)")
    
    # Check forced value distribution
    forced_val_counts = Counter(forced_directions.values())
    print(f"Forced value distribution (cert guard): {dict(forced_val_counts)}")
    
    # Parity analysis
    # Under cert saturation guard, any support using only forced directions must satisfy:
    # sum v(p_i) = T_rhs_parity = 1 (mod 2)
    # Since support has 19 points: we need odd number of v=1 forced directions
    n_forced_1 = forced_val_counts.get(1, 0)
    n_forced_0 = forced_val_counts.get(0, 0)
    print(f"\nParity analysis: {n_forced_1} forced-1 directions, {n_forced_0} forced-0 directions")
    print(f"A 19-point support from forced-only directions needs odd count of forced-1 directions")
    
    # Detailed analysis of escape directions
    escape_analysis = []
    for p in escape_directions:
        F_p = compute_F(p)
        F_weight = popcount(F_p)
        cert_hits = sum(1 for q in cert_trace_qs if popcount(q & p) & 1)
        all_hits = sum(1 for q in rank9_qs if popcount(q & p) & 1)
        # Check if F(p) is in the full trace span
        in_full = p in forced_in_full
        escape_analysis.append({
            "p": p,
            "F_weight": F_weight,
            "cert_hits": cert_hits,
            "all_rk9_hits": all_hits,
            "in_full_trace_span": in_full,
        })
    
    # How many escapes resolve with full 72?
    resolved_by_full = sum(1 for e in escape_analysis if e["in_full_trace_span"])
    still_escape = sum(1 for e in escape_analysis if not e["in_full_trace_span"])
    print(f"\nEscape directions resolved by full 72 contractions: {resolved_by_full}")
    print(f"Escape directions remaining even with full 72: {still_escape}")
    
    if still_escape > 0:
        # These are directions where F(p) is genuinely outside V_trace
        perp_escapes = [e for e in escape_analysis if not e["in_full_trace_span"]]
        print(f"\nPerpendicular escape directions (F(p) outside V_trace):")
        for e in perp_escapes[:20]:
            print(f"  p={e['p']}: F_weight={e['F_weight']}, all_rk9_hits={e['all_rk9_hits']}")
    
    # Full 72 guard analysis
    full_val_counts = Counter(forced_in_full.values())
    print(f"\nFull 72 forced value distribution: {dict(full_val_counts)}")
    n_full_1 = full_val_counts.get(1, 0)
    n_full_0 = full_val_counts.get(0, 0)
    print(f"Full 72: {n_full_1} forced-1, {n_full_0} forced-0, {len(escape_from_full)} escape")
    
    # Check: for near-miss support, are the cert-guard forced values consistent?
    nm_cert_forced = []
    for p in NEAR_MISS:
        if p in forced_directions:
            nm_cert_forced.append(forced_directions[p])
        else:
            nm_cert_forced.append("escape")
    print(f"\nNear-miss cert-forced values: {nm_cert_forced}")
    
    # Also check full-72 forced values for near-miss
    nm_full_forced = []
    for p in NEAR_MISS:
        if p in forced_in_full:
            nm_full_forced.append(forced_in_full[p])
        else:
            nm_full_forced.append("escape")
    print(f"Near-miss full-72 forced values: {nm_full_forced}")
    
    # Verify: for the near-miss, all directions should be cert-forced (since the certificate works)
    all_nm_forced = all(p in forced_directions for p in NEAR_MISS)
    if all_nm_forced:
        nm_parity = sum(forced_directions[p] for p in NEAR_MISS) % 2
        print(f"All near-miss directions cert-forced: parity sum = {nm_parity} vs required {tensor_rhs_parity}")
        print(f"  Contradiction: {nm_parity != tensor_rhs_parity} (parity_sum ≠ tensor_rhs iff cert works)")
    
    # Compute the forced-direction parity class
    # For any 19-point support from forced-only directions:
    # sum v(p) = 1 (mod 2) is REQUIRED
    # But this is NOT a contradiction - it's just a parity constraint
    
    # The REAL question: what fraction of potential 19-point supports are
    # restricted by this parity + the escape analysis?
    
    elapsed = time.time() - t0
    
    result = {
        "schema": "family_consequence_v1",
        "elapsed_sec": round(elapsed, 3),
        "certificate_tensor_rows": cert_tensor_count,
        "certificate_trace_rows": len(cert_trace_labels),
        "certificate_contractions": cert_trace_qs,
        "tensor_rhs_parity": tensor_rhs_parity,
        "trace_rhs_parity": trace_rhs_parity,
        "total_rhs_parity": total_rhs,
        "full_trace_span_dim": full_trace_rank,
        "cert_guard": {
            "forced_count": len(forced_directions),
            "escape_count": len(escape_directions),
            "forced_val_distribution": dict(forced_val_counts),
            "escape_directions": escape_directions[:50],
            "escape_directions_count": len(escape_directions),
        },
        "full_72_guard": {
            "forced_count": len(forced_in_full),
            "escape_count": len(escape_from_full),
            "forced_val_distribution": dict(full_val_counts),
            "escape_directions": escape_from_full[:50],
            "escape_directions_count": len(escape_from_full),
            "resolved_from_cert_escape": resolved_by_full,
        },
        "near_miss_cert_forced_values": nm_cert_forced,
        "near_miss_full_forced_values": nm_full_forced,
        "near_miss_all_forced": all_nm_forced,
        "near_miss_support": NEAR_MISS,
        "escape_sample": escape_analysis[:30],
    }
    
    out = OUTDIR / "family_consequence_analysis.json"
    with open(out, 'w') as f:
        json.dump(result, f, indent=2, default=str)
    print(f"\nSaved {out}")
    print(f"Elapsed: {elapsed:.3f}s")


if __name__ == '__main__':
    main()
