#!/usr/bin/env python3
r"""analysis: 9D trace basis analysis and multi-certificate family coverage.

Key finding from vtrace_perp: all F(p) are in V_trace (9D), but 4 directions
{5,7,33,35} escape under full-72 guard because their hitting rank-9 contractions
span < 9D of V_trace.

This script:
1) Computes hitting-contraction span rank for all 255 directions
2) Expresses everything in a 9D V_trace basis for compact analysis
3) Generates certificates for multiple stored trace-inconsistent near-misses
4) Checks complementarity of parity restrictions
5) Determines whether multiple certificates can exclude more supports
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    build_matmul_tensor_f2,
    contraction_matrix,
    gf2_linear_consistency,
    mat_rank_f2,
)
from dual_basis_instrument import gf2_mat_inv

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/family_consequence"
CERT_PATH = ROOT / "workspace/data/corrected_independent-verification-record"
NEAR_MISS = [1, 2, 3, 4, 8, 20, 24, 31, 32, 64, 73, 109, 127, 128, 141, 160, 182, 192, 219]


def build_e11_core_tensor():
    return build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2


def popcount(x):
    return bin(x).count('1')


def gf2_rref_basis(vecs):
    basis = []
    for v in vecs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    return basis


def gf2_rank(vecs):
    return len(gf2_rref_basis(vecs))


def gf2_in_span_with_decomp(target, generators):
    n = len(generators)
    basis = []
    for i, g in enumerate(generators):
        mask = 1 << i
        v, m = g, mask
        for bv, bm in basis:
            v2 = v ^ bv
            if v2 < v:
                v, m = v2, m ^ bm
        if v:
            basis.append((v, m))
    v, m = target, 0
    for bv, bm in basis:
        v2 = v ^ bv
        if v2 < v:
            v, m = v2, m ^ bm
    return (v == 0, m if v == 0 else None)


def compute_phi_q(M_inv):
    result = 0
    for b in range(9):
        for c in range(9):
            if int(M_inv[c, b]) & 1:
                result |= 1 << (b * 9 + c)
    return result


def build_trace_system(T_core, A_support, q_subset=None):
    """Build labeled rows for tensor + trace system."""
    na, nb, nc = T_core.shape
    nterms = len(A_support)
    nvars = nterms * nb * nc

    def var_idx(s, b, c):
        return s * nb * nc + b * nc + c

    rows, labels = [], []
    for i in range(na):
        for b in range(nb):
            for c in range(nc):
                row = 0
                for s, a in enumerate(A_support):
                    if (int(a) >> i) & 1:
                        row ^= 1 << var_idx(s, b, c)
                row |= (int(T_core[i, b, c]) & 1) << nvars
                rows.append(row)
                labels.append(("tensor", i, b, c))

    saturated_qs = []
    for q in range(1, 1 << na):
        if q_subset is not None and q not in q_subset:
            continue
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) != 9:
            continue
        I = [s for s, a in enumerate(A_support) if popcount(int(a) & q) & 1]
        if len(I) != 9:
            continue
        saturated_qs.append(q)
        M_inv = gf2_mat_inv(M)
        if M_inv is None:
            continue
        for s in I:
            row = 0
            for b in range(nb):
                for c in range(nc):
                    if int(M_inv[c, b]) & 1:
                        row ^= 1 << var_idx(s, b, c)
            row |= 1 << nvars
            rows.append(row)
            labels.append(("trace", q, s))

    return rows, labels, nvars, saturated_qs


def extract_parity_info(labels, cert_bitmask, A_support, T_core, phi_vectors, cert_sat_qs):
    """From a certificate, extract per-direction forced values and escape info."""
    na = T_core.shape[0]
    nb, nc = T_core.shape[1], T_core.shape[2]

    # Build tensor_mask(b,c) from certificate tensor rows
    tensor_masks = {}
    cert_trace_by_term = defaultdict(list)
    tensor_rhs = 0
    trace_count = 0

    used_labels = [labels[i] for i in range(len(labels)) if (cert_bitmask >> i) & 1]
    for lbl in used_labels:
        if lbl[0] == "tensor":
            i, b, c = int(lbl[1]), int(lbl[2]), int(lbl[3])
            tensor_masks[(b, c)] = tensor_masks.get((b, c), 0) ^ (1 << i)
            tensor_rhs ^= int(T_core[i, b, c]) & 1
        elif lbl[0] == "trace":
            q, s = int(lbl[1]), int(lbl[2])
            cert_trace_by_term[s].append(q)
            trace_count += 1

    total_rhs = tensor_rhs ^ (trace_count % 2)

    def compute_F(p):
        result = 0
        for b in range(nb):
            for c in range(nc):
                mask = tensor_masks.get((b, c), 0)
                if popcount(p & mask) & 1:
                    result |= 1 << (b * nc + c)
        return result

    cert_q_set = set()
    for s, qs in cert_trace_by_term.items():
        cert_q_set.update(qs)

    forced = {}
    escapes = []
    for p in range(1, 256):
        F_p = compute_F(p)
        if F_p == 0:
            forced[p] = 0
            continue
        cert_phis = [phi_vectors[q] for q in cert_q_set if popcount(q & p) & 1]
        ok, decomp = gf2_in_span_with_decomp(F_p, cert_phis)
        if ok:
            forced[p] = popcount(decomp) % 2
        else:
            escapes.append(p)

    return forced, escapes, total_rhs, tensor_rhs, trace_count, list(cert_q_set)


def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)

    T_core = build_e11_core_tensor()
    na, nb, nc = T_core.shape

    # Build rank-9 contractions and phi vectors
    rank9_qs = []
    phi_vectors = {}
    for q in range(1, 1 << na):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) != 9:
            continue
        rank9_qs.append(q)
        M_inv = gf2_mat_inv(M)
        phi_vectors[q] = compute_phi_q(M_inv)

    # Compute hitting-contraction span rank for each direction
    print("=== Hitting-contraction span ranks (full 72) ===")
    span_rank_hist = Counter()
    rank_deficient_dirs = []
    for p in range(1, 256):
        hitting = [phi_vectors[q] for q in rank9_qs if popcount(q & p) & 1]
        rk = gf2_rank(hitting)
        span_rank_hist[rk] += 1
        if rk < 9:
            rank_deficient_dirs.append((p, rk))
    print(f"Span rank distribution: {dict(sorted(span_rank_hist.items()))}")
    print(f"Rank-deficient directions: {len(rank_deficient_dirs)}")
    for p, rk in rank_deficient_dirs:
        print(f"  p={p}: hitting phi span = {rk}")

    # Load stored near-misses from analysis completion batch
    batch_path = ROOT / "workspace/data/completion/distinct_candidate_completion_repaired.json"
    with open(batch_path) as f:
        batch_data = json.load(f)

    # Also load the corrected trace batch results from analysis
    trace_batch_path = ROOT / "workspace/data/corrected_independent-verification-record"
    with open(trace_batch_path) as f:
        trace_batch = json.load(f)

    # Identify trace-inconsistent near-misses
    trace_inconsistent = []
    trace_consistent = []
    for rec in trace_batch.get("existing_candidate_batch_records", []):
        support = rec.get("support", [])
        is_consistent = rec.get("compressed_trace_consistent", True)
        wang_viol = rec.get("complete_wang_violations", 999)
        if support and not is_consistent:
            trace_inconsistent.append((support, wang_viol))
        elif support and is_consistent:
            trace_consistent.append((support, wang_viol))

    print(f"\n=== Multi-certificate generation ===")
    print(f"Trace-inconsistent near-misses: {len(trace_inconsistent)}")
    print(f"Trace-consistent near-misses: {len(trace_consistent)}")

    # Generate certificates for up to 5 trace-inconsistent supports
    # (including the primary near-miss)
    certificates = []

    supports_to_cert = [NEAR_MISS]
    for sup, wv in trace_inconsistent[:6]:
        if sup != NEAR_MISS:
            supports_to_cert.append(sup)
    supports_to_cert = supports_to_cert[:5]

    for idx, support in enumerate(supports_to_cert):
        rows, labels, nvars, sat_qs = build_trace_system(T_core, support)
        consistent, rank, cert = gf2_linear_consistency(rows, nvars)
        if not consistent and cert is not None:
            forced, escapes, total_rhs, t_rhs, tr_cnt, cert_qs = \
                extract_parity_info(labels, cert, support, T_core, phi_vectors, sat_qs)

            # Check near-miss parity
            nm_in_forced = all(p in forced for p in support)
            if nm_in_forced:
                parity = sum(forced[p] for p in support) % 2
                is_contradiction = (parity != t_rhs)
            else:
                parity = "escape"
                is_contradiction = False

            cert_info = {
                "index": idx,
                "support_head": support[:5],
                "wang_violations": "?" if idx == 0 else trace_inconsistent[idx-1][1] if idx-1 < len(trace_inconsistent) else "?",
                "sat_rank9_count": len(sat_qs),
                "cert_contractions": cert_qs[:15],
                "cert_contraction_count": len(cert_qs),
                "total_rhs": total_rhs,
                "tensor_rhs": t_rhs,
                "forced_count": len(forced),
                "escape_count": len(escapes),
                "self_contradiction": is_contradiction,
                "self_parity": parity,
            }
            certificates.append(cert_info)
            print(f"\nCert {idx}: support={support[:5]}... sat_rk9={len(sat_qs)}")
            print(f"  cert_qs={len(cert_qs)} contractions, forced={len(forced)}, escape={len(escapes)}")
            print(f"  self-parity={parity}, tensor_rhs={t_rhs}, contradiction={is_contradiction}")
        else:
            print(f"\nCert {idx}: support={support[:5]}... trace-consistent (no certificate)")
            certificates.append({"index": idx, "trace_consistent": True})

    # Cross-certificate analysis: check how certificates interact
    print("\n=== Cross-certificate parity analysis ===")
    # For the primary certificate (near-miss), check other supports
    if len(certificates) >= 2:
        primary = certificates[0]
        if primary.get("forced_count"):
            # Re-extract primary forced values
            rows0, labels0, nvars0, sat0 = build_trace_system(T_core, NEAR_MISS)
            c0, _, cert0 = gf2_linear_consistency(rows0, nvars0)
            forced0, _, total_rhs0, t_rhs0, _, _ = \
                extract_parity_info(labels0, cert0, NEAR_MISS, T_core, phi_vectors, sat0)

            for idx, support in enumerate(supports_to_cert[1:], 1):
                # Check if this support satisfies the primary certificate's guard
                all_forced = all(p in forced0 for p in support)
                if all_forced:
                    parity = sum(forced0[p] for p in support) % 2
                    cross_contradiction = (parity != t_rhs0)
                    print(f"  Support {idx} under primary cert: parity={parity}, contradiction={cross_contradiction}")
                else:
                    escape_dirs = [p for p in support if p not in forced0]
                    print(f"  Support {idx} under primary cert: {len(escape_dirs)} escape dirs")

    # Summarize the forced-value vectors
    # For each certificate, record the forced-value function on {1,...,255}
    print("\n=== Certificate forced-value patterns ===")
    for ci in certificates:
        if ci.get("forced_count"):
            print(f"Cert {ci['index']}: {ci['forced_count']} forced, {ci['escape_count']} escape")

    elapsed = time.time() - t0
    result = {
        "schema": "multi_cert_analysis_v1",
        "elapsed_sec": round(elapsed, 3),
        "rank_deficient_directions": [{"p": p, "span_rank": rk} for p, rk in rank_deficient_dirs],
        "span_rank_histogram": dict(sorted(span_rank_hist.items())),
        "certificates": certificates,
        "trace_inconsistent_count": len(trace_inconsistent),
        "trace_consistent_count": len(trace_consistent),
    }
    out = OUTDIR / "multi_cert_analysis.json"
    with open(out, 'w') as f:
        json.dump(result, f, indent=2, default=str)
    print(f"\nSaved {out}")
    print(f"Elapsed: {elapsed:.1f}s")


if __name__ == '__main__':
    main()
