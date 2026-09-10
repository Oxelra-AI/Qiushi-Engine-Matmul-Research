#!/usr/bin/env python3
r"""analysis: parity well-definedness check.

Key concern: F(p) = sum alpha_q phi_q may have multiple decompositions over GF(2).
If sum alpha_q and sum beta_q differ (mod 2) for different valid decompositions,
the "forced value" is ambiguous.

The forced value is well-defined iff the "all-ones vector" (sum of all participating
phi_q generators) is NOT zero; specifically, the parity is NOT determined when
there exists a non-empty subset S of hitting phi_q's with sum=0 and |S| odd.
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

def compute_phi_q(M_inv):
    result = 0
    for b in range(9):
        for c in range(9):
            if int(M_inv[c,b]) & 1: result |= 1<<(b*9+c)
    return result


def gf2_rref_basis(vecs):
    basis = []
    for v in vecs:
        for b in basis: v = min(v, v^b)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    return basis


def check_parity_ambiguity(generators):
    """Check if there exists a non-empty subset of generators that XORs to 0
    with odd cardinality. If so, parity is ambiguous."""
    # The all-ones vector [1,1,...,1] applied to the null space of the generator matrix
    # Check: is the all-ones indicator in the null space of the augmented system?
    # Equivalently: does sum of all generators = 0?
    # More precisely: find the null space and check its minimum weight parity
    
    # Build augmented vectors: (gen, indicator_bit)
    n = len(generators)
    # Use Gaussian elimination to find the null space
    # Each row is (generator_value, indicator_mask)
    rows = [(g, 1 << i) for i, g in enumerate(generators)]
    
    # Gaussian elimination
    pivot_rows = []
    for g, m in rows:
        for pg, pm in pivot_rows:
            g2 = g ^ pg
            if g2 < g:
                g, m = g2, m ^ pm
        if g:
            pivot_rows.append((g, m))
            pivot_rows.sort(key=lambda x: x[0], reverse=True)
        else:
            # g = 0: the combination m gives sum = 0
            # Check if |m| is odd
            if m and popcount(m) & 1:
                return True, popcount(m), m  # Ambiguous! Odd-size null combination
    
    return False, 0, 0  # No ambiguity


def main():
    t0 = time.time()
    T_core = build_e11_core_tensor()
    na = T_core.shape[0]

    # Build phi vectors
    rank9_qs = []
    phi_vectors = {}
    for q in range(1, 1<<na):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) != 9: continue
        rank9_qs.append(q)
        M_inv = gf2_mat_inv(M)
        phi_vectors[q] = compute_phi_q(M_inv)

    # Load cert contractions
    with open(CERT_PATH) as f:
        cert = json.load(f)
    cert_labels = cert["full_greedy_row_shrink"]["labels"]
    cert_qs = set()
    for lbl in cert_labels:
        if lbl[0] == "trace":
            cert_qs.add(int(lbl[1]))

    print("=== Parity well-definedness: cert-only guard (10 contractions) ===")
    cert_ambig = 0
    cert_defined = 0
    for p in range(1, 256):
        gens = [phi_vectors[q] for q in cert_qs if popcount(q & p) & 1]
        if not gens:
            cert_defined += 1  # F(p)=0 forced to 0
            continue
        ambig, size, _ = check_parity_ambiguity(gens)
        if ambig:
            cert_ambig += 1
        else:
            cert_defined += 1
    print(f"Parity well-defined: {cert_defined}/255")
    print(f"Parity ambiguous: {cert_ambig}/255")

    print("\n=== Parity well-definedness: full 72 guard ===")
    full_ambig = 0
    full_defined = 0
    full_ambig_dirs = []
    for p in range(1, 256):
        gens = [phi_vectors[q] for q in rank9_qs if popcount(q & p) & 1]
        if not gens:
            full_defined += 1
            continue
        ambig, size, _ = check_parity_ambiguity(gens)
        if ambig:
            full_ambig += 1
            full_ambig_dirs.append(p)
        else:
            full_defined += 1
    print(f"Parity well-defined: {full_defined}/255")
    print(f"Parity ambiguous: {full_ambig}/255")
    if full_ambig_dirs:
        print(f"Ambiguous directions: {full_ambig_dirs[:20]}")

    # For near-miss: check cert-only parity
    print("\n=== Near-miss cert-only parity ===")
    # The cert forced values are well-defined because the cert specifies exact trace rows
    # The forced value for term s = |cert_trace_by_term[s]| mod 2
    cert_trace_by_term = {}
    for lbl in cert_labels:
        if lbl[0] == "trace":
            q, s = int(lbl[1]), int(lbl[2])
            cert_trace_by_term.setdefault(s, []).append(q)
    
    forced_values = []
    for s in range(len(NEAR_MISS)):
        fv = len(cert_trace_by_term.get(s, [])) % 2
        forced_values.append(fv)
    print(f"Cert trace rows per term: {[len(cert_trace_by_term.get(s, [])) for s in range(19)]}")
    print(f"Forced values: {forced_values}")
    print(f"Sum = {sum(forced_values)}, parity = {sum(forced_values) % 2}")

    tensor_rhs = 0
    for lbl in cert_labels:
        if lbl[0] == "tensor":
            i,b,c = int(lbl[1]),int(lbl[2]),int(lbl[3])
            tensor_rhs ^= int(T_core[i,b,c]) & 1
    print(f"Tensor RHS = {tensor_rhs}")
    print(f"Contradiction: {sum(forced_values) % 2 != tensor_rhs}")

    # The CORRECT statement about the family consequence:
    # Under the cert-only guard, for directions where parity IS well-defined,
    # the forced value is determined. For others, it's ambiguous.
    # The near-miss uses ONLY cert-only forced directions (since it's the source).
    # Its contradiction is genuine because the cert specifies exact decompositions.
    
    elapsed = time.time() - t0
    result = {
        "schema": "parity_welldef_v1",
        "elapsed_sec": round(elapsed, 3),
        "cert_parity_defined": cert_defined,
        "cert_parity_ambiguous": cert_ambig,
        "full72_parity_defined": full_defined,
        "full72_parity_ambiguous": full_ambig,
        "full72_ambiguous_dirs": full_ambig_dirs[:50],
        "near_miss_forced_values": forced_values,
        "near_miss_parity_sum": sum(forced_values) % 2,
        "tensor_rhs": tensor_rhs,
        "near_miss_contradiction": sum(forced_values) % 2 != tensor_rhs,
    }
    out = OUTDIR / "parity_welldef.json"
    with open(out, 'w') as f:
        json.dump(result, f, indent=2)
    print(f"\nSaved {out}")

if __name__ == '__main__':
    main()
