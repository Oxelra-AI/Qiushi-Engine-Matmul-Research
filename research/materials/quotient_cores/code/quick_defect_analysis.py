#!/usr/bin/env python3
"""analysis: Quick structural analysis of K-defect landscape."""
from __future__ import annotations
import json, time, sys, random
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from linear_completion import (
    build_t333_f2, tensor_to_D, parse_qmm_scheme_f2, mask_to_vec, gf2_rref
)
from b_repair_hillclimb import build_K, D_defect


def A_span_dim(A):
    vecs = np.array([mask_to_vec(a) for a in A], dtype=np.uint8)
    _, _, r = gf2_rref(vecs)
    return r


def VA_dim_and_D_cover(A, D):
    """Compute dim(V_A) and check if col(D) ⊂ V_A."""
    basis_vecs = []
    for a in set(A):
        a_vec = mask_to_vec(a)
        for j in range(9):
            ej = np.zeros(9, dtype=np.uint8)
            ej[j] = 1
            basis_vecs.append(np.outer(a_vec, ej).ravel())
    V = np.array(basis_vecs, dtype=np.uint8)
    _, _, rank_V = gf2_rref(V)
    # Check D-columns
    covered = 0
    for c in range(D.shape[1]):
        V_aug = np.vstack([V, D[:, c]])
        _, _, r2 = gf2_rref(V_aug)
        if r2 == rank_V:
            covered += 1
    return rank_V, covered


def main():
    scheme = Path('data/cn122_3x3_r23_repro/scheme.qmm')
    outdir = Path('data/defect_analysis')
    outdir.mkdir(parents=True, exist_ok=True)
    
    A23, B23, C23 = parse_qmm_scheme_f2(scheme)
    T = build_t333_f2()
    D = tensor_to_D(T)
    
    # Quick: rank of D over F2
    _, _, rank_D = gf2_rref(D.T.copy())
    print(f"rank(D over F2) = {rank_D}")
    
    # rank-23 scheme
    ad = A_span_dim(A23)
    K23 = build_K(A23, B23)
    _, _, rK23 = gf2_rref(K23.T.copy())
    d23 = D_defect(K23, D)
    print(f"Rank-23: A_span_dim={ad}, rank(K23)={rK23}, D_defect={d23}")
    
    # peer candidate
    peer_A = [400,260,73,393,292,8,265,274,269,72,392,144,278,9,256,146,448,7,32,268,56,16]
    pad = A_span_dim(peer_A)
    va_dim, d_covered = VA_dim_and_D_cover(peer_A, D)
    print(f"\nPeer candidate: A_span_dim={pad}, VA_dim={va_dim}, D_cols_in_VA={d_covered}/9")
    
    # Random B samples for peer
    rng = random.Random(42)
    defects_peer = []
    for _ in range(50):
        B = [rng.randrange(1, 512) for _ in range(22)]
        defects_peer.append(D_defect(build_K(peer_A, B), D))
    dh = {}
    for d in defects_peer:
        dh[d] = dh.get(d, 0) + 1
    print(f"  Random B defect hist (50 samples): {dict(sorted(dh.items()))}")
    
    # Defect-1 deletions structural analysis
    print("\n=== Defect-1 deletions ===")
    for del_t in range(23):
        A22 = [A23[t] for t in range(23) if t != del_t]
        B22 = [B23[t] for t in range(23) if t != del_t]
        base_d = D_defect(build_K(A22, B22), D)
        if base_d != 1:
            continue
        ad22 = A_span_dim(A22)
        va_dim22, dc22 = VA_dim_and_D_cover(A22, D)
        # Quick random sample
        rng2 = random.Random(del_t)
        defs = []
        for _ in range(30):
            B = [rng2.randrange(1, 512) for _ in range(22)]
            defs.append(D_defect(build_K(A22, B), D))
        dh2 = {}
        for d in defs:
            dh2[d] = dh2.get(d, 0) + 1
        print(f"  del {del_t}: A_dim={ad22}, VA_dim={va_dim22}, D_in_VA={dc22}/9, "
              f"random_defect: {dict(sorted(dh2.items()))}")
    
    print(f"\nElapsed: {time.time():.0f}s (relative)")

main()
