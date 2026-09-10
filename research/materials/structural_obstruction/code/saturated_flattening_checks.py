#!/usr/bin/env python3
"""analysis checks for saturated A-slot split-flattening projection identities.

For T_333, the A-split flattening P is a 27 x 27 permutation matrix.  For a
simple tensor a \otimes b \otimes c, the flattened matrix F has rank rank(a),
when b,c are nonzero.  If a rank-20 decomposition has A-rank profile
16*1 + 1*2 + 3*3 = 27, then rank(P) = sum rank(F_t).  In that equality case,
writing G_t = P^{-1} F_t should produce complementary idempotent projections:

    G_t^2=G_t,   G_t G_s=0 (t != s),   sum_t G_t=I.

Equivalently F_t P^{-1} F_s = F_t if t=s and 0 otherwise.  This script builds
P and F_t in the actual index convention, proves the identities on verified
rank-23 controls (which also saturate if all A-factors have rank one), then
optionally checks the normalized high-rank profile algebraically on symbolic
random b,c choices only for shape sanity.
"""
from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import List, Sequence, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from linear_completion import parse_qmm_scheme_f2, verify_decomposition_f2  # type: ignore
from residual_repair_geometry import parse_rank23_text  # type: ignore

CN122 = Path('data/cn122_3x3_r23_repro/scheme.qmm')
FLIP_TXT = Path('data/flip_cpd_inspect/src/khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt')
PIVOT17_JSON = Path('data/pivot_fixed/pivot17_rank23_transformed_control.json')
OUT = Path('data/structural/saturated_flattening_checks.json')


def gf2_rank(M: np.ndarray) -> int:
    A = (np.array(M, dtype=np.uint8) & 1).copy()
    m,n = A.shape
    r = 0
    for c in range(n):
        piv = None
        for i in range(r,m):
            if A[i,c]:
                piv = i; break
        if piv is None:
            continue
        if piv != r:
            A[[r,piv]] = A[[piv,r]]
        for i in range(m):
            if i != r and A[i,c]:
                A[i,:] ^= A[r,:]
        r += 1
        if r == m:
            break
    return r


def mat3_from_mask(a: int) -> np.ndarray:
    M = np.zeros((3,3), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            M[i,j] = (int(a) >> (3*i+j)) & 1
    return M


def mask_to_vec9(x: int) -> np.ndarray:
    return np.array([(int(x)>>i)&1 for i in range(9)], dtype=np.uint8)


def build_P() -> np.ndarray:
    # Row of Phi_A: (i, 3*j+k) from A-row i and B coordinate (j,k).
    # Col of Phi_A: (j, 3*i+k) from A-col j and C coordinate (i,k).
    P = np.zeros((27,27), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                row = i*9 + (j*3+k)
                col = j*9 + (i*3+k)
                P[row,col] ^= 1
    return P


def term_F(a: int, b: int, c: int) -> np.ndarray:
    # For a simple tensor, F row index (i, beta=(j,k)) and col index (j, gamma=(i,k))
    # is a_{ij} b_beta c_gamma with the split A indices carried into row/col.
    A = mat3_from_mask(a)
    bv = mask_to_vec9(b)
    cv = mask_to_vec9(c)
    F = np.zeros((27,27), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            if A[i,j] == 0:
                continue
            for beta in range(9):
                if not bv[beta]:
                    continue
                row = i*9 + beta
                for gamma in range(9):
                    if cv[gamma]:
                        col = j*9 + gamma
                        F[row,col] ^= 1
    return F


def load_sources() -> dict[str, List[Tuple[int,int,int]]]:
    sources = {}
    if CN122.exists():
        A,B,C = parse_qmm_scheme_f2(CN122)
        sources['cn122_qmm'] = list(zip(A,B,C))
    if FLIP_TXT.exists():
        sources['flip_rank23_text'] = parse_rank23_text(FLIP_TXT)
    if PIVOT17_JSON.exists():
        d = json.loads(PIVOT17_JSON.read_text())
        sources['pivot17_transformed_rank23'] = [tuple(map(int,t)) for t in d['terms']]
    return sources


def analyze_source(name: str, terms: Sequence[Tuple[int,int,int]], P: np.ndarray) -> dict:
    Pinv = P.T.copy()  # permutation inverse; P is symmetric in this convention, but P.T is safe.
    Fs = [term_F(a,b,c) for a,b,c in terms]
    sumF = np.bitwise_xor.reduce(np.stack(Fs), axis=0) if Fs else np.zeros_like(P)
    verify_diff = verify_decomposition_f2([a for a,b,c in terms], [b for a,b,c in terms], [c for a,b,c in terms])
    ranksA = [gf2_rank(mat3_from_mask(a)) for a,b,c in terms]
    ranksF = [gf2_rank(F) for F in Fs]
    Gs = [(Pinv @ F) & 1 for F in Fs]
    idem_bad = []
    cross_bad = []
    FtPF_bad = []
    for i,G in enumerate(Gs):
        if np.any(((G @ G) & 1) ^ G):
            idem_bad.append(i)
    for i,Gi in enumerate(Gs):
        for j,Gj in enumerate(Gs):
            prod = (Gi @ Gj) & 1
            if i == j:
                if np.any(prod ^ Gi):
                    cross_bad.append([i,j])
            elif np.any(prod):
                cross_bad.append([i,j])
            H = (Fs[i] @ Pinv @ Fs[j]) & 1
            expected = Fs[i] if i == j else np.zeros_like(P)
            if np.any(H ^ expected):
                FtPF_bad.append([i,j,int(np.count_nonzero(H ^ expected))])
    sumG = np.bitwise_xor.reduce(np.stack(Gs), axis=0) if Gs else np.zeros_like(P)
    return {
        'term_count': len(terms),
        'verify_brent_diff': int(verify_diff),
        'sumF_equals_P': bool(not np.any(sumF ^ P)),
        'sumG_equals_I': bool(not np.any(sumG ^ np.eye(27, dtype=np.uint8))),
        'rankA_hist': {str(k): int(v) for k,v in sorted(Counter(ranksA).items())},
        'rankF_hist': {str(k): int(v) for k,v in sorted(Counter(ranksF).items())},
        'rankF_matches_rankA': bool(ranksF == ranksA),
        'rank_sum_A': int(sum(ranksA)),
        'rank_sum_F': int(sum(ranksF)),
        'rank_P': int(gf2_rank(P)),
        'saturates_split_flattening': bool(sum(ranksF) == gf2_rank(P)),
        'idempotent_bad_count': len(idem_bad),
        'idempotent_bad_head': idem_bad[:20],
        'orthogonal_projection_bad_count': len(cross_bad),
        'orthogonal_projection_bad_head': cross_bad[:20],
        'Ft_Pinv_Fs_bad_count': len(FtPF_bad),
        'Ft_Pinv_Fs_bad_head': FtPF_bad[:20],
    }


def main():
    P = build_P()
    Pinv = P.T.copy()
    # The schoolbook 27-term decomposition is an applicable saturated control:
    # every A factor is one matrix unit, and P is the sum of 27 rank-one flattened terms.
    schoolbook = []
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a = 1 << (3*i + j)
                b = 1 << (3*j + k)
                c = 1 << (3*i + k)
                schoolbook.append((a,b,c))
    out = {
        'schema': 's0908_saturated_flattening_checks_v1',
        'meaning': 'Checks the split-flattening equality identities in the actual convention. These are necessary conditions for a saturated rank-20 profile, not by themselves a contradiction.',
        'P': {
            'shape': list(P.shape),
            'is_permutation': bool(np.all(P.sum(axis=0)==1) and np.all(P.sum(axis=1)==1)),
            'rank': int(gf2_rank(P)),
            'PinvP_identity': bool(not np.any(((Pinv @ P) & 1) ^ np.eye(27, dtype=np.uint8))),
        },
        'sources': {'schoolbook_27': analyze_source('schoolbook_27', schoolbook, P)},
        'profile27_statement': 'For any decomposition with sum rank(A_t)=27 and nonzero B,C, the G_t=P^{-1}F_t are complementary idempotent projections. A rank20 survivor after analysis coset reduction would have A-rank profile 16 rank1, one rank2, three rank3, hence sum rank(A_t)=27.',
    }
    for name, terms in load_sources().items():
        print('analyzing', name, flush=True)
        out['sources'][name] = analyze_source(name, terms, P)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'status': 'ok',
        'out': str(OUT),
        'P': out['P'],
        'source_summary': {k: {kk:v for kk,v in rec.items() if kk in ['term_count','verify_brent_diff','sumF_equals_P','rank_sum_A','saturates_split_flattening','idempotent_bad_count','orthogonal_projection_bad_count','Ft_Pinv_Fs_bad_count']} for k,rec in out['sources'].items()},
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
