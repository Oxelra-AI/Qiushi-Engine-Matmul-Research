#!/usr/bin/env python3
"""Check the companion tensor actions for the Wang A-side transports.

The Wang certificate acts only on A-side constraint subspaces.  To use those
transports in a tensor-rank proof, the A-action must be the A component of an
actual automorphism of the 3x3 matrix-multiplication tensor.  This script checks
that link in the two coordinate conventions used in this investigation:

  source/Wang convention: T[a=3i+j, b=3j+k, c=3k+i] = 1, C is N2 x N0;
  proof convention:      T[a=3i+j, b=3j+k, c=3i+k] = 1, C is N0 x N2.

For every L,R in GL(3,2) and both transpose branches it verifies that the
A-image from `wang_capacity_lazy.basis_image_for_action` agrees with the stated
matrix formula and that the companion B/C transformation fixes the corresponding
T exactly.  It also checks the source-convention split-flattening product
formula F(A,B,C)P^{-1}F(A',B',C') = F(A(B'C)A',B,C') on all elementary pairs.
The proof-convention product formula with C^T was already checked in analysis.
"""
from __future__ import annotations

import json
import sys
import time
from itertools import product
from pathlib import Path

S04 = Path('scripts')
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
import wang_capacity_lazy as wc  # type: ignore

OUT = Path('data/tensor_action/companion_tensor_action_check.json')


def E(i: int, j: int) -> int:
    return 1 << (3 * i + j)


def entries(mask: int):
    m = int(mask)
    while m:
        lb = m & -m
        yield lb.bit_length() - 1
        m ^= lb


def left_mul(L, M: int) -> int:
    return wc.mat3_mask_from_rows(wc.mat3_mul(L, wc.mat3_rows_from_mask(M)))


def right_mul(M: int, R) -> int:
    return wc.mat3_mask_from_rows(wc.mat3_mul(wc.mat3_rows_from_mask(M), R))


def both_mul(L, M: int, R) -> int:
    return wc.mat3_mask_from_rows(wc.mat3_mul(wc.mat3_mul(L, wc.mat3_rows_from_mask(M)), R))


def transpose_mask(M: int) -> int:
    return wc.mat3_mask_from_rows(wc.mat3_transpose(wc.mat3_rows_from_mask(M)))


def idx(a: int, b: int, c: int) -> int:
    return a * 81 + b * 9 + c


def source_positions():
    return [(3 * i + j, 3 * j + k, 3 * k + i) for i in range(3) for j in range(3) for k in range(3)]


def proof_positions():
    return [(3 * i + j, 3 * j + k, 3 * i + k) for i in range(3) for j in range(3) for k in range(3)]


def bitset_from_positions(pos):
    out = 0
    for a, b, c in pos:
        out ^= 1 << idx(a, b, c)
    return out


def bc_bitset(bmask: int, cmask: int, cache: dict) -> int:
    key = (int(bmask), int(cmask))
    got = cache.get(key)
    if got is not None:
        return got
    out = 0
    for b in entries(bmask):
        base = b * 9
        for c in entries(cmask):
            out ^= 1 << (base + c)
    cache[key] = out
    return out


def add_term(out: int, amask: int, bmask: int, cmask: int, cache: dict) -> int:
    bc = bc_bitset(bmask, cmask, cache)
    for a in entries(amask):
        out ^= bc << (a * 81)
    return out


def transform_tensor_source(L, R, transpose_branch: bool, Aimgs):
    Linv = wc.mat3_inv(L); Rinv = wc.mat3_inv(R)
    LT = wc.mat3_transpose(L); RT = wc.mat3_transpose(R)
    cache = {}
    out = 0
    for a, b, c in source_positions():
        Am = Aimgs[a]
        if not transpose_branch:
            Bm = left_mul(RT, 1 << b)       # B -> R^T B
            Cm = right_mul(1 << c, LT)      # C(source N2xN0) -> C L^T
        else:
            # Proof convention has B -> L C_out and C_out -> R^T B.
            # With source C = C_out^T this is B -> L C^T and C -> B^T R.
            Bm = left_mul(L, transpose_mask(1 << c))
            Cm = right_mul(transpose_mask(1 << b), R)
        out = add_term(out, Am, Bm, Cm, cache)
    return out


def transform_tensor_proof(L, R, transpose_branch: bool, Aimgs):
    RT = wc.mat3_transpose(R)
    cache = {}
    out = 0
    for a, b, c in proof_positions():
        Am = Aimgs[a]
        if not transpose_branch:
            Bm = left_mul(RT, 1 << b)       # B -> R^T B
            Cm = left_mul(L, 1 << c)        # C(output N0xN2) -> L C
        else:
            Bm = left_mul(L, 1 << c)        # B -> L C
            Cm = left_mul(RT, 1 << b)       # C -> R^T B
        out = add_term(out, Am, Bm, Cm, cache)
    return out


def direct_A_images(L, R, transpose_branch: bool):
    Linv = wc.mat3_inv(L); Rinv = wc.mat3_inv(R)
    LinvT = wc.mat3_transpose(Linv); RinvT = wc.mat3_transpose(Rinv)
    imgs = []
    for bit in range(9):
        M = 1 << bit
        if not transpose_branch:
            imgs.append(both_mul(LinvT, M, RinvT))
        else:
            imgs.append(both_mul(Rinv, transpose_mask(M), Linv))
    return tuple(imgs)


def idx_AB(i: int, p: int, q: int) -> int:
    return i * 9 + p * 3 + q


def idx_AC_source(j: int, r: int, s: int) -> int:
    # column index: A-column j and source C coordinate (r,s) = (k,i)
    return j * 9 + r * 3 + s


def source_P_positions():
    # P[row=(i,(j,k)), col=(j,(k,i))] = 1 in source convention.
    return [(idx_AB(i, j, k), idx_AC_source(j, k, i)) for i in range(3) for j in range(3) for k in range(3)]


def source_elementary_F_pos(A, B, C):
    (i, j), (p, q), (r, s) = A, B, C
    return (idx_AB(i, p, q), idx_AC_source(j, r, s))


def source_predicted_sparse(A, B, C, Ap, Bp, Cp):
    # Source convention: C is N2 x N0, so middle product is B' C.
    (i, j) = A; (p, q) = B; (r, s) = C
    (u, v) = Ap; (x, y) = Bp; (z, w) = Cp
    # B' C has nonzero entry (x,s) iff y=r; E_ij (B'C) E_uv nonzero iff j=x, s=u.
    if j == x and y == r and s == u:
        return {(idx_AB(i, p, q), idx_AC_source(v, z, w))}
    return set()


def check_source_product_formula():
    P = source_P_positions()
    pinv = {(c, r): 1 for r, c in P}
    coords = list(product(range(3), range(3)))
    elems = list(product(coords, coords, coords))
    failures = []
    checks = nonzero_lhs = nonzero_rhs = 0
    for A, B, C in elems:
        f1 = source_elementary_F_pos(A, B, C)
        for Ap, Bp, Cp in elems:
            checks += 1
            f2 = source_elementary_F_pos(Ap, Bp, Cp)
            lhs = {(f1[0], f2[1])} if pinv.get((f1[1], f2[0]), 0) else set()
            rhs = source_predicted_sparse(A, B, C, Ap, Bp, Cp)
            if lhs: nonzero_lhs += 1
            if rhs: nonzero_rhs += 1
            if lhs != rhs:
                failures.append({'A': A, 'B': B, 'C': C, 'Ap': Ap, 'Bp': Bp, 'Cp': Cp, 'lhs': sorted(lhs), 'rhs': sorted(rhs)})
                if len(failures) >= 20:
                    break
        if len(failures) >= 20:
            break
    return {'checks': checks, 'failure_count': len(failures), 'failures_head': failures, 'nonzero_lhs_count': nonzero_lhs, 'nonzero_rhs_count': nonzero_rhs, 'P_is_permutation': len({r for r, c in P}) == 27 and len({c for r, c in P}) == 27}


def main():
    t0 = time.time()
    GL = wc.generate_gl3()
    target_source = bitset_from_positions(source_positions())
    target_proof = bitset_from_positions(proof_positions())
    action_count = 0
    bad_A = []
    bad_source = []
    bad_proof = []
    branch_counts = {False: 0, True: 0}
    for L in GL:
        for R in GL:
            for tr in (False, True):
                action_count += 1
                branch_counts[tr] += 1
                Aimgs = wc.basis_image_for_action(L, R, tr)
                Aimgs_direct = direct_A_images(L, R, tr)
                if Aimgs != Aimgs_direct and len(bad_A) < 20:
                    bad_A.append({'L': L, 'R': R, 'transpose': tr, 'wang': Aimgs, 'direct': Aimgs_direct})
                if transform_tensor_source(L, R, tr, Aimgs) != target_source and len(bad_source) < 20:
                    bad_source.append({'L': L, 'R': R, 'transpose': tr})
                if transform_tensor_proof(L, R, tr, Aimgs) != target_proof and len(bad_proof) < 20:
                    bad_proof.append({'L': L, 'R': R, 'transpose': tr})
    source_formula = check_source_product_formula()
    out = {
        'schema': 's0908_companion_tensor_action_check_v1',
        'meaning': 'Exact finite check that every A-side transport action used for Wang certificate witnesses is the A component of a matrix-multiplication tensor automorphism, in both the source/Wang C-index convention and the proof C-index convention. Also checks the source-convention split-flattening product formula on all elementary pairs.',
        'conventions': {
            'source_wang': 'T[3*i+j, 3*j+k, 3*k+i]=1; C is N2 x N0; nontranspose companion B->R^T B, C->C L^T; transpose companion B->L C^T, C->B^T R.',
            'proof_convention': 'T[3*i+j, 3*j+k, 3*i+k]=1; C is N0 x N2; nontranspose companion B->R^T B, C->L C; transpose companion B->L C, C->R^T B.',
            'A_action_both': 'nontranspose A->L^{-T} A R^{-T}; transpose A->R^{-1} A^T L^{-1}, matching wang_capacity_lazy.basis_image_for_action.'
        },
        'action_count': action_count,
        'branch_counts': {'nontranspose': branch_counts[False], 'transpose': branch_counts[True]},
        'gl3_count': len(GL),
        'A_image_formula_failure_count': len(bad_A),
        'A_image_failures_head': bad_A,
        'source_tensor_action_failure_count': len(bad_source),
        'source_tensor_action_failures_head': bad_source,
        'proof_tensor_action_failure_count': len(bad_proof),
        'proof_tensor_action_failures_head': bad_proof,
        'source_product_formula': source_formula,
        'all_ok': (not bad_A and not bad_source and not bad_proof and source_formula['failure_count'] == 0 and source_formula['P_is_permutation']),
        'elapsed_sec': time.time() - t0,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'ok', 'out': str(OUT), 'all_ok': out['all_ok'], 'action_count': action_count, 'A_failures': len(bad_A), 'source_failures': len(bad_source), 'proof_failures': len(bad_proof), 'source_product_failures': source_formula['failure_count'], 'elapsed_sec': out['elapsed_sec']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
