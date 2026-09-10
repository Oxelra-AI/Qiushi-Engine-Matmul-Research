#!/usr/bin/env python3
"""analysis convention check for the saturated split-flattening product formula.

Index derivation predicts

  F(a,b,c) P^{-1} F(a',b',c') = F(a (B' C^T) a', b, c')

over F2, where F is the A-slot split flattening, and a,B',C,a' are 3x3
matrices represented by the same 9-bit row-major masks.  This script checks
that formula on elementary terms and random dense masks, and checks the derived
schoolbook identities A_t B_s C_t^T A_s = delta_ts A_t.
"""
from __future__ import annotations

import json
import random
from pathlib import Path
from typing import List

import numpy as np

OUT = Path('data/structural/flattening_product_formula.json')


def mat3_from_mask(x: int) -> np.ndarray:
    M = np.zeros((3,3), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            M[i,j] = (int(x) >> (3*i+j)) & 1
    return M


def mask_from_mat3(M: np.ndarray) -> int:
    z = 0
    A = np.array(M, dtype=np.uint8) & 1
    for i in range(3):
        for j in range(3):
            if A[i,j]:
                z |= 1 << (3*i+j)
    return z


def matmul_mask(A: int, B: int) -> int:
    return mask_from_mat3((mat3_from_mask(A) @ mat3_from_mask(B)) & 1)


def transpose_mask(A: int) -> int:
    return mask_from_mat3(mat3_from_mask(A).T)


def build_P() -> np.ndarray:
    P = np.zeros((27,27), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                row = i*9 + (j*3+k)
                col = j*9 + (i*3+k)
                P[row,col] ^= 1
    return P


def mask_to_vec9(x: int) -> List[int]:
    return [(int(x) >> i) & 1 for i in range(9)]


def F(a: int, b: int, c: int) -> np.ndarray:
    A = mat3_from_mask(a); bv = mask_to_vec9(b); cv = mask_to_vec9(c)
    M = np.zeros((27,27), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            if not A[i,j]:
                continue
            for beta in range(9):
                if not bv[beta]:
                    continue
                row = i*9 + beta
                for gamma in range(9):
                    if cv[gamma]:
                        col = j*9 + gamma
                        M[row,col] ^= 1
    return M


def predicted_a(a: int, bp: int, c: int, ap: int) -> int:
    # a (B' C^T) a'
    middle = matmul_mask(bp, transpose_mask(c))
    return matmul_mask(matmul_mask(a, middle), ap)


def check_tuple(a: int, b: int, c: int, ap: int, bp: int, cp: int, Pinv: np.ndarray) -> bool:
    lhs = (F(a,b,c) @ Pinv @ F(ap,bp,cp)) & 1
    aa = predicted_a(a,bp,c,ap)
    rhs = F(aa,b,cp)
    return not np.any(lhs ^ rhs)


def schoolbook_terms():
    terms=[]
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a = 1 << (3*i+j)
                b = 1 << (3*j+k)
                c = 1 << (3*i+k)
                terms.append((a,b,c,i,j,k))
    return terms


def main():
    P = build_P(); Pinv = P.T.copy()
    failures=[]
    # Exhaust all elementary matrix-unit triples for both terms: 27^2 product checks.
    elems=schoolbook_terms()
    for t,(a,b,c,*_) in enumerate(elems):
        for s,(ap,bp,cp,*__) in enumerate(elems):
            if not check_tuple(a,b,c,ap,bp,cp,Pinv):
                failures.append({'kind':'elementary_formula','t':t,'s':s})
                break
        if failures:
            break
    # Random dense checks.
    rng=random.Random(9033)
    random_fail=[]
    for q in range(5000):
        vals=[rng.randrange(1,512) for _ in range(6)]
        if not check_tuple(*vals, Pinv):
            random_fail.append({'trial':q,'vals':vals})
            break
    # Derived schoolbook scalar A identities.
    scalar_fail=[]
    for t,(a,b,c,*_) in enumerate(elems):
        for s,(ap,bp,cp,*__) in enumerate(elems):
            got=predicted_a(a,bp,c,ap)
            expect=a if t==s else 0
            if got != expect:
                scalar_fail.append({'t':t,'s':s,'got':got,'expect':expect,'a':a,'bp':bp,'c':c,'ap':ap})
                if len(scalar_fail)>20:
                    break
        if len(scalar_fail)>20:
            break
    out={
        'schema':'s0908_flattening_product_formula_v1',
        'meaning':'Convention check for F(a,b,c)P^{-1}F(a_prime,b_prime,c_prime)=F(a(B_prime C^T)a_prime,b,c_prime), and schoolbook saturated identities.',
        'elementary_formula_checks':len(elems)**2,
        'elementary_formula_failure_count':len(failures),
        'elementary_formula_failures_head':failures[:20],
        'random_formula_checks':5000,
        'random_formula_failure_count':len(random_fail),
        'random_formula_failures_head':random_fail[:20],
        'schoolbook_scalar_identity_checks':len(elems)**2,
        'schoolbook_scalar_failure_count':len(scalar_fail),
        'schoolbook_scalar_failures_head':scalar_fail[:20],
        'derived_saturated_condition':'For a saturated decomposition of T, A_t (B_s C_t^T) A_s = 0 for t!=s and A_t (B_t C_t^T) A_t = A_t, provided B_t,C_t are nonzero so F(M,B_t,C_t)=0 implies M=0.',
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(OUT),'elementary_failures':len(failures),'random_failures':len(random_fail),'schoolbook_scalar_failures':len(scalar_fail)},indent=2,sort_keys=True))


if __name__=='__main__':
    main()
