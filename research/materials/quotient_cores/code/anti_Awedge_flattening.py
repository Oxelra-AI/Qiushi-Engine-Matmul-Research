#!/usr/bin/env python3
"""A-factor exterior flattening for the tau complementary target.

For T_anti in A \otimes Lambda^2 W, with dim A=3 and dim W=9, compute
  F_T : A \otimes W^* -> Lambda^2 A \otimes W,
  e_s \otimes beta |-> sum_r (e_r wedge e_s) \otimes theta_r(beta).
For one tau-free orbit c \otimes (p wedge q), the image lies in
(c wedge A) \otimes span(p,q), so its rank is at most 4.  If rank F_T=27,
then the complementary sector needs at least 7 free orbits in characteristic
not 2.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

SESSION = Path(__file__).resolve().parents[1]
OUT = SESSION / "data" / "transpose_component"
OUT.mkdir(parents=True, exist_ok=True)
p = 1000003

def inv(a): return pow(int(a) % p, p-2, p)
def rank(M):
    M = np.array(M, dtype=np.int64) % p
    rows, cols = M.shape
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c] % p:
                piv = i; break
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]
        M[r] = M[r] * inv(M[r, c]) % p
        for i in range(rows):
            if i != r and M[i, c] % p:
                M[i] = (M[i] - int(M[i, c]) * M[r]) % p
        r += 1
        if r == rows: break
    return r

def idx(i, k): return 3*i + k
Apairs = [(0,1),(0,2),(1,2)]
Api = {q:i for i,q in enumerate(Apairs)}

def wedge_A(a, s):
    if a == s: return None, 0
    if a < s: return (a,s), 1
    return (s,a), -1

def theta_contract(a_pair, beta_index):
    """theta_{a_pair}(beta), as a vector in W, for theta=-sum_k e_ik wedge e_jk.

    For a wedge vector x_i wedge x_j, contraction by beta=e_t^* is
    beta(x_i) x_j - beta(x_j) x_i.  Include the target's leading minus sign.
    """
    i, j = a_pair
    out = np.zeros(9, dtype=np.int64)
    for k in range(3):
        ai = idx(i,k); bj = idx(j,k)
        if beta_index == ai:
            out[bj] -= 1
        if beta_index == bj:
            out[ai] += 1
    return out % p

def build_F():
    # Rows: Lambda^2 A pair (3) times W coordinate (9). Cols: A basis s (3) times W* basis beta (9).
    F = np.zeros((27,27), dtype=np.int64)
    for s in range(3):
        for beta in range(9):
            col = s*9 + beta
            for r, ap in enumerate(Apairs):
                wa, sign = wedge_A(r, s)
                if sign == 0: continue
                avec_index = Api[wa]
                wvec = theta_contract(ap, beta)
                for wcoord, coeff in enumerate(wvec):
                    if coeff % p:
                        row = avec_index*9 + wcoord
                        F[row, col] = (F[row, col] + sign*int(coeff)) % p
    return F

def one_term_rank_samples():
    # Confirm the rank cap 4 on a few random structured rank-one terms by building the same map.
    rng=np.random.default_rng(61061)
    ranks=[]
    for t in range(20):
        c=rng.integers(0,p,3,dtype=np.int64)
        a=rng.integers(0,p,9,dtype=np.int64)
        b=rng.integers(0,p,9,dtype=np.int64)
        M=np.zeros((27,27),dtype=np.int64)
        # term theta = (a wedge b), A coefficient c. contraction by beta gives beta(a)b - beta(b)a.
        for s in range(3):
            for beta in range(9):
                col=s*9+beta
                # wedge c with e_s in A
                for r in range(3):
                    if c[r] % p == 0: continue
                    wa,sign=wedge_A(r,s)
                    if sign==0: continue
                    avec=Api[wa]
                    wvec=(int(a[beta])*b - int(b[beta])*a) % p
                    for wc,coeff in enumerate(wvec):
                        if coeff%p:
                            M[avec*9+wc,col]=(M[avec*9+wc,col]+int(c[r])*sign*int(coeff))%p
        ranks.append(rank(M))
    return ranks

def main():
    F=build_F()
    R=rank(F)
    term_ranks=one_term_rank_samples()
    out={
        "prime":p,
        "matrix_shape":[27,27],
        "rank_F_T":R,
        "det_nonzero_mod_p": bool(R==27),
        "structured_one_term_rank_cap":4,
        "sample_one_term_ranks": term_ranks,
        "lower_bound_m0": int((R + 3)//4),
        "field_scope":"odd characteristic with the displayed determinant nonzero mod p; symbolically the operator is V -> V^T - tr(V)I on Mat_3 tensored with I_3, hence invertible when char != 2.",
    }
    path=OUT/"anti_Awedge_flattening.json"
    path.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2))
    print(f"SAVED {path}")

if __name__=='__main__':
    main()
