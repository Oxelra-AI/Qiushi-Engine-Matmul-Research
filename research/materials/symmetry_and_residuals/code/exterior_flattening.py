#!/usr/bin/env python3
"""
analysis: exterior flattening tests for the cyclic quotient 3-form.

The quotient E_inv/Sym^3 for cyclic-invariant tensors is naturally Lambda^3(K^9):
a free cyclic orbit U⊗V⊗W + cyclic maps to U∧V∧W, while fixed cube terms vanish.
The quotient of T_<3,3,3> is the 3-form given by the eight degree-3 monomials
in the ANF of tr(M^3), equivalently the alternating part of tr(A B C).

If a 3-form is a sum of m decomposable 3-vectors, the wedge map
    L_a(omega): Lambda^a V -> Lambda^{a+3} V, eta |-> eta ∧ omega
has rank at most m * binom(n-3, a) for a <= n-3 for a single decomposable term.
This script computes these ranks for the target over Q (via modular exact rank)
and compares them to the bounds for m=1,2,3,4.
"""
from __future__ import annotations

import itertools, json, math
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / 'data' / 'exterior_flattening'
N=9

def idx(a,b): return 3*a+b

def omega_terms():
    # Use ordered triples with coefficient +1 in increasing basis order for the quotient 3-form.
    terms={}
    raw=[]
    for a,b,c in itertools.product(range(3), repeat=3):
        mask_tuple=(idx(a,b), idx(b,c), idx(c,a))
        if len(set(mask_tuple))<3:
            continue
        sorted_tuple=tuple(sorted(mask_tuple))
        # Sign of permutation from sorted_tuple to mask_tuple.
        perm=[sorted_tuple.index(x) for x in mask_tuple]
        inv=sum(1 for i in range(3) for j in range(i+1,3) if perm[i]>perm[j])
        sign=-1 if inv%2 else 1
        terms[sorted_tuple]=terms.get(sorted_tuple,0)+sign
        raw.append((mask_tuple,sorted_tuple,sign))
    # The cyclic quotient coordinate for each unordered triple is the alternating coefficient.
    # Remove zeros.
    return {k:v for k,v in terms.items() if v}

def wedge_sign(a,b):
    # a,b sorted disjoint tuples. sign for concatenation a+b -> sorted(a+b)
    inv=0
    for x in a:
        for y in b:
            if x>y: inv+=1
    return -1 if inv%2 else 1

def rank_mod(mat, p):
    A=[row[:] for row in mat]
    m=len(A); n=len(A[0]) if m else 0
    r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if A[i][c]%p:
                piv=i; break
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]
        inv=pow(A[r][c]%p, -1, p)
        A[r]=[(x*inv)%p for x in A[r]]
        for i in range(m):
            if i!=r and A[i][c]%p:
                f=A[i][c]%p
                A[i]=[(A[i][j]-f*A[r][j])%p for j in range(n)]
        r+=1
        if r==m: break
    return r

def wedge_matrix(a):
    src=list(itertools.combinations(range(N),a))
    dst=list(itertools.combinations(range(N),a+3))
    dst_i={t:i for i,t in enumerate(dst)}
    omega=omega_terms()
    mat=[[0 for _ in src] for __ in dst]
    for j,s in enumerate(src):
        ss=set(s)
        for t,coef in omega.items():
            if ss.intersection(t): continue
            out=tuple(sorted(s+t))
            mat[dst_i[out]][j]+=coef*wedge_sign(s,t)
    return mat,src,dst

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    omega=omega_terms()
    print('omega terms:',omega)
    records=[]
    for a in range(0,7):
        mat,src,dst=wedge_matrix(a)
        ranks={str(p):rank_mod(mat,p) for p in [1000003,1000033,1000037,65521,32003]}
        rank=max(ranks.values())
        single=math.comb(N-3,a) if a<=N-3 else 0
        rec={'a':a,'domain_dim':len(src),'codomain_dim':len(dst),'rank_mods':ranks,'rank_certified':rank,'single_decomposable_bound':single,
             'rank_lower_bound_from_flattening':math.ceil(rank/single) if single else None,
             'bounds_for_m':{str(m):m*single for m in [1,2,3,4,5]}}
        print(rec)
        records.append(rec)
    out=OUT/'exterior_flattening_ranks.json'
    out.write_text(json.dumps({'omega_terms':{str(k):v for k,v in omega.items()},'records':records},indent=2)+'\n')
    print(f'Saved {out}')
if __name__=='__main__': main()
