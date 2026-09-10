#!/usr/bin/env python3
"""Exact tangent-kernel check for the BILR rank-4 exterior decomposition.

Verifies over several primes that the 40-dimensional kernel of the ordered-vector
map (four triples in sl3 -> Lambda^3 sl3) is exactly spanned by:
  * 32 per-summand internal sl3 basis changes, and
  * 8 global adjoint sl3 stabilizer directions.
This upgrades the Jacobian-rank observation into a precise local rigidity statement:
modulo the expected internal bases and PGL3 stabilizer, the m=4 exterior decomposition
is locally isolated at the BILR point.
"""
from __future__ import annotations
import itertools, json
from pathlib import Path
import numpy as np
import ballard_cyclic_analysis_v2 as a
import ballard_z4_cyclic_scheme as bilr

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'ballard_z4_cyclic'
OUT.mkdir(parents=True,exist_ok=True)

# sl3 basis matrices in the analysis order.
BAS=[]
for pos in [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]:
    M=np.zeros((3,3),dtype=object); M[pos]=1; BAS.append(M)
M=np.zeros((3,3),dtype=object); M[0,0]=1; M[1,1]=-1; BAS.append(M)
M=np.zeros((3,3),dtype=object); M[1,1]=1; M[2,2]=-1; BAS.append(M)

# internal generators acting on the 3 row vectors of each summand.
GEN=[]
for i in range(3):
    for j in range(3):
        if i!=j:
            G=np.zeros((3,3),dtype=object); G[i,j]=1; GEN.append(G)
G=np.diag([1,-1,0]).astype(object); GEN.append(G)
G=np.diag([0,1,-1]).astype(object); GEN.append(G)


def sl_coords_from_mat(M):
    x=np.array(M,dtype=object).reshape(9)
    assert int(x[0]+x[4]+x[8])==0
    return np.array([x[1],x[2],x[3],x[5],x[6],x[7],x[0],-x[8]],dtype=object)


def mat_from_sl_coords(c):
    return sum(c[i]*BAS[i] for i in range(8))


def ad_matrix(H):
    A=np.zeros((8,8),dtype=object)
    for j,E in enumerate(BAS):
        C=H@E-E@H
        A[:,j]=sl_coords_from_mat(C)
    return A


def rank_mod(A,p):
    A=np.array(A,dtype=object); m,n=A.shape
    B=[[int(A[i,j])%p for j in range(n)] for i in range(m)]
    r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if B[i][c]%p: piv=i; break
        if piv is None: continue
        B[r],B[piv]=B[piv],B[r]
        inv=pow(B[r][c]%p,-1,p)
        B[r]=[(x*inv)%p for x in B[r]]
        for i in range(m):
            if i!=r and B[i][c]%p:
                f=B[i][c]%p
                B[i]=[(B[i][j]-f*B[r][j])%p for j in range(n)]
        r+=1
        if r==m: break
    return r


def main():
    terms,cubes,free,_,_=bilr.build_scheme()
    decomp=[]
    for U,V,W in free:
        decomp.append(np.array([a.gl_traceless_to_sl_coords(U), a.gl_traceless_to_sl_coords(V), a.gl_traceless_to_sl_coords(W)],dtype=object))
    decomp=np.array(decomp,dtype=object)
    J=a.exterior_jacobian(decomp)
    tangent_cols=[]; meta=[]
    # internal term basis changes
    for j in range(4):
        M=decomp[j] # 3x8 row matrix
        for gi,G in enumerate(GEN):
            dM=G@M
            vec=np.zeros(96,dtype=object)
            vec[(j*3)*8:(j*3+3)*8]=dM.reshape(24)
            tangent_cols.append(vec); meta.append(('internal',j,gi))
    # global adjoint stabilizer directions
    for hi,H in enumerate(BAS):
        A=ad_matrix(H)
        vec=np.zeros(96,dtype=object)
        for j in range(4):
            for s in range(3):
                vec[(j*3+s)*8:(j*3+s+1)*8]=A@decomp[j,s]
        tangent_cols.append(vec); meta.append(('global_ad',hi))
    T=np.stack(tangent_cols,axis=1)
    JT=J@T
    primes=[1000003,1000033,65521,32003]
    ranks={}; jranks={}; jtranks={}
    for p in primes:
        ranks[str(p)]=rank_mod(T,p)
        jranks[str(p)]=rank_mod(J,p)
        jtranks[str(p)]=rank_mod(JT,p)
        print('p',p,'rank(T)',ranks[str(p)],'rank(J)',jranks[str(p)],'rank(JT)',jtranks[str(p)])
    result={
        'J_shape':list(J.shape),'T_shape':list(T.shape),'JT_shape':list(JT.shape),
        'tangent_span_components':{'internal_sl3_per_summand':32,'global_ad_sl3':8},
        'rank_T_mod_primes':ranks,'rank_J_mod_primes':jranks,'rank_JT_mod_primes':jtranks,
        'kernel_dim_from_J':{q:96-r for q,r in jranks.items()},
        'expected_kernel_spanned_all_tested': all(ranks[q]==40 and jranks[q]==56 and jtranks[q]==0 for q in ranks),
    }
    out=OUT/'bilr_exterior_kernel_check.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('Saved',out)

if __name__=='__main__': main()
