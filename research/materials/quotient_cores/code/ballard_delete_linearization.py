#!/usr/bin/env python3
"""
analysis: first-order deletion repair test inside the BILR cyclic m=4 chart.

Starting from the exact BILR Z4 x Z3 cyclic rank-23 scheme (11 cubes + four free
cyclic orbits), delete one cube.  Ask whether the missing cube cubic lies in the
first-order image of:
  * independent SL_3 changes of the ordered basis in each of the four exterior
    3-planes (these keep the m=4 exterior equation fixed to first order/exactly), and
  * first-order perturbations of the remaining 10 cube vectors.
If not, the corresponding one-cube deletion has no first-order repair within this
cyclic m=4 component.  This is local evidence around the known cyclic rank-23 point,
not a global m=4 exclusion.
"""
from __future__ import annotations
import itertools, json
from pathlib import Path
import numpy as np

import ballard_z4_cyclic_scheme as bilr

WS = Path(__file__).resolve().parent.parent
OUT = WS/'data'/'ballard_z4_cyclic'
OUT.mkdir(parents=True, exist_ok=True)

MONOS=list(itertools.combinations_with_replacement(range(9),3))
MI={m:i for i,m in enumerate(MONOS)}
PERMS={m:sorted(set(itertools.permutations(m))) for m in MONOS}

# traceless 3x3 generators acting on the three ordered vectors in one decomposable 3-vector
GEN=[]
for i in range(3):
    for j in range(3):
        if i!=j:
            G=np.zeros((3,3), dtype=object); G[i,j]=1; GEN.append(G)
G=np.diag([1,-1,0]).astype(object); GEN.append(G)
G=np.diag([0,1,-1]).astype(object); GEN.append(G)


def flatten(M):
    return np.array(M,dtype=object).reshape(9)


def prod_coeff(u,v,w):
    u=list(u); v=list(v); w=list(w)
    out=np.zeros(len(MONOS), dtype=object)
    for idx,m in enumerate(MONOS):
        s=0
        for p in PERMS[m]:
            s += u[p[0]]*v[p[1]]*w[p[2]]
        out[idx]=s
    return out


def cube_coeff(c):
    return prod_coeff(c,c,c)


def build_jacobian_for_drop(cubes, free_orbits, drop):
    cols=[]; col_meta=[]
    # internal SL3 changes of four free orbit representatives; orbit contribution has factor 3.
    for j,(U,V,W) in enumerate(free_orbits):
        M=np.array([flatten(U), flatten(V), flatten(W)], dtype=object)
        for gidx,G in enumerate(GEN):
            dM=G @ M
            d = 3*(prod_coeff(dM[0],M[1],M[2]) + prod_coeff(M[0],dM[1],M[2]) + prod_coeff(M[0],M[1],dM[2]))
            cols.append(d)
            col_meta.append({'kind':'orbit_internal_sl3','orbit':j,'generator':gidx})
    # cube perturbations of the ten kept cubes; cube contribution derivative is 3*c^2*dc.
    evecs=[]
    for q in range(9):
        e=np.zeros(9,dtype=object); e[q]=1; evecs.append(e)
    for ci,C in enumerate(cubes):
        if ci==drop: continue
        c=flatten(C)
        for q,e in enumerate(evecs):
            d=3*prod_coeff(c,c,e)
            cols.append(d)
            col_meta.append({'kind':'cube_vector','cube':ci,'coord':q})
    J=np.stack(cols, axis=1)
    rhs=cube_coeff(flatten(cubes[drop]))
    return J, rhs, col_meta


def rank_mod(A, p):
    A=np.array(A,dtype=object)
    m,n=A.shape
    B=[[int(A[i,j])%p for j in range(n)] for i in range(m)]
    r=0; pivots=[]
    for c in range(n):
        piv=None
        for i in range(r,m):
            if B[i][c]%p:
                piv=i; break
        if piv is None: continue
        B[r],B[piv]=B[piv],B[r]
        inv=pow(B[r][c]%p, -1, p)
        B[r]=[(x*inv)%p for x in B[r]]
        for i in range(m):
            if i!=r and B[i][c]%p:
                f=B[i][c]%p
                B[i]=[(B[i][j]-f*B[r][j])%p for j in range(n)]
        pivots.append(c); r+=1
        if r==m: break
    return r


def main():
    terms,cubes,free_orbits,_,_=bilr.build_scheme()
    records=[]
    primes=[1000003,1000033,65521,32003]
    for drop in range(len(cubes)):
        J,rhs,_=build_jacobian_for_drop(cubes,free_orbits,drop)
        Aaug=np.concatenate([J, rhs.reshape(-1,1)], axis=1)
        ranks={}; aug={}
        in_span=True
        for p in primes:
            r=rank_mod(J,p); ra=rank_mod(Aaug,p)
            ranks[str(p)]=int(r); aug[str(p)]=int(ra)
            if ra>r: in_span=False
        records.append({
            'drop':drop,
            'rhs_nonzero_monomials':int(sum(1 for x in rhs if x)),
            'jacobian_shape':list(J.shape),
            'rank_mod_primes':ranks,
            'augmented_rank_mod_primes':aug,
            'rhs_in_first_order_image_all_tested_primes':bool(in_span),
        })
        print(records[-1])
    summary={
        'interpretation':'If augmented rank exceeds Jacobian rank over a tested prime, the deleted cube is not in the first-order repair image over Q for that drop. This tests only the known BILR cyclic m=4 point and internal SL3 plus remaining-cube perturbations.',
        'records':records,
        'all_drops_first_order_nonrepairable': bool(all(not r['rhs_in_first_order_image_all_tested_primes'] for r in records)),
    }
    out=OUT/'ballard_delete_linearization.json'
    out.write_text(json.dumps(summary,indent=2)+'\n')
    print('Saved',out)

if __name__=='__main__':
    main()
