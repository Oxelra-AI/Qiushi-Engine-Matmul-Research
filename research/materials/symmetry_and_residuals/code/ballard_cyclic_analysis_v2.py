#!/usr/bin/env python3
"""
analysis corrected exact analysis of the BILR Z4 x Z3 cyclic rank-23 scheme.

Uses the scheme reconstructed in ballard_z4_cyclic_scheme.py.  Corrects the
normalization of the exterior quotient: with the unnormalised alternating coefficients
omega built from tr(XYZ), one free cyclic 3-orbit contributes 3*(U wedge V wedge W),
so the four BILR free orbits satisfy sum wedge = omega/3.
"""
from __future__ import annotations
import itertools, json, math
from pathlib import Path
import numpy as np

import ballard_z4_cyclic_scheme as bilr

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'ballard_z4_cyclic'
OUT.mkdir(parents=True, exist_ok=True)

TRIPLES8=list(itertools.combinations(range(8),3)); T8={t:i for i,t in enumerate(TRIPLES8)}
PAIRS8=list(itertools.combinations(range(8),2)); P8={p:i for i,p in enumerate(PAIRS8)}


def gl_traceless_to_sl_coords(M):
    x=np.array(M,dtype=object).reshape(9)
    # Requires trace zero.
    assert int(x[0]+x[4]+x[8]) == 0
    return np.array([x[1],x[2],x[3],x[5],x[6],x[7],x[0],-x[8]], dtype=object)


def wedge3(u,v,w):
    out=np.zeros(56,dtype=object)
    for r,(a,b,c) in enumerate(TRIPLES8):
        out[r]=u[a]*(v[b]*w[c]-v[c]*w[b])-u[b]*(v[a]*w[c]-v[c]*w[a])+u[c]*(v[a]*w[b]-v[b]*w[a])
    return out


def wedge2(u,v):
    out=np.zeros(28,dtype=object)
    for r,(a,b) in enumerate(PAIRS8):
        out[r]=u[a]*v[b]-u[b]*v[a]
    return out


def omega_int():
    out=np.zeros(56,dtype=object)
    for t,c in { (0,2,6):3, (0,3,4):3, (1,2,5):-3, (1,4,6):3, (1,4,7):3, (3,5,7):3}.items():
        out[T8[t]]=c
    return out


def exterior_jacobian(decomp):
    J=np.zeros((56,96),dtype=object)
    for j in range(4):
        u,v,w=decomp[j]
        for q in range(8):
            e=np.zeros(8,dtype=object); e[q]=1
            J[:,(j*3+0)*8+q]=wedge3(e,v,w)
            J[:,(j*3+1)*8+q]=wedge3(u,e,w)
            J[:,(j*3+2)*8+q]=wedge3(u,v,e)
    return J


def mixed_matrix(decomp):
    M=np.zeros((28,12),dtype=object)
    for j in range(4):
        u,v,w=decomp[j]
        M[:,3*j+0]=wedge2(v,w)
        M[:,3*j+1]=-wedge2(u,w)
        M[:,3*j+2]=wedge2(u,v)
    return M


def rank_mod_obj(A, p):
    A=np.array(A,dtype=object)
    m,n=A.shape
    B=[[int(A[i,j])%p for j in range(n)] for i in range(m)]
    r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if B[i][c]%p:
                piv=i; break
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
    terms,cubes,free_orbits,powers,a0=bilr.build_scheme()
    decomp=[]
    for U,V,W in free_orbits:
        decomp.append(np.array([gl_traceless_to_sl_coords(U), gl_traceless_to_sl_coords(V), gl_traceless_to_sl_coords(W)], dtype=object))
    decomp=np.array(decomp,dtype=object)
    ext=sum((wedge3(*decomp[j]) for j in range(4)), np.zeros(56,dtype=object))
    omega=omega_int()
    diff_scaled=[int(3*ext[i]-omega[i]) for i in range(56)]
    diff_normalized=[int(ext[i]-omega[i]//3) for i in range(56)]
    print('3*sum_wedge - omega nonzero', sum(1 for x in diff_scaled if x))
    print('sum_wedge - omega/3 nonzero', sum(1 for x in diff_normalized if x))

    J=exterior_jacobian(decomp)
    M=mixed_matrix(decomp)
    ranks_J={str(p):rank_mod_obj(J,p) for p in [1000003,65521,32003]}
    ranks_M={str(p):rank_mod_obj(M,p) for p in [1000003,65521,32003]}
    print('exterior Jacobian ranks', ranks_J)
    print('mixed trace ranks', ranks_M)

    # Reuse the exact Koszul computation from the first script.
    cubec=bilr.cube_coeffs(cubes)
    K=bilr.koszul_matrix_from_coeffs(cubec,p=4)
    ranks_K={str(p):bilr.rank_mod_np(K,p) for p in [1000003,1000033,65521,32003]}
    print('residual cube Koszul ranks', ranks_K)

    result={
        'normalization':'unnormalised target omega has coefficients +/-3; a free cyclic 3-orbit contributes 3*(U wedge V wedge W), so the exterior equation is sum_wedge=omega/3',
        'scheme_terms':len(terms), 'cube_count':len(cubes), 'free_cyclic_orbit_count':len(free_orbits),
        'brent_errors': int(np.count_nonzero(bilr.terms_tensor(terms)-bilr.target_tensor_int())),
        'three_sum_wedge_minus_omega_nonzero': sum(1 for x in diff_scaled if x),
        'sum_wedge_minus_omega_over_3_nonzero': sum(1 for x in diff_normalized if x),
        'exterior_jacobian_shape':[56,96],
        'exterior_jacobian_ranks_mod_primes':ranks_J,
        'exterior_fiber_kernel_dim_at_scheme': {q:96-r for q,r in ranks_J.items()},
        'mixed_trace_map_shape':[28,12],
        'mixed_trace_map_ranks_mod_primes':ranks_M,
        'mixed_trace_nullity_at_scheme': {q:12-r for q,r in ranks_M.items()},
        'residual_cubic':'the 11 displayed cubes; diagonal identity tr(M^3)=sum_11 cube^3 + 3 sum_4 orbit products is exact',
        'residual_cube_koszul_matrix_shape':list(K.shape),
        'residual_cube_koszul_ranks_mod_primes':ranks_K,
        'rank_one_koszul_upper':70,
        'residual_waring_rank_lower_bound': math.ceil(min(ranks_K.values())/70),
        'residual_waring_rank_upper_bound_from_displayed_cubes':11,
        'conclusion_for_this_member':'residual Waring rank is exactly 11; deleting one cube from this known cyclic rank-23 scheme cannot give a cyclic rank-22 decomposition without moving in the m=4 exterior fiber',
        'free_orbit_sl3_representatives': decomp.astype(int).tolist(),
    }
    out=OUT/'ballard_cyclic_analysis_v2.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('Saved',out)

if __name__=='__main__':
    main()
