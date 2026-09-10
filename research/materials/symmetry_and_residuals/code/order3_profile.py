#!/usr/bin/env python3
r"""Profile corrected diagonal order-3 sandwich action over F2.

This is a setup/probe for the order-3 analogue of the analysis order-7 certificate.
It verifies the action convention, enumerates all rank-one UV point orbits, and
records fixed/nonfixed dimensions and orbit-sum locations.  It does not claim an
exhaustive rank-22 exclusion by itself.
"""
from __future__ import annotations
import json, time
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np
import order7_family_certificate as c

def build_T(): return c.build_T333_flat()
def rowmajor(L,R): return np.kron(L,R.T).astype(np.uint8)&1
def actions(F):
    Fi=c.gf2_inv(F); M9=rowmajor(F.T&1,Fi.T&1); hW=rowmajor(Fi,F); gE=np.kron(M9,M9).astype(np.uint8)&1; return M9,gE,hW
def fixed_coord(v,pivots): return c.fixed_coord(v,pivots)
def span_all(gens): return c.span_all_ints(gens)

def main():
    t0=time.time(); out_dir=Path('data/order3_profile'); out_dir.mkdir(parents=True,exist_ok=True)
    T=build_T(); L=T.T&1; Q=c.quotient_Q(T); Qp=c.right_inverse_Q(Q)
    F3=np.array([[0,1,0],[0,0,1],[1,0,0]],dtype=np.uint8)
    M9,gE,hW=actions(F3); gbar=(Q@gE@Qp)&1
    checks={'gE_T_equals_T_hW':bool(np.array_equal((gE@T)&1,(T@hW)&1)),'gbar_Q_equals_Q_gE':bool(np.array_equal((gbar@Q)&1,(Q@gE)&1)),'orders':{'F3':bool(np.array_equal(c.gf2_matpow(F3,3),np.eye(3,dtype=np.uint8))),'M9':bool(np.array_equal(c.gf2_matpow(M9,3),np.eye(9,dtype=np.uint8))),'gE':bool(np.array_equal(c.gf2_matpow(gE,3),np.eye(81,dtype=np.uint8))),'hW':bool(np.array_equal(c.gf2_matpow(hW,3),np.eye(9,dtype=np.uint8))),'gbar':bool(np.array_equal(c.gf2_matpow(gbar,3),np.eye(72,dtype=np.uint8)))}}
    if not checks['gE_T_equals_T_hW']: raise AssertionError('bad action')
    fixE=c.gf2_nullspace((gE^np.eye(81,dtype=np.uint8))&1); _,fixE_dim,fix_pivots=c.gf2_rref(fixE)
    fixQ_dim=c.gf2_nullspace((gbar^np.eye(72,dtype=np.uint8))&1).shape[0]
    L0=(c.gf2_nullspace((hW^np.eye(9,dtype=np.uint8))&1)@L)&1; L0_basis,L0_dim,_=c.gf2_rref(L0)
    L0_coords=span_all([fixed_coord(v,fix_pivots) for v in L0_basis])
    L0_eq=(c.intersection_dim(L,fixE)==L0_dim and c.gf2_rank(np.vstack([fixE,L0_basis]))==fixE_dim)
    sigma=np.zeros((81,81),dtype=np.uint8); pwr=np.eye(81,dtype=np.uint8)
    for _ in range(3): sigma^=pwr; pwr=(gE@pwr)&1
    sigma_checks={'rank':int(c.gf2_rank(sigma)),'idempotent':bool(np.array_equal((sigma@sigma)&1,sigma)),'image_fixed_rank':int(c.gf2_rank(((gE^np.eye(81,dtype=np.uint8))@sigma)&1)),'image_equals_FixE':bool(c.gf2_rank(sigma)==fixE_dim and c.gf2_rank(((gE^np.eye(81,dtype=np.uint8))@sigma)&1)==0)}
    pts=c.enumerate_rank_one(); fixed,free=c.classify_orbits(gE,pts,3); fixed_pts=pts[fixed]
    fixed_span_rank=c.gf2_rank(fixed_pts); fixed_L_int=c.intersection_dim(fixed_pts,L); fixed_L0_int=c.intersection_dim(fixed_pts,L0_basis)
    fixed_coord_map={fixed_coord(pts[i],fix_pivots):local for local,i in enumerate(fixed)}
    prof=Counter(); sum_loc=Counter(); per_fixed=Counter(); nonzero_L0=0; pplus_nonzero=0
    for orb in free:
        X=pts[orb]; xr=c.gf2_rank(X); sig=np.bitwise_xor.reduce(X,axis=0).astype(np.uint8); assert np.array_equal(sig,(sigma@X[0])&1)
        sc=fixed_coord(sig,fix_pivots); in_L0=sc in L0_coords; in_fixed=sc in fixed_coord_map
        matches=0; nonzero_matches=0
        for pc,local in fixed_coord_map.items():
            if (sc^pc) in L0_coords:
                matches+=1; per_fixed[local]+=1
                if sc^pc: nonzero_matches+=1
        if in_L0 and sc!=0: nonzero_L0+=1
        pplus_nonzero += nonzero_matches
        tag='L0' if in_L0 else ('p_plus_L0' if matches else 'other')
        prof[(xr,tag,int(sc==0),int(in_fixed),matches)] += 1
    # Full-rank-22 skeletons under termwise order-3 and full UV independence.
    skeletons=[]
    for m in range(8):
        f=22-3*m
        if f<0: continue
        max_rank=min(f,fixed_span_rank)+3*m
        if max_rank>=22:
            skeletons.append({'free_orbits':m,'fixed_terms':f,'max_uv_rank_bound':int(max_rank)})
    results={'purpose':'Corrected order-3 diagonal sandwich orbit profile over F2; setup for later finite-family search.','field':'F2','F3_matrix':F3.astype(int).tolist(),'action':checks,'fixed_spaces':{'FixE_dim':int(fixE_dim),'FixE_mod_L_dim':int(fixQ_dim),'L0_dim':int(L0_dim),'L0_equals_L_intersection_FixE':bool(L0_eq),'sigma':sigma_checks},'rank_one_orbits':{'total':int(len(pts)),'fixed_count':int(len(fixed)),'free_orbit_count':int(len(free)),'total_check':int(len(fixed)+3*len(free)),'fixed_span_rank':int(fixed_span_rank),'fixed_span_intersection_L':int(fixed_L_int),'fixed_span_intersection_L0':int(fixed_L0_int),'free_orbit_profile':{str(k):int(v) for k,v in sorted(prof.items())},'orbits_with_nonzero_sigma_in_L0':int(nonzero_L0),'p_plus_L0_nonzero_matches_over_all_p':int(pplus_nonzero),'per_fixed_filtered_count_hist':{str(k):int(v) for k,v in sorted(Counter(per_fixed.values()).items())}},'full_uv_rank22_possible_skeletons':skeletons,'elapsed_sec':time.time()-t0}
    out=out_dir/'order3_profile.json'; out.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps({'fixed_spaces':results['fixed_spaces'],'rank_one_orbits':results['rank_one_orbits'],'full_uv_rank22_possible_skeletons':skeletons,'out':str(out),'elapsed_sec':results['elapsed_sec']},indent=2))
if __name__=='__main__': main()
