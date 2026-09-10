#!/usr/bin/env python3
"""analysis: exact small-f fixed completion in the quotient V/F over F_p.

For a fixed free-orbit span F, a rank-22 skeleton with f fixed tau-terms needs
f projective tau-fixed rank-one squares x P(x) whose images in V/F span the image
of L1.  When q=dim((F+L1)/F) equals f this reduces to Z(F) = squares inside F+L1.
When q<f, the individual squares need not lie in F+L1.  This script performs the
exact quotient test for q=3,f=4 by grouping fixed-square images inside each
4-plane containing the target 3-plane.

It currently analyzes the pure row-column anti core (m=9,f=4) and the transported
Laderman core (m=8,f=6) as controls.  The pure core is important because the
older Z(F)-only test is too strict there.
"""
from __future__ import annotations
import argparse, json, importlib.util
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "zF_search"
OUT.mkdir(parents=True, exist_ok=True)

spec = importlib.util.spec_from_file_location("zcore", SCRIPT_DIR / "zF_laderman_anti_span_search.py")
z = importlib.util.module_from_spec(spec)
spec.loader.exec_module(z)

def pure_core_pairs(p):
    pairs=[]
    for a in range(3):
        for b in range(a+1,3):
            for k in range(3):
                v=np.zeros(9,dtype=np.int64); w=np.zeros(9,dtype=np.int64)
                v[3*b+k]=1; w[3*a+k]=1
                pairs.append((v%p,w%p))
    return pairs

def F_from_pairs(p, pairs):
    rows=[]
    for v,w in pairs:
        rows.extend(z.free_slots_from_pair(v,w,p))
    return np.vstack(rows)%p

def rref_with_pivots(M,p):
    R,r,piv=z.rref(M,p)
    return R[:r].copy(),piv

def reduce_mod_basis_rows(X, basis_rref, pivots, p):
    X=np.asarray(X,dtype=np.int64)%p
    one=False
    if X.ndim==1:
        X=X.reshape(1,-1); one=True
    Y=X.copy()%p
    for row,col in enumerate(pivots):
        coeff=Y[:,col].copy()%p
        nz=np.nonzero(coeff)[0]
        if len(nz):
            Y[nz,:]=(Y[nz,:]-coeff[nz,None]*basis_rref[row])%p
    free=[c for c in range(Y.shape[1]) if c not in set(pivots)]
    Q=Y[:,free]%p
    return Q[0] if one else Q

def canonical_projective(v,p):
    v=np.asarray(v,dtype=np.int64)%p
    if not np.any(v): return ('ZERO',)
    i=int(np.nonzero(v)[0][0]); v=v*z.inv(v[i],p)%p
    return tuple(int(x) for x in v.tolist())

def quotient_data(p,pairs):
    L1=z.build_L1(p); Xproj,Sq=z.precompute_fixed_squares(p)
    F=F_from_pairs(p,pairs); Fb,_=z.row_basis(F,p); Frref,piv=rref_with_pivots(Fb,p)
    T=reduce_mod_basis_rows(L1,Frref,piv,p)
    Trref,Tpiv=rref_with_pivots(T,p)
    T_rank=Trref.shape[0]
    SqQ=reduce_mod_basis_rows(Sq,Frref,piv,p)
    Sq_mod_T=reduce_mod_basis_rows(SqQ,Trref,Tpiv,p)
    return L1,Xproj,Sq,Fb,T,Trref,T_rank,SqQ,Sq_mod_T

def row_contains_q(selected_Q,T,p):
    if len(selected_Q)==0:
        S=np.zeros((0,T.shape[1]),dtype=np.int64)
    else:
        S=np.vstack(selected_Q)%p
    ok,rS,rST,defect=z.row_contains(S,T,p)
    return ok,rS,rST,defect

def basis_indices_for_group(qrows, indices, p):
    cur=np.zeros((0,qrows.shape[1]),dtype=np.int64); chosen=[]; cr=0
    for idx in indices:
        row=qrows[idx]
        nr=z.rank(np.vstack([cur,row])%p,p) if cur.size else (0 if np.all(row==0) else 1)
        if nr>cr:
            chosen.append(idx); cur=np.vstack([cur,row])%p if cur.size else row.reshape(1,-1)%p; cr=nr
    return chosen,cur,cr

def analyze_core(name,p,pairs,f_allowed):
    L1,Xproj,Sq,Fb,T,Trref,T_rank,SqQ,Sq_mod_T=quotient_data(p,pairs)
    rankF=Fb.shape[0]; rankS=z.rank(np.vstack([Fb,L1])%p,p); Fcap=rankF+z.rank(L1,p)-rankS; qdim=rankS-rankF
    # Direct Z(F) count for comparison: fixed squares in target subspace exactly.
    zero_mod_T=np.all(Sq_mod_T==0,axis=1)
    Z_idx=np.nonzero(zero_mod_T)[0]
    Zrank=z.rank(SqQ[Z_idx],p) if len(Z_idx) else 0
    Z_contains,_,_,_=row_contains_q(SqQ[Z_idx],T,p) if len(Z_idx) else (False,0,T_rank,T_rank)
    result={'core':name,'m':len(pairs),'f_allowed':f_allowed,'rankF':int(rankF),'rankF_plus_L1':int(rankS),'F_cap_L1_dim':int(Fcap),'quotient_target_dim':int(qdim),'target_rank_check':int(T_rank),'Z_count':int(len(Z_idx)),'Z_rank_in_VmodF':int(Zrank),'Z_contains_target':bool(Z_contains),'general_completion_hit':False}
    # If qdim==f, Z is necessary and sufficient.
    if qdim==f_allowed:
        result['method']='qdim_equals_f_so_Z_is_forced'
        if Z_contains:
            chosen,_,_=basis_indices_for_group(SqQ,Z_idx.tolist(),p)
            result['general_completion_hit']=True; result['chosen_indices']=chosen[:f_allowed]; result['chosen_vectors']=[[int(x) for x in Xproj[i].tolist()] for i in chosen[:f_allowed]]
        return result
    if qdim>f_allowed:
        result['method']='target_dimension_exceeds_number_of_fixed_terms'
        return result
    if qdim==3 and f_allowed==4:
        # Group by projective image modulo target; each group lies in target + one line.
        groups={}
        for i,key in enumerate(canonical_projective(row,p) for row in Sq_mod_T):
            groups.setdefault(key,[]).append(i)
        best=[]; hit=None
        for key,idxs in groups.items():
            chosen,Qbasis,grank=basis_indices_for_group(SqQ,idxs,p)
            contains,rSel,rAug,defect=row_contains_q(Qbasis,T,p)
            rec={'key':key if key==('ZERO',) else list(key),'group_size':len(idxs),'group_rank':int(grank),'contains_target':bool(contains),'defect':int(defect),'basis_indices':chosen[:6]}
            if contains and grank<=f_allowed:
                hit=rec; break
            score=(1 if contains else 0,-defect,grank,len(idxs))
            rec['score']=[int(score[0]),int(score[1]),int(score[2]),int(score[3])]
            best.append(rec); best=sorted(best,key=lambda x:tuple(x['score']),reverse=True)[:12]
        result['method']='group_by_line_mod_target_for_q3_f4'
        result['num_groups_mod_target_projective']=len(groups)
        result['best_groups']=best
        if hit is not None:
            chosen=hit['basis_indices'][:f_allowed]
            # Verify direct containment in original ambient space.
            selected=Sq[chosen]
            ok,rG,rGL,defect=z.row_contains(np.vstack([Fb,selected])%p,L1,p)
            result['general_completion_hit']=bool(ok)
            result['hit_group']=hit
            result['chosen_indices']=chosen
            result['chosen_vectors']=[[int(x) for x in Xproj[i].tolist()] for i in chosen]
            result['direct_containment']={'contains_L1':bool(ok),'rank_F_plus_selected':int(rG),'rank_aug_with_L1':int(rGL),'defect':int(defect),'num_fixed_used':len(chosen)}
        return result
    result['method']='general_case_not_implemented_in_this_exact_group_script'
    return result

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--p',type=int,default=3)
    args=ap.parse_args(); p=args.p
    lad_pairs,_,delta,R=z.laderman_free_pairs_vectors(p)
    pure=pure_core_pairs(p)
    out={'field':f'F_{p}','scaled_transport_delta':int(delta),'scaled_transport_R_columns':R.astype(int).tolist(),'analyses':[analyze_core('transported_laderman_m8',p,lad_pairs,6),analyze_core('pure_row_column_m9',p,pure,4)],'interpretation':'This corrects the Z-only test when qdim<f. For qdim=f, fixed squares must lie in F+L1; for qdim=3,f=4, a fourth fixed square may lie outside F+L1, so fixed-square images are grouped by their line modulo the target quotient.'}
    path=OUT/f'fixed_completion_group_search_F{p}.json'; path.write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2)); print(f'SAVED {path}')
if __name__=='__main__': main()
