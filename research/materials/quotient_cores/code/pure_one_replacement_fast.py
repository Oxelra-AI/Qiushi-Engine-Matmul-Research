#!/usr/bin/env python3
"""analysis: fast exhaustive one-plane replacement of the pure (4,9) core over F3.

This is a corrected and optimized version of pure_one_replacement_search.py.
It precomputes the 9841 tau-fixed projective squares once, then exhaustively tests
all one-plane anti-preserving replacements of the pure row-column anti core.  The
fixed-completion test is the full quotient condition, not just Z(F), so it handles
qdim=3,f=4 correctly.
"""
from __future__ import annotations
import argparse, json, importlib.util, itertools, time
from pathlib import Path
import numpy as np

SCRIPT_DIR=Path(__file__).resolve().parent
WS=SCRIPT_DIR.parent
OUT=WS/'data'/'zF_search'
OUT.mkdir(parents=True,exist_ok=True)

spec=importlib.util.spec_from_file_location('zcore', SCRIPT_DIR/'zF_laderman_anti_span_search.py')
z=importlib.util.module_from_spec(spec); spec.loader.exec_module(z)

def pure_core_pairs(p):
    pairs=[]
    for a in range(3):
        for b in range(a+1,3):
            for k in range(3):
                v=np.zeros(9,dtype=np.int64); w=np.zeros(9,dtype=np.int64)
                v[3*b+k]=1; w[3*a+k]=1
                pairs.append((v%p,w%p))
    return pairs

def span_basis_rows(rows,p):
    B,_=z.row_basis(np.vstack(rows)%p,p)
    return B

def quotient_extension_rows(R,T,p):
    cur=R.copy(); cr=z.rank(cur,p) if cur.size else 0; ext=[]
    for row in T:
        nr=z.rank(np.vstack([cur,row])%p,p) if cur.size else (0 if np.all(row==0) else 1)
        if nr>cr:
            ext.append(row.copy()%p); cur=np.vstack([cur,row])%p if cur.size else row.reshape(1,-1)%p; cr=nr
    return ext

def affine_replacement_betas(R_basis, missing, p):
    d=R_basis.shape[0]; seen=set(); out=[]
    for coeff in itertools.product(range(p), repeat=d):
        beta=missing.copy()%p
        for i,c in enumerate(coeff):
            if c: beta=(beta+c*R_basis[i])%p
        if np.all(beta==0): continue
        first=int(np.nonzero(beta%p)[0][0]); beta=beta*z.inv(beta[first],p)%p
        key=tuple(int(x) for x in beta.tolist())
        if key in seen: continue
        fac=z.factor_decomposable(beta,p)
        if fac is not None:
            seen.add(key); out.append((beta,fac))
    return out

def rref_with_pivots(M,p):
    R,r,piv=z.rref(M,p)
    return R[:r].copy(),piv

def reduce_mod_basis_rows(X,basis_rref,pivots,p):
    X=np.asarray(X,dtype=np.int64)%p; one=False
    if X.ndim==1: X=X.reshape(1,-1); one=True
    Y=X.copy()%p
    for row,col in enumerate(pivots):
        coeff=Y[:,col].copy()%p; nz=np.nonzero(coeff)[0]
        if len(nz): Y[nz,:]=(Y[nz,:]-coeff[nz,None]*basis_rref[row])%p
    free=[c for c in range(Y.shape[1]) if c not in set(pivots)]
    Q=Y[:,free]%p
    return Q[0] if one else Q

def canonical_projective(row,p):
    row=np.asarray(row,dtype=np.int64)%p
    if not np.any(row): return ('ZERO',)
    i=int(np.nonzero(row)[0][0])
    row=row*z.inv(row[i],p)%p
    return tuple(int(x) for x in row.tolist())

def F_from_pairs(p,pairs):
    rows=[]
    for v,w in pairs: rows.extend(z.free_slots_from_pair(v,w,p))
    return np.vstack(rows)%p

def quotient_data_precomputed(p,pairs,L1,Sq):
    F=F_from_pairs(p,pairs); Fb,_=z.row_basis(F,p); Frref,piv=rref_with_pivots(Fb,p)
    T=reduce_mod_basis_rows(L1,Frref,piv,p)
    Trref,Tpiv=rref_with_pivots(T,p); T_rank=Trref.shape[0]
    SqQ=reduce_mod_basis_rows(Sq,Frref,piv,p)
    SqModT=reduce_mod_basis_rows(SqQ,Trref,Tpiv,p)
    rankF=Fb.shape[0]; rankS=z.rank(np.vstack([Fb,L1])%p,p); Fcap=rankF+z.rank(L1,p)-rankS; qdim=rankS-rankF
    return Fb,T,Trref,T_rank,SqQ,SqModT,rankF,rankS,Fcap,qdim

def basis_indices_for_group(qrows,indices,p):
    cur=np.zeros((0,qrows.shape[1]),dtype=np.int64); chosen=[]; cr=0
    for idx in indices:
        row=qrows[idx]
        nr=z.rank(np.vstack([cur,row])%p,p) if cur.size else (0 if np.all(row==0) else 1)
        if nr>cr:
            chosen.append(idx); cur=np.vstack([cur,row])%p if cur.size else row.reshape(1,-1)%p; cr=nr
    return chosen,cur,cr

def row_contains_q(selected_Q,T,p):
    S=selected_Q if selected_Q.size else np.zeros((0,T.shape[1]),dtype=np.int64)
    ok,rS,rST,defect=z.row_contains(S,T,p)
    return ok,rS,rST,defect

def term_BC_from_pairs(p,pairs):
    out=[]
    for v,w in pairs:
        out.append((z.mat_from_vec(v)%p,z.mat_from_vec(z.Pvec(w))%p))
        out.append((z.mat_from_vec(w)%p,z.mat_from_vec(z.Pvec(v))%p))
    return out

def replay_with_fixed(p,pairs,fixed_vectors,L1):
    gens=[]
    for v,w in pairs: gens.extend(z.free_slots_from_pair(v,w,p))
    for x in fixed_vectors: gens.append(z.fixed_slot(x,p))
    ok,rG,rGL,defect=z.row_contains(np.vstack(gens)%p,L1,p)
    us=z.recover_u(gens,L1,p)
    replay_ok=None
    if us is not None:
        terms=[]; BC=term_BC_from_pairs(p,pairs)
        for ell,(B,C) in enumerate(BC): terms.append((us[ell],B,C))
        base=len(BC)
        for j,x in enumerate(fixed_vectors): terms.append((us[base+j], z.mat_from_vec(x)%p, z.mat_from_vec(z.Pvec(x))%p))
        replay_ok=bool(np.array_equal(z.tensor_from_terms(terms,p), z.build_T333(p)))
    return {'contains_L1':bool(ok),'rank_generators':int(rG),'rank_aug_with_L1':int(rGL),'defect':int(defect),'u_recovered':us is not None,'full_T333_replay':replay_ok}

def fixed_completion_test_fast(p,pairs,L1,Xproj,Sq,f_allowed=4,want_replay=False):
    Fb,T,Trref,T_rank,SqQ,SqModT,rankF,rankS,Fcap,qdim=quotient_data_precomputed(p,pairs,L1,Sq)
    res={'rankF':int(rankF),'rankF_plus_L1':int(rankS),'F_cap_L1_dim':int(Fcap),'qdim':int(qdim),'f_allowed':int(f_allowed),'hit':False}
    if qdim>f_allowed:
        res['method']='qdim_exceeds_f'; return res
    zero=np.all(SqModT==0,axis=1); Zidx=np.nonzero(zero)[0]
    Zrank=z.rank(SqQ[Zidx],p) if len(Zidx) else 0
    res['Z_count']=int(len(Zidx)); res['Z_rank']=int(Zrank)
    if qdim==f_allowed:
        contains,_,_,_=row_contains_q(SqQ[Zidx],T,p) if len(Zidx) else (False,0,qdim,qdim)
        res['method']='qdim_equals_f_Z_forced'; res['Z_contains_target']=bool(contains)
        if contains:
            chosen,_,_=basis_indices_for_group(SqQ,Zidx.tolist(),p)
            res['hit']=True; res['chosen_indices']=chosen[:f_allowed]
            if want_replay:
                res['chosen_vectors']=[[int(x) for x in Xproj[i].tolist()] for i in chosen[:f_allowed]]
                res['replay']=replay_with_fixed(p,pairs,[Xproj[i] for i in chosen[:f_allowed]],L1)
        return res
    if qdim==3 and f_allowed==4:
        groups={}
        for i,row in enumerate(SqModT): groups.setdefault(canonical_projective(row,p),[]).append(i)
        hist={}; best=[]
        for key,idxs in groups.items():
            chosen,Qbasis,grank=basis_indices_for_group(SqQ,idxs,p)
            contains,rSel,rAug,defect=row_contains_q(Qbasis,T,p)
            hkey=(len(idxs),grank,defect,contains); hist[str(hkey)]=hist.get(str(hkey),0)+1
            if contains and grank<=f_allowed:
                res['hit']=True; res['method']='q3_f4_group_hit'; res['hit_group_size']=len(idxs); res['hit_group_rank']=int(grank); res['chosen_indices']=chosen[:f_allowed]
                if want_replay:
                    res['chosen_vectors']=[[int(x) for x in Xproj[i].tolist()] for i in chosen[:f_allowed]]
                    res['replay']=replay_with_fixed(p,pairs,[Xproj[i] for i in chosen[:f_allowed]],L1)
                return res
            score=(1 if contains else 0,-defect,grank,len(idxs))
            best.append({'score':[int(score[0]),int(score[1]),int(score[2]),int(score[3])],'group_size':len(idxs),'group_rank':int(grank),'defect':int(defect),'contains_target':bool(contains),'basis_indices':chosen[:5]})
            best=sorted(best,key=lambda x:tuple(x['score']),reverse=True)[:5]
        res['method']='q3_f4_group_by_line'; res['num_groups']=len(groups); res['group_histogram_(size,rank,defect,contains)']=hist; res['best_groups']=best
        return res
    res['method']='q_less_f_case_not_implemented'; return res

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--p',type=int,default=3); ap.add_argument('--time-budget',type=float,default=600)
    args=ap.parse_args(); p=args.p; t0=time.time()
    L1=z.build_L1(p); Xproj,Sq=z.precompute_fixed_squares(p); Lanti=z.anti_target_wedge(p); gl2s=z.GL2_list(p)
    core=pure_core_pairs(p); base=fixed_completion_test_fast(p,core,L1,Xproj,Sq,4)
    out={'field':f'F_{p}','time_budget_sec':args.time_budget,'projective_fixed_vectors_count':int(Xproj.shape[0]),'base_pure_core':base,'deletions':[],'hits':[], 'interpretation':'Complete one-plane anti-preserving replacement of the pure (4,9) core using the full q=3,f=4 fixed-square quotient condition.'}
    total=0; timed_out=False
    for rem in range(9):
        betas=[z.wedge_vec(v,w,p) for v,w in core]
        retained=[betas[i] for i in range(9) if i!=rem]
        R=span_basis_rows(retained,p); ext=quotient_extension_rows(R,Lanti,p)
        drec={'removed_index':rem,'retained_anti_rank':int(R.shape[0]),'Lanti_extension_dim':len(ext)}
        if len(ext)!=1:
            drec['skipped']='extension_dim_not_one'; out['deletions'].append(drec); continue
        repl=affine_replacement_betas(R,ext[0],p); drec['decomposable_replacements_in_coset']=len(repl)
        hist={}; best=[]
        for bi,(beta,fac) in enumerate(repl):
            for g2 in gl2s:
                if time.time()-t0>args.time_budget:
                    timed_out=True; break
                pairs=list(core); pairs[rem]=z.apply_GL2(fac,g2,p)
                rec=fixed_completion_test_fast(p,pairs,L1,Xproj,Sq,4,want_replay=False)
                total+=1
                key=(rec['F_cap_L1_dim'],rec['qdim'],rec.get('Z_count',-1),rec.get('Z_rank',-1),rec.get('hit',False),rec.get('method',''))
                hist[str(key)]=hist.get(str(key),0)+1
                score=(1 if rec.get('hit') else 0,rec['F_cap_L1_dim'],-rec['qdim'],rec.get('Z_rank',0),rec.get('Z_count',0))
                comp={'score':[int(x) for x in score],'replacement_number':bi,'GL2':[int(x) for x in g2[:4]],'det':int(g2[4]),'record':{k:v for k,v in rec.items() if k not in ('group_histogram_(size,rank,defect,contains)','best_groups','chosen_vectors','replay')}}
                if 'best_groups' in rec: comp['best_groups']=rec['best_groups']
                best.append(comp); best=sorted(best,key=lambda x:tuple(x['score']),reverse=True)[:10]
                if rec.get('hit'):
                    rec2=fixed_completion_test_fast(p,pairs,L1,Xproj,Sq,4,want_replay=True)
                    hit={'removed_index':rem,'replacement_number':bi,'GL2':[int(x) for x in g2[:4]],'record':rec2,'replacement_pair':{'v':[int(x) for x in pairs[rem][0].tolist()],'w':[int(x) for x in pairs[rem][1].tolist()]}}
                    out['hits'].append(hit)
                    if rec2.get('replay',{}).get('full_T333_replay'):
                        drec['histogram']=hist; drec['best']=best; out['deletions'].append(drec); out['total_configurations_tested']=total; out['timed_out']=timed_out
                        path=OUT/f'pure_one_replacement_fast_F{p}.json'; path.write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2)); print(f'SAVED {path}'); return
            if timed_out: break
        drec['histogram']=hist; drec['best']=best; out['deletions'].append(drec)
        if timed_out: break
    out['total_configurations_tested']=total; out['timed_out']=timed_out
    path=OUT/f'pure_one_replacement_fast_F{p}.json'; path.write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2)); print(f'SAVED {path}')
if __name__=='__main__': main()
