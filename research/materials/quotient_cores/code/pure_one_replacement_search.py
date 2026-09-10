#!/usr/bin/env python3
"""analysis: one-plane anti-preserving replacements of the pure (4,9) core.

The pure row-column core has m=9, qdim=3, and no four fixed squares complete it
over F3.  This script changes one free plane at a time while preserving the exact
anti containment L_anti <= span{v_j∧w_j}.  For each replacement it computes the
full fixed-term quotient condition for the (4,9) rank-22 skeleton.

Anti preservation is enforced linearly.  If R is the span of the eight retained
bivectors and dim((R+L_anti)/R)=1, every replacement bivector must lie in an affine
coset t+R.  Over F3 this is only 3^8 points per deletion; we test which are
decomposable, factor them, vary the GL2 basis on the plane, and then run the exact
fixed-completion quotient test.  A hit recovers A-factors and replays all 729 Brent
coordinates.
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
spec2=importlib.util.spec_from_file_location('gcore', SCRIPT_DIR/'fixed_completion_group_search.py')
g=importlib.util.module_from_spec(spec2); spec2.loader.exec_module(g)

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
    # beta = missing + sum c_i R_i, canonical projective normalized, decomposable.
    d=R_basis.shape[0]
    seen=set(); out=[]
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

def term_BC_from_pairs(p,pairs):
    out=[]
    for v,w in pairs:
        out.append((z.mat_from_vec(v)%p, z.mat_from_vec(z.Pvec(w))%p))
        out.append((z.mat_from_vec(w)%p, z.mat_from_vec(z.Pvec(v))%p))
    return out

def replay_with_fixed(p,pairs,fixed_vectors):
    L1=z.build_L1(p)
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

def fixed_completion_test(p,pairs,f_allowed=4):
    L1,Xproj,Sq,Fb,T,Trref,T_rank,SqQ,Sq_mod_T=g.quotient_data(p,pairs)
    rankF=Fb.shape[0]; rankS=z.rank(np.vstack([Fb,L1])%p,p); Fcap=rankF+z.rank(L1,p)-rankS; qdim=rankS-rankF
    res={'rankF':int(rankF),'rankF_plus_L1':int(rankS),'F_cap_L1_dim':int(Fcap),'qdim':int(qdim),'f_allowed':int(f_allowed),'hit':False}
    if qdim>f_allowed:
        res['method']='qdim_exceeds_f'; return res
    zero=np.all(Sq_mod_T==0,axis=1); Zidx=np.nonzero(zero)[0]
    if len(Zidx): Zrank=z.rank(SqQ[Zidx],p)
    else: Zrank=0
    res['Z_count']=int(len(Zidx)); res['Z_rank']=int(Zrank)
    if qdim==f_allowed:
        contains,_,_,_=g.row_contains_q(SqQ[Zidx],T,p) if len(Zidx) else (False,0,qdim,qdim)
        res['method']='qdim_equals_f_Z_forced'; res['Z_contains_target']=bool(contains)
        if contains:
            chosen,_,_=g.basis_indices_for_group(SqQ,Zidx.tolist(),p)
            fixed=[Xproj[i] for i in chosen[:f_allowed]]
            res['hit']=True; res['chosen_indices']=chosen[:f_allowed]; res['replay']=replay_with_fixed(p,pairs,fixed)
        return res
    if qdim==3 and f_allowed==4:
        groups={}
        for i,row in enumerate(Sq_mod_T):
            key=g.canonical_projective(row,p)
            groups.setdefault(key,[]).append(i)
        best=[]
        for key,idxs in groups.items():
            chosen,Qbasis,grank=g.basis_indices_for_group(SqQ,idxs,p)
            contains,rSel,rAug,defect=g.row_contains_q(Qbasis,T,p)
            rec={'key':key if key==('ZERO',) else list(key),'group_size':len(idxs),'group_rank':int(grank),'contains_target':bool(contains),'defect':int(defect),'basis_indices':chosen[:5]}
            score=(1 if contains else 0,-defect,grank,len(idxs))
            rec['score']=[int(score[0]),int(score[1]),int(score[2]),int(score[3])]
            if contains and grank<=f_allowed:
                fixed=[Xproj[i] for i in chosen[:f_allowed]]
                res['hit']=True; res['method']='q3_f4_group_hit'; res['hit_group']=rec; res['chosen_indices']=chosen[:f_allowed]; res['replay']=replay_with_fixed(p,pairs,fixed)
                return res
            best.append(rec); best=sorted(best,key=lambda x:tuple(x['score']),reverse=True)[:5]
        res['method']='q3_f4_group_by_line'; res['num_groups']=len(groups); res['best_groups']=best
        return res
    res['method']='unimplemented_q_less_f_case'; return res

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--p',type=int,default=3); ap.add_argument('--max-gl2-per-beta',type=int,default=48); ap.add_argument('--time-budget',type=float,default=600)
    args=ap.parse_args(); p=args.p; t0=time.time()
    core=pure_core_pairs(p); Lanti=z.anti_target_wedge(p); gl2s=z.GL2_list(p)[:args.max_gl2_per_beta]
    base=fixed_completion_test(p,core,4)
    out={'field':f'F_{p}','time_budget_sec':args.time_budget,'base_pure_core':base,'deletions':[],'hits':[], 'interpretation':'One free plane of the pure (4,9) anti core is replaced by every decomposable bivector in the affine coset preserving L_anti, with GL2 basis variations and exact fixed-completion tests.'}
    total_configs=0; timed_out=False
    for rem in range(9):
        betas=[z.wedge_vec(v,w,p) for v,w in core]
        retained=[betas[i] for i in range(9) if i!=rem]
        R=span_basis_rows(retained,p)
        ext=quotient_extension_rows(R,Lanti,p)
        drec={'removed_index':rem,'removed_pair':[int(x) for x in core[rem][0].tolist()]+[int(x) for x in core[rem][1].tolist()],'retained_anti_rank':int(R.shape[0]),'Lanti_extension_dim':len(ext)}
        if len(ext)!=1:
            drec['skipped']='one replacement cannot repair this quotient dimension' if len(ext)>1 else 'Lanti already contained; broad case skipped'
            out['deletions'].append(drec); continue
        repl=affine_replacement_betas(R,ext[0],p)
        drec['decomposable_replacements_in_coset']=len(repl)
        hist={}; best=[]
        for bi,(beta,fac) in enumerate(repl):
            for gi,g2 in enumerate(gl2s):
                if time.time()-t0>args.time_budget:
                    timed_out=True; break
                newpair=z.apply_GL2(fac,g2,p)
                pairs=list(core); pairs[rem]=newpair
                rec=fixed_completion_test(p,pairs,4)
                total_configs+=1
                key=(rec['F_cap_L1_dim'],rec['qdim'],rec.get('Z_count',-1),rec.get('Z_rank',-1),rec.get('hit',False))
                hist[str(key)]=hist.get(str(key),0)+1
                score=(1 if rec.get('hit') else 0, rec['F_cap_L1_dim'], -rec['qdim'], rec.get('Z_rank',0), rec.get('Z_count',0))
                comp={'score':[int(x) for x in score],'replacement_number':bi,'GL2':[int(x) for x in g2[:4]],'det':int(g2[4]),'record':{k:v for k,v in rec.items() if k not in ('replay','best_groups','hit_group')},'beta':[int(x) for x in beta.tolist()]}
                if 'best_groups' in rec: comp['best_groups']=rec['best_groups']
                best.append(comp); best=sorted(best,key=lambda x:tuple(x['score']),reverse=True)[:10]
                if rec.get('hit'):
                    hit={'removed_index':rem,'replacement_number':bi,'GL2':[int(x) for x in g2[:4]],'record':rec,'pair':{'v':[int(x) for x in newpair[0].tolist()],'w':[int(x) for x in newpair[1].tolist()]}}
                    out['hits'].append(hit)
                    if rec.get('replay',{}).get('full_T333_replay'):
                        drec['histogram']=hist; drec['best']=best; out['deletions'].append(drec); out['total_configurations_tested']=total_configs; out['timed_out']=timed_out
                        path=OUT/f'pure_one_replacement_search_F{p}.json'; path.write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2)); print(f'SAVED {path}'); return
            if timed_out: break
        drec['histogram']=hist; drec['best']=best; out['deletions'].append(drec)
        if timed_out: break
    out['total_configurations_tested']=total_configs; out['timed_out']=timed_out
    path=OUT/f'pure_one_replacement_search_F{p}.json'; path.write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2)); print(f'SAVED {path}')
if __name__=='__main__': main()
