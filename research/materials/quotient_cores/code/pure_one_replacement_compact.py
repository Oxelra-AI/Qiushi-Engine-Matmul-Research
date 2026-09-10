#!/usr/bin/env python3
"""analysis compact completion of the pure-core one-plane replacement search over F3.

This completes the exact one-plane anti-preserving replacement test without writing
large per-configuration records.  It uses the full fixed-square quotient condition
for qdim=3,f=4: four fixed square images span the target iff a projective class
modulo the target contains rows whose span contains the target.
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

def rref_with_pivots(M,p):
    R,r,piv=z.rref(M,p); return R[:r].copy(),piv

def reduce_mod_basis_rows(X,basis,pivots,p):
    X=np.asarray(X,dtype=np.int64)%p
    if X.ndim==1: X=X.reshape(1,-1)
    Y=X.copy()%p
    for row,col in enumerate(pivots):
        coeff=Y[:,col].copy()%p; nz=np.nonzero(coeff)[0]
        if len(nz): Y[nz,:]=(Y[nz,:]-coeff[nz,None]*basis[row])%p
    free=[c for c in range(Y.shape[1]) if c not in set(pivots)]
    return Y[:,free]%p

def canonical(row,p):
    row=np.asarray(row,dtype=np.int64)%p
    if not np.any(row): return ('ZERO',)
    i=int(np.nonzero(row)[0][0]); row=row*z.inv(row[i],p)%p
    return tuple(int(x) for x in row.tolist())

def F_from_pairs(p,pairs):
    rows=[]
    for v,w in pairs: rows.extend(z.free_slots_from_pair(v,w,p))
    return np.vstack(rows)%p

def span_basis(rows,p):
    B,_=z.row_basis(np.vstack(rows)%p,p); return B

def extension_rows(R,T,p):
    cur=R.copy(); cr=z.rank(cur,p) if cur.size else 0; ext=[]
    for row in T:
        nr=z.rank(np.vstack([cur,row])%p,p) if cur.size else (0 if np.all(row==0) else 1)
        if nr>cr:
            ext.append(row.copy()%p); cur=np.vstack([cur,row])%p if cur.size else row.reshape(1,-1)%p; cr=nr
    return ext

def affine_decomposable_replacements(R,missing,p):
    d=R.shape[0]; seen=set(); out=[]
    for coeff in itertools.product(range(p), repeat=d):
        beta=missing.copy()%p
        for i,c in enumerate(coeff):
            if c: beta=(beta+c*R[i])%p
        if np.all(beta==0): continue
        first=int(np.nonzero(beta)[0][0]); beta=beta*z.inv(beta[first],p)%p
        key=tuple(int(x) for x in beta.tolist())
        if key in seen: continue
        fac=z.factor_decomposable(beta,p)
        if fac is not None:
            seen.add(key); out.append((beta,fac))
    return out

def row_contains_q(Q,T,p):
    if Q.size==0: Q=np.zeros((0,T.shape[1]),dtype=np.int64)
    ok,rQ,rQT,defect=z.row_contains(Q,T,p); return ok,rQ,rQT,defect

def quotient_test(p,pairs,L1,Sq,f_allowed=4):
    F=F_from_pairs(p,pairs); Fb,_=z.row_basis(F,p); Frref,Fpiv=rref_with_pivots(Fb,p)
    T=reduce_mod_basis_rows(L1,Frref,Fpiv,p); Trref,Tpiv=rref_with_pivots(T,p); qdim=Trref.shape[0]
    rankF=Fb.shape[0]; rankS=z.rank(np.vstack([Fb,L1])%p,p); Fcap=rankF+z.rank(L1,p)-rankS
    base={'rankF':int(rankF),'rankF_plus_L1':int(rankS),'Fcap':int(Fcap),'qdim':int(qdim)}
    if qdim>f_allowed:
        base.update({'hit':False,'mode':'qdim>f'}); return base
    SqQ=reduce_mod_basis_rows(Sq,Frref,Fpiv,p); SqModT=reduce_mod_basis_rows(SqQ,Trref,Tpiv,p)
    if qdim==f_allowed:
        mask=np.all(SqModT==0,axis=1); idx=np.nonzero(mask)[0]
        qr=z.rank(SqQ[idx],p) if len(idx) else 0
        contains=False
        if len(idx): contains=row_contains_q(SqQ[idx],T,p)[0]
        base.update({'mode':'Z-forced','Z_count':int(len(idx)),'Z_rank':int(qr),'hit':bool(contains)})
        return base
    if qdim==3 and f_allowed==4:
        groups={}; sizes={}
        # Count groups first.
        for i,row in enumerate(SqModT):
            key=canonical(row,p); groups.setdefault(key,[]).append(i)
        possible_groups=0; best_defect=3; best_rank=0; best_size=0
        for key,idx in groups.items():
            # A group of fewer than 3 rows cannot contain a 3-dimensional target.
            if len(idx)<3: continue
            possible_groups+=1
            Q=SqQ[idx]
            qrank=z.rank(Q,p)
            best_rank=max(best_rank,int(qrank)); best_size=max(best_size,len(idx))
            contains,rQ,rQT,defect=row_contains_q(Q,T,p)
            best_defect=min(best_defect,int(defect))
            if contains and rQ<=f_allowed:
                base.update({'mode':'q3f4-group','num_groups':len(groups),'large_groups':possible_groups,'hit':True,'hit_group_size':len(idx),'hit_group_rank':int(rQ)})
                return base
        base.update({'mode':'q3f4-group','num_groups':len(groups),'large_groups':possible_groups,'best_group_defect':int(best_defect),'best_group_rank':int(best_rank),'best_group_size':int(best_size),'hit':False})
        return base
    base.update({'hit':False,'mode':'unimplemented'}); return base

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--p',type=int,default=3); ap.add_argument('--time-budget',type=float,default=1500)
    args=ap.parse_args(); p=args.p; t0=time.time()
    L1=z.build_L1(p); X,Sq=z.precompute_fixed_squares(p); Lanti=z.anti_target_wedge(p); gl2=z.GL2_list(p)
    core=pure_core_pairs(p); base=quotient_test(p,core,L1,Sq,4)
    out={'field':f'F_{p}','time_budget_sec':args.time_budget,'base':base,'deletions':[],'hits':[],'interpretation':'Exact one-plane anti-preserving replacement search for the pure m=9 core; compact output.'}
    total=0; timed=False
    for rem in range(9):
        betas=[z.wedge_vec(v,w,p) for v,w in core]
        retained=[betas[i] for i in range(9) if i!=rem]
        R=span_basis(retained,p); ext=extension_rows(R,Lanti,p)
        d={'removed_index':rem,'retained_anti_rank':int(R.shape[0]),'Lanti_extension_dim':len(ext),'hist':{}}
        if len(ext)!=1:
            d['skipped']=True; out['deletions'].append(d); continue
        repl=affine_decomposable_replacements(R,ext[0],p); d['decomposable_replacements_in_coset']=len(repl)
        for bi,(beta,fac) in enumerate(repl):
            for gg in gl2:
                if time.time()-t0>args.time_budget:
                    timed=True; break
                pairs=list(core); pairs[rem]=z.apply_GL2(fac,gg,p)
                rec=quotient_test(p,pairs,L1,Sq,4); total+=1
                key=(rec['Fcap'],rec['qdim'],rec.get('Z_count',-1),rec.get('Z_rank',-1),rec.get('mode'),rec.get('hit'))
                d['hist'][str(key)]=d['hist'].get(str(key),0)+1
                if rec.get('hit'):
                    out['hits'].append({'removed_index':rem,'replacement_index':bi,'GL2':[int(x) for x in gg[:4]],'record':rec,'replacement_beta':[int(x) for x in beta.tolist()]})
            if timed: break
        out['deletions'].append(d)
        if timed: break
    out['total_configurations_tested']=total; out['timed_out']=timed
    path=OUT/f'pure_one_replacement_compact_F{p}.json'; path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2)); print(f'SAVED {path}')
if __name__=='__main__': main()
