#!/usr/bin/env python3
"""Exact finite-field random search for tau anti subspace rank m0.

For p odd, target L = span{sum_k e_{ik} wedge e_{jk}: (i,j)=(01),(02),(12)}
inside Lambda^2(F_p^9).  For m=5..8, choose random m-dimensional subspaces
K containing L, enumerate all p^m vectors of K, extract decomposable bivectors
(rank-2 skew matrices), and test whether those decomposables span K.  If so,
L is contained in a span of m decomposable bivectors, giving an exact anti-entry
upper bound m0 <= m over F_p.

Failures are random-search evidence only, not lower bounds.
"""
from __future__ import annotations
import itertools, json, time
from pathlib import Path
import numpy as np

SESSION=Path(__file__).resolve().parents[1]
OUT=SESSION/"data"/"transpose_complement"
OUT.mkdir(parents=True, exist_ok=True)
PAIRS=[(i,j) for i in range(9) for j in range(i+1,9)]
PAIR_INDEX={p:i for i,p in enumerate(PAIRS)}
def idx(i,k): return 3*i+k

def mod_inv(a,p): return pow(int(a)%p,p-2,p)
def rref_rank(M,p, return_pivots=False):
    M=np.array(M,dtype=np.int64)%p
    rows,cols=M.shape
    r=0; piv=[]
    for c in range(cols):
        pivrow=None
        for i in range(r,rows):
            if M[i,c]%p:
                pivrow=i; break
        if pivrow is None: continue
        M[[r,pivrow]]=M[[pivrow,r]]
        inv=mod_inv(M[r,c],p)
        M[r]=(M[r]*inv)%p
        for i in range(rows):
            if i!=r and M[i,c]%p:
                M[i]=(M[i]-int(M[i,c])*M[r])%p
        piv.append(c); r+=1
        if r==rows: break
    if return_pivots: return r,piv,M
    return r

def in_span_rank(B, cols, p):
    if len(cols)==0: return 0
    return rref_rank(np.array(cols,dtype=np.int64),p)

def skew_mat(v,p):
    M=np.zeros((9,9),dtype=np.int64)
    for coeff,(i,j) in zip(v,PAIRS):
        M[i,j]=coeff%p; M[j,i]=(-coeff)%p
    return M%p

def is_decomp(v,p):
    if not np.any(np.array(v)%p): return False
    # A bivector is decomposable iff the skew matrix has rank 2 (for nonzero forms).
    return rref_rank(skew_mat(v,p),p)==2

def target_basis(p):
    rows=[]
    for (i,j) in [(0,1),(0,2),(1,2)]:
        v=np.zeros(36,dtype=np.int64)
        for k in range(3):
            a=idx(i,k); b=idx(j,k)
            if a<b: v[PAIR_INDEX[(a,b)]] = (v[PAIR_INDEX[(a,b)]] - 1)%p
            else: v[PAIR_INDEX[(b,a)]] = (v[PAIR_INDEX[(b,a)]] + 1)%p
        rows.append(v%p)
    return np.array(rows,dtype=np.int64)%p

def canonical9(p):
    rows=[]
    for (i,j) in [(0,1),(0,2),(1,2)]:
        for k in range(3):
            v=np.zeros(36,dtype=np.int64)
            a=idx(i,k); b=idx(j,k)
            if a<b: v[PAIR_INDEX[(a,b)]]=1
            else: v[PAIR_INDEX[(b,a)]]=-1
            rows.append(v%p)
    return np.array(rows,dtype=np.int64)%p

def random_complement_vector(rng,p,existing):
    while True:
        v=rng.integers(0,p,36,dtype=np.int64)
        if rref_rank(np.vstack([existing,v]),p)>rref_rank(existing,p):
            return v%p

def enumerate_decomp_span(B,p,limit_store=40):
    m=B.shape[0]
    decomp=[]; span=[]; rank=0; count=0
    # Enumerate projectively: first nonzero coefficient normalized to 1.
    for first in range(m):
        tail_len=m-first-1
        for tail in itertools.product(range(p), repeat=tail_len):
            coeff=np.zeros(m,dtype=np.int64); coeff[first]=1
            if tail_len: coeff[first+1:]=tail
            v=(coeff @ B)%p
            if is_decomp(v,p):
                count+=1
                new_rank=rref_rank(np.array(span+[v.tolist()],dtype=np.int64),p) if span else 1
                if new_rank>rank:
                    span.append(v.tolist()); rank=new_rank
                    if rank==m:
                        return {"decomp_projective_count_lower": count, "decomp_span_rank": rank, "basis": span[:m]}
                elif len(decomp)<limit_store:
                    decomp.append(v.tolist())
    return {"decomp_projective_count": count, "decomp_span_rank": rank, "basis": span}

def try_random(p,m,trials,seed):
    rng=np.random.default_rng(seed)
    L=target_basis(p)
    can=canonical9(p)
    out={"p":p,"m":m,"trials":trials,"success":False,"best_decomp_span_rank":0,"examples_checked":0}
    # For m=9 canonical positive control
    if m==9:
        res=enumerate_decomp_span(can,p)
        out.update({"canonical9":res,"success":res["decomp_span_rank"]>=9})
        return out
    for t in range(trials):
        B=L.copy()
        while B.shape[0]<m:
            v=random_complement_vector(rng,p,B)
            B=np.vstack([B,v])%p
        if rref_rank(B,p)!=m: continue
        res=enumerate_decomp_span(B,p)
        out["examples_checked"]+=1
        out["best_decomp_span_rank"]=max(out["best_decomp_span_rank"], int(res["decomp_span_rank"]))
        if res["decomp_span_rank"]>=m:
            out.update({"success":True,"trial":t,"basis_K":B.tolist(),"decomp_basis":res["basis"],"decomp_projective_count":res.get("decomp_projective_count",res.get("decomp_projective_count_lower"))})
            pth=OUT/f"anti_subspace_p{p}_m{m}_success.json"
            pth.write_text(json.dumps(out,indent=2)+"\n")
            out["success_path"]=str(pth.relative_to(SESSION))
            return out
    return out

def main():
    configs=[]
    for p in [3,5]:
        configs += [(p,5,200),(p,6,200),(p,7,200),(p,8,120)]
        configs += [(p,9,1)]
    allout={"warning":"random finite-field K search; failures are not lower bounds","results":[]}
    t0=time.time()
    for p,m,trials in configs:
        print(f"p={p} m={m} trials={trials}", flush=True)
        res=try_random(p,m,trials,seed=61061+1000*p+37*m)
        print(json.dumps({k:res[k] for k in res if k not in ('basis_K','decomp_basis','canonical9')},indent=2), flush=True)
        allout["results"].append(res)
    allout["elapsed_sec"]=round(time.time()-t0,3)
    path=OUT/"anti_subspace_randomK.json"
    path.write_text(json.dumps(allout,indent=2)+"\n")
    print(f"SAVED {path}")

if __name__=='__main__':
    main()
