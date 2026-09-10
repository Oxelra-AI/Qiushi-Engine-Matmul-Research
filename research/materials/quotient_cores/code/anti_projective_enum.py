#!/usr/bin/env python3
"""analysis: projective decomposable-bivector enumeration over F3 for L_anti.

Enumerates points of G(2,9)(F3) in reduced-row-echelon 2-plane form.  For each
plane <p,q>, compute eta=p∧q in P(Lambda^2 F3^9) and its quotient by the target
anti plane L.  This builds a reusable finite-field oracle for the exact anti
problem:
    m0 <= m iff there are m decomposable bivectors whose span contains L.
Equivalently, their quotient images have rank at most m-3 and the target rows
are recovered in the original span.

This script performs bounded enumeration/sampling diagnostics and writes compact
hash/count data.  Full exhaustive m=7/8 set cover is a larger task.
"""
from __future__ import annotations
import argparse, json, time, hashlib, random
from pathlib import Path
from collections import Counter, defaultdict
import numpy as np

P=3
SESSION=Path(__file__).resolve().parents[1]
OUT=SESSION/'data'/'anti_exact'
OUT.mkdir(parents=True,exist_ok=True)

def idx(i,k): return 3*i+k

def inv(a): return 1 if int(a)%P==1 else 2

def canon_vec(v):
    v=np.asarray(v,dtype=np.int8)%P
    if not np.any(v): return None
    w=v.copy()
    for x in w:
        if x%P:
            return tuple(int(y) for y in (w*inv(x))%P)
    return None

def rref_rows(M):
    M=np.array(M,dtype=np.int8)%P
    rows,cols=M.shape; r=0; piv=[]
    for c in range(cols):
        pivrow=None
        for i in range(r,rows):
            if M[i,c]%P: pivrow=i; break
        if pivrow is None: continue
        if pivrow!=r: M[[r,pivrow]]=M[[pivrow,r]]
        M[r]=(M[r]*inv(M[r,c]))%P
        for i in range(rows):
            if i!=r and M[i,c]%P:
                M[i]=(M[i]-int(M[i,c])*M[r])%P
        piv.append(c); r+=1
        if r==rows: break
    return M[:r].copy(),piv

def rank_mod(M): return len(rref_rows(M)[1])

def wedge_vec(p,q):
    v=np.zeros(36,dtype=np.int8); t=0
    for i in range(9):
        for j in range(i+1,9):
            v[t]=(int(p[i])*int(q[j])-int(p[j])*int(q[i]))%P; t+=1
    return v%P

def target_rows():
    T=np.zeros((3,36),dtype=np.int8); pairs=[(i,j) for i in range(9) for j in range(i+1,9)]; pi={p:i for i,p in enumerate(pairs)}
    for r,(a,b) in enumerate([(0,1),(0,2),(1,2)]):
        for k in range(3):
            i=idx(a,k); j=idx(b,k)
            if i<j: T[r,pi[(i,j)]]-=1
            else: T[r,pi[(j,i)]]+=1
    return T%P
L=target_rows()
L_rref,L_piv=rref_rows(L)
nonpiv=[i for i in range(36) if i not in L_piv]

def quotient_vec(v):
    # Reduce v modulo row span of L_rref and return non-pivot coordinates.
    w=np.asarray(v,dtype=np.int8).copy()%P
    for row,piv in enumerate(L_piv):
        if w[piv]%P:
            w=(w-int(w[piv])*L_rref[row])%P
    return tuple(int(x) for x in w[nonpiv]%P)

def solve_coords(etas):
    # Return true iff L rows lie in row span of etas.
    E=np.array(etas,dtype=np.int8)%P
    return rank_mod(E)==rank_mod(np.vstack([E,L]))

def canonical_pairs():
    out=[]
    for a,b in [(0,1),(0,2),(1,2)]:
        for k in range(3):
            p=np.zeros(9,dtype=np.int8); q=np.zeros(9,dtype=np.int8)
            p[idx(a,k)]=1; q[idx(b,k)]=1
            out.append((p,q))
    return out

def enumerate_rref_2planes(limit=None, sample_mod=1):
    """Yield RREF bases for 2-planes in F3^9. Pivots i<j; free entries constrained."""
    count=0
    # RREF rows have pivots i<j. Row0 pivot i, row1 pivot j, entries before pivots zero,
    # pivot columns unit, row0 has zero in column j. Free columns c not pivots and c>i for row0,
    # c>j for row1; row0 free also for c>i,c!=j; row1 free c>j.
    for i in range(9):
        for j in range(i+1,9):
            row0=np.zeros(9,dtype=np.int8); row1=np.zeros(9,dtype=np.int8)
            row0[i]=1; row1[j]=1
            free0=[c for c in range(i+1,9) if c!=j]
            free1=[c for c in range(j+1,9)]
            n=len(free0)+len(free1)
            total=3**n
            for code in range(total):
                if sample_mod>1 and (code % sample_mod)!=0:
                    continue
                x=code; r0=row0.copy(); r1=row1.copy()
                for c in free0:
                    r0[c]=x%3; x//=3
                for c in free1:
                    r1[c]=x%3; x//=3
                count+=1
                yield r0,r1
                if limit is not None and count>=limit:
                    return

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--limit',type=int,default=0,help='0 means exhaustive')
    ap.add_argument('--sample-mod',type=int,default=1)
    ap.add_argument('--reservoir',type=int,default=20000)
    ap.add_argument('--seed',type=int,default=6412)
    args=ap.parse_args()
    limit=None if args.limit==0 else args.limit
    rng=random.Random(args.seed)
    t0=time.time(); total=0; unique_eta=set(); unique_q=set(); zero_q=0
    q_hist=Counter(); reservoir=[]; sha=hashlib.sha256()
    rankL=rank_mod(L)
    can_etas=[wedge_vec(p,q) for p,q in canonical_pairs()]
    can_q=[quotient_vec(e) for e in can_etas]
    for p,q in enumerate_rref_2planes(limit=limit,sample_mod=args.sample_mod):
        eta=wedge_vec(p,q); ce=canon_vec(eta)
        if ce is None: continue
        total+=1; unique_eta.add(ce)
        qv=quotient_vec(eta); cq=canon_vec(np.array(qv,dtype=np.int8))
        if cq is None:
            zero_q+=1
        else:
            unique_q.add(cq); q_hist[sum(1 for x in cq if x)] += 1
        if len(reservoir)<args.reservoir:
            reservoir.append((p.copy(),q.copy(),eta.copy(),qv))
        else:
            r=rng.randrange(total)
            if r<args.reservoir: reservoir[r]=(p.copy(),q.copy(),eta.copy(),qv)
        sha.update(bytes(int(x) for x in ce))
    # Random subset diagnostics from reservoir.
    subset_stats={}
    for m in [7,8,9]:
        hit=0; best=(99,0,0); trials=5000 if len(reservoir)>=m else 0
        for _ in range(trials):
            sample=rng.sample(reservoir,m)
            etas=[x[2] for x in sample]
            d=rank_mod(np.vstack([etas,L]))-rank_mod(etas)
            if d==0: hit+=1
            sc=(d,rank_mod(etas),rank_mod(np.vstack([etas,L])))
            if sc<best: best=sc
        subset_stats[str(m)]={'trials':trials,'hits':hit,'best_defect_rank_joint':list(best)}
    out={'field':'F3','limit':args.limit,'sample_mod':args.sample_mod,'elapsed_sec':time.time()-t0,
         'target_L_rank':rankL,'L_pivots':L_piv,'quotient_dimension':len(nonpiv),
         'enumerated_planes':total,'unique_projective_eta':len(unique_eta),'sha256_projective_eta_stream':sha.hexdigest(),
         'zero_quotient_projective_count':zero_q,'unique_projective_quotient_images':len(unique_q),
         'quotient_support_weight_hist_sample_or_full':{str(k):int(v) for k,v in sorted(q_hist.items())},
         'canonical9_target_contained':solve_coords(can_etas),'canonical9_quotient_rank':rank_mod(np.array(can_q,dtype=np.int8)),
         'canonical_drop8_defects':[int(rank_mod(np.vstack([can_etas[:i]+can_etas[i+1:],L]))-rank_mod(can_etas[:i]+can_etas[i+1:])) for i in range(9)],
         'reservoir_size':len(reservoir),'random_subset_diagnostics':subset_stats,
         'interpretation':'Enumeration of F3 Grassmannian points. Projective quotient images are for later exact span/search; random subset diagnostics are not proofs.'}
    path=OUT/'anti_projective_enum_F3.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2)[:20000])
    print('SAVED',path)

if __name__=='__main__': main()
