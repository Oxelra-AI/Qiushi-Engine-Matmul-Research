#!/usr/bin/env python3
"""Exact entry-condition subset test inside the naive_27 tau orbit data.

The tau split of the naive 27-term algorithm has 9 fixed orbits and 9 free
2-orbits.  For a rank-22 tau skeleton f+2m=22, ask whether any subset of these
existing (v,w)-pairs with that (f,m) satisfies both linear entry conditions:
  Gram: six Gram quadrics lie in span(f fixed squares + m free products)
  Anti: three complementary target bivectors lie in span(m free wedges)
This is only an entry-condition test for the inherited naive pairs; failure does
not exclude general tau-skeletons.
"""
from __future__ import annotations
import itertools, json
from pathlib import Path
import numpy as np

SESSION=Path(__file__).resolve().parents[1]
OUT=SESSION/"data"/"transpose_complement"
OUT.mkdir(parents=True, exist_ok=True)
p=65521

def idx(i,k): return 3*i+k

def inv(a): return pow(int(a)%p,p-2,p)
def rank(M):
    M=np.array(M,dtype=np.int64)%p
    rows,cols=M.shape
    r=0
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i,c]%p: piv=i; break
        if piv is None: continue
        M[[r,piv]]=M[[piv,r]]
        M[r]=M[r]*inv(M[r,c])%p
        for i in range(rows):
            if i!=r and M[i,c]%p:
                M[i]=(M[i]-int(M[i,c])*M[r])%p
        r+=1
        if r==rows: break
    return r

def contains(cols, targets):
    # cols and targets are lists/arrays of row vectors; test row-span containment.
    C=np.array(cols,dtype=np.int64)%p
    T=np.array(targets,dtype=np.int64)%p
    if len(C)==0: return False
    return rank(C)==rank(np.vstack([C,T]))

def sym_idx(a,b):
    if a>b: a,b=b,a
    return a*9-a*(a-1)//2+(b-a)
WEDGE_PAIRS=[(i,j) for i in range(9) for j in range(i+1,9)]
WEDGE_INDEX={q:i for i,q in enumerate(WEDGE_PAIRS)}

def product(a,b):
    v=np.zeros(45,dtype=np.int64)
    a=np.array(a,dtype=np.int64)%p; b=np.array(b,dtype=np.int64)%p
    for i in range(9):
        for j in range(i,9):
            if i==j: v[sym_idx(i,j)]=(a[i]*b[j])%p
            else: v[sym_idx(i,j)]=(a[i]*b[j]+a[j]*b[i])%p
    return v%p

def wedge(a,b):
    v=np.zeros(36,dtype=np.int64)
    a=np.array(a,dtype=np.int64)%p; b=np.array(b,dtype=np.int64)%p
    for t,(i,j) in enumerate(WEDGE_PAIRS):
        v[t]=(a[i]*b[j]-a[j]*b[i])%p
    return v%p

def gram_target():
    G=[]
    for i,j in [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]:
        v=np.zeros(45,dtype=np.int64); coeff=1 if i==j else 2
        for k in range(3): v[sym_idx(idx(i,k),idx(j,k))]+=coeff
        G.append(v%p)
    return G

def anti_target():
    A=[]
    for i,j in [(0,1),(0,2),(1,2)]:
        v=np.zeros(36,dtype=np.int64)
        for k in range(3):
            a=idx(i,k); b=idx(j,k)
            if a<b: v[WEDGE_INDEX[(a,b)]]-=1
            else: v[WEDGE_INDEX[(b,a)]]+=1
        A.append(v%p)
    return A

def naive_terms():
    terms=[]
    for i in range(3):
        for j in range(3):
            for k in range(3):
                u=np.zeros((3,3),dtype=int); u[i,j]=1
                v=np.zeros((3,3),dtype=int); v[j,k]=1
                w=np.zeros((3,3),dtype=int); w[k,i]=1
                terms.append((u,v,w))
    return terms

def key(t): return tuple(np.concatenate([t[0].ravel(),t[1].ravel(),t[2].ravel()]).tolist())
def tau(t):
    u,v,w=t
    return (u.T.copy(),w.T.copy(),v.T.copy())

def tau_orbits():
    terms=naive_terms(); pos={key(t):i for i,t in enumerate(terms)}; seen=set(); fixed=[]; free=[]
    for i,t in enumerate(terms):
        if i in seen: continue
        j=pos[key(tau(t))]
        if i==j:
            fixed.append(i); seen.add(i)
        else:
            free.append((i,j)); seen.add(i); seen.add(j)
    fixed_forms=[]; free_prod=[]; free_wedge=[]
    for i in fixed:
        u,v,w=terms[i]
        a=v.reshape(9)
        fixed_forms.append(product(a,a))
    for i,j in free:
        u,v,w=terms[i]
        a=v.reshape(9)
        b=w.T.reshape(9)
        free_prod.append(product(a,b))
        free_wedge.append(wedge(a,b))
    return fixed,free,fixed_forms,free_prod,free_wedge

def main():
    fixed,free,FQ,FP,FW=tau_orbits()
    G=gram_target(); A=anti_target()
    out={"prime":p,"fixed_orbits":fixed,"free_orbits":free,"full_naive":{"gram":contains(FQ+FP,G),"anti":contains(FW,A),"f":9,"m":9},"rank22_skeletons":{}}
    for f in range(0,23,2):
        m=(22-f)//2
        if m<0: continue
        if f>9 or m>9:
            continue
        total=0; gram_ok=0; anti_ok=0; both=[]
        anti_good_subsets=[]
        for Fs in itertools.combinations(range(9), f):
            gram_cols_fixed=[FQ[i] for i in Fs]
            for Ms in itertools.combinations(range(9), m):
                total+=1
                gram=contains(gram_cols_fixed+[FP[i] for i in Ms],G)
                anti=contains([FW[i] for i in Ms],A)
                if gram: gram_ok+=1
                if anti:
                    anti_ok+=1
                    if len(anti_good_subsets)<5: anti_good_subsets.append(Ms)
                if gram and anti:
                    both.append({"fixed_subset":Fs,"free_subset":Ms})
                    if len(both)>=20: break
            if len(both)>=20: break
        out["rank22_skeletons"][f"f{f}_m{m}"]={"tested":total,"gram_ok":gram_ok,"anti_ok":anti_ok,"both_ok_count_recorded":len(both),"both_examples":both,"anti_good_examples":anti_good_subsets}
        print(f"(f={f},m={m}) tested={total} gram_ok={gram_ok} anti_ok={anti_ok} both_recorded={len(both)}")
    path=OUT/"naive27_rank22_subset_entry_feasibility.json"
    path.write_text(json.dumps(out,indent=2)+"\n")
    print(f"SAVED {path}")

if __name__=='__main__':
    main()
