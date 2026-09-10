#!/usr/bin/env python3
"""analysis: general finite-field transport of Laderman Phi3*Phi4 to standard tau.

The diagonal transport used R^T R = eps1, hence needed sqrt(-1).  More generally,
with P=I, Q=delta*Q0, Q0=eps1*pi12, it is enough to choose R with
    R^T R = delta*eps1.
Then tau g = g Phi for g(A,B,C)=(A Q^{-1}, Q B R^{-1}, R C).
This script finds such R over small odd finite fields, transports Laderman, and
checks the anti-sector eight-bivector witness.
"""
from __future__ import annotations
import argparse, itertools, json
from pathlib import Path
import numpy as np

SCRIPT_DIR=Path(__file__).resolve().parent
WS=SCRIPT_DIR.parent
OUT=WS/"data"/"transport_laderman_tau"
OUT.mkdir(parents=True,exist_ok=True)

def inv(a,p): return pow(int(a)%p,-1,p)
def mod(A,p): return np.asarray(A,dtype=object)%p

def mat_inv(A,p):
    A=mod(A,p); n=A.shape[0]
    aug=np.concatenate([A.copy(),np.eye(n,dtype=object)],axis=1)%p
    r=0
    for c in range(n):
        piv=next((i for i in range(r,n) if int(aug[i,c])%p),None)
        if piv is None: raise ValueError('singular')
        if piv!=r: aug[[r,piv]]=aug[[piv,r]]
        aug[r,:]=(aug[r,:]*inv(aug[r,c],p))%p
        for i in range(n):
            if i!=r and int(aug[i,c])%p:
                aug[i,:]=(aug[i,:]-aug[i,c]*aug[r,:])%p
        r+=1
    return aug[:,n:]%p

def rref(M,p):
    M=mod(M,p).copy(); m,n=M.shape; r=0; piv=[]
    for c in range(n):
        pivrow=next((i for i in range(r,m) if int(M[i,c])%p),None)
        if pivrow is None: continue
        if pivrow!=r: M[[r,pivrow]]=M[[pivrow,r]]
        M[r,:]=(M[r,:]*inv(M[r,c],p))%p
        for i in range(m):
            if i!=r and int(M[i,c])%p:
                M[i,:]=(M[i,:]-M[i,c]*M[r,:])%p
        piv.append(c); r+=1
        if r==m: break
    return M,r,piv

def rank(M,p): return rref(M,p)[1]
def row_contains(B,L,p):
    rB=rank(B,p); rBL=rank(np.vstack([B,L])%p,p); return rB==rBL,rB,rBL,rBL-rB

def dot(u,v,p): return sum(int(u[i])*int(v[i]) for i in range(3))%p

def find_R_delta(p):
    vecs=[np.array(v,dtype=object) for v in itertools.product(range(p), repeat=3) if any(v)]
    for delta in range(1,p):
        targets=[(-delta)%p, delta%p, delta%p]
        candidates=[]
        for t in targets:
            candidates.append([v for v in vecs if dot(v,v,p)==t])
        for c0 in candidates[0]:
            for c1 in candidates[1]:
                if dot(c0,c1,p)!=0: continue
                for c2 in candidates[2]:
                    if dot(c0,c2,p)==0 and dot(c1,c2,p)==0:
                        R=np.column_stack([c0,c1,c2])%p
                        if rank(R,p)==3:
                            return delta,R
    raise RuntimeError(f"no R found over F{p}")

def load_terms(p):
    src_path=SCRIPT_DIR/"laderman_tau_decomp.py"
    src=src_path.read_text(); prefix=src.split('print(f"Sum matches T333')[0]
    ns={"__file__":str(src_path),"__name__":"defs_only"}
    exec(compile(prefix,str(src_path),"exec"),ns)
    return [(mod(a,p),mod(b,p),mod(c,p)) for a,b,c in ns['terms']], mod(ns['eps1'],p), mod(ns['pi12'],p), mod(ns['eps2'],p)

def Phi_factory(eps1,pi12,eps2,p):
    def Phi(a,b,c):
        a4=eps1@c@pi12%p
        b4=pi12@a@pi12@eps1%p
        c4=eps1@pi12@b@eps1%p
        return (b4.T@eps2%p, eps2@a4.T%p, c4.T%p)
    return Phi

def tau(a,b,c,p): return (a.T%p,c.T%p,b.T%p)

def vec9(M,p): return np.asarray(M,dtype=object).reshape(9)%p

def wedge(v,w,p):
    pairs=[(a,b) for a in range(9) for b in range(a+1,9)]
    out=np.zeros(36,dtype=object)
    for t,(i,j) in enumerate(pairs): out[t]=(v[i]*w[j]-v[j]*w[i])%p
    return out

def anti_target(p):
    wedge_pairs=[(a,b) for a in range(9) for b in range(a+1,9)]
    skew_pairs=[(0,1),(0,2),(1,2)]
    def idx(i,k): return 3*i+k
    T=np.zeros((3,36),dtype=object)
    for r,(a,b) in enumerate(skew_pairs):
        M=np.zeros((9,9),dtype=object)
        for i in range(3):
            for j in range(3):
                Aij=0
                if (i,j)==(a,b): Aij=1
                elif (i,j)==(b,a): Aij=-1
                if Aij==0: continue
                for k in range(3): M[idx(j,k),idx(i,k)]=(M[idx(j,k),idx(i,k)]+Aij)%p
        for t,(i,j) in enumerate(wedge_pairs): T[r,t]=M[i,j]%p
    return T%p

def build_T333(p):
    T=np.zeros((9,9,9),dtype=object)
    for i in range(3):
        for j in range(3):
            for k in range(3): T[3*i+j,3*j+k,3*k+i]=1
    return T%p

def tensor_sum(terms,p):
    T=np.zeros((9,9,9),dtype=object)
    for a,b,c in terms:
        av=vec9(a,p); bv=vec9(b,p); cv=vec9(c,p)
        for i,x in enumerate(av):
            if int(x)%p==0: continue
            for j,y in enumerate(bv):
                if int(y)%p==0: continue
                for k,z in enumerate(cv):
                    if int(z)%p: T[i,j,k]=(T[i,j,k]+x*y*z)%p
    return T%p

def prop(X,Y,p):
    xv=list(np.asarray(X,dtype=object).reshape(-1)%p); yv=list(np.asarray(Y,dtype=object).reshape(-1)%p)
    lam=None
    for x,y in zip(xv,yv):
        x=int(x)%p; y=int(y)%p
        if y:
            if lam is None: lam=x*inv(y,p)%p
            elif x != lam*y%p: return None
        else:
            if x: return None
    return lam if lam is not None else 0

def match_term(term,cands,p):
    a,b,c=term
    for j,(aa,bb,cc) in enumerate(cands):
        la=prop(a,aa,p); lb=prop(b,bb,p); lc=prop(c,cc,p)
        if la is None or lb is None or lc is None or la==0 or lb==0 or lc==0: continue
        if la*lb*lc%p==1: return j,(int(la),int(lb),int(lc))
    return None,None

def process_field(p):
    terms,eps1,pi12,eps2=load_terms(p)
    Q0=eps1@pi12%p
    delta,R=find_R_delta(p)
    Q=(delta*Q0)%p
    Qinv=mat_inv(Q,p); Rinv=mat_inv(R,p)
    Phi=Phi_factory(eps1,pi12,eps2,p)
    def g(a,b,c): return (a@Qinv%p, Q@b@Rinv%p, R@c%p)
    # basis conjugacy
    basis_ok=True
    for comp in range(3):
        for pos in range(9):
            mats=[np.zeros((3,3),dtype=object) for _ in range(3)]
            mats[comp][pos//3,pos%3]=1
            lhs=tau(*g(*mats),p)
            rhs=g(*Phi(*mats))
            if any(not np.array_equal(lhs[k]%p,rhs[k]%p) for k in range(3)):
                basis_ok=False
    transported=[g(a,b,c) for a,b,c in terms]
    replay=bool(np.array_equal(tensor_sum(transported,p), build_T333(p)))
    fixed=[0,3,9,11,18,20,22]
    two=[(1,4),(2,5),(6,15),(7,17),(8,16),(10,13),(12,14),(19,21)]
    perm=list(range(23))
    for i,j in two: perm[i]=j; perm[j]=i
    matches=[]
    for t in transported:
        j,sc=match_term(tau(*t,p),transported,p)
        matches.append((j,sc))
    perm_ok=[j for j,sc in matches]==perm
    B=[]
    for i,j in two:
        a,b,c=transported[i]
        B.append(wedge(vec9(b,p),vec9(c.T,p),p))
    B=np.vstack(B)%p
    A=anti_target(p)
    rep_ok,rep_r,rep_aug,rep_def=row_contains(B,A,p)
    fixed_zero=[]
    for i in fixed:
        a,b,c=transported[i]
        fixed_zero.append(bool(np.all(wedge(vec9(b,p),vec9(c.T,p),p)%p==0)))
    return {
        "field":f"F_{p}","delta":int(delta),"R_columns":R.astype(int).tolist(),
        "R_T_R_equals_delta_eps1":bool(np.array_equal(R.T@R%p, (delta*eps1)%p)),
        "basis_tau_g_equals_g_Phi":bool(basis_ok),"transported_replay_T333":bool(replay),
        "standard_tau_perm_matches":bool(perm_ok),"fixed_bivectors_all_zero":bool(all(fixed_zero)),
        "eight_rep_bivector_rank":int(rep_r),"eight_rep_augmented_rank_with_Lanti":int(rep_aug),
        "eight_rep_span_Lanti":bool(rep_ok),"eight_rep_defect":int(rep_def),
        "standard_tau_matches":[{"term":i+1,"tau_term":None if matches[i][0] is None else matches[i][0]+1,"scales":matches[i][1]} for i in range(23)]
    }

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--primes',default='3,5,7,11,13')
    args=ap.parse_args(); primes=[int(x) for x in args.primes.split(',') if x]
    results=[process_field(p) for p in primes]
    out={"results":results,"interpretation":"General scaled-congruence finite-field transport. If checks pass, the standard-tau Laderman eight-bivector anti witness is available over that finite field, not only fields with sqrt(-1)."}
    path=OUT/"transported_laderman_general_finite_fields.json"
    path.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2))
    print(f"SAVED {path}")
if __name__=='__main__': main()
