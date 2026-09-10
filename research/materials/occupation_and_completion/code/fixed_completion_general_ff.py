#!/usr/bin/env python3
"""analysis: fixed-free completion using general finite-field Laderman transport.

This repeats the fixed-completion enumeration with the scaled-congruence transport
R^T R = delta eps1, so it applies to F3 as well as primes containing sqrt(-1).
It holds the eight transported Laderman free orbits fixed and asks whether six
standard-tau fixed generators can complete L1.
"""
from __future__ import annotations
import argparse, itertools, json
from pathlib import Path
import numpy as np

SCRIPT_DIR=Path(__file__).resolve().parent
WS=SCRIPT_DIR.parent
OUT=WS/"data"/"fixed_completion_enum"
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
def row_basis(M,p):
    R,r,piv=rref(M,p); return R[:r],piv

def nullspace_rows(M,p):
    R,r,piv=rref(M,p); n=M.shape[1]; free=[c for c in range(n) if c not in set(piv)]
    out=[]
    for f in free:
        x=np.zeros(n,dtype=object); x[f]=1
        for row,col in enumerate(piv): x[col]=(-R[row,f])%p
        out.append(x%p)
    return np.vstack(out)%p if out else np.zeros((0,n),dtype=object)

def solve_linear(A,b,p):
    A=mod(A,p); b=mod(b,p).reshape(A.shape[0],1); m,n=A.shape
    aug=np.concatenate([A.copy(),b],axis=1)%p; r=0; piv=[]
    for c in range(n):
        pivrow=next((i for i in range(r,m) if int(aug[i,c])%p),None)
        if pivrow is None: continue
        if pivrow!=r: aug[[r,pivrow]]=aug[[pivrow,r]]
        aug[r,:]=(aug[r,:]*inv(aug[r,c],p))%p
        for i in range(m):
            if i!=r and int(aug[i,c])%p:
                aug[i,:]=(aug[i,:]-aug[i,c]*aug[r,:])%p
        piv.append(c); r+=1
        if r==m: break
    for i in range(r,m):
        if all(int(aug[i,c])%p==0 for c in range(n)) and int(aug[i,n])%p: return None
    x=np.zeros(n,dtype=object)
    for row,col in enumerate(piv): x[col]=aug[row,n]%p
    return x%p

def row_contains(B,L,p):
    rB=rank(B,p); rBL=rank(np.vstack([B,L])%p,p); return rB==rBL,rB,rBL,rBL-rB

def dot(u,v,p): return sum(int(u[i])*int(v[i]) for i in range(3))%p

def find_R_delta(p):
    vecs=[np.array(v,dtype=object) for v in itertools.product(range(p), repeat=3) if any(v)]
    for delta in range(1,p):
        targets=[(-delta)%p,delta%p,delta%p]
        cand=[[v for v in vecs if dot(v,v,p)==t] for t in targets]
        for c0 in cand[0]:
            for c1 in cand[1]:
                if dot(c0,c1,p): continue
                for c2 in cand[2]:
                    if dot(c0,c2,p)==0 and dot(c1,c2,p)==0:
                        R=np.column_stack([c0,c1,c2])%p
                        if rank(R,p)==3: return delta,R
    raise RuntimeError('no R')

def load_transported(p):
    src_path=SCRIPT_DIR/"laderman_tau_decomp.py"
    src=src_path.read_text(); prefix=src.split('print(f"Sum matches T333')[0]
    ns={"__file__":str(src_path),"__name__":"defs_only"}
    exec(compile(prefix,str(src_path),"exec"),ns)
    terms=[(mod(a,p),mod(b,p),mod(c,p)) for a,b,c in ns['terms']]
    eps1=mod(ns['eps1'],p); pi12=mod(ns['pi12'],p)
    Q0=eps1@pi12%p; delta,R=find_R_delta(p); Q=(delta*Q0)%p
    Qinv=mat_inv(Q,p); Rinv=mat_inv(R,p)
    def g(a,b,c): return (a@Qinv%p, Q@b@Rinv%p, R@c%p)
    return [g(a,b,c) for a,b,c in terms],delta,R

def vec9(M,p): return np.asarray(M,dtype=object).reshape(9)%p
def Tvec(v,p): return np.asarray(v,dtype=object).reshape(3,3).T.reshape(9)%p
def fixed_x(v,p): return np.outer(v,Tvec(v,p)).reshape(81)%p
def slot_x(t,p):
    _,b,c=t; return np.outer(vec9(b,p),vec9(c,p)).reshape(81)%p

def build_L1(p):
    rows=[]
    for a in range(3):
        for b in range(3):
            M=np.zeros((9,9),dtype=object)
            for k in range(3): M[3*b+k,3*k+a]=1
            rows.append(M.reshape(81))
    return np.vstack(rows)%p

def build_T333(p):
    T=np.zeros((9,9,9),dtype=object)
    for i in range(3):
        for j in range(3):
            for k in range(3): T[3*i+j,3*j+k,3*k+i]=1
    return T%p

def tensor_from_slots(slot_terms,p):
    T=np.zeros((9,9,9),dtype=object)
    for u,v,w in slot_terms:
        uu=vec9(u,p); vv=vec9(v,p); ww=vec9(w,p)
        for i,a in enumerate(uu):
            if not int(a)%p: continue
            for j,b in enumerate(vv):
                if not int(b)%p: continue
                for k,c in enumerate(ww):
                    if int(c)%p: T[i,j,k]=(T[i,j,k]+a*b*c)%p
    return T%p

def recover_u(gens,L,p):
    X=np.vstack(gens)%p; A=X.T; coeffs=[]
    for row in L:
        sol=solve_linear(A,row,p)
        if sol is None: return None
        coeffs.append(sol)
    C=np.vstack(coeffs)%p; us=[]
    for ell in range(X.shape[0]):
        U=np.zeros((3,3),dtype=object)
        for a in range(3):
            for b in range(3): U[a,b]=C[3*a+b,ell]%p
        us.append(U)
    return us

def proj_vectors(p):
    for tup in itertools.product(range(p), repeat=9):
        if not any(tup): continue
        first=next(i for i,x in enumerate(tup) if x%p)
        if tup[first]!=1: continue
        yield np.array(tup,dtype=object)

def process(p):
    terms,delta,R=load_transported(p)
    free_pairs=[(1,4),(2,5),(6,15),(7,17),(8,16),(10,13),(12,14),(19,21)]
    free_slots=[i for pair in free_pairs for i in pair]
    free_terms=[terms[i] for i in free_slots]
    F=np.vstack([slot_x(t,p) for t in free_terms])%p; L=build_L1(p)
    free_ok,free_r,free_aug,free_def=row_contains(F,L,p)
    F_basis,_=row_basis(F,p)
    # Select L extension basis modulo F and quotient functionals Phi.
    current=F_basis.copy(); cur=rank(current,p); Lext=[]; Lext_idx=[]
    for i,row in enumerate(L):
        nr=rank(np.vstack([current,row])%p,p)
        if nr>cur:
            Lext.append(row); Lext_idx.append(i); current=np.vstack([current,row])%p; cur=nr
    Lext=np.vstack(Lext)%p; qdim=len(Lext_idx)
    S_basis,_=row_basis(np.vstack([F,L])%p,p); N=nullspace_rows(S_basis,p)
    constraints=np.vstack([F_basis,Lext])%p
    Phi=[]
    for k in range(qdim):
        rhs=np.zeros(constraints.shape[0],dtype=object); rhs[F_basis.shape[0]+k]=1
        Phi.append(solve_linear(constraints,rhs,p))
    Phi=np.vstack(Phi).T%p
    candidates=[]; qcoords=[]; qspan=np.zeros((0,qdim),dtype=object); selected=[]; total=0
    for v in proj_vectors(p):
        total+=1; x=fixed_x(v,p)
        if N.shape[0] and np.any((N@x.reshape(81,1)).reshape(-1)%p): continue
        q=(x@Phi)%p
        if np.all(q==0): continue
        candidates.append(v.copy()); qcoords.append(q.copy())
        old=rank(qspan,p) if qspan.size else 0
        newspan=np.vstack([qspan,q])%p if qspan.size else q.reshape(1,qdim)%p
        new=rank(newspan,p)
        if new>old:
            selected.append(len(candidates)-1); qspan=newspan
            if new==qdim: break
    qrank=rank(np.vstack(qcoords),p) if qcoords else 0
    hit=(qrank==qdim)
    replay=None
    if hit:
        selected_vectors=[candidates[i] for i in selected[:qdim]]
        fixed_gens=[fixed_x(v,p) for v in selected_vectors]
        gens=list(F)+fixed_gens
        ok,rG,rGL,defect=row_contains(np.vstack(gens),L,p)
        us=recover_u(gens,L,p)
        if us is not None:
            slot_terms=[]
            for idx,t in enumerate(free_terms):
                _,b,c=t; slot_terms.append((us[idx],b,c))
            base=len(free_terms)
            for j,v in enumerate(selected_vectors):
                V=v.reshape(3,3)%p; slot_terms.append((us[base+j],V,V.T%p))
            replay_ok=bool(np.array_equal(tensor_from_slots(slot_terms,p),build_T333(p)))
            replay={
                "combined_contains_L1":bool(ok),"combined_rank":int(rG),"combined_aug_rank":int(rGL),"combined_defect":int(defect),
                "recovered_u_exists":True,"full_T333_replay_with_recovered_u":replay_ok,
                "selected_fixed_vectors":[[int(x) for x in v.tolist()] for v in selected_vectors],
                "selected_fixed_u_matrices":[[[int(us[base+j][a,b]) for b in range(3)] for a in range(3)] for j in range(qdim)]
            }
        else:
            replay={"combined_contains_L1":bool(ok),"recovered_u_exists":False}
    return {
        "field":f"F_{p}","delta":int(delta),"R_columns":R.astype(int).tolist(),
        "free_span_rank":int(free_r),"rank_free_plus_L1":int(free_aug),"residual_quotient_dimension":int(qdim),
        "projective_vectors_tested":int(total),"compatible_fixed_candidates_seen_before_stop":int(len(candidates)),
        "compatible_candidate_vectors":[[int(x) for x in v.tolist()] for v in candidates[:50]],
        "compatible_candidate_qcoords":[[int(x) for x in q.tolist()] for q in qcoords[:50]],
        "candidate_quotient_span_rank":int(qrank),"selected_candidate_indices":selected,
        "hit_six_fixed_completion":bool(hit),"replay":replay
    }

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--primes',default='3,5')
    args=ap.parse_args(); primes=[int(x) for x in args.primes.split(',')]
    results=[process(p) for p in primes]
    out={"results":results,"interpretation":"Fixed-Laderman-free-pair six-fixed completion using general finite-field transport. A hit with replay true would be a rank-22 scheme over that finite field; a miss is only this fixed-free slice."}
    path=OUT/"fixed_completion_general_finite_fields.json"
    path.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2)); print(f"SAVED {path}")
if __name__=='__main__': main()
