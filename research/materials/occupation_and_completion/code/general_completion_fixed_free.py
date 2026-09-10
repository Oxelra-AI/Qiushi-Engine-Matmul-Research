#!/usr/bin/env python3
"""analysis: unrestricted rank-one completion with transported Laderman free slots fixed.

Keep the 16 rank-one matrices from the eight transported Laderman free orbits.
Let F be their span and S=F+L1. Since dim S=22, any six additional rank-one
matrices that make F plus them contain L1 must themselves lie in S and have quotient
images spanning S/F. This script enumerates rank-one matrices v w^T in S over small
finite fields and greedily selects six quotient directions. A successful replay is
an exact rank-22 decomposition over that finite field (not necessarily tau-invariant).
"""
from __future__ import annotations
import argparse, itertools, json, time
from pathlib import Path
import numpy as np

SCRIPT_DIR=Path(__file__).resolve().parent
WS=SCRIPT_DIR.parent
OUT=WS/"data"/"general_completion"
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
def slot_x_from_vecs(v,w,p): return np.outer(v,w).reshape(81)%p
def slot_x(t,p):
    _,b,c=t; return slot_x_from_vecs(vec9(b,p),vec9(c,p),p)

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

def enumerate_w_subspace_basis(A,p):
    # A w = 0; return projective vectors in nullspace for small p/dim.
    Wbasis=nullspace_rows(A,p)
    d=Wbasis.shape[0]
    if d==0: return []
    out=[]
    for coeff in itertools.product(range(p), repeat=d):
        if not any(coeff): continue
        first=next(i for i,x in enumerate(coeff) if x%p)
        if coeff[first] != 1: continue
        w=sum((coeff[i]*Wbasis[i] for i in range(d)), np.zeros(9,dtype=object))%p
        if np.any(w%p): out.append(w)
    return out

def process(p, max_w_dim_enum=9, time_budget=240.0):
    t0=time.time()
    terms,delta,R=load_transported(p)
    free_pairs=[(1,4),(2,5),(6,15),(7,17),(8,16),(10,13),(12,14),(19,21)]
    free_slots=[i for pair in free_pairs for i in pair]
    free_terms=[terms[i] for i in free_slots]
    F=np.vstack([slot_x(t,p) for t in free_terms])%p; L=build_L1(p)
    free_ok,free_r,free_aug,free_def=row_contains(F,L,p)
    F_basis,_=row_basis(F,p)
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
    # For each v, equations N*(v w^T)=0 are linear in w. qcoords also linear in w.
    qspan=np.zeros((0,qdim),dtype=object); selected=[]; candidates_seen=0; total_v=0
    wdim_hist={}; qdim_hist={}; timed_out=False
    for v in proj_vectors(p):
        total_v+=1
        if time.time()-t0 > time_budget:
            timed_out=True; break
        A=[]
        for nrow in N:
            coeff=np.zeros(9,dtype=object)
            # x[9*i+j]=v_i*w_j
            for j in range(9):
                coeff[j]=sum(nrow[9*i+j]*v[i] for i in range(9))%p
            A.append(coeff)
        A=np.vstack(A)%p if A else np.zeros((0,9),dtype=object)
        Wbasis=nullspace_rows(A,p)
        d=Wbasis.shape[0]
        wdim_hist[str(d)]=wdim_hist.get(str(d),0)+1
        if d==0: continue
        # q = (v w^T) Phi. For basis w rows, compute q rows.
        qrows=[]
        wrows=[]
        for wb in Wbasis:
            x=slot_x_from_vecs(v,wb,p)
            q=(x@Phi)%p
            if not np.all(q==0):
                qrows.append(q); wrows.append(wb)
        if not qrows: continue
        local_qrank=rank(np.vstack(qrows),p)
        qdim_hist[str(local_qrank)]=qdim_hist.get(str(local_qrank),0)+1
        # enumerate projective w if dimension manageable; otherwise basis rows only.
        if d <= max_w_dim_enum:
            wlist=enumerate_w_subspace_basis(A,p)
        else:
            wlist=wrows
        for w in wlist:
            x=slot_x_from_vecs(v,w,p)
            q=(x@Phi)%p
            if np.all(q==0): continue
            candidates_seen+=1
            old=rank(qspan,p) if qspan.size else 0
            newspan=np.vstack([qspan,q])%p if qspan.size else q.reshape(1,qdim)%p
            new=rank(newspan,p)
            if new>old:
                selected.append({"v":v.copy(),"w":w.copy(),"q":[int(z) for z in q.tolist()],"rank_after":int(new)})
                qspan=newspan
                if new==qdim: break
        current_qrank = rank(qspan,p) if qspan.size else 0
        if current_qrank == qdim:
            break
    qrank=rank(qspan,p) if qspan.size else 0
    hit=qrank==qdim
    replay=None
    if hit:
        selected_pairs=[(s['v'],s['w']) for s in selected[:qdim]]
        comp_gens=[slot_x_from_vecs(v,w,p) for v,w in selected_pairs]
        gens=list(F)+comp_gens
        ok,rG,rGL,defect=row_contains(np.vstack(gens),L,p)
        us=recover_u(gens,L,p)
        if us is not None:
            slot_terms=[]
            for idx,t in enumerate(free_terms):
                _,b,c=t; slot_terms.append((us[idx],b,c))
            base=len(free_terms)
            for j,(v,w) in enumerate(selected_pairs):
                slot_terms.append((us[base+j],v.reshape(3,3)%p,w.reshape(3,3)%p))
            replay_ok=bool(np.array_equal(tensor_from_slots(slot_terms,p),build_T333(p)))
            replay={
                "combined_contains_L1":bool(ok),"combined_rank":int(rG),"combined_aug_rank":int(rGL),"combined_defect":int(defect),
                "recovered_u_exists":True,"full_T333_replay_with_recovered_u":replay_ok,
                "selected_pairs":[{"v":[int(x) for x in v.tolist()],"w":[int(x) for x in w.tolist()]} for v,w in selected_pairs],
                "selected_u_matrices":[[[int(us[base+j][a,b]) for b in range(3)] for a in range(3)] for j in range(qdim)],
                "free_u_matrices_first16":[[[int(us[j][a,b]) for b in range(3)] for a in range(3)] for j in range(len(free_terms))]
            }
    return {
        "field":f"F_{p}","delta":int(delta),"R_columns":R.astype(int).tolist(),
        "free_span_rank":int(free_r),"rank_free_plus_L1":int(free_aug),"residual_quotient_dimension":int(qdim),
        "left_nullity_of_S":int(N.shape[0]),"projective_v_tested":int(total_v),"timed_out":timed_out,
        "w_nullity_histogram_by_v":wdim_hist,"local_qrank_histogram_by_v":qdim_hist,
        "rank_one_candidates_seen_before_stop":int(candidates_seen),
        "selected_rank_increasing_candidates":[{"v":[int(x) for x in s['v'].tolist()],"w":[int(x) for x in s['w'].tolist()],"q":s['q'],"rank_after":s['rank_after']} for s in selected],
        "candidate_quotient_span_rank":int(qrank),"hit_six_general_rankone_completion":bool(hit),"replay":replay,
        "interpretation":"Unrestricted completion with transported Laderman free slots fixed. A replay hit is an exact rank-22 decomposition over the field; a miss only concerns this fixed 16-slot free span."
    }

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--p',type=int,default=3); ap.add_argument('--time-budget',type=float,default=240.0)
    args=ap.parse_args(); out=process(args.p,time_budget=args.time_budget)
    path=OUT/f"general_completion_fixed_free_F{args.p}.json"; path.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2)); print(f"SAVED {path}")
if __name__=='__main__': main()
