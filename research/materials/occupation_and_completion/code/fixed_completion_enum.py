#!/usr/bin/env python3
"""analysis: finite-field fixed-generator completion with Laderman free pairs fixed.

Over fields with sqrt(-1), the transported Laderman scheme is standard-tau invariant
with skeleton (7,8).  Keep its eight free orbits (16 slots) fixed.  Enumerate
tau-fixed rank-one slice generators x(v)=vec(V) vec(V^T)^T over F5 that lie in
F + L1, and test whether their images span the residual quotient (F+L1)/F.

If six such fixed generators span the residual quotient, then the fixed free pairs
plus those six fixed generators contain L1 with 22 slots, giving a finite-field
rank-22 tau-invariant containment candidate.  The script then recovers u-coefficients
and replays the full tensor identity over F5.
"""
from __future__ import annotations
import argparse, json, itertools
from pathlib import Path
import numpy as np

SCRIPT_DIR=Path(__file__).resolve().parent
WS=SCRIPT_DIR.parent
OUT=WS/"data"/"fixed_completion_enum"
OUT.mkdir(parents=True, exist_ok=True)

ROOTS_MINUS_ONE={5:2,13:5,17:4,29:12,37:6,41:9,65521:41224}

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
    R,r,piv=rref(M,p)
    return R[:r],piv

def nullspace_rows(M,p):
    """Basis of right nullspace {x: M x =0}; returned as rows."""
    R,r,piv=rref(M,p)
    n=M.shape[1]
    pivset=set(piv); free=[c for c in range(n) if c not in pivset]
    basis=[]
    for f in free:
        x=np.zeros(n,dtype=object); x[f]=1
        for row,col in enumerate(piv):
            x[col]=(-R[row,f])%p
        basis.append(x%p)
    return np.vstack(basis)%p if basis else np.zeros((0,n),dtype=object)

def solve_linear(A,b,p):
    """Solve A x=b over F_p; returns one solution or None."""
    A=mod(A,p); b=mod(b,p).reshape(A.shape[0],1)
    m,n=A.shape
    aug=np.concatenate([A.copy(),b],axis=1)%p
    r=0; piv=[]
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
        if all(int(aug[i,c])%p==0 for c in range(n)) and int(aug[i,n])%p:
            return None
    x=np.zeros(n,dtype=object)
    for row,col in enumerate(piv): x[col]=aug[row,n]%p
    return x%p

def row_contains(B,L,p):
    rB=rank(B,p); rBL=rank(np.vstack([B,L])%p,p)
    return rB==rBL,rB,rBL,rBL-rB

# data construction
def load_transported(p):
    root=ROOTS_MINUS_ONE[p]
    src_path=SCRIPT_DIR/"laderman_tau_decomp.py"
    src=src_path.read_text(); prefix=src.split('print(f"Sum matches T333')[0]
    ns={"__file__":str(src_path),"__name__":"defs_only"}
    exec(compile(prefix,str(src_path),"exec"),ns)
    terms=[(mod(a,p),mod(b,p),mod(c,p)) for a,b,c in ns['terms']]
    eps1=mod(ns['eps1'],p); pi12=mod(ns['pi12'],p)
    Q=eps1@pi12%p; R=np.diag([root,1,1]).astype(object)%p
    Qinv=mat_inv(Q,p); Rinv=mat_inv(R,p)
    def g(a,b,c): return (a@Qinv%p, Q@b@Rinv%p, R@c%p)
    return [g(a,b,c) for a,b,c in terms]

def vec9(M,p): return np.asarray(M,dtype=object).reshape(9)%p

def Tvec(v,p): return np.asarray(v,dtype=object).reshape(3,3).T.reshape(9)%p

def fixed_x(v,p): return np.outer(v,Tvec(v,p)).reshape(81)%p

def slot_x(term,p):
    a,b,c=term
    return np.outer(vec9(b,p),vec9(c,p)).reshape(81)%p

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
            if int(a)%p==0: continue
            for j,b in enumerate(vv):
                if int(b)%p==0: continue
                for k,c in enumerate(ww):
                    if int(c)%p: T[i,j,k]=(T[i,j,k]+a*b*c)%p
    return T%p

def recover_u_coeffs(generators,L,p):
    """Given generator rows X_l (n x 81), solve for each L_ab row coefficients u_l_ab."""
    X=np.vstack(generators)%p
    coeffs=[]
    A=X.T
    for row in L:
        sol=solve_linear(A,row,p)
        if sol is None: return None
        coeffs.append(sol)
    # coeffs order ab (a major then b), shape 9 x n. Return u matrices per generator.
    C=np.vstack(coeffs)%p
    us=[]
    for ell in range(X.shape[0]):
        U=np.zeros((3,3),dtype=object)
        for a in range(3):
            for b in range(3): U[a,b]=C[3*a+b,ell]%p
        us.append(U)
    return us

def enumerate_projective_vectors(p,limit=0):
    count=0
    for tup in itertools.product(range(p), repeat=9):
        if all(x==0 for x in tup): continue
        # normalize first nonzero to 1
        first=next(i for i,x in enumerate(tup) if x%p)
        if tup[first] != 1: continue
        v=np.array(tup,dtype=object)
        count+=1
        yield v
        if limit and count>=limit: break

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--p',type=int,default=5)
    ap.add_argument('--limit',type=int,default=0)
    args=ap.parse_args()
    p=args.p
    assert p in ROOTS_MINUS_ONE and (ROOTS_MINUS_ONE[p]**2+1)%p==0
    terms=load_transported(p)
    free_pairs=[(1,4),(2,5),(6,15),(7,17),(8,16),(10,13),(12,14),(19,21)]
    free_slots=[i for pair in free_pairs for i in pair]
    free_terms=[terms[i] for i in free_slots]
    F=np.vstack([slot_x(t,p) for t in free_terms])%p
    L=build_L1(p)
    S=np.vstack([F,L])%p
    S_basis,_=row_basis(S,p)
    N=nullspace_rows(S_basis,p)  # x in F+L iff N x^T = 0, i.e. x dot each N row=0
    free_ok,free_r,free_aug,free_def=row_contains(F,L,p)

    # Build quotient functionals Phi (81 x qdim): annihilate F, map chosen L extension rows to identity.
    F_basis,_=row_basis(F,p)
    B_rows=[]; labels=[]
    for row in F_basis:
        B_rows.append(row); labels.append(('F',None))
    current=np.vstack(B_rows)%p if B_rows else np.zeros((0,81),dtype=object)
    Lext=[]; Lext_indices=[]
    cur_rank=rank(current,p)
    for i,row in enumerate(L):
        new_rank=rank(np.vstack([current,row])%p,p)
        if new_rank>cur_rank:
            Lext.append(row); Lext_indices.append(i)
            current=np.vstack([current,row])%p; cur_rank=new_rank
    Lext=np.vstack(Lext)%p
    qdim=len(Lext_indices)
    assert qdim==free_aug-free_r
    constraints=np.vstack([F_basis,Lext])%p
    Phi=[]
    for k in range(qdim):
        rhs=np.zeros(constraints.shape[0],dtype=object); rhs[F_basis.shape[0]+k]=1
        sol=solve_linear(constraints,rhs,p)  # constraints * phi = rhs
        assert sol is not None
        Phi.append(sol)
    Phi=np.vstack(Phi).T%p  # 81 x qdim
    # Verify quotient coords of Lext are identity and F zero.
    assert np.all((F_basis@Phi)%p==0)
    assert np.array_equal((Lext@Phi)%p, np.eye(qdim,dtype=object)%p)

    candidates=[]; qcoords=[]; total=0
    qspan=np.zeros((0,qdim),dtype=object)
    selected=[]
    for v in enumerate_projective_vectors(p,args.limit):
        total+=1
        x=fixed_x(v,p)
        if N.shape[0] and np.any((N@x.reshape(81,1)).reshape(-1)%p):
            continue
        q=(x@Phi)%p
        if np.all(q==0):
            continue
        candidates.append(v.copy()); qcoords.append(q.copy())
        old=rank(qspan,p) if qspan.size else 0
        newspan=np.vstack([qspan,q])%p if qspan.size else q.reshape(1,qdim)%p
        new=rank(newspan,p)
        if new>old:
            selected.append(len(candidates)-1); qspan=newspan
            if new==qdim: break
    candidate_count=len(candidates)
    qrank=rank(np.vstack(qcoords),p) if qcoords else 0
    selected_vectors=[candidates[i] for i in selected]
    hit=(qrank==qdim)

    replay=None
    if hit:
        fixed_terms=[]
        fixed_gens=[]
        for v in selected_vectors[:qdim]:
            V=v.reshape(3,3)%p
            W=V.T%p
            fixed_terms.append((None,V,W))
            fixed_gens.append(fixed_x(v,p))
        gens=list(F)+fixed_gens
        ok,rG,rGL,defect=row_contains(np.vstack(gens),L,p)
        us=recover_u_coeffs(gens,L,p)
        if us is not None:
            slot_terms=[]
            # free slots keep original transported v,w; u recovered per slot
            for idx,t in enumerate(free_terms):
                _,b,c=t
                slot_terms.append((us[idx],b,c))
            base=len(free_terms)
            for j,v in enumerate(selected_vectors[:qdim]):
                V=v.reshape(3,3)%p; W=V.T%p
                slot_terms.append((us[base+j],V,W))
            T=tensor_from_slots(slot_terms,p)
            replay_ok=bool(np.array_equal(T,build_T333(p)))
            # tau invariance of recovered u for fixed terms: should be symmetric if solution chosen by quotient functionals? check.
            fixed_u_sym=[bool(np.array_equal(us[base+j]%p, us[base+j].T%p)) for j in range(qdim)]
            # free u pairing: order is both slots from each free pair; check if slot terms are tau-paired roughly by raw matrices.
            replay={
                "combined_contains_L1":bool(ok),"combined_rank":int(rG),"combined_aug_rank":int(rGL),"combined_defect":int(defect),
                "recovered_u_exists":True,"full_T333_replay_with_recovered_u":replay_ok,
                "fixed_u_symmetric_by_selected_solution":fixed_u_sym,
                "selected_fixed_vectors": [[int(x) for x in v.tolist()] for v in selected_vectors[:qdim]],
                "selected_fixed_u_matrices": [[[int(us[base+j][a,b]) for b in range(3)] for a in range(3)] for j in range(qdim)]
            }
        else:
            replay={"combined_contains_L1":bool(ok),"combined_rank":int(rG),"combined_aug_rank":int(rGL),"combined_defect":int(defect),"recovered_u_exists":False}

    out={
        "field":f"F_{p}","sqrt_minus_one":ROOTS_MINUS_ONE[p],"limit":args.limit,
        "free_span_rank":int(free_r),"rank_free_plus_L1":int(free_aug),"residual_quotient_dimension":int(qdim),
        "left_nullity_of_free_plus_L1":int(N.shape[0]),"projective_vectors_tested":int(total),
        "compatible_fixed_candidates_seen_before_stop":int(candidate_count),
        "compatible_candidate_vectors": [[int(x) for x in v.tolist()] for v in candidates[:50]],
        "compatible_candidate_qcoords": [[int(x) for x in q.tolist()] for q in qcoords[:50]],
        "candidate_quotient_span_rank":int(qrank),"selected_candidate_indices":selected,
        "hit_six_fixed_completion":bool(hit),"replay":replay,
        "interpretation":"Exact finite-field test with transported Laderman free pairs fixed. A replay hit is a genuine rank-22 tau-symmetric scheme over this finite field; a miss only concerns this fixed-free-pair slice and this field/search limit."
    }
    path=OUT/f"fixed_completion_enum_F{p}.json"
    path.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2))
    print(f"SAVED {path}")

if __name__=='__main__': main()
