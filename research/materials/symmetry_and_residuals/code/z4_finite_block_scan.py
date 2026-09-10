#!/usr/bin/env python3
"""
analysis: finite-field exact scan using the corrected Z4 eigenblock instrument.

This is not a characteristic-zero proof.  It is an exact finite-field pressure test of
one SL3/T LU chart for the single-free-Z4 exterior component and Z4-stable rank-10
residual decompositions.  It uses the pairing-corrected variable action
    M -> a0^T M a0^{-T}
from z4_pairing_pencil.py, then performs the block solve:
  qz^2 conic -> z-lines and q's,
  qw^2 -> w's,
  pzw -> p's,
  H_W tail -> either one length-2 orbit (pattern 4+4+2) or two fixed cubes
              (pattern 4+4+1+1).

For small primes p == 1 mod 4, exhaustive enumeration over the LU chart
M=U(u12,u13,u23)L(l21,l31,l32) is feasible.  A found solution is converted back to
old coordinates and all 729 Brent entries are checked over F_p.
"""
from __future__ import annotations

import argparse, itertools, json, time
from pathlib import Path
import numpy as np

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "z4_block_scan"
OUT.mkdir(parents=True, exist_ok=True)
N=9
MONOS=list(itertools.combinations_with_replacement(range(N),3))
MONO_IDX={m:i for i,m in enumerate(MONOS)}


def mat_inv_mod(M,p):
    M=np.array(M,dtype=object)%p; n=M.shape[0]
    aug=[[int(M[i,j])%p for j in range(n)]+[1 if i==j else 0 for j in range(n)] for i in range(n)]
    r=0
    for c in range(n):
        piv=None
        for i in range(r,n):
            if aug[i][c]%p: piv=i; break
        if piv is None: raise ValueError('singular')
        aug[r],aug[piv]=aug[piv],aug[r]
        inv=pow(aug[r][c]%p,-1,p); aug[r]=[(x*inv)%p for x in aug[r]]
        for i in range(n):
            if i!=r and aug[i][c]%p:
                f=aug[i][c]%p; aug[i]=[(aug[i][j]-f*aug[r][j])%p for j in range(2*n)]
        r+=1
    R=np.zeros((n,n),dtype=object)
    for i in range(n):
        for j in range(n): R[i,j]=aug[i][n+j]%p
    return R


def matmul_mod(A,B,p):
    A=np.array(A,dtype=object)%p; B=np.array(B,dtype=object)%p
    C=np.zeros((A.shape[0],B.shape[1]),dtype=object)
    for i in range(A.shape[0]):
        for j in range(B.shape[1]):
            s=0
            for k in range(A.shape[1]): s += int(A[i,k])*int(B[k,j])
            C[i,j]=s%p
    return C


def rank_mod(A,p):
    A=np.array(A,dtype=object)%p; m,n=A.shape
    B=[[int(A[i,j])%p for j in range(n)] for i in range(m)]
    r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if B[i][c]%p: piv=i; break
        if piv is None: continue
        B[r],B[piv]=B[piv],B[r]
        inv=pow(B[r][c]%p,-1,p); B[r]=[(x*inv)%p for x in B[r]]
        for i in range(m):
            if i!=r and B[i][c]%p:
                f=B[i][c]%p; B[i]=[(B[i][j]-f*B[r][j])%p for j in range(n)]
        r+=1
        if r==m: break
    return r


def nullspace_mod(A,p):
    A=np.array(A,dtype=object)%p; m,n=A.shape
    B=[[int(A[i,j])%p for j in range(n)] for i in range(m)]
    pivots=[]; r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if B[i][c]%p: piv=i; break
        if piv is None: continue
        B[r],B[piv]=B[piv],B[r]
        inv=pow(B[r][c]%p,-1,p); B[r]=[(x*inv)%p for x in B[r]]
        for i in range(m):
            if i!=r and B[i][c]%p:
                f=B[i][c]%p; B[i]=[(B[i][j]-f*B[r][j])%p for j in range(n)]
        pivots.append(c); r+=1
    free=[c for c in range(n) if c not in pivots]
    vecs=[]
    for fc in free:
        v=[0]*n; v[fc]=1
        for row,pc in enumerate(pivots): v[pc]=(-B[row][fc])%p
        vecs.append(v)
    return np.array(vecs,dtype=object).T if vecs else np.zeros((n,0),dtype=object)


def affine_solutions(A,b,p,max_solutions=100000):
    A=np.array(A,dtype=object)%p; b=np.array(b,dtype=object).reshape(-1)%p
    m,n=A.shape
    B=[[int(A[i,j])%p for j in range(n)]+[int(b[i])%p] for i in range(m)]
    pivots=[]; r=0
    for c in range(n):
        piv=None
        for i in range(r,m):
            if B[i][c]%p: piv=i; break
        if piv is None: continue
        B[r],B[piv]=B[piv],B[r]
        inv=pow(B[r][c]%p,-1,p); B[r]=[(x*inv)%p for x in B[r]]
        for i in range(m):
            if i!=r and B[i][c]%p:
                f=B[i][c]%p; B[i]=[(B[i][j]-f*B[r][j])%p for j in range(n+1)]
        pivots.append(c); r+=1
    for i in range(r,m):
        if all(B[i][j]%p==0 for j in range(n)) and B[i][n]%p:
            return []
    free=[c for c in range(n) if c not in pivots]
    part=[0]*n
    for row,pc in enumerate(pivots): part[pc]=B[row][n]%p
    null=[]
    for fc in free:
        v=[0]*n; v[fc]=1
        for row,pc in enumerate(pivots): v[pc]=(-B[row][fc])%p
        null.append(v)
    total=p**len(null)
    if total>max_solutions:
        return None
    sols=[]
    for coeffs in itertools.product(range(p), repeat=len(null)):
        x=part[:]
        for c,v in zip(coeffs,null):
            if c:
                x=[(x[i]+c*v[i])%p for i in range(n)]
        sols.append(np.array(x,dtype=object))
    return sols


def eigenspace(M,ev,p):
    A=np.array(M,dtype=object)%p
    for i in range(A.shape[0]): A[i,i]=(int(A[i,i])-ev)%p
    return nullspace_mod(A,p)


def linear_action(left,right,p):
    R=np.zeros((N,N),dtype=object)
    for k in range(N):
        E=np.zeros((3,3),dtype=object); E[k//3,k%3]=1
        Y=matmul_mod(matmul_mod(left,E,p),right,p)
        R[:,k]=Y.reshape(N)%p
    return R


def cube_coeff(l,p):
    l=[int(x)%p for x in np.array(l,dtype=object).reshape(N)]
    out=np.zeros(len(MONOS),dtype=object)
    for a in range(N):
        if l[a]==0: continue
        for b in range(N):
            if l[b]==0: continue
            for c in range(N):
                if l[c]==0: continue
                idx = MONO_IDX[tuple(sorted((a,b,c)))]
                out[idx] = (int(out[idx]) + l[a]*l[b]*l[c]) % p
    return out


def prod_coeff(u,v,w,p,factor=1):
    u=[int(x)%p for x in u]; v=[int(x)%p for x in v]; w=[int(x)%p for x in w]
    out=np.zeros(len(MONOS),dtype=object)
    for a in range(N):
        if u[a]==0: continue
        for b in range(N):
            if v[b]==0: continue
            for c in range(N):
                if w[c]==0: continue
                idx = MONO_IDX[tuple(sorted((a,b,c)))]
                out[idx] = (int(out[idx]) + factor*u[a]*v[b]*w[c]) % p
    return out


def orbit_cube(l,Ddiag,p,steps):
    out=np.zeros(len(MONOS),dtype=object)
    l=np.array(l,dtype=object).reshape(N)%p
    for k in range(steps):
        scales=np.array([pow(int(d),k,p) for d in Ddiag],dtype=object)
        out=(out+cube_coeff((l*scales)%p,p))%p
    return out


def target_trX3(change,p):
    out=np.zeros(len(MONOS),dtype=object)
    for a,b,c in itertools.product(range(3),repeat=3):
        r1=3*a+b; r2=3*b+c; r3=3*c+a
        out=(out+prod_coeff(change[r1,:],change[r2,:],change[r3,:],p))%p
    return out


def free_contribution(Tcols,Ddiag,p):
    out=np.zeros(len(MONOS),dtype=object)
    A=Tcols[:,0]; B=Tcols[:,1]; C=Tcols[:,2]
    for k in range(4):
        scales=np.array([pow(int(d),k,p) for d in Ddiag],dtype=object)
        out=(out+prod_coeff((A*scales)%p,(B*scales)%p,(C*scales)%p,p,factor=3))%p
    return out


def conic_points_rowspace(M,p):
    M=np.array(M,dtype=object)%p
    r0=[int(M[0,j])%p for j in range(3)]; r1=[int(M[1,j])%p for j in range(3)]
    pts=[]
    def add(v):
        if all(x%p==0 for x in v): return
        if (int(v[1])*int(v[1])-4*int(v[0])*int(v[2]))%p !=0: return
        inv=None
        for x in v:
            if x%p:
                inv=pow(int(x)%p,-1,p); break
        vn=tuple((int(x)*inv)%p for x in v)
        if vn not in pts: pts.append(vn)
    for t in range(p): add([(t*r0[j]+r1[j])%p for j in range(3)])
    add(r0)
    return pts


def square_vec(v,p):
    a,b=int(v[0])%p,int(v[1])%p
    return [(a*a)%p,(2*a*b)%p,(b*b)%p]


def projective_norm(v,p):
    v=[int(x)%p for x in v]
    if all(x==0 for x in v): return tuple(v)
    for x in v:
        if x:
            inv=pow(x,-1,p); return tuple((y*inv)%p for y in v)


def z_vectors_for_projective_square(pt,p):
    want=tuple(int(x)%p for x in pt)
    reps=[]; seen=set()
    for a,b in itertools.product(range(p), repeat=2):
        if a==0 and b==0: continue
        sq=square_vec((a,b),p)
        if projective_norm(sq,p)==want:
            # keep all scalings; exact scale matters downstream
            key=(a,b)
            if key not in seen:
                seen.add(key); reps.append(np.array([a,b],dtype=object))
    return reps


def exact_vectors_for_square(sq,p):
    sq=[int(x)%p for x in sq]
    reps=[]
    for a,b in itertools.product(range(p), repeat=2):
        if square_vec((a,b),p)==sq:
            reps.append(np.array([a,b],dtype=object))
    return reps


def extract_blocks(C):
    qz=np.zeros((2,3),dtype=object); qw=np.zeros((2,3),dtype=object); pzw=np.zeros((3,2,2),dtype=object)
    for qi,qvar in enumerate([3,4]):
        for ci,(a,b) in enumerate([(5,5),(5,6),(6,6)]): qz[qi,ci]=C[MONO_IDX[tuple(sorted((qvar,a,b)))]]
        for ci,(a,b) in enumerate([(7,7),(7,8),(8,8)]): qw[qi,ci]=C[MONO_IDX[tuple(sorted((qvar,a,b)))]]
    for pi,pvar in enumerate([0,1,2]):
        for zi,zvar in enumerate([5,6]):
            for wi,wvar in enumerate([7,8]): pzw[pi,zi,wi]=C[MONO_IDX[tuple(sorted((pvar,zvar,wvar)))]]
    return qz%P_GLOBAL, qw%P_GLOBAL, pzw%P_GLOBAL

P_GLOBAL=5

def build_context(p):
    global P_GLOBAL
    P_GLOBAL=p
    a0=np.array([[0,0,-1],[1,0,-1],[0,1,-1]],dtype=object)%p
    a0i=mat_inv_mod(a0,p); a0T=a0.T%p; a0mT=mat_inv_mod(a0T,p)
    R=linear_action(a0T,a0mT,p)
    # sqrt(-1)
    imag=None
    for x in range(p):
        if (x*x)%p==p-1: imag=x; break
    if imag is None: raise ValueError('p must have sqrt(-1)')
    order=[('p',1,0),('q',p-1,2),('z',imag,1),('w',(p-imag)%p,3)]
    blocks=[]; Ddiag=[]; dims={}
    for label,ev,exp in order:
        E=eigenspace(R,ev,p); blocks.append(E); dims[label]=E.shape[1]; Ddiag += [ev]*E.shape[1]
    change=np.hstack(blocks)%p
    assert rank_mod(change,p)==9
    sch=json.loads((WS/'data'/'ballard_z4_cyclic'/'ballard_z4_cyclic_scheme.json').read_text())
    U0=np.array(sch['free_orbit_representatives'][0]['U'],dtype=object).reshape(N)%p
    V0=np.array(sch['free_orbit_representatives'][0]['V'],dtype=object).reshape(N)%p
    W0=np.array(sch['free_orbit_representatives'][0]['W'],dtype=object).reshape(N)%p
    T0_old=np.stack([U0,V0,W0],axis=1)%p
    T0_y=matmul_mod(change.T,T0_old,p)
    target_y=target_trX3(change,p)
    # monomial block indices
    def typ(i):
        return 'p' if i<3 else ('q' if i<5 else ('z' if i<7 else 'w'))
    exps=[0]*3+[2]*2+[1]*2+[3]*2
    block_indices={k:[] for k in ['p3','pq2','pzw','qz2','qw2','noninv']}
    tail_idx=[]; off_idx=[]
    for mi,m in enumerate(MONOS):
        e=sum(exps[i] for i in m)%4
        if e!=0:
            block_indices['noninv'].append(mi); continue
        counts={k:0 for k in ['p','q','z','w']}
        for i in m: counts[typ(i)]+=1
        b=None
        if counts=={'p':3,'q':0,'z':0,'w':0}: b='p3'
        elif counts=={'p':1,'q':2,'z':0,'w':0}: b='pq2'
        elif counts=={'p':1,'q':0,'z':1,'w':1}: b='pzw'
        elif counts=={'p':0,'q':1,'z':2,'w':0}: b='qz2'
        elif counts=={'p':0,'q':1,'z':0,'w':2}: b='qw2'
        else: raise RuntimeError(('other invariant',m,counts))
        block_indices[b].append(mi)
        if b in ('p3','pq2'): tail_idx.append(mi)
        else: off_idx.append(mi)
    return {'p':p,'a0':a0,'R':R,'imag':imag,'Ddiag':Ddiag,'change':change,'T0_y':T0_y,'target_y':target_y,'tail_idx':tail_idx,'off_idx':off_idx,'block_indices':block_indices}


def precompute_tails(ctx):
    p=ctx['p']; Ddiag=ctx['Ddiag']; tail_idx=ctx['tail_idx']
    len2={}; fixed2={}
    # one length-2 orbit l=p+q
    for coords in itertools.product(range(p), repeat=5):
        l=np.zeros(N,dtype=object); l[0:3]=coords[0:3]; l[3:5]=coords[3:5]
        C=orbit_cube(l,Ddiag,p,steps=2)
        key=tuple(int(C[i])%p for i in tail_idx)
        if key not in len2: len2[key]=coords
    # two fixed cubes in p-space.  Store one witness pair.
    pforms=list(itertools.product(range(p), repeat=3))
    cube_p=[]
    for coords in pforms:
        l=np.zeros(N,dtype=object); l[0:3]=coords
        C=cube_coeff(l,p)
        cube_p.append(tuple(int(C[i])%p for i in tail_idx))
    for i,a in enumerate(cube_p):
        for j,b in enumerate(cube_p[i:], start=i):
            key=tuple((a[k]+b[k])%p for k in range(len(tail_idx)))
            if key not in fixed2: fixed2[key]=(pforms[i],pforms[j])
    return len2,fixed2


def qz_target_vec(qz):
    return np.array([qz[0,0],qz[0,1],qz[0,2],qz[1,0],qz[1,1],qz[1,2]],dtype=object)


def build_qz_matrix_for_zs(zs,Ddiag,p):
    cols=[]
    for oj,z in enumerate(zs):
        for qi in range(2):
            l=np.zeros(N,dtype=object); l[3+qi]=1; l[5:7]=z
            C=orbit_cube(l,Ddiag,p,steps=4)
            cols.append(qz_target_vec(extract_blocks(C)[0]))
    return np.stack(cols,axis=1)%p


def decompose_C(C,ctx,len2_tails,fixed2_tails,max_records=1):
    p=ctx['p']; Ddiag=ctx['Ddiag']; tail_idx=ctx['tail_idx']; off_idx=ctx['off_idx']
    qz,qw,pzw=extract_blocks(C)
    if rank_mod(qz,p)!=2 or rank_mod(qw,p)!=2:
        return []
    pts=conic_points_rowspace(qz,p)
    if len(pts)!=2: return []
    zrep_lists=[z_vectors_for_projective_square(pt,p) for pt in pts]
    if any(len(L)==0 for L in zrep_lists): return []
    records=[]
    # try both orderings of the two conic points, and all exact line scalings over Fp.
    for order in [(0,1),(1,0)]:
        for z1 in zrep_lists[order[0]]:
            for z2 in zrep_lists[order[1]]:
                zs=[z1,z2]
                Aq=build_qz_matrix_for_zs(zs,Ddiag,p)
                qsols=affine_solutions(Aq,qz_target_vec(qz),p,max_solutions=200)
                if not qsols: continue
                if qsols is None: continue
                for qs in qsols:
                    q1=np.array([qs[0],qs[1]],dtype=object); q2=np.array([qs[2],qs[3]],dtype=object)
                    # solve square vectors for w: qw entries = 12 * sum q_i * [w0^2,2w0w1,w1^2]
                    Aw=np.zeros((6,6),dtype=object)
                    for qi in range(2):
                        for col in range(3):
                            row=qi*3+col
                            Aw[row,col]=(12*int(q1[qi]))%p
                            Aw[row,3+col]=(12*int(q2[qi]))%p
                    wsols=affine_solutions(Aw,qz_target_vec(qw),p,max_solutions=200)
                    if not wsols: continue
                    if wsols is None: continue
                    for ws in wsols:
                        w1sq=[int(x)%p for x in ws[:3]]; w2sq=[int(x)%p for x in ws[3:6]]
                        if (w1sq[1]*w1sq[1]-4*w1sq[0]*w1sq[2])%p or (w2sq[1]*w2sq[1]-4*w2sq[0]*w2sq[2])%p:
                            continue
                        w1s=exact_vectors_for_square(w1sq,p); w2s=exact_vectors_for_square(w2sq,p)
                        if not w1s or not w2s: continue
                        for w1 in w1s:
                            for w2 in w2s:
                                # solve pzw linear in p1,p2
                                Ap=np.zeros((12,6),dtype=object); b=[]; row=0
                                for pi in range(3):
                                    for zi in range(2):
                                        for wi in range(2):
                                            b.append(pzw[pi,zi,wi])
                                            Ap[row,pi]=(24*int(z1[zi])*int(w1[wi]))%p
                                            Ap[row,3+pi]=(24*int(z2[zi])*int(w2[wi]))%p
                                            row+=1
                                psols=affine_solutions(Ap,np.array(b,dtype=object),p,max_solutions=200)
                                if not psols: continue
                                if psols is None: continue
                                for ps in psols:
                                    p1=np.array(ps[:3],dtype=object); p2=np.array(ps[3:6],dtype=object)
                                    l1=np.zeros(N,dtype=object); l2=np.zeros(N,dtype=object)
                                    l1[0:3]=p1; l1[3:5]=q1; l1[5:7]=z1; l1[7:9]=w1
                                    l2[0:3]=p2; l2[3:5]=q2; l2[5:7]=z2; l2[7:9]=w2
                                    H=(C-orbit_cube(l1,Ddiag,p,4)-orbit_cube(l2,Ddiag,p,4))%p
                                    if any(int(H[i])%p for i in off_idx):
                                        continue
                                    tail=tuple(int(H[i])%p for i in tail_idx)
                                    pat=[]
                                    if tail in len2_tails: pat.append(('4+4+2',len2_tails[tail]))
                                    if tail in fixed2_tails: pat.append(('4+4+1+1',fixed2_tails[tail]))
                                    for name,wit in pat:
                                        records.append({'pattern':name,'l1':[int(x)%p for x in l1], 'l2':[int(x)%p for x in l2], 'tail_witness':wit})
                                        if len(records)>=max_records: return records
    return records


def M_from_lu(vals,p):
    u12,u13,u23,l21,l31,l32=vals
    U=np.array([[1,u12,u13],[0,1,u23],[0,0,1]],dtype=object)%p
    L=np.array([[1,0,0],[l21,1,0],[l31,l32,1]],dtype=object)%p
    return matmul_mod(U,L,p)


def tensor_verify_candidate(ctx,M,record):
    # Convert y-forms back to old coefficient vectors: l_y = change^T l_old, so l_old = change^{-T} l_y.
    p=ctx['p']; change=ctx['change']; change_inv=mat_inv_mod(change,p); old_from_y=change_inv.T%p
    Ddiag=ctx['Ddiag']; R=ctx['R']
    # coefficient action G = R^T on old forms; in y it is D.
    G=R.T%p
    Gpows=[np.eye(N,dtype=object)]
    for _ in range(3): Gpows.append(matmul_mod(G,Gpows[-1],p))
    # Load T0 old.
    sch=json.loads((WS/'data'/'ballard_z4_cyclic'/'ballard_z4_cyclic_scheme.json').read_text())
    U0=np.array(sch['free_orbit_representatives'][0]['U'],dtype=object).reshape(N)%p
    V0=np.array(sch['free_orbit_representatives'][0]['V'],dtype=object).reshape(N)%p
    W0=np.array(sch['free_orbit_representatives'][0]['W'],dtype=object).reshape(N)%p
    T0=np.stack([U0,V0,W0],axis=1)%p
    Tcols=matmul_mod(T0,M,p)
    terms=[]
    # free cyclic terms for four Z4 images.
    for k in range(4):
        A=matmul_mod(Gpows[k],Tcols[:,0].reshape(N,1),p).reshape(N)
        B=matmul_mod(Gpows[k],Tcols[:,1].reshape(N,1),p).reshape(N)
        C=matmul_mod(Gpows[k],Tcols[:,2].reshape(N,1),p).reshape(N)
        terms.append((A,B,C)); terms.append((B,C,A)); terms.append((C,A,B))
    # two length-4 cube orbits.
    for l_y in [np.array(record['l1'],dtype=object),np.array(record['l2'],dtype=object)]:
        l_old=matmul_mod(old_from_y,l_y.reshape(N,1),p).reshape(N)
        for k in range(4):
            lk=matmul_mod(Gpows[k],l_old.reshape(N,1),p).reshape(N)
            terms.append((lk,lk,lk))
    if record['pattern']=='4+4+2':
        coords=record['tail_witness']
        l_y=np.zeros(N,dtype=object); l_y[0:3]=coords[0:3]; l_y[3:5]=coords[3:5]
        l_old=matmul_mod(old_from_y,l_y.reshape(N,1),p).reshape(N)
        for k in range(2):
            lk=matmul_mod(Gpows[k],l_old.reshape(N,1),p).reshape(N)
            terms.append((lk,lk,lk))
    else:
        f1,f2=record['tail_witness']
        for coords in [f1,f2]:
            l_y=np.zeros(N,dtype=object); l_y[0:3]=coords
            l_old=matmul_mod(old_from_y,l_y.reshape(N,1),p).reshape(N)
            terms.append((l_old,l_old,l_old))
    # target tensor.
    T=np.zeros((N,N,N),dtype=object)
    for a,b,c in itertools.product(range(3), repeat=3):
        T[3*a+b,3*b+c,3*c+a]=(int(T[3*a+b,3*b+c,3*c+a])+1)%p
    S=np.zeros((N,N,N),dtype=object)
    for A,B,C in terms:
        for i in range(N):
            if int(A[i])%p==0: continue
            for j in range(N):
                if int(B[j])%p==0: continue
                for k in range(N):
                    if int(C[k])%p==0: continue
                    S[i,j,k]=(int(S[i,j,k])+int(A[i])*int(B[j])*int(C[k]))%p
    diff=(S-T)%p
    return {'term_count':len(terms),'brent_nonzero':int(sum(1 for x in diff.reshape(-1) if int(x)%p)), 'max_entry_mod':int(max(int(x)%p for x in diff.reshape(-1)) if diff.size else 0)}


def positive_control(ctx,len2_tails,fixed2_tails):
    # BILR M=I residual should decompose as 4+4+2+1, not a rank-10 pattern.
    p=ctx['p']; C=(ctx['target_y']-free_contribution(ctx['T0_y'],ctx['Ddiag'],p))%p
    qz,qw,pzw=extract_blocks(C)
    return {'qz_rank':int(rank_mod(qz,p)), 'qw_rank':int(rank_mod(qw,p)), 'qz_conic_points': [list(map(int,x)) for x in conic_points_rowspace(qz,p)], 'rank10_matches_at_BILR':len(decompose_C(C,ctx,len2_tails,fixed2_tails,max_records=2))}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--prime',type=int,default=5)
    ap.add_argument('--limit',type=int,default=0,help='0 means full LU chart p^6')
    ap.add_argument('--stop-on-hit',action='store_true')
    args=ap.parse_args()
    p=args.prime
    if p%4!=1 or p in (2,3): raise SystemExit('prime must be !=2,3 and 1 mod 4')
    t0=time.time(); ctx=build_context(p); len2,fixed2=precompute_tails(ctx)
    pc=positive_control(ctx,len2,fixed2)
    total=p**6 if args.limit==0 else min(args.limit,p**6)
    records=[]; stats={'tested':0,'off_qz_rank2':0,'conic_two':0,'hits':0}
    start=time.time()
    for idx,vals in enumerate(itertools.product(range(p), repeat=6)):
        if idx>=total: break
        M=M_from_lu(vals,p)
        Tcols=matmul_mod(ctx['T0_y'],M,p)
        C=(ctx['target_y']-free_contribution(Tcols,ctx['Ddiag'],p))%p
        stats['tested']+=1
        qz,qw,_=extract_blocks(C)
        if rank_mod(qz,p)==2 and rank_mod(qw,p)==2:
            stats['off_qz_rank2']+=1
            if len(conic_points_rowspace(qz,p))==2:
                stats['conic_two']+=1
        decs=decompose_C(C,ctx,len2,fixed2,max_records=2)
        if decs:
            for rec in decs:
                ver=tensor_verify_candidate(ctx,M,rec)
                records.append({'lu_values':list(map(int,vals)),'M':[[int(M[i,j])%p for j in range(3)] for i in range(3)],'decomposition':rec,'verification':ver})
                print('HIT',records[-1],flush=True)
            stats['hits']+=len(decs)
            if args.stop_on_hit: break
        if stats['tested']%5000==0:
            print(f"tested {stats['tested']}/{total}, hits={stats['hits']}, elapsed={time.time()-start:.1f}s",flush=True)
    summary={'prime':p,'scope':'exact F_p-rational scan of LU SL3/T chart using corrected Z4 pairing action; not a characteristic-zero proof',
             'setup_seconds':time.time()-t0,'scan_seconds':time.time()-start,'positive_control':pc,
             'tail_dictionary_sizes':{'length2':len(len2),'two_fixed':len(fixed2)},'stats':stats,'hits':records[:20]}
    out=OUT/f'f{p}_lu_block_scan.json'
    out.write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'out':str(out),'stats':stats,'positive_control':pc,'hit_count_saved':len(records)},indent=2),flush=True)

if __name__=='__main__':
    main()
