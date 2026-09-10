#!/usr/bin/env python3
"""analysis: direct finite-field local search for the tau anti-sector m0.

m0 is the least number of decomposable bivectors eta_j=p_j∧q_j in Lambda^2(F^9)
whose linear span contains the 3-dimensional target plane
    L_anti = < -sum_k e_{0k}∧e_{1k}, -sum_k e_{0k}∧e_{2k}, -sum_k e_{1k}∧e_{2k} >.
The c_j coefficients in T_anti = sum c_j⊗eta_j are then obtained by linear
coordinates, so they need not be searched separately.

This script does exact arithmetic over F_3 and uses randomized hill climbing on
    defect = rank(span(eta_j) + L_anti) - rank(span(eta_j)).
A defect-zero hit for m=7 or 8 is a real finite-field anti configuration.  A miss
is only search information.
"""
from __future__ import annotations
import argparse, json, random, time
from pathlib import Path
from collections import Counter
import numpy as np

P=3
SESSION=Path(__file__).resolve().parents[1]
OUT=SESSION/'data'/'anti_exact'
OUT.mkdir(parents=True,exist_ok=True)

def idx(i,k): return 3*i+k

def inv(a): return 1 if int(a)%P==1 else 2

def rref_rank(M):
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
    return r,M,piv

def rank_mod(M): return rref_rank(M)[0]

def solve_coords(basis_rows, targets):
    """Find coordinates C with C @ basis_rows = targets over F3, if possible."""
    B=np.array(basis_rows,dtype=np.int8)%P
    T=np.array(targets,dtype=np.int8)%P
    m,d=B.shape
    coords=[]
    for t in T:
        # solve B^T x = t^T
        A=np.concatenate([B.T, t.reshape(d,1)],axis=1).astype(np.int8)%P
        rows,cols=A.shape; r=0; piv=[]
        for c in range(m):
            pivrow=None
            for i in range(r,rows):
                if A[i,c]%P: pivrow=i; break
            if pivrow is None: continue
            if pivrow!=r: A[[r,pivrow]]=A[[pivrow,r]]
            A[r]=(A[r]*inv(A[r,c]))%P
            for i in range(rows):
                if i!=r and A[i,c]%P:
                    A[i]=(A[i]-int(A[i,c])*A[r])%P
            piv.append(c); r+=1
        # inconsistency row 0...0 | nonzero
        bad=False
        for i in range(r,rows):
            if not np.any(A[i,:m]%P) and A[i,m]%P:
                bad=True; break
        if bad: return None
        x=np.zeros(m,dtype=np.int8)
        for row,c in enumerate(piv): x[c]=A[row,m]%P
        coords.append(x)
    return np.array(coords,dtype=np.int8)%P

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

def defect(etas):
    E=np.array(etas,dtype=np.int8)%P
    rE=rank_mod(E) if len(E) else 0
    rEL=rank_mod(np.vstack([E,L])) if len(E) else rank_mod(L)
    return int(rEL-rE), int(rE), int(rEL)

def rand_nonzero(rng,n=9):
    while True:
        v=np.array([rng.randrange(P) for _ in range(n)],dtype=np.int8)
        if np.any(v): return v

def rand_pair(rng):
    p=rand_nonzero(rng)
    for _ in range(100):
        q=rand_nonzero(rng)
        if np.any(wedge_vec(p,q)): return p,q
    return p,rand_nonzero(rng)

def canonical_pairs():
    pairs=[]
    for a,b in [(0,1),(0,2),(1,2)]:
        for k in range(3):
            p=np.zeros(9,dtype=np.int8); q=np.zeros(9,dtype=np.int8)
            p[idx(a,k)]=1; q[idx(b,k)]=1
            pairs.append((p,q))
    return pairs

def eval_pairs(pairs):
    return defect([wedge_vec(p,q) for p,q in pairs])

def save_hit(m,pairs,seed,restart,step,path_tail):
    etas=np.array([wedge_vec(p,q) for p,q in pairs],dtype=np.int8)%P
    coords=solve_coords(etas,L)
    data={'field':'F3','m':m,'seed':seed,'restart':restart,'ARTIFACT':step,
          'defect':defect(etas),'coordinates_for_target_rows':None if coords is None else coords.astype(int).tolist(),
          'pairs':[{'p':[int(x) for x in p%P],'q':[int(x) for x in q%P],'eta':[int(x) for x in wedge_vec(p,q)%P]} for p,q in pairs],
          'path_tail':path_tail,
          'verification':{'target_contained':coords is not None and np.array_equal((coords@etas)%P,L%P)}}
    pth=OUT/f'anti_subspace_m{m}_hit_F3_seed{seed}_r{restart}_s{step}.json'
    pth.write_text(json.dumps(data,indent=2)+'\n')
    return str(pth.relative_to(SESSION))

def run(args):
    rng=random.Random(args.seed)
    best={'score':(99,99,99),'pairs':None,'restart':None,'ARTIFACT':None,'path_tail':[]}
    hit_path=None; hist=Counter(); restarts=[]; t0=time.time()
    canonical=canonical_pairs()
    for r in range(args.restarts):
        if args.m==9 and r==0:
            pairs=[(p.copy(),q.copy()) for p,q in canonical]
        elif args.seed_from_canonical and args.m < 9 and r < 60:
            # Seed by canonical subsets of the requested length.  Earlier analysis
            # runs incorrectly dropped only one canonical pair for every m<9,
            # so the m=7 best record could contain eight pairs.  Keep this
            # assertion to protect the finite-field evidence provenance.
            drops = set(rng.sample(range(9), 9 - args.m))
            pairs=[(p.copy(),q.copy()) for i,(p,q) in enumerate(canonical) if i not in drops]
            while len(pairs)<args.m: pairs.append(rand_pair(rng))
            assert len(pairs) == args.m
        else:
            pairs=[rand_pair(rng) for _ in range(args.m)]
        cur=eval_pairs(pairs); local_best=cur; path=[]; temp=args.temperature
        for s in range(args.steps):
            hist[cur[0]]+=1
            if cur[0]==0:
                hit_path=save_hit(args.m,pairs,args.seed,r,s,path[-80:])
                return hit_path,best,hist,restarts,time.time()-t0
            if cur < best['score']:
                best={'score':cur,'pairs':[(p.copy(),q.copy()) for p,q in pairs],'restart':r,'ARTIFACT':s,'path_tail':path[-80:]}
            # mutation: replace one pair, or tweak entries of p/q for one pair.
            j=rng.randrange(args.m)
            old=(pairs[j][0].copy(),pairs[j][1].copy())
            move_type=rng.randrange(3)
            if move_type==0:
                pairs[j]=rand_pair(rng)
            else:
                p,q=old[0].copy(),old[1].copy()
                n_changes=1 if rng.random()<0.7 else 2
                for _ in range(n_changes):
                    which=rng.randrange(2); pos=rng.randrange(9); val=rng.randrange(P)
                    if which==0: p[pos]=val
                    else: q[pos]=val
                if np.any(p) and np.any(q) and np.any(wedge_vec(p,q)):
                    pairs[j]=(p%P,q%P)
                else:
                    pairs[j]=rand_pair(rng)
            new=eval_pairs(pairs)
            accept = new <= cur
            if not accept:
                # small chance to escape plateaus; defect dominates, then ranks.
                delta=(new[0]-cur[0])*8 + (new[2]-cur[2]) + (new[1]-cur[1])
                if rng.random() < min(0.2, temp/(1+max(0,delta)**2)):
                    accept=True
            if accept:
                cur=new; local_best=min(local_best,cur)
                if new[0] <= 1 or rng.random()<0.01:
                    path.append({'ARTIFACT':s,'score':list(new),'move':move_type,'term':j})
                    path=path[-100:]
            else:
                pairs[j]=old
            temp*=args.cool
            if time.time()-t0 > args.time_budget:
                break
        restarts.append({'restart':r,'local_best':list(local_best),'final':list(cur)})
        if time.time()-t0 > args.time_budget:
            break
    return hit_path,best,hist,restarts,time.time()-t0

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--m',type=int,default=8)
    ap.add_argument('--restarts',type=int,default=2000)
    ap.add_argument('--steps',type=int,default=400)
    ap.add_argument('--seed',type=int,default=6411)
    ap.add_argument('--time-budget',type=int,default=300)
    ap.add_argument('--temperature',type=float,default=0.03)
    ap.add_argument('--cool',type=float,default=0.9995)
    ap.add_argument('--seed-from-canonical',action='store_true')
    args=ap.parse_args()
    hit,best,hist,restarts,elapsed=run(args)
    out={'field':'F3','m':args.m,'args':vars(args),'hit_path':hit,
         'best':{'score':list(best['score']),'restart':best['restart'],'ARTIFACT':best['ARTIFACT'],
                 'pairs':None if best['pairs'] is None else [{'p':[int(x) for x in p%P],'q':[int(x) for x in q%P]} for p,q in best['pairs']],
                 'path_tail':best['path_tail']},
         'defect_hist':{str(k):int(v) for k,v in sorted(hist.items())},
         'restarts_completed':len(restarts),'restart_summaries_first20':restarts[:20],'restart_summaries_last10':restarts[-10:],
         'elapsed_sec':elapsed,
         'interpretation':'Exact F3 local search on decomposable-bivector containment. A hit is valid finite-field anti-sector data; a miss is not a proof.'}
    path=OUT/f'anti_subspace_local_m{args.m}_F3.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'m':args.m,'hit_path':hit,'best_score':out['best']['score'],'defect_hist':out['defect_hist'],
                      'restarts_completed':out['restarts_completed'],'saved':str(path),'elapsed_sec':elapsed},indent=2)[:20000])
    print('SAVED',path)

if __name__=='__main__': main()
