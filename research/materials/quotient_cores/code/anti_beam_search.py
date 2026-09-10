#!/usr/bin/env python3
"""analysis: heuristic exact F3 beam search for the tau anti-sector m0.

Target: T_anti in A \otimes Lambda^2 W from analysis, with rows
    theta_ab = - sum_k e_{a,k} wedge e_{b,k}.
A tau-free orbit supplies one structured term c \otimes (p wedge q).
This script searches over F_3 for decompositions with m=7 or m=8 terms.

The search is exact arithmetic but heuristic: a hit is a real finite-field anti
configuration; a miss is not a theorem.  The ranking uses the analysis A-wedge
flattening F_T, whose rank gives the lower bound m>=7.
"""
from __future__ import annotations
import argparse, json, random, time, heapq
from pathlib import Path
from collections import Counter
import numpy as np

P=3
SESSION=Path(__file__).resolve().parents[1]
OUT=SESSION/'data'/'anti_exact'
OUT.mkdir(parents=True,exist_ok=True)
Apairs=[(0,1),(0,2),(1,2)]; Api={q:i for i,q in enumerate(Apairs)}

def idx(i,k): return 3*i+k

def inv(a): return 1 if a%P==1 else 2

def rank_mod(M):
    M=np.array(M,dtype=np.int8)%P
    rows,cols=M.shape; r=0
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i,c]%P: piv=i; break
        if piv is None: continue
        if piv!=r: M[[r,piv]]=M[[piv,r]]
        M[r]=(M[r]*inv(int(M[r,c])))%P
        for i in range(rows):
            if i!=r and M[i,c]%P:
                M[i]=(M[i]-int(M[i,c])*M[r])%P
        r+=1
        if r==rows: break
    return int(r)

def wedge_A(a,s):
    if a==s: return None,0
    if a<s: return (a,s),1
    return (s,a),-1

def theta_rows():
    T=np.zeros((3,36),dtype=np.int8)
    pairs=[(i,j) for i in range(9) for j in range(i+1,9)]
    pi={p:i for i,p in enumerate(pairs)}
    for r,(a,b) in enumerate(Apairs):
        for k in range(3):
            i=idx(a,k); j=idx(b,k)
            if i<j: T[r,pi[(i,j)]] -= 1
            else: T[r,pi[(j,i)]] += 1
    return T%P

def wedge_vec(p,q):
    v=np.zeros(36,dtype=np.int8); t=0
    for i in range(9):
        for j in range(i+1,9):
            v[t]=(int(p[i])*int(q[j])-int(p[j])*int(q[i]))%P; t+=1
    return v%P

def build_F_from_rows(R):
    # R is 3 x 36, coordinates in wedge pairs i<j. Build F_R: A⊗W* -> Λ²A⊗W.
    pairs=[(i,j) for i in range(9) for j in range(i+1,9)]
    F=np.zeros((27,27),dtype=np.int8)
    for s in range(3):
        for beta in range(9):
            col=s*9+beta
            for r in range(3):
                wa,sgn=wedge_A(r,s)
                if sgn==0: continue
                avec=Api[wa]
                # contraction of row R[r] by e_beta^*: sum coeff*(δ_beta,i e_j - δ_beta,j e_i)
                for coeff,(i,j) in zip(R[r],pairs):
                    if coeff%P==0: continue
                    if beta==i:
                        F[avec*9+j,col]=(F[avec*9+j,col]+sgn*int(coeff))%P
                    if beta==j:
                        F[avec*9+i,col]=(F[avec*9+i,col]-sgn*int(coeff))%P
    return F%P

def term_rows(c,p,q):
    eta=wedge_vec(p,q)
    return (np.asarray(c,dtype=np.int8).reshape(3,1)%P * eta.reshape(1,36))%P

def term_record(c,p,q):
    return {'c':[int(x) for x in c%P],'p':[int(x) for x in p%P],'q':[int(x) for x in q%P]}

def rand_nonzero(n,rng):
    while True:
        v=np.array([rng.randrange(P) for _ in range(n)],dtype=np.int8)
        if np.any(v): return v

def random_term(rng):
    c=rand_nonzero(3,rng); p=rand_nonzero(9,rng)
    for _ in range(40):
        q=rand_nonzero(9,rng)
        if np.any(wedge_vec(p,q)): return c,p,q
    return c,p,rand_nonzero(9,rng)

def canonical_decomp():
    terms=[]
    for r,(a,b) in enumerate(Apairs):
        for k in range(3):
            c=np.zeros(3,dtype=np.int8); c[r]=2  # minus sign in target
            p=np.zeros(9,dtype=np.int8); q=np.zeros(9,dtype=np.int8)
            p[idx(a,k)]=1; q[idx(b,k)]=1
            terms.append((c,p,q))
    return terms

def residual_from_terms(terms,target):
    R=target.copy()
    for c,p,q in terms:
        R=(R-term_rows(c,p,q))%P
    return R

def state_score(R, depth, m):
    F=build_F_from_rows(R)
    rf=rank_mod(F)
    nz=int(np.count_nonzero(R%P))
    rr=rank_mod(R)
    rem=m-depth
    # Penalize states that violate the flattening bound for remaining terms heavily.
    infeas = 1 if rf>4*rem else 0
    return (infeas, max(0,rf-4*rem), rf, rr, nz)

def seed_states(target,m):
    states=[{'terms':[], 'R':target.copy(), 'origin':'empty'}]
    if m>=9:
        states.append({'terms':canonical_decomp(), 'R':residual_from_terms(canonical_decomp(),target), 'origin':'canonical9'})
    # For m=8/7, seed by dropping each canonical term and by merging two random canonical terms is still just a start.
    can=canonical_decomp()
    if m<9:
        for drop in range(9):
            terms=[t for i,t in enumerate(can) if i!=drop]
            if len(terms)<=m:
                states.append({'terms':terms,'R':residual_from_terms(terms,target),'origin':f'canonical_drop_{drop}'})
    return states

def beam_search(m, trials_per_state, beam, rounds, seed):
    rng=random.Random(seed)
    target=theta_rows()
    start=seed_states(target,m)
    frontier=[]
    for st in start:
        if len(st['terms'])<=m:
            sc=state_score(st['R'],len(st['terms']),m)
            frontier.append((sc, rng.random(), st))
    frontier=sorted(frontier,key=lambda x:x[0])[:beam]
    best={'score':frontier[0][0],'terms':frontier[0][2]['terms'],'R':frontier[0][2]['R'],'depth':len(frontier[0][2]['terms']),'origin':frontier[0][2].get('origin')}
    depth_summaries=[]; hit=None; t0=time.time()
    for depth in range(0,m):
        candidates=[]; considered=0; feasible_rank=Counter()
        # Expand only states with current number of terms == depth when possible; otherwise fill partial states.
        active=[st for _,__,st in frontier if len(st['terms'])==depth]
        if not active:
            active=[st for _,__,st in frontier if len(st['terms'])<m]
        for st in active[:beam]:
            cur_depth=len(st['terms'])
            if cur_depth>=m: continue
            # include a small deterministic pool of canonical terms plus random terms.
            pool=[]
            pool.extend(canonical_decomp())
            for _ in range(trials_per_state):
                pool.append(random_term(rng))
            for c,p,q in pool:
                R2=(st['R']-term_rows(c,p,q))%P
                terms2=st['terms']+[(c,p,q)]
                sc=state_score(R2,len(terms2),m)
                considered+=1; feasible_rank[sc[2]]+=1
                if sc < best['score'] or (np.count_nonzero(R2)==0 and hit is None):
                    best={'score':sc,'terms':terms2,'R':R2,'depth':len(terms2),'origin':st.get('origin')}
                if np.count_nonzero(R2)==0:
                    hit={'m':m,'terms':[term_record(*t) for t in terms2], 'depth':len(terms2),'score':sc,'elapsed_sec':time.time()-t0}
                    return hit,best,depth_summaries
                # Keep candidates that are not blatantly impossible by flattening when possible.
                if sc[0]==0 or len(terms2)>=m-1:
                    candidates.append((sc,rng.random(),{'terms':terms2,'R':R2,'origin':st.get('origin','random')}))
                elif len(candidates)<beam:
                    candidates.append((sc,rng.random(),{'terms':terms2,'R':R2,'origin':st.get('origin','random')}))
        if not candidates:
            break
        frontier=sorted(candidates,key=lambda x:(x[0],x[1]))[:beam]
        scores=[x[0] for x in frontier]
        depth_summaries.append({'after_terms':min(len(x[2]['terms']) for x in frontier),'considered':considered,
                                'best_score':list(scores[0]),'worst_kept_score':list(scores[-1]),
                                'residual_rank_hist_considered':{str(k):int(v) for k,v in sorted(feasible_rank.items())}})
        if time.time()-t0>rounds:
            break
    return hit,best,depth_summaries

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--m',type=int,default=7)
    ap.add_argument('--trials-per-state',type=int,default=1500)
    ap.add_argument('--beam',type=int,default=80)
    ap.add_argument('--time-budget',type=int,default=300)
    ap.add_argument('--seed',type=int,default=6407)
    args=ap.parse_args()
    hit,best,summ=beam_search(args.m,args.trials_per_state,args.beam,args.time_budget,args.seed)
    out={'field':'F3','m':args.m,'trials_per_state':args.trials_per_state,'beam':args.beam,
         'hit':hit,'best':{'score':list(best['score']),'depth':best['depth'],'nonzero_residual_entries':int(np.count_nonzero(best['R']%P)),
                          'residual_rows':best['R'].astype(int).tolist(),
                          'terms':[term_record(*t) for t in best['terms']], 'origin':best.get('origin')},
         'depth_summaries':summ,
         'interpretation':'Exact finite-field heuristic. A hit gives an F3 anti-sector configuration; no hit is not a proof.'}
    path=OUT/f'anti_beam_m{args.m}_F3.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'m':args.m,'hit':hit is not None,'best_score':out['best']['score'],'best_depth':out['best']['depth'],
                      'best_nonzero':out['best']['nonzero_residual_entries'],'depth_summaries':summ[-5:],'saved':str(path)},indent=2)[:20000])
    print('SAVED',path)

if __name__=='__main__': main()
