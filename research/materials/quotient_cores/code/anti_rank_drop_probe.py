#!/usr/bin/env python3
"""analysis: exact finite-field rank-drop probe for the tau anti-sector.

For the complementary transpose sector
    T_anti in A \otimes Lambda^2 W,  dim A=3, dim W=9,
analysis built the A-wedge flattening
    F_T: A \otimes W^* -> Lambda^2 A \otimes W
with rank 27 and one structured free orbit c \otimes (p wedge q) contributing
rank at most 4.  Therefore an m0=7 anti decomposition would have a strong
necessary property: for every one of its seven terms,
    rank(F_T - F_{c,p,q}) <= 6*4 = 24.
This script checks that condition over F_3 for the canonical 9-term upper bound
and for many random structured terms.  It is a necessary-condition probe, not an
algebraic proof over characteristic zero.
"""
from __future__ import annotations
import argparse, json, random, time
from pathlib import Path
import numpy as np
from collections import Counter

P=3
SESSION=Path(__file__).resolve().parents[1]
OUT=SESSION/'data'/'anti_exact'
OUT.mkdir(parents=True, exist_ok=True)

Apairs=[(0,1),(0,2),(1,2)]
Api={q:i for i,q in enumerate(Apairs)}

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
        iv=inv(int(M[r,c]))
        M[r]=(M[r]*iv)%P
        for i in range(rows):
            if i!=r and M[i,c]%P:
                M[i]=(M[i]-int(M[i,c])*M[r])%P
        r+=1
        if r==rows: break
    return r

def wedge_A(a,s):
    if a==s: return None,0
    if a<s: return (a,s),1
    return (s,a),-1

def theta_contract(ap,beta):
    i,j=ap; out=np.zeros(9,dtype=np.int8)
    for k in range(3):
        ai=idx(i,k); bj=idx(j,k)
        if beta==ai: out[bj]-=1
        if beta==bj: out[ai]+=1
    return out%P

def build_target_F():
    F=np.zeros((27,27),dtype=np.int8)
    for s in range(3):
        for beta in range(9):
            col=s*9+beta
            for r,ap in enumerate(Apairs):
                wa,sgn=wedge_A(r,s)
                if sgn==0: continue
                avec=Api[wa]
                wv=theta_contract(ap,beta)
                for wc,coef in enumerate(wv):
                    if coef%P:
                        F[avec*9+wc,col]=(F[avec*9+wc,col]+sgn*int(coef))%P
    return F%P

def term_F(c,p,q):
    c=np.asarray(c,dtype=np.int8)%P; p=np.asarray(p,dtype=np.int8)%P; q=np.asarray(q,dtype=np.int8)%P
    F=np.zeros((27,27),dtype=np.int8)
    for s in range(3):
        for beta in range(9):
            col=s*9+beta
            wv=(int(p[beta])*q - int(q[beta])*p)%P
            if not np.any(wv): continue
            for r in range(3):
                if c[r]%P==0: continue
                wa,sgn=wedge_A(r,s)
                if sgn==0: continue
                avec=Api[wa]
                for wc,coef in enumerate(wv):
                    if coef%P:
                        F[avec*9+wc,col]=(F[avec*9+wc,col]+int(c[r])*sgn*int(coef))%P
    return F%P

def canonical_terms():
    # theta_{ab} = - sum_k e_{a,k} wedge e_{b,k}; c is row-pair basis coefficient.
    terms=[]
    for r,(a,b) in enumerate(Apairs):
        for k in range(3):
            c=np.zeros(3,dtype=np.int8); c[r]=1
            p=np.zeros(9,dtype=np.int8); q=np.zeros(9,dtype=np.int8)
            # use p=e_a,k, q=e_b,k, coefficient sign chosen by trying both; rank drop invariant under nonzero scalar only tested both.
            p[idx(a,k)]=1; q[idx(b,k)]=1
            terms.append((c,p,q,{'row_pair':(a,b),'k':k,'sign':1}))
            terms.append(((2*c)%P,p,q,{'row_pair':(a,b),'k':k,'sign':-1}))
    return terms

def rand_nonzero_vec(n,rng):
    while True:
        v=np.array([rng.randrange(P) for _ in range(n)],dtype=np.int8)
        if np.any(v): return v

def rankdrop_stats(F, trials, seed):
    rng=random.Random(seed)
    hist=Counter(); best=[]; critical=[]
    for t in range(trials):
        c=rand_nonzero_vec(3,rng)
        p=rand_nonzero_vec(9,rng)
        # ensure q not scalar multiple of p, so wedge nonzero
        for attempt in range(20):
            q=rand_nonzero_vec(9,rng)
            TF=term_F(c,p,q)
            if rank_mod(TF)>0: break
        r=rank_mod((F-TF)%P)
        hist[r]+=1
        item={'trial':t,'rank_after_subtract':r,'c':[int(x) for x in c],'p':[int(x) for x in p],'q':[int(x) for x in q]}
        if len(best)<20 or r<max(x['rank_after_subtract'] for x in best):
            best.append(item); best=sorted(best,key=lambda x:x['rank_after_subtract'])[:20]
        if r<=24:
            critical.append(item)
            if len(critical)>=20:
                # keep searching? critical would be major; return enough examples.
                pass
    return {'trials':trials,'rank_hist':{str(k):int(v) for k,v in sorted(hist.items())},'best_terms':best,'critical_rank_le_24_count':len(critical),'critical_examples':critical[:20]}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--trials',type=int,default=20000)
    ap.add_argument('--seed',type=int,default=6406)
    args=ap.parse_args()
    t0=time.time(); F=build_target_F(); rF=rank_mod(F)
    canon=[]
    for c,p,q,meta in canonical_terms():
        TF=term_F(c,p,q)
        canon.append({**meta,'term_rank':rank_mod(TF),'rank_after_subtract':rank_mod((F-TF)%P)})
    stats=rankdrop_stats(F,args.trials,args.seed)
    out={'field':'F3','target_rank':rF,'canonical_9_upper_term_rankdrop':canon,
         'random_rankdrop_probe':stats,
         'm7_necessary_condition':'If m0=7, at least seven structured terms with rank(F-term)<=24 must exist; random absence is not proof.',
         'elapsed_sec':time.time()-t0}
    path=OUT/'anti_rank_drop_probe_F3.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2)[:20000])
    print('SAVED',path)

if __name__=='__main__': main()
