#!/usr/bin/env python3
"""analysis: faster tau-orbit flip sampler from the standard 27-term seed.

This is a calibration walk in the transpose-invariant flip graph over F_3.
It implements only the clean full-orbit move: choose two distinct tau-free orbits,
perform an ordinary flip on representatives that share one factor, and replace
the tau-image representatives by the exact tau images of the two updated terms.
The local four-term identity is checked exactly over F_3 for every accepted move;
full 729-coordinate replay and tau-invariance replay are checked at rank records
and periodically.

The walk is meant to answer whether the implementation can at least reach rank 23
from the standard tau-invariant rank-27 seed.  A failure to find rank 22 is only
heuristic search information, not a mathematical lower bound.
"""
from __future__ import annotations
import argparse, json, random, time
from pathlib import Path
from collections import Counter, defaultdict
import numpy as np

P=3
SESSION=Path(__file__).resolve().parents[1]
OUT=SESSION/'data'/'tau_orbit_walk'
OUT.mkdir(parents=True, exist_ok=True)
NEXT={0:1,1:2,2:0}; PREV={0:2,1:0,2:1}


def eij(i,j):
    v=np.zeros(9,dtype=np.int8); v[3*i+j]=1; return v

def matT(v):
    return np.asarray(v,dtype=np.int8).reshape(3,3).T.reshape(9)%P

def tau_term(t):
    a,b,c=t; return (matT(a),matT(c),matT(b))

def standard_scheme():
    return [(eij(i,j),eij(j,k),eij(k,i)) for i in range(3) for j in range(3) for k in range(3)]

def is_zero_vec(v): return not bool(np.any(np.asarray(v)%P))
def is_zero_term(t): return is_zero_vec(t[0]) or is_zero_vec(t[1]) or is_zero_vec(t[2])
def zero_term():
    z=np.zeros(9,dtype=np.int8); return (z.copy(),z.copy(),z.copy())
def copy_scheme(S): return [(a.copy(),b.copy(),c.copy()) for a,b,c in S]
def rank_count(S): return sum(0 if is_zero_term(t) else 1 for t in S)
def term_key(t): return tuple(int(x) for comp in t for x in (comp%P))

def term_tensor(t):
    if is_zero_term(t): return np.zeros(729,dtype=np.int8)
    a,b,c=t
    return np.einsum('i,j,k->ijk',a%P,b%P,c%P,optimize=True).reshape(-1)%P

T333=np.zeros((9,9,9),dtype=np.int8)
for i in range(3):
  for j in range(3):
    for k in range(3): T333[3*i+j,3*j+k,3*k+i]=1
T333_VEC=T333.reshape(-1)%P

def tensor_sum_terms(terms):
    acc=np.zeros(729,dtype=np.int16)
    for t in terms:
        if not is_zero_term(t): acc += term_tensor(t).astype(np.int16)
    return (acc%P).astype(np.int8)

def scheme_tensor(S): return tensor_sum_terms(S)

def exact_tau_perm(S):
    buckets=defaultdict(list)
    for i,t in enumerate(S):
        if not is_zero_term(t): buckets[term_key(t)].append(i)
    used=set(); perm=[None]*len(S)
    for i,t in enumerate(S):
        if is_zero_term(t): continue
        key=term_key(tau_term(t)); cand=None
        for j in buckets.get(key,[]):
            if j not in used: cand=j; break
        if cand is None: return None
        used.add(cand); perm[i]=cand
    return perm

def orbit_class(perm,i,j):
    if perm is None or i>=len(perm) or j>=len(perm) or perm[i] is None or perm[j] is None: return 'zero_or_no_perm'
    ti,tj=perm[i],perm[j]
    if ti==i and tj==j: return 'fixed-fixed'
    if ti==i or tj==j: return 'fixed-free'
    if ti==j and tj==i: return 'same-free-orbit'
    if len({i,j,ti,tj})==4: return 'free-free-4'
    return 'overlap-other'

def duplicate_pairs(S):
    pairs=[]
    for typ in range(3):
        buckets=defaultdict(list)
        for i,t in enumerate(S):
            if not is_zero_term(t): buckets[tuple(int(x) for x in t[typ]%P)].append(i)
        for inds in buckets.values():
            if len(inds)>=2:
                for i in inds:
                    for j in inds:
                        if i!=j: pairs.append((typ,i,j))
    return pairs

def set_comp_raw(t,comp,val):
    lst=[x.copy() for x in t]
    lst[comp]=np.asarray(val,dtype=np.int8)%P
    return zero_term() if any(is_zero_vec(x) for x in lst) else tuple(lst)

def flipped_pair(t1,t2,typ):
    if is_zero_term(t1) or is_zero_term(t2): return None
    if not np.array_equal(t1[typ]%P,t2[typ]%P): return None
    tn,tp=NEXT[typ],PREV[typ]
    nt1=set_comp_raw(t1,tn,(t1[tn]-t2[tn])%P)
    nt2=set_comp_raw(t2,tp,(t1[tp]+t2[tp])%P)
    return nt1,nt2

def make_clean_move(S,perm,typ,i,j,check_local=True):
    cls=orbit_class(perm,i,j)
    if cls!='free-free-4': return None,'filtered_'+cls
    ti,tj=perm[i],perm[j]
    fp=flipped_pair(S[i],S[j],typ)
    if fp is None: return None,'primary_invalid'
    nt_i,nt_j=fp
    old4=[S[i],S[j],S[ti],S[tj]]
    new4=[nt_i,nt_j,tau_term(nt_i) if not is_zero_term(nt_i) else zero_term(), tau_term(nt_j) if not is_zero_term(nt_j) else zero_term()]
    if check_local and not np.array_equal(tensor_sum_terms(old4),tensor_sum_terms(new4)):
        return None,'local_tensor_delta_failed'
    new=copy_scheme(S)
    new[i]=nt_i; new[j]=nt_j; new[ti]=new4[2]; new[tj]=new4[3]
    return new,'accepted_free-free-4'

def summarize(S):
    perm=exact_tau_perm(S); fixed=[]; free=[]; seen=set()
    if perm is not None:
        for i,j in enumerate(perm):
            if j is None or i in seen: continue
            if i==j: fixed.append(i); seen.add(i)
            else: free.append((i,j)); seen.add(i); seen.add(j)
    return {'rank':rank_count(S),'tau_invariant_exact':perm is not None,
            'tensor_matches_T333_F3':bool(np.array_equal(scheme_tensor(S),T333_VEC)),
            'fixed_count':len(fixed),'free_orbit_count':len(free),
            'duplicate_ordered_pair_count':len(duplicate_pairs(S))}

def save_scheme(path,S,meta):
    data=dict(meta); data.update(summarize(S))
    data['terms']=[{'A':[int(x) for x in a%P],'B':[int(x) for x in b%P],'C':[int(x) for x in c%P]} for a,b,c in S if not is_zero_term((a,b,c))]
    path.write_text(json.dumps(data,indent=2)+'\n')

def one_step(seed):
    rng=random.Random(1); perm=exact_tau_perm(seed)
    reasons=Counter(); rh=Counter(); samples=[]
    for typ,i,j in duplicate_pairs(seed):
        new,reason=make_clean_move(seed,perm,typ,i,j,check_local=True)
        reasons[reason]+=1
        if new is not None:
            r=rank_count(new); rh[r]+=1
            if len(samples)<20: samples.append({'type':typ,'i':i+1,'j':j+1,'rank':r})
    return {'reason_counts':dict(reasons),'accepted':sum(rh.values()),'rank_hist':{str(k):int(v) for k,v in sorted(rh.items())},'samples':samples}

def choose_move(S,rng,tries,prefer_reduction=True):
    perm=exact_tau_perm(S)
    if perm is None: return None,'not_tau_before'
    pairs=duplicate_pairs(S)
    if not pairs: return None,'no_duplicate_pairs'
    rng.shuffle(pairs)
    tested=0; reasons=Counter(); best=None
    for typ,i,j in pairs[:tries]:
        tested+=1
        new,reason=make_clean_move(S,perm,typ,i,j,check_local=True)
        reasons[reason]+=1
        if new is None: continue
        item=(typ,i,j,rank_count(new),new)
        if best is None: best=item
        if prefer_reduction and item[3] < rank_count(S):
            return item, {'tested':tested,'reasons':dict(reasons),'reduction_chosen':True}
        # Reservoir-like occasional replacement among valid non-reductions.
        if rng.randrange(4)==0: best=item
    if best is not None: return best, {'tested':tested,'reasons':dict(reasons),'reduction_chosen':False}
    return None, {'tested':tested,'reasons':dict(reasons),'reduction_chosen':False}

def run_walks(args):
    rng=random.Random(args.seed)
    seed=standard_scheme()
    best_rank=rank_count(seed); bestS=copy_scheme(seed); best_meta={}
    first23=None; first22=None
    summaries=[]; total_reasons=Counter(); accepted_total=0; no_move=0; full_check_failures=0
    t0=time.time()
    for r in range(args.restarts):
        S=copy_scheme(seed); hist=Counter({rank_count(S):1}); local_best=rank_count(S); path=[]
        for s in range(args.steps):
            mv,info=choose_move(S,rng,args.tries,prefer_reduction=True)
            total_reasons.update(info.get('reasons',{}))
            if mv is None:
                no_move+=1; break
            typ,i,j,rr,Snew=mv
            S=Snew; accepted_total+=1; hist[rr]+=1; local_best=min(local_best,rr)
            path.append({'type':typ,'i':i+1,'j':j+1,'rank':rr,'tested':info['tested'],'reduction':info['reduction_chosen']})
            if (s+1)%args.full_check_interval==0 or rr<best_rank or rr<=23:
                summ=summarize(S)
                if not (summ['tensor_matches_T333_F3'] and summ['tau_invariant_exact']):
                    full_check_failures+=1
                    raise RuntimeError(f'full replay failed at restart {r} ARTIFACT {s+1}: {summ}')
            if rr<best_rank:
                best_rank=rr; bestS=copy_scheme(S); best_meta={'restart':r,'ARTIFACT':s+1,'path_tail':path[-80:]}
                save_scheme(OUT/f'sample_walk_best_rank{best_rank}.json',bestS,{'kind':'best',**best_meta})
            if rr<=23 and first23 is None:
                p=OUT/f'sample_walk_first_rank{rr}_restart{r}_step{s+1}.json'
                save_scheme(p,S,{'kind':'first_rank_le_23','restart':r,'ARTIFACT':s+1,'path_tail':path[-100:]})
                first23=str(p.relative_to(SESSION))
            if rr<=22 and first22 is None:
                p=OUT/f'sample_walk_first_rank{rr}_restart{r}_step{s+1}.json'
                save_scheme(p,S,{'kind':'first_rank_le_22','restart':r,'ARTIFACT':s+1,'path_tail':path[-150:]})
                first22=str(p.relative_to(SESSION))
                break
        summaries.append({'restart':r,'steps_done':sum(hist.values())-1,'best_rank':local_best,'final_rank':rank_count(S),'rank_hist':{str(k):int(v) for k,v in sorted(hist.items())}})
        if first22 is not None: break
    if not (OUT/f'sample_walk_best_rank{best_rank}.json').exists():
        save_scheme(OUT/f'sample_walk_best_rank{best_rank}.json',bestS,{'kind':'best',**best_meta})
    return {'restarts_requested':args.restarts,'steps_per_restart':args.steps,'tries_per_step':args.tries,
            'full_check_interval':args.full_check_interval,'restarts_completed':len(summaries),'accepted_moves':accepted_total,
            'nodes_with_no_move':no_move,'best_rank':best_rank,'best_scheme_path':str((OUT/f'sample_walk_best_rank{best_rank}.json').relative_to(SESSION)),
            'first_rank_le_23_path':first23,'first_rank_le_22_path':first22,'reason_counts':dict(total_reasons),
            'full_check_failures':full_check_failures,'restart_summaries_first20':summaries[:20],'restart_summaries_last10':summaries[-10:],
            'elapsed_sec':time.time()-t0}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--restarts',type=int,default=1000)
    ap.add_argument('--steps',type=int,default=1000)
    ap.add_argument('--tries',type=int,default=250)
    ap.add_argument('--full-check-interval',type=int,default=200)
    ap.add_argument('--seed',type=int,default=6404)
    args=ap.parse_args()
    seed=standard_scheme()
    out={'field':'F3','seed_summary':summarize(seed),'one_step':one_step(seed),
         'move':'full tau-orbit flip on two distinct free orbits; local four-term tensor delta checked every accepted move',
         'walk':run_walks(args),
         'interpretation':'Calibration of a tau-restricted flip walk from the standard seed. Rank<=23 hits are exact F3 decompositions and useful positive controls; no rank-22 hit is not a proof.'}
    path=OUT/'tau_orbit_sample_walk_summary.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'seed':out['seed_summary'],'one_step':out['one_step'],'walk':out['walk'],'saved':str(path)},indent=2)[:20000])
    print('SAVED',path)

if __name__=='__main__': main()
