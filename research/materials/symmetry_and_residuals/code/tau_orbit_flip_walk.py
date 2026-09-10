#!/usr/bin/env python3
"""analysis: corrected tau-orbit flip walk from the standard 27-term seed.

The analysis/early-analysis paired-flip probe applied the ordinary flip-cpd update
also to the tau-image pair.  That is too restrictive for a transpose-type action:
tau swaps the second and third tensor factors, so the conjugate update is the
transpose image of the primary updated pair, not the same ordered flip formula.

This script implements the clean order-2 orbit move directly.  If two terms i,j
in full tau-orbits share one component, apply a flip-cpd flip to i,j, then replace
tau(i),tau(j) by the exact tau-images of the two new terms.  This preserves the
matrix-multiplication tensor because the primary two-term identity and its tau
image both hold.  It preserves exact tau-invariance by construction, and every
accepted move is replayed against all 729 coordinates over F_3.

The experiment is a calibration of the transpose-invariant flip graph, not an
emptiness proof for rank 22.
"""
from __future__ import annotations
import argparse, json, random, time
from pathlib import Path
from collections import Counter, defaultdict
import numpy as np

P = 3
SESSION = Path(__file__).resolve().parents[1]
OUT = SESSION / "data" / "tau_orbit_walk"
OUT.mkdir(parents=True, exist_ok=True)

NEXT = {0: 1, 1: 2, 2: 0}
PREV = {0: 2, 1: 0, 2: 1}
SIGMA = {0: 0, 1: 2, 2: 1}


def eij(i, j):
    v = np.zeros(9, dtype=np.int8)
    v[3*i+j] = 1
    return v


def matT(v):
    return np.asarray(v, dtype=np.int8).reshape(3, 3).T.reshape(9) % P


def tau_term(t):
    a, b, c = t
    return (matT(a), matT(c), matT(b))


def standard_scheme():
    terms=[]
    for i in range(3):
        for j in range(3):
            for k in range(3):
                terms.append((eij(i,j), eij(j,k), eij(k,i)))
    return terms


def is_zero_vec(v):
    return not bool(np.any(np.asarray(v) % P))


def is_zero_term(t):
    return is_zero_vec(t[0]) or is_zero_vec(t[1]) or is_zero_vec(t[2])


def zero_term():
    z=np.zeros(9,dtype=np.int8)
    return (z.copy(),z.copy(),z.copy())


def term_key(t):
    return tuple(int(x) for comp in t for x in (comp % P))


def copy_scheme(scheme):
    return [(a.copy(),b.copy(),c.copy()) for a,b,c in scheme]


def rank_count(scheme):
    return sum(0 if is_zero_term(t) else 1 for t in scheme)


T333 = np.zeros((9,9,9), dtype=np.int8)
for i in range(3):
    for j in range(3):
        for k in range(3):
            T333[3*i+j, 3*j+k, 3*k+i] = 1
T333_VEC = T333.reshape(-1) % P


def term_tensor(t):
    if is_zero_term(t):
        return np.zeros(729,dtype=np.int8)
    a,b,c=t
    return np.einsum('i,j,k->ijk', a%P,b%P,c%P, optimize=True).reshape(-1)%P


def scheme_tensor(scheme):
    acc=np.zeros(729,dtype=np.int16)
    for t in scheme:
        if not is_zero_term(t):
            acc += term_tensor(t).astype(np.int16)
    return (acc%P).astype(np.int8)


def exact_tau_perm(scheme):
    buckets=defaultdict(list)
    for i,t in enumerate(scheme):
        if not is_zero_term(t):
            buckets[term_key(t)].append(i)
    used=set(); perm=[None]*len(scheme)
    for i,t in enumerate(scheme):
        if is_zero_term(t):
            continue
        key=term_key(tau_term(t))
        cand=None
        for j in buckets.get(key,[]):
            if j not in used:
                cand=j; break
        if cand is None:
            return None
        used.add(cand); perm[i]=cand
    return perm


def tau_invariant(scheme):
    return exact_tau_perm(scheme) is not None


def set_comp_raw(term, comp, val):
    lst=[x.copy() for x in term]
    lst[comp]=np.asarray(val,dtype=np.int8)%P
    if is_zero_vec(lst[0]) or is_zero_vec(lst[1]) or is_zero_vec(lst[2]):
        return zero_term()
    return tuple(lst)


def flipped_pair(t1, t2, typ):
    """Return the ordinary flip-cpd updated ordered pair, or None if typ not shared."""
    if is_zero_term(t1) or is_zero_term(t2) or np.array_equal(t1,t2):
        pass
    if is_zero_term(t1) or is_zero_term(t2):
        return None
    if not np.array_equal(t1[typ] % P, t2[typ] % P):
        return None
    tn,tp=NEXT[typ],PREV[typ]
    n1=t1[tn].copy(); n2=t2[tn].copy()
    p1=t1[tp].copy(); p2=t2[tp].copy()
    nt1=set_comp_raw(t1, tn, (n1-n2)%P)
    nt2=set_comp_raw(t2, tp, (p1+p2)%P)
    return nt1,nt2


def duplicate_pairs(scheme):
    out=[]
    for typ in range(3):
        buckets=defaultdict(list)
        for i,t in enumerate(scheme):
            if not is_zero_term(t):
                buckets[tuple(int(x) for x in (t[typ]%P))].append(i)
        for inds in buckets.values():
            if len(inds)>=2:
                for i in inds:
                    for j in inds:
                        if i!=j:
                            out.append((typ,i,j))
    return out


def orbit_class(perm,i,j):
    if perm is None or perm[i] is None or perm[j] is None:
        return 'zero_or_no_perm'
    ti,tj=perm[i],perm[j]
    if ti==i and tj==j:
        return 'fixed-fixed'
    if ti==i or tj==j:
        return 'fixed-free'
    if ti==j and tj==i:
        return 'same-free-orbit'
    if len({i,j,ti,tj})==4:
        return 'free-free-4'
    return 'overlap-other'


def clean_tau_orbit_flip(scheme, typ, i, j, *, allowed_classes=frozenset({'free-free-4'})):
    perm=exact_tau_perm(scheme)
    if perm is None:
        return None,'not_tau_before'
    cls=orbit_class(perm,i,j)
    if cls not in allowed_classes:
        return None,'filtered_'+cls
    ti,tj=perm[i],perm[j]
    fp=flipped_pair(scheme[i],scheme[j],typ)
    if fp is None:
        return None,'primary_invalid'
    nt_i, nt_j=fp
    new=copy_scheme(scheme)
    new[i]=nt_i; new[j]=nt_j
    # Replace image orbit by actual tau-images of the newly created terms.
    new[ti]=tau_term(nt_i) if not is_zero_term(nt_i) else zero_term()
    new[tj]=tau_term(nt_j) if not is_zero_term(nt_j) else zero_term()
    if not np.array_equal(scheme_tensor(new), T333_VEC):
        return None,'tensor_changed'
    if not tau_invariant(new):
        return None,'tau_lost'
    return new,'accepted_'+cls


def all_moves(scheme, rng=None, max_pairs=None, allowed_classes=frozenset({'free-free-4'})):
    pairs=duplicate_pairs(scheme)
    if rng is not None:
        rng.shuffle(pairs)
    if max_pairs is not None:
        pairs=pairs[:max_pairs]
    moves=[]; reasons=Counter()
    for typ,i,j in pairs:
        new,reason=clean_tau_orbit_flip(scheme,typ,i,j,allowed_classes=allowed_classes)
        reasons[reason]+=1
        if new is not None:
            moves.append((typ,i,j,rank_count(new),new,reason.replace('accepted_','')))
    return moves,reasons,len(pairs)


def fingerprint(scheme):
    return tuple(sorted(term_key(t) for t in scheme if not is_zero_term(t)))


def summarize_scheme(scheme):
    perm=exact_tau_perm(scheme)
    fixed=[]; free=[]; seen=set()
    if perm is not None:
        for i,j in enumerate(perm):
            if j is None or i in seen: continue
            if i==j:
                fixed.append(i); seen.add(i)
            else:
                free.append((i,j)); seen.add(i); seen.add(j)
    bucket_hist={}
    for typ in range(3):
        buckets=defaultdict(list)
        for i,t in enumerate(scheme):
            if not is_zero_term(t):
                buckets[tuple(int(x) for x in t[typ])].append(i+1)
        bucket_hist[str(typ)]={str(k):int(v) for k,v in sorted(Counter(len(x) for x in buckets.values()).items())}
    return {
        'rank':rank_count(scheme),
        'tensor_matches_T333_F3':bool(np.array_equal(scheme_tensor(scheme),T333_VEC)),
        'tau_invariant_exact':perm is not None,
        'fixed_count':len(fixed),
        'free_orbit_count':len(free),
        'fixed_indices_1based':[i+1 for i in fixed],
        'free_orbits_1based':[[i+1,j+1] for i,j in free],
        'duplicate_ordered_pair_count':len(duplicate_pairs(scheme)),
        'duplicate_bucket_size_hist_by_component':bucket_hist,
    }


def save_scheme(path, scheme, meta):
    data=dict(meta)
    data.update({
        'field':'F3',
        'rank':rank_count(scheme),
        'tensor_matches_T333_F3':bool(np.array_equal(scheme_tensor(scheme),T333_VEC)),
        'tau_invariant_exact':bool(tau_invariant(scheme)),
        'terms':[{'A':[int(x) for x in a%P], 'B':[int(x) for x in b%P], 'C':[int(x) for x in c%P]}
                 for a,b,c in scheme if not is_zero_term((a,b,c))],
    })
    path.write_text(json.dumps(data,indent=2)+'\n')


def one_step(seed, rng, allowed_classes):
    moves,reasons,tested=all_moves(seed,rng=rng,allowed_classes=allowed_classes)
    rh=Counter(r for *_,r,__,___ in moves)
    return {
        'tested_duplicate_pairs':tested,
        'accepted_move_count':len(moves),
        'reason_counts':dict(reasons),
        'rank_hist_after_one_step':{str(k):int(v) for k,v in sorted(rh.items())},
        'min_rank_after_one_step':min(rh) if rh else rank_count(seed),
        'sample_accepted_moves':[{'type':typ,'i':i+1,'j':j+1,'rank':r,'class':cls} for typ,i,j,r,_,cls in moves[:20]],
    }


def random_walks(seed, *, restarts, steps, max_pairs, rng_seed, allowed_classes, mode_name):
    rng=random.Random(rng_seed)
    best_rank=rank_count(seed); best_scheme=copy_scheme(seed); best_meta={}
    first23=None; first22=None
    reason_total=Counter(); accepted_total=0; no_move_nodes=0
    summaries=[]; t0=time.time()
    for r in range(restarts):
        scheme=copy_scheme(seed)
        hist=Counter({rank_count(scheme):1})
        local_best=rank_count(scheme); path=[]
        for s in range(steps):
            moves,reasons,tested=all_moves(scheme,rng=rng,max_pairs=max_pairs,allowed_classes=allowed_classes)
            reason_total.update(reasons)
            if not moves:
                no_move_nodes+=1
                break
            # Prefer reductions, otherwise random.  A rank-preserving walk is still useful
            # because it creates new repeated factors for later reductions.
            cur=rank_count(scheme)
            minr=min(m[3] for m in moves)
            cand=[m for m in moves if m[3]==minr] if minr<cur else moves
            typ,i,j,rr,new,cls=rng.choice(cand)
            scheme=new; accepted_total+=1
            path.append({'type':typ,'i':i+1,'j':j+1,'rank':rr,'class':cls})
            hist[rr]+=1; local_best=min(local_best,rr)
            if rr<best_rank:
                best_rank=rr; best_scheme=copy_scheme(scheme); best_meta={'restart':r,'ARTIFACT':s+1,'path_tail':path[-50:]}
                save_scheme(OUT/f'{mode_name}_best_rank{best_rank}.json', best_scheme, {'mode':mode_name, **best_meta})
            if rr<=23 and first23 is None:
                p=OUT/f'{mode_name}_first_rank{rr}_restart{r}_step{s+1}.json'
                save_scheme(p,scheme,{'mode':mode_name,'restart':r,'ARTIFACT':s+1,'path_tail':path[-50:]})
                first23=str(p.relative_to(SESSION))
            if rr<=22 and first22 is None:
                p=OUT/f'{mode_name}_first_rank{rr}_restart{r}_step{s+1}.json'
                save_scheme(p,scheme,{'mode':mode_name,'restart':r,'ARTIFACT':s+1,'path_tail':path[-80:]})
                first22=str(p.relative_to(SESSION))
                break
        summaries.append({'restart':r,'steps_done':sum(hist.values())-1,'best_rank':local_best,'final_rank':rank_count(scheme),
                          'rank_hist':{str(k):int(v) for k,v in sorted(hist.items())}})
        if first22 is not None:
            break
    best_path=OUT/f'{mode_name}_best_rank{best_rank}.json'
    if not best_path.exists():
        save_scheme(best_path,best_scheme,{'mode':mode_name, **best_meta})
    return {
        'mode':mode_name,
        'allowed_classes':sorted(allowed_classes),
        'restarts_requested':restarts,
        'steps_per_restart':steps,
        'max_pairs_per_node':max_pairs,
        'restarts_completed':len(summaries),
        'total_accepted_moves':accepted_total,
        'nodes_with_no_accepted_moves':no_move_nodes,
        'best_rank':best_rank,
        'best_scheme_path':str(best_path.relative_to(SESSION)),
        'first_rank_le_23_path':first23,
        'first_rank_le_22_path':first22,
        'reason_counts':dict(reason_total),
        'restart_summaries_first20':summaries[:20],
        'restart_summaries_last5':summaries[-5:],
        'elapsed_sec':time.time()-t0,
    }


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--restarts',type=int,default=100)
    ap.add_argument('--steps',type=int,default=200)
    ap.add_argument('--max-pairs',type=int,default=400)
    ap.add_argument('--seed',type=int,default=6402)
    ap.add_argument('--classes',default='free-free-4',help='comma-separated allowed orbit classes')
    args=ap.parse_args()
    allowed=frozenset(x.strip() for x in args.classes.split(',') if x.strip())
    seed_scheme=standard_scheme()
    rng=random.Random(args.seed)
    out={
        'source':'standard 27-term T333 decomposition over F3',
        'tau':'tau(A,B,C)=(A^T,C^T,B^T)',
        'move':'clean orbit flip: flip representative pair, replace image pair by exact tau-images of updated pair; exact 729-coordinate replay after each move',
        'mp_paper_lookup':{
            'finding':'Moosbauer--Poole use C3 and C3 x Z2 where Z2 is row/column reversal inside each factor, not transpose-type factor-swap tau; their n=3 statement is C3 rank 23, not a single tau-Z2 walk table.',
            'source_lines':'Knowledge object lines 104, 198, 263, 294'
        },
        'seed_summary':summarize_scheme(seed_scheme),
        'one_step':one_step(seed_scheme,rng,allowed),
    }
    out['walk']=random_walks(seed_scheme,restarts=args.restarts,steps=args.steps,max_pairs=args.max_pairs,
                             rng_seed=args.seed+17,allowed_classes=allowed,mode_name='clean_tau_'+('_'.join(sorted(allowed)).replace('-','')))
    path=OUT/'tau_orbit_walk_summary.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'seed':out['seed_summary'],'one_step':out['one_step'],'walk':out['walk'],'saved':str(path)},indent=2)[:20000])
    print('SAVED',path)

if __name__=='__main__':
    main()
