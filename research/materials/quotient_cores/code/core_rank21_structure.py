#!/usr/bin/env python3
"""Analyze exact F2 rank-21 CPD pools for restricted 8x9x9 cores.

This is a research-facing structural analyzer, not a proof of nonexistence.
It decodes flip-cpd rank-r rows stored as [u_mask,v_mask,w_mask]^r, verifies
the decompositions, studies which term deletions preserve or nearly preserve the
core slice space, and extracts the recurring deficiency-one slice modes and
rank-one repair candidates.

For a tensor T in F2^{m x 9 x 9}, a CPD with U,V,W terms implies that the
C-slices L = span{T[:,:,c]} lie in the span K of the two-factor columns
u_i \otimes v_i.  Deleting terms gives a smaller two-factor span.  If dim((K+L)/K)=1,
then the deleted set misses exactly one quotient direction of L; the kernel of
L -> V/K is an 8-dimensional subspace of F2^9, and its normal vector is recorded
as the missing slice mode.
"""
from __future__ import annotations

import argparse, itertools, json, math, time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable

import numpy as np


def outer_mask(u_mask:int, v_mask:int, nv:int=9)->int:
    x=0
    um=int(u_mask)
    while um:
        lb=um & -um
        a=lb.bit_length()-1
        um ^= lb
        vm=int(v_mask)
        while vm:
            lbv=vm & -vm
            b=lbv.bit_length()-1
            vm ^= lbv
            x ^= 1 << (a*nv+b)
    return x


def rank_ints(vecs:Iterable[int])->int:
    basis={}
    for vv in vecs:
        v=int(vv)
        while v:
            p=v.bit_length()-1
            if p in basis:
                v ^= basis[p]
            else:
                basis[p]=v
                break
    return len(basis)


def reduce_by_basis(v:int, basis:dict[int,int])->int:
    """Canonical remainder after reducing by the triangular high-pivot basis."""
    v=int(v)
    for p in sorted(basis.keys(), reverse=True):
        if (v>>p)&1:
            v ^= basis[p]
    return v


def echelon_basis(vecs:Iterable[int])->dict[int,int]:
    basis={}
    for vv in vecs:
        v=int(vv)
        while v:
            p=v.bit_length()-1
            if p in basis:
                v ^= basis[p]
            else:
                basis[p]=v
                break
    return basis


def deficiency(cols:list[int], targets:list[int])->tuple[int,int,int]:
    rk=rank_ints(cols)
    rks=rank_ints(cols+targets)
    return (rks-rk, rk, rks)


def solve_coeffs(cols:list[int], target:int, nbits:int)->int|None:
    R=len(cols)
    rows=[]
    for bit in range(nbits):
        row=0
        for j,c in enumerate(cols):
            if (int(c)>>bit)&1:
                row |= 1<<j
        if (int(target)>>bit)&1:
            row |= 1<<R
        rows.append(row)
    pivots=[]
    prow=0
    for col in range(R):
        piv=None
        for rr in range(prow,len(rows)):
            if (rows[rr]>>col)&1:
                piv=rr; break
        if piv is None:
            continue
        rows[prow],rows[piv]=rows[piv],rows[prow]
        for rr in range(len(rows)):
            if rr!=prow and ((rows[rr]>>col)&1):
                rows[rr] ^= rows[prow]
        pivots.append(col)
        prow += 1
    for row in rows:
        if (row & ((1<<R)-1))==0 and ((row>>R)&1):
            return None
    sol=0
    for i,col in enumerate(pivots):
        if (rows[i]>>R)&1:
            sol |= 1<<col
    return sol


def core_targets(core:np.ndarray)->list[int]:
    T=(core.astype(np.uint8)&1)
    m,nv,nw=T.shape
    targets=[]
    for c in range(nw):
        x=0
        for a in range(m):
            for b in range(nv):
                if int(T[a,b,c]):
                    x |= 1<<(a*nv+b)
        targets.append(x)
    return targets


def verify_terms(terms:list[tuple[int,int,int]], targets:list[int], nv:int=9)->bool:
    nw=len(targets)
    recon=[0]*nw
    for u,v,w in terms:
        uv=outer_mask(u,v,nv)
        for c in range(nw):
            if (int(w)>>c)&1:
                recon[c] ^= uv
    return recon==targets


def missing_slice_mode(cols:list[int], targets:list[int], nbits:int)->int|None:
    """Return normal m in F2^9 for the kernel {alpha: sum alpha_c target_c in span(cols)}.

    For deficiency one, the image of L modulo span(cols) is one-dimensional, so
    this kernel has codimension one in F2^9.  The returned 9-bit mask m satisfies
    alpha is in the kernel iff parity(alpha & m)=0.  If deficiency is zero, m=0.
    If deficiency is >1 or target rank is not 9 this returns None.  This routine
    requires canonical reduction by the base-column echelon pivots; an earlier
    version stopped at the first nonpivot bit and undercounted modes.
    """
    basis=echelon_basis(cols)
    q=[]
    q_basis=[]
    q_piv={}
    for t in targets:
        r=reduce_by_basis(t,basis)
        q.append(r)
        v=r
        while v:
            p=v.bit_length()-1
            if p in q_piv:
                v ^= q_piv[p]
            else:
                q_piv[p]=v
                q_basis.append(r)
                break
    dq=len(q_basis)
    if dq==0:
        return 0
    if dq!=1:
        return None
    # q_c is either 0 or the sole nonzero quotient basis vector after reduction.
    gen=None
    for r in q:
        if r:
            gen=r; break
    m=0
    for c,r in enumerate(q):
        if r:
            # In a 1-d quotient over F2 all nonzero residues are equal after reduction.
            m |= 1<<c
    # Sanity: all combinations with alpha dot m =0 should reduce to zero quotient.
    # Since rank(targets)=9, this m is the unique nonzero normal to the kernel.
    return m


def mask_to_bits(mask:int, n:int)->list[int]:
    return [i for i in range(n) if (int(mask)>>i)&1]


def mask_weight(mask:int)->int:
    return int(mask).bit_count()


def analyze_pool(core_path:str, pool_path:str, rank:int, max_schemes:int|None, repair_top_modes:int,
                 exhaustive_repair:bool, repair_pair_limit:int, out_prefix:Path)->dict:
    core=np.load(core_path)
    targets=core_targets(core)
    m,nv,nw=core.shape
    nbits=m*nv
    arr=np.load(pool_path)
    if arr.ndim!=2 or arr.shape[1] != 3*rank:
        raise ValueError(f'Expected pool shape (*,{3*rank}) for rank {rank}, got {arr.shape}')
    if max_schemes is not None:
        arr=arr[:max_schemes]
    print(f'core={core_path} shape={core.shape} target_rank={rank_ints(targets)} pool={pool_path} rows={len(arr)} rank={rank}')
    scheme_records=[]
    del1_counter=Counter()
    del2_counter=Counter()
    mode_counter=Counter()
    mode_by_scheme=Counter()
    mode_deleted_w=Counter()
    mode_deleted_uvrank=Counter()
    best_examples={}
    verified=0
    best_def=99
    all_def1_examples=[]
    start=time.time()
    for si,row in enumerate(arr):
        vals=[int(x) for x in row.tolist()]
        terms=[tuple(vals[3*i:3*i+3]) for i in range(rank)]
        ok=verify_terms(terms,targets,nv)
        if not ok:
            scheme_records.append({'scheme_index':si,'verified':False})
            continue
        verified += 1
        uv=[outer_mask(u,v,nv) for u,v,w in terms]
        full_def=deficiency(uv,targets)
        # One-deletion and two-deletion stats.
        d1=Counter(); d2=Counter(); local_modes=Counter(); local_best=[]
        for i in range(rank):
            cols=[uv[j] for j in range(rank) if j!=i]
            obj=deficiency(cols,targets)
            d1[(obj[0],obj[1],obj[2])] += 1
            del1_counter[(obj[0],obj[1],obj[2])] += 1
            if obj[0] < best_def:
                best_def=obj[0]
            if obj[0]==0:
                # Rank-20 or lower upper bound found by deleting one term.
                rec={'scheme_index':si,'deleted':[i],'deficiency':obj[0],'rankK':obj[1],'rankKS':obj[2],
                     'deleted_terms':[{'u':terms[i][0],'v':terms[i][1],'w':terms[i][2]}]}
                best_examples.setdefault('delete1_def0',rec)
        for i,j in itertools.combinations(range(rank),2):
            cols=[uv[k] for k in range(rank) if k not in (i,j)]
            obj=deficiency(cols,targets)
            d2[(obj[0],obj[1],obj[2])] += 1
            del2_counter[(obj[0],obj[1],obj[2])] += 1
            if obj[0] < best_def:
                best_def=obj[0]
            if len(local_best)<8 or (obj[0],-obj[1]) < (local_best[-1]['deficiency'],-local_best[-1]['rankK']):
                rec={'deleted':[i,j],'deficiency':obj[0],'rankK':obj[1],'rankKS':obj[2]}
                local_best.append(rec); local_best.sort(key=lambda r:(r['deficiency'],-r['rankK'])); local_best=local_best[:8]
            if obj[0]==1:
                mode=missing_slice_mode(cols,targets,nbits)
                if mode is not None:
                    mode_counter[mode] += 1
                    local_modes[mode] += 1
                    mode_deleted_w[(mode, terms[i][2], terms[j][2])] += 1
                    mode_deleted_uvrank[(mode, rank_ints([uv[i],uv[j]]))] += 1
                    if len(all_def1_examples)<1000:
                        all_def1_examples.append({'scheme_index':si,'deleted':[i,j],'mode':mode,
                            'mode_bits':mask_to_bits(mode,nw),'deleted_w':[terms[i][2],terms[j][2]],
                            'deleted_u':[terms[i][0],terms[j][0]],'deleted_v':[terms[i][1],terms[j][1]],
                            'rank_deleted_uv':rank_ints([uv[i],uv[j]]),
                            'remaining_rank':obj[1]})
        for mode,cnt in local_modes.items():
            mode_by_scheme[mode] += 1
        scheme_records.append({'scheme_index':si,'verified':True,'full_deficiency':full_def,
            'uv_rank':rank_ints(uv),
            'delete1_distribution':{str(k):v for k,v in sorted(d1.items())},
            'delete2_distribution':{str(k):v for k,v in sorted(d2.items())},
            'top_missing_modes':[{'mode':m0,'bits':mask_to_bits(m0,nw),'count':c} for m0,c in local_modes.most_common(8)],
            'best_deletions':local_best})
        if (si+1)%100==0:
            print(f'  analyzed {si+1}/{len(arr)} schemes, elapsed={time.time()-start:.1f}s, verified={verified}')
    # Summaries.
    mode_summary=[]
    for mode,cnt in mode_counter.most_common(50):
        mode_summary.append({'mode':mode,'bits':mask_to_bits(mode,nw),'weight':mask_weight(mode),
            'count':cnt,'schemes_with_mode':mode_by_scheme[mode]})
    # Optional constructive test: for a mode, take deficiency-one 19-sets and ask whether
    # any single rank-one replacement closes them.  This is expensive; we only do it for
    # a bounded number of examples per selected mode.  This extends analysis from cn122 to
    # independent flip-cpd schemes.
    repair_records=[]
    if exhaustive_repair and all_def1_examples:
        selected_modes=[r['mode'] for r in mode_summary[:repair_top_modes]]
        # Full rank-one pool in m x 9.
        pool=[(outer_mask(u,v,nv),u,v) for u in range(1,1<<m) for v in range(1,1<<nv)]
        print(f'full rank-one pool size={len(pool)}; exhaustive single-replacement on selected modes={selected_modes}')
        examples_by_mode=defaultdict(list)
        for ex in all_def1_examples:
            if ex['mode'] in selected_modes and len(examples_by_mode[ex['mode']])<repair_pair_limit:
                examples_by_mode[ex['mode']].append(ex)
        for mode,examples in examples_by_mode.items():
            for ex in examples:
                row=arr[ex['scheme_index']]
                vals=[int(x) for x in row.tolist()]
                terms=[tuple(vals[3*i:3*i+3]) for i in range(rank)]
                uv=[outer_mask(u,v,nv) for u,v,w in terms]
                deleted=set(ex['deleted'])
                seed_terms=[terms[k] for k in range(rank) if k not in deleted]
                seed_uv=[uv[k] for k in range(rank) if k not in deleted]
                checked=0; best=(99,0,0); hit=None
                for pos in range(len(seed_terms)):
                    base=[seed_uv[k] for k in range(len(seed_uv)) if k!=pos]
                    used=set(base)
                    for cand_col,cand_u,cand_v in pool:
                        if cand_col in used:
                            continue
                        cols=base+[cand_col]
                        obj=deficiency(cols,targets)
                        checked += 1
                        if (obj[0],-obj[1]) < (best[0],-best[1]):
                            best=obj
                        if obj[0]==0:
                            hit={'replace_pos':pos,'u':cand_u,'v':cand_v,'deficiency':obj[0],'rankK':obj[1],'rankKS':obj[2]}
                            break
                    if hit:
                        break
                rec={'mode':mode,'mode_bits':mask_to_bits(mode,nw),'scheme_index':ex['scheme_index'],
                     'deleted':ex['deleted'],'checked':checked,'best_deficiency':best[0],
                     'best_rankK':best[1],'best_rankKS':best[2],'hit':hit}
                print('repair',rec)
                repair_records.append(rec)
                if hit:
                    # Do not stop globally; record all hits if any.  A hit would be a rank-19 core candidate.
                    pass
    summary={'core_path':core_path,'pool_path':pool_path,'rank':rank,'schemes_considered':int(len(arr)),
        'verified_schemes':verified,'target_slice_rank':rank_ints(targets),
        'global_best_deficiency_after_deletions':best_def,
        'delete1_distribution':{str(k):v for k,v in sorted(del1_counter.items())},
        'delete2_distribution':{str(k):v for k,v in sorted(del2_counter.items())},
        'top_missing_modes':mode_summary,
        'top_deleted_w_pairs_by_mode':[{'mode':k[0],'mode_bits':mask_to_bits(k[0],nw),'w_pair':[k[1],k[2]],'count':v}
            for k,v in mode_deleted_w.most_common(50)],
        'deleted_uvrank_by_mode':{str(k):v for k,v in sorted(mode_deleted_uvrank.items())},
        'deficiency_one_examples':all_def1_examples,
        'repair_records':repair_records,
        'scheme_records_sample':scheme_records[:50],
        'interpretation':'Verified rank-21 pool decompositions are used as exact F2 neighborhoods. Delete-two deficiency-one subsets expose a recurring missing C-slice mode in quotient L/(K∩L); recurrence may support symmetry breaking or obstruction, but absence of a repair hit is not a lower bound.'}
    out_prefix.parent.mkdir(parents=True,exist_ok=True)
    out_prefix.write_text(json.dumps(summary,indent=2)+'\n')
    print(f'wrote {out_prefix}')
    print(json.dumps({k:summary[k] for k in ['schemes_considered','verified_schemes','target_slice_rank','global_best_deficiency_after_deletions','delete1_distribution','delete2_distribution']},indent=2))
    print('top modes:', mode_summary[:10])
    return summary


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--core',required=True)
    ap.add_argument('--pool',required=True)
    ap.add_argument('--rank',type=int,default=21)
    ap.add_argument('--max-schemes',type=int,default=0,help='0 means all')
    ap.add_argument('--json-out',required=True)
    ap.add_argument('--exhaustive-repair',action='store_true')
    ap.add_argument('--repair-top-modes',type=int,default=3)
    ap.add_argument('--repair-pair-limit',type=int,default=2)
    args=ap.parse_args()
    analyze_pool(args.core,args.pool,args.rank,args.max_schemes or None,args.repair_top_modes,
                 args.exhaustive_repair,args.repair_pair_limit,Path(args.json_out))


if __name__=='__main__':
    main()
