#!/usr/bin/env python3
"""Scan the tight-contraction row/column-space obstruction over S samples."""
from __future__ import annotations
import argparse, json, sys, time
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np

SCRIPTS=Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0,str(SCRIPTS))
import e11_s_coset_rank_sat as sc  # noqa: E402
import e11_s_tight_space_obstruction as tso  # noqa: E402


def matrix_mask_from_np(M):
    out=0
    for b in range(9):
        row=0
        for c in range(9):
            if int(M[b,c])&1: row |= 1<<c
        out |= row << (9*b)
    return out


def build_Rphi_masks(Rcoords):
    Rphi={}
    for phi in range(1,16):
        M=np.zeros((9,9),dtype=np.uint8)
        for k in range(4):
            if (phi>>k)&1: M ^= Rcoords[k]
        Rphi[phi]=matrix_mask_from_np(M)
    return Rphi


def mininfo_for_S(S, Rphi):
    out={}; m={}
    for phi in range(1,16):
        best, mins=tso.min_matrices(Rphi[phi], S)
        m[phi]=best
        b_union=set(); c_union=set(); pair_count=0
        # Union of column/row spaces over all minimum matrices.
        for mat in mins:
            rows=sc.rows_from_mask81(mat)
            cb=tso.row_basis_mask(tso.col_rows_from_rows(rows))
            rb=tso.row_basis_mask(rows)
            bs=tso.span_set(cb); cs=tso.span_set(rb)
            b_union |= bs; c_union |= cs
            pair_count += (len(bs)-1)*(len(cs)-1)
        out[phi]={'m':best,'min_count':len(mins),'b_union':b_union-{0},'c_union':c_union-{0},'pair_count_raw_sum':pair_count}
    return m,out


def cover_block_record(cover, m, mininfo):
    cov={phi:sum(1 for a in cover if ((phi&a).bit_count()&1)) for phi in range(1,16)}
    tight=[phi for phi in range(1,16) if cov[phi]==m[phi]]
    empty=[]
    tight_count_by_a=Counter()
    for ti,a in enumerate(cover):
        phis=[phi for phi in tight if (phi&a).bit_count()&1]
        for phi in phis: tight_count_by_a[a]+=1
        allowed_b=set(range(1,512)); allowed_c=set(range(1,512))
        for phi in phis:
            allowed_b &= mininfo[phi]['b_union']
            allowed_c &= mininfo[phi]['c_union']
        if (not allowed_b) or (not allowed_c):
            empty.append({'term':ti,'a':int(a),'tight_phis':phis,'allowed_b_count':len(allowed_b),'allowed_c_count':len(allowed_c)})
    return {'tight_phis':tight,'empty_terms':empty,'blocked':bool(empty),'tight_count_by_a':{str(k):int(v) for k,v in tight_count_by_a.items()}}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--prefix', required=True)
    ap.add_argument('--pool', type=Path, required=True)
    ap.add_argument('--rank-res', type=int, default=8)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--max-S', type=int, default=0)
    args=ap.parse_args(); t0=time.time()
    prefix=[int(x) for x in args.prefix.split(',') if x.strip()]
    pool=np.load(args.pool)
    basis_to_schemes=defaultdict(list)
    for i,scheme in enumerate(pool):
        basis_to_schemes[sc.scheme_s_basis(scheme)].append(i)
    S_list=sorted(basis_to_schemes)
    total_S=len(S_list)
    if args.max_S: S_list=S_list[:args.max_S]
    _,_,_,Rcoords=sc.quotient_base_residual(prefix)
    Rphi=build_Rphi_masks(Rcoords)
    cover_cache={}
    records=[]; status_counts=Counter(); blocked_cover_count_dist=Counter(); first_survivors=[]; first_blocked=[]
    for si,S in enumerate(S_list):
        m,mininfo=mininfo_for_S(S,Rphi)
        mt=tuple(m[p] for p in range(1,16))
        if mt not in cover_cache:
            cover_cache[mt]=sc.enumerate_covers(mt,args.rank_res)
        covers=cover_cache[mt]
        blocked=0; cover_recs=[]
        for ci,cov in enumerate(covers):
            br=cover_block_record(cov,m,mininfo)
            if br['blocked']:
                blocked+=1
                if len(first_blocked)<5:
                    first_blocked.append({'S_index':si,'S_hash':sc.basis_hash(S),'cover_index':ci,'cover':cov,**br})
            else:
                if len(first_survivors)<20:
                    first_survivors.append({'S_index':si,'S_hash':sc.basis_hash(S),'cover_index':ci,'cover':cov,**br})
            if ci<3 or not br['blocked']:
                cr=dict(br); cr['cover_index']=ci; cr['cover']=cov
                cover_recs.append(cr)
        if blocked==len(covers): status='ALL_COVERS_SPACE_BLOCKED'
        elif blocked==0: status='NO_COVER_SPACE_BLOCKED'
        else: status='SOME_COVERS_SURVIVE_SPACE'
        status_counts[status]+=1; blocked_cover_count_dist[blocked]+=1
        if si<20 or status!='ALL_COVERS_SPACE_BLOCKED':
            records.append({'S_index':si,'S_hash':sc.basis_hash(S),'scheme_indices':basis_to_schemes[S][:20],'m_by_phi':{str(k):int(v) for k,v in m.items()},'valid_cover_count':len(covers),'space_blocked_cover_count':blocked,'status':status,'cover_records_head':cover_recs})
        if si<5 or si%100==0 or status!='ALL_COVERS_SPACE_BLOCKED':
            print(f'S {si+1}/{len(S_list)} covers={len(covers)} blocked={blocked} status={status}', flush=True)
    result={'purpose':'tight row/column-space necessary obstruction over sampled S spaces','field':'F2','prefix':prefix,'pool':str(args.pool),'rank_res':args.rank_res,'distinct_S_total_in_pool':total_S,'distinct_S_scanned':len(S_list),'status_counts':dict(status_counts),'blocked_cover_count_distribution':{str(k):int(v) for k,v in sorted(blocked_cover_count_dist.items())},'m_profile_cache_count':len(cover_cache),'first_space_blocked_examples':first_blocked,'first_space_surviving_examples':first_survivors,'records':records,'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True,default=int)+'\n')
    print(json.dumps({k:result[k] for k in ['distinct_S_scanned','status_counts','blocked_cover_count_distribution','m_profile_cache_count','elapsed_sec']},indent=2,sort_keys=True))
    print('wrote',args.out)

if __name__=='__main__': main()
