#!/usr/bin/env python3
"""analysis independent checks of the normalized coset/AG(3,2) arithmetic.

This does not prove the peer's whole coset structural theorem.  It verifies the
finite arithmetic facts currently being used in that route:

* in the normalized column coset p + e0⊗F2^3, with p having nonzero lower block,
  all 63 such cosets have at least four high-rank points;
* the span <p,e0⊗F2^3> is 4-dimensional and has Wang LUT lower bound 14;
* for lower-block rank two, the coset splits into four rank-2 and four rank-3
  points; selecting one rank-2 and three rank-3 gives 16 H-configurations, all
  affine-plane-free in AG(3,2);
* across all normalized cosets, all four-high-rank subsets whose linear span has
  dimension 3 give exactly 651 instances and every such dim-3 span has Wang LUT
  lower bound 17, matching the peer's corrected message.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

SCRIPT=Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0,str(SCRIPT))

import dim2_replay_compat_graph as dg  # type: ignore

LUT=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
OUT=Path('data/coset/coset_plane_verify.json')


def gf2_rank_rows(rows:Sequence[int])->int:
    return len(dg.rref_basis(rows,9))


def lower_block_rank(x:int)->int:
    # rows 1 and 2 as a 2x3 matrix
    rows=[]
    for i in [1,2]:
        row=0
        for j in range(3):
            if (x>>(3*i+j))&1:
                row |= 1<<j
        rows.append(row)
    return len(dg.rref_basis(rows,3))


def pack(gens:Iterable[int])->int:
    return dg.pack_basis(dg.rref_basis(list(gens),9))


def load_lut(path:Path):
    obj=pickle.load(open(path,'rb'))
    return {int(k):int(v) for k,v in (obj['lut'] if isinstance(obj,dict) and 'lut' in obj else obj).items()}


def wang_lb(lut, gens:Iterable[int])->int:
    k=pack(gens)
    if k not in lut:
        raise KeyError(k)
    return int(lut[k])


def affine_planes_ag3():
    planes=set()
    pts=range(8)
    for base in pts:
        for u,v in combinations([x for x in pts if x],2):
            P=tuple(sorted({base,base^u,base^v,base^u^v}))
            if len(P)==4:
                planes.add(P)
    return sorted(planes)


def plane_count(S:Sequence[int])->int:
    ss=set(S)
    return sum(1 for P in affine_planes_ag3() if set(P).issubset(ss))


def firstrow(x:int)->int:
    return x & 7


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--out',type=Path,default=OUT)
    args=ap.parse_args()
    t0=time.time(); lut=load_lut(LUT)
    plane_count_dist_by_size={}
    for k in range(9):
        c=Counter(plane_count(sub) for sub in combinations(range(8),k))
        plane_count_dist_by_size[str(k)]={str(a):int(b) for a,b in sorted(c.items())}
    coset_records=[]; dim3_records=[]
    dim4_lb_dist=Counter(); n_ge2_dist=Counter(); lower_rank_dist=Counter(); split_dist=Counter()
    # Normalize line L=e0⊗F2^3; lower block in bits 3..8.
    line_basis=[1,2,4]
    for lower_block in range(1,64):
        p=lower_block<<3
        coset=[p|r for r in range(8)]
        ranks=[dg.rank3(x) for x in coset]
        n_ge2=sum(1 for r in ranks if r>=2)
        n_ge3=sum(1 for r in ranks if r==3)
        n_ge2_dist[n_ge2]+=1; lower_rank_dist[lower_block_rank(p)]+=1
        split_dist[(ranks.count(1),ranks.count(2),ranks.count(3))]+=1
        S_basis=dg.rref_basis([p,*line_basis],9)
        S_dim=len(S_basis); S_lb=wang_lb(lut,S_basis)
        dim4_lb_dist[S_lb]+=1
        # all four-high-rank subsets with span dim 3
        high=[x for x in coset if dg.rank3(x)>=2]
        d3_this=0
        for quad in combinations(high,4):
            rb=dg.rref_basis(quad,9)
            if len(rb)!=3:
                continue
            lb=wang_lb(lut,rb)
            fr=[firstrow(x) for x in quad]
            dim3_records.append({'lower_block':lower_block,'p':p,'quad':list(quad),'firstrows':fr,'span_basis':list(rb),'lb':lb,'plane_count':plane_count(fr),'rank_hist':{str(k):int(v) for k,v in sorted(Counter(dg.rank3(x) for x in quad).items())}})
            d3_this+=1
        # surviving ansatz configurations for lower-rank=2: exactly one rank2 and three rank3
        H_count=0; H_plane_hist=Counter(); H_firstrow_examples=[]
        if lower_block_rank(p)==2:
            rank2=[x for x in coset if dg.rank3(x)==2]
            rank3=[x for x in coset if dg.rank3(x)==3]
            for H in (list(c2)+list(c3) for c2 in combinations(rank2,1) for c3 in combinations(rank3,3)):
                H_count+=1; fr=tuple(sorted(firstrow(x) for x in H)); H_plane_hist[plane_count(fr)]+=1
                if len(H_firstrow_examples)<4:
                    H_firstrow_examples.append(list(fr))
        coset_records.append({'lower_block':lower_block,'p':p,'lower_block_rank':lower_block_rank(p),'coset_ranks':ranks,'rank_hist':{str(k):int(v) for k,v in sorted(Counter(ranks).items())},'n_ge2':n_ge2,'n_rank3':n_ge3,'S_dim':S_dim,'S_lb':S_lb,'dim3_quad_count':d3_this,'H_one_r2_three_r3_count':H_count,'H_plane_count_hist':{str(k):int(v) for k,v in sorted(H_plane_hist.items())},'H_firstrow_examples':H_firstrow_examples})
    dim3_lb_dist=Counter(r['lb'] for r in dim3_records)
    dim3_plane_dist=Counter(r['plane_count'] for r in dim3_records)
    out={'schema':'s0908_coset_plane_verify_v1','meaning':'Independent finite checks of normalized coset and AG(3,2) arithmetic; this is not by itself a proof that every rank20 algorithm has this coset form.','ag3_plane_count_by_subset_size':plane_count_dist_by_size,'coset_count':len(coset_records),'lower_block_rank_dist':{str(k):int(v) for k,v in sorted(lower_rank_dist.items())},'coset_rank_split_dist':{str(k):int(v) for k,v in sorted(split_dist.items())},'n_ge2_dist':{str(k):int(v) for k,v in sorted(n_ge2_dist.items())},'dim4_span_lb_dist':{str(k):int(v) for k,v in sorted(dim4_lb_dist.items())},'dim3_quad_count':len(dim3_records),'dim3_quad_lb_dist':{str(k):int(v) for k,v in sorted(dim3_lb_dist.items())},'dim3_quad_plane_count_dist':{str(k):int(v) for k,v in sorted(dim3_plane_dist.items())},'lower_rank2_H_count_dist':{str(c['H_one_r2_three_r3_count']):sum(1 for r in coset_records if r['H_one_r2_three_r3_count']==c['H_one_r2_three_r3_count']) for c in coset_records},'rank2_lower_block_H_plane_hists':Counter(json.dumps(c['H_plane_count_hist'],sort_keys=True) for c in coset_records if c['lower_block_rank']==2),'coset_records_head':coset_records[:12],'dim3_records_head':dim3_records[:20],'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(args.out),'ag3_planes':len(affine_planes_ag3()),'cosets':len(coset_records),'dim4_lb_dist':out['dim4_span_lb_dist'],'dim3_quad_count':out['dim3_quad_count'],'dim3_lb_dist':out['dim3_quad_lb_dist'],'dim3_plane_dist':out['dim3_quad_plane_count_dist'],'split_dist':out['coset_rank_split_dist'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__':
    main()
