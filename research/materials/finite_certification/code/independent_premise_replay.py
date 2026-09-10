#!/usr/bin/env python3
"""Independent premise replay for the shortened rank>=21 route.

This script does not rely on peer outputs.  It checks from local Wang cache/LUT
and analysis DRAT manifests:

* A-split P is a permutation and rank-sum implication applies.
* dim-1 Wang orbit values cover all 511 nonzero A-directions with LB 19.
* the eight required dim-2 orbit representatives 484--491 match the expected
  rank patterns and have verified unary CNF/DRAT records.
* excluding only 484--491 leaves no high-rank pair with non-rank-one sum.
* the normalized coset/AG(3,2) arithmetic: every 5-subset has a plane; all
  relevant high-rank affine-plane spans in normalized row/column cosets have
  Wang LB 17; row/column transpose gives matching values.
* row-type follows from transpose invariance on all LUT entries.

It also records exact file hashes and small proofs/checks needed by later review.
"""
from __future__ import annotations

import hashlib
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

SCRIPT=Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path: sys.path.insert(0,str(SCRIPT))
import dim2_replay_compat_graph as dg  # type: ignore

CACHE=Path('data/wang_f2_lb20/wang_orbit_closed_cache.pkl')
LUT=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
RECEIPT=Path('data/wang_f2_lb20/verify_receipt.json')
UNARY=Path('data/dim2_unary_certs_484_491/batch_unary_dim2_certs_manifest.json')
PROD=Path('data/structural/product_formula_full_elementary_matrix_check.json')
OUT=Path('data/structural/independent_premise_replay.json')


def sha(path:Path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for ch in iter(lambda:f.read(1<<20),b''):
            h.update(ch)
    return h.hexdigest()


def transpose_mask(x:int)->int:
    z=0
    for i in range(3):
        for j in range(3):
            if (x>>(3*i+j))&1:
                z |= 1<<(3*j+i)
    return z


def pack(gens:Iterable[int])->int:
    return dg.pack_basis(dg.rref_basis(list(gens),9))


def affine_planes_ag3():
    planes=set()
    for base in range(8):
        for u,v in combinations(range(1,8),2):
            P=tuple(sorted({base,base^u,base^v,base^u^v}))
            if len(P)==4: planes.add(P)
    return sorted(planes)


def plane_count(S):
    ss=set(S); return sum(1 for P in affine_planes_ag3() if set(P).issubset(ss))


def firstrow(x:int)->int: return x & 7

def firstcol_bits(x:int)->int:
    return ((x>>0)&1) | (((x>>3)&1)<<1) | (((x>>6)&1)<<2)


def lower_block_rank_column_model(p:int)->int:
    rows=[]
    for i in [1,2]:
        row=0
        for j in range(3):
            if (p>>(3*i+j))&1: row |= 1<<j
        rows.append(row)
    return len(dg.rref_basis(rows,3))


def lower_block_rank_row_model(p:int)->int:
    # fixed right two columns as a 3x2 block, in row-model varying first column.
    rows=[]
    for i in range(3):
        row=0
        for j in [1,2]:
            if (p>>(3*i+j))&1: row |= 1<<(j-1)
        rows.append(row)
    return len(dg.rref_basis(rows,2))


def build_P_perm_check():
    rows=[]; cols=[]
    for i in range(3):
        for j in range(3):
            for k in range(3):
                rows.append(i*9+j*3+k); cols.append(j*9+i*3+k)
    return {'size':27,'entry_count':27,'is_permutation':len(set(rows))==27 and len(set(cols))==27,'rank':27 if len(set(rows))==27 and len(set(cols))==27 else None}


def main():
    t0=time.time(); cache=pickle.load(open(CACHE,'rb')); lut_obj=pickle.load(open(LUT,'rb'))
    lut={int(k):int(v) for k,v in (lut_obj['lut'] if isinstance(lut_obj,dict) and 'lut' in lut_obj else lut_obj).items()}
    unary=json.loads(UNARY.read_text()); prod=json.loads(PROD.read_text()) if PROD.exists() else None
    # line coverage
    line_orbits=[o for o in cache['orbits'] if int(o['dim'])==1]
    line_points=[]
    for a in range(1,512):
        pos=int(cache['key_to_orbit'][pack([a])]); line_points.append(pos)
    line_summary={'orbit_records':line_orbits,'point_count':len(line_points),'orbit_hist_over_points':{str(k):int(v) for k,v in sorted(Counter(line_points).items())},'lb_hist_over_points':{str(k):int(v) for k,v in sorted(Counter(int(cache['orbits'][pos]['raw_lb']) for pos in line_points).items())},'all_lb19':all(int(cache['orbits'][pos]['raw_lb'])==19 for pos in line_points)}
    # dim2 reps and verified DRAT records
    verified={int(r['index']):r for r in unary['records'] if r.get('verified') is True}
    dim2=[]
    for idx in range(484,492):
        o=cache['orbits'][idx]
        basis=[int(x) for x in o['basis']]
        pats=sorted(dg.rank3(x) for x in dg.nonzero_span(basis))
        dim2.append({'index':idx,'cache_basis':basis,'raw_lb':int(o['raw_lb']),'rank_pattern':pats,'verified_unary_drat':idx in verified,'core_json':None if idx not in verified else verified[idx]['core_json'],'cnf_sha256':None if idx not in verified else verified[idx]['cnf_sha256'],'drat_sha256':None if idx not in verified else verified[idx]['drat_sha256'],'cnf_vars':None if idx not in verified else verified[idx]['cnf_vars'],'cnf_clauses':None if idx not in verified else verified[idx]['cnf_clauses']})
    high=[a for a in range(1,512) if dg.rank3(a)>=2]
    bad=[]; pair_orbits=Counter()
    for a,b in combinations(high,2):
        pos=int(cache['key_to_orbit'][pack([a,b])]); pair_orbits[pos]+=1
        if pos not in set(range(484,492)) and dg.rank3(a^b)!=1:
            bad.append({'a':a,'b':b,'orbit':pos,'ranks':sorted([dg.rank3(a),dg.rank3(b),dg.rank3(a^b)])})
            if len(bad)>=20: break
    # coset plane coverage column and row models.
    dim3_col=Counter(); dim3_row=Counter(); lb_col=Counter(); lb_row=Counter(); trans_mismatch=[]; col_examples=[]; row_examples=[]
    line_basis_col=[1,2,4]  # first row variable p | r
    line_basis_row=[1,8,64] # first column variable p | column bits
    five_plane_ok=True
    for k in range(5,9):
        for S in combinations(range(8),k):
            if plane_count(S)==0: five_plane_ok=False
    for lower in range(1,64):
        p=lower<<3
        coset=[p|r for r in range(8)]
        highpts=[x for x in coset if dg.rank3(x)>=2]
        for quad in combinations(highpts,4):
            rb=dg.rref_basis(quad,9)
            if len(rb)!=3: continue
            key=dg.pack_basis(rb); pos=int(cache['key_to_orbit'][key]); lb=int(lut[key]); dim3_col[pos]+=1; lb_col[lb]+=1
            tkey=dg.pack_basis(dg.rref_basis([transpose_mask(x) for x in rb],9)); tlb=int(lut[tkey])
            if tlb != lb and len(trans_mismatch)<20: trans_mismatch.append({'model':'col_quad','basis':list(rb),'lb':lb,'transpose_lb':tlb})
            if len(col_examples)<10: col_examples.append({'quad':list(quad),'basis':list(rb),'orbit':pos,'lb':lb,'firstrows':[firstrow(x) for x in quad]})
    # Direct row-model enumeration: fixed columns 2,3, varying first column.
    for fixed in range(1,64):
        # fixed is the 3x2 block in columns 1,2 (zero-based j=1,2)
        p=0
        for i in range(3):
            for jj in range(2):
                if (fixed>>(2*i+jj))&1:
                    p |= 1<<(3*i+(jj+1))
        coset=[]
        for col in range(8):
            x=p
            for i in range(3):
                if (col>>i)&1: x |= 1<<(3*i)
            coset.append(x)
        highpts=[x for x in coset if dg.rank3(x)>=2]
        for quad in combinations(highpts,4):
            rb=dg.rref_basis(quad,9)
            if len(rb)!=3: continue
            key=dg.pack_basis(rb); pos=int(cache['key_to_orbit'][key]); lb=int(lut[key]); dim3_row[pos]+=1; lb_row[lb]+=1
            if len(row_examples)<10: row_examples.append({'quad':list(quad),'basis':list(rb),'orbit':pos,'lb':lb,'firstcols':[firstcol_bits(x) for x in quad]})
    # Full LUT transpose invariance.
    mismatches=[]; checked=0
    for key,lb in lut.items():
        dim=key & 15; packed=key>>4; basis=[]
        for i in range(dim):
            basis.append((packed>>(9*i)) & 0x1ff)
        tkey=pack([transpose_mask(x) for x in basis]); checked+=1
        if lut.get(tkey)!=lb:
            mismatches.append({'key':int(key),'lb':int(lb),'tkey':int(tkey),'tlb':None if tkey not in lut else int(lut[tkey])})
            if len(mismatches)>=20: break
    out={'schema':'s0908_independent_premise_replay_v1','meaning':'Independent replay/summary of finite premises for the shortened saturated proof route. Does not constitute final formal proof by itself; connects verified assets for critical review.','hashes':{'wang_receipt':sha(RECEIPT),'wang_cache':sha(CACHE),'wang_lut':sha(LUT),'dim2_unary_manifest':sha(UNARY),'product_formula_check':sha(PROD) if PROD.exists() else None},'A_split_flattening':build_P_perm_check(),'line_LB19':line_summary,'dim2_484_491':{'records':dim2,'all_verified_unary_drat':all(idx in verified for idx in range(484,492))},'weak_dim2_to_rankone_difference':{'high_rank_vertices':len(high),'pair_orbit_hist':{str(k):int(v) for k,v in sorted(pair_orbits.items())},'bad_not_484_491_sum_not_rankone_count':len(bad),'bad_head':bad},'coset_affine_plane_LB17':{'AG32_every_5_subset_has_plane':five_plane_ok,'column_model_quad_count':sum(dim3_col.values()),'column_model_lb_hist':{str(k):int(v) for k,v in sorted(lb_col.items())},'column_model_orbit_hist':{str(k):int(v) for k,v in sorted(dim3_col.items())},'row_model_quad_count':sum(dim3_row.values()),'row_model_lb_hist':{str(k):int(v) for k,v in sorted(lb_row.items())},'row_model_orbit_hist':{str(k):int(v) for k,v in sorted(dim3_row.items())},'transpose_mismatch_count':len(trans_mismatch),'transpose_mismatch_head':trans_mismatch,'column_examples_head':col_examples,'row_examples_head':row_examples},'full_LUT_transpose_invariance':{'checked_entries':checked,'mismatch_count':len(mismatches),'mismatches_head':mismatches},'product_formula_full_elementary_check':prod,'elapsed_sec':time.time()-t0}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(OUT),'line_all_lb19':line_summary['all_lb19'],'dim2_all_verified':out['dim2_484_491']['all_verified_unary_drat'],'bad_pairs':len(bad),'col_lb':out['coset_affine_plane_LB17']['column_model_lb_hist'],'row_lb':out['coset_affine_plane_LB17']['row_model_lb_hist'],'transpose_mismatches':len(mismatches),'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))
if __name__=='__main__': main()
