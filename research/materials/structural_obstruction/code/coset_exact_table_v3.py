#!/usr/bin/env python3
"""Correct exact Wang tables for the coset-structure lower-bound route.

This supersedes the misleading dim4-closure language in coset_closure_v2.py.
It records exact LUT values and canonical orbit data without declaring closure
from possible numbers of points in a subspace.
"""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path
from itertools import combinations
from collections import Counter, defaultdict
SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from surviving_coset_ansatz import load_lut, rref_basis, pack_basis, span_elements, mat_rank, gf2_rank_rows, affine_planes_in_ag3, affine_plane_count  # type: ignore

PROFILE=Path('data/wang_f2_lb20/cert_profile.json')
RAISE900=Path('data/wang_analysis/node_local/dim2_raise_original_900s.json')


def wang_lb(lut, gens):
    rb=rref_basis(gens); key=pack_basis(rb)
    return int(lut[key]), rb, key

def lower_block_rank(lb:int)->int:
    # lower two rows of p_base = lb << 3.
    row1=lb & 7
    row2=(lb>>3)&7
    return gf2_rank_rows([row1,row2],3)

def load_raise_status():
    if not RAISE900.exists(): return {}
    d=json.load(open(RAISE900))
    out={}
    for r in d.get('results',[]):
        out[int(r['cert_index'])]={'status':r['solve'].get('status'),'feasible':r['solve'].get('feasible'),'support_size_tested':r.get('support_size_tested'),'basis':r.get('basis')}
    return out


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, default=Path('data/coset_analysis/coset_exact_table_v3.json'))
    args=ap.parse_args(); t0=time.time()
    lut=load_lut(Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    profile=json.load(open(PROFILE))
    raises=load_raise_status()
    dim2=[]
    for rec in profile['dimension_2_orbits']:
        basis=[int(x) for x in rec['constraint_values']]
        elts=span_elements(basis)
        ranks=[mat_rank(x) for x in elts]
        dim2.append({'index':int(rec['index']),'basis':basis,'basis_hex':[hex(x) for x in basis],'old_lb':int(rec['rank_lower_bound']),'proof_type':rec.get('proof_type'),'rank_pattern':ranks,'rank_hist':dict(Counter(ranks)),'nonzero_elements':elts,'raise900':raises.get(int(rec['index']))})

    cosets=[]
    dim3_occurrences=[]
    dim3_by_key={}
    for lb in range(1,64):
        p=lb<<3
        coset=[p|fr for fr in range(8)]
        ranks=[mat_rank(x) for x in coset]
        S_basis=[p,1,2,4]
        S_lb,S_rb,S_key=wang_lb(lut,S_basis)
        rec={'lower_block':lb,'p_base':p,'lower_block_rank':lower_block_rank(lb),'coset_points':coset,'rank_hist':dict(Counter(ranks)),'n_rank_ge2':sum(r>=2 for r in ranks),'S_rref':list(S_rb),'S_key':str(S_key),'S_lb':S_lb}
        cosets.append(rec)
        ge2=[x for x in coset if mat_rank(x)>=2]
        for quad in combinations(ge2,4):
            rb=rref_basis(quad)
            if len(rb)!=3: continue
            key=pack_basis(rb); lbv=int(lut[key]); elts=span_elements(rb); hist=dict(Counter(mat_rank(x) for x in elts))
            dim3_occurrences.append({'lower_block':lb,'quad':list(quad),'rref':list(rb),'key':str(key),'lb':lbv,'rank_hist':hist})
            if key not in dim3_by_key:
                dim3_by_key[key]={'rref':list(rb),'key':str(key),'lb':lbv,'rank_hist':hist,'occurrences':0}
            dim3_by_key[key]['occurrences']+=1

    plane_counts={}
    for k in range(9):
        c=Counter()
        for sub in combinations(range(8),k): c[affine_plane_count(sub)]+=1
        plane_counts[str(k)]={str(a):b for a,b in sorted(c.items())}

    summary={
        'schema':'coset_exact_table_v3',
        'meaning':'Exact LUT-value tables; no closure is inferred from possible point counts in S.',
        'dim2_orbits_from_cert_profile':dim2,
        'dim2_raise900_summary':{'raised_to_19_by_original_lut':[r['index'] for r in dim2 if r.get('raise900',{}).get('feasible') is False and r['old_lb']==18], 'feasible_at_18':[r['index'] for r in dim2 if r.get('raise900',{}).get('feasible') is True and r['old_lb']==18]},
        'coset_dim4_records':cosets,
        'coset_dim4_lb_hist':dict(Counter(c['S_lb'] for c in cosets)),
        'coset_dim4_by_lower_block_rank_and_lb':{str(k):v for k,v in Counter((c['lower_block_rank'],c['S_lb'],c['n_rank_ge2']) for c in cosets).items()},
        'dim3_occurrence_count':len(dim3_occurrences),
        'dim3_occurrence_lb_hist':dict(Counter(r['lb'] for r in dim3_occurrences)),
        'dim3_unique_count':len(dim3_by_key),
        'dim3_unique_lb_hist':dict(Counter(r['lb'] for r in dim3_by_key.values())),
        'dim3_unique_records':list(dim3_by_key.values()),
        'ag3_plane_count_by_subset_size':plane_counts,
        'elapsed_sec':time.time()-t0,
    }
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(args.out),'dim4_lb_hist':summary['coset_dim4_lb_hist'],'dim3_occurrences':len(dim3_occurrences),'dim3_occurrence_lb_hist':summary['dim3_occurrence_lb_hist'],'dim3_unique_count':len(dim3_by_key),'dim3_unique_lb_hist':summary['dim3_unique_lb_hist'],'raised_to_19':summary['dim2_raise900_summary']['raised_to_19_by_original_lut'],'feasible_at_18':summary['dim2_raise900_summary']['feasible_at_18'],'elapsed_sec':summary['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__': main()
