#!/usr/bin/env python3
"""analysis: exact residual-space A/B block repair search near rank-23 schemes.

Given a verified rank-23 scheme, delete one term.  Retain 22-k old columns
k_t=a_t\otimes b_t and allow k chosen slots to replace BOTH A and B factors.
Let E be the image of col(D) modulo the retained-column span L.  If dim(E)=k,
then a successful local repair is exactly a choice of one vector from each
H_t(a)=pi(a\otimes F_2^9)\cap E whose k vectors form a basis of E.  We scan all
nonzero A choices for k=1 and k=2 minimal-defect blocks and solve C when the
criterion succeeds.

This is an exact local construction search, not a lower bound: failure applies
only to these retained-column neighborhoods of the chosen rank-23 seeds.
"""
from __future__ import annotations
import argparse, itertools, json, sys, time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
import residual_repair_geometry as rg  # type: ignore
from linear_completion import build_t333_f2, tensor_to_D, gf2_solve_multi, vec_to_mask, verify_decomposition_f2  # type: ignore

OUTDIR = Path('data/ab_repair')


def nonzero_tag_options_for_A(tagged_basis, a: int) -> Dict[int, int]:
    """Return tag->B representative for nonzero tags in H(a)=pi(a⊗F2^9)∩E."""
    tag_to_b: Dict[int, int] = {}
    for b in range(1, 512):
        v = rg.vec_mask9_to_outer81(a, b)
        rem, tag = rg.reduce_by_basis(tagged_basis, v)
        if rem == 0 and tag != 0 and tag not in tag_to_b:
            tag_to_b[int(tag)] = int(b)
    return tag_to_b


def build_final_and_verify(seed_terms, block: Sequence[int], A_choices: Sequence[int], B_choices: Sequence[int]) -> dict:
    A_new = [int(a) for a, _b, _c in seed_terms]
    B_new = [int(b) for _a, b, _c in seed_terms]
    for slot, a, b in zip(block, A_choices, B_choices):
        A_new[int(slot)] = int(a)
        B_new[int(slot)] = int(b)
    cols = [rg.vec_mask9_to_outer81(a, b) for a, b in zip(A_new, B_new)]
    K = rg.build_K_np_from_int_cols(cols)
    D_np = tensor_to_D(build_t333_f2())
    CT = gf2_solve_multi(K, D_np)
    if CT is None:
        return {'status': 'K_C_SOLVE_FAILED'}
    C_new = [vec_to_mask(CT[i]) for i in range(len(A_new))]
    diff = verify_decomposition_f2(A_new, B_new, C_new)
    return {'status': 'VERIFIED' if diff == 0 else 'BRENT_DIFF', 'brent_diff': int(diff), 'A': A_new, 'B': B_new, 'C': C_new}


def scan_source(source_name: str, terms: Sequence[Tuple[int,int,int]], D_cols: Sequence[int], max_witnesses: int = 1) -> dict:
    out = {
        'source': source_name,
        'delete_records': [],
        'aggregate': {},
        'witness_paths': [],
    }
    agg = defaultdict(Counter)
    source_witness_count = 0
    for del_idx in range(len(terms)):
        seed_terms = list(terms[:del_idx] + terms[del_idx+1:])
        del_rec = {'delete_index': del_idx, 'deleted_A': int(terms[del_idx][0]), 'k1': None, 'k2': None}
        # k=1 scan: exact if d=1.
        k1_hist = Counter(); k1_examples=[]
        for block in itertools.combinations(range(22), 1):
            retained_cols = [rg.vec_mask9_to_outer81(a,b) for i,(a,b,_c) in enumerate(seed_terms) if i not in block]
            tagged_basis, E_reps, rank_L, d = rg.build_quotient_basis(retained_cols, D_cols)
            if d != 1:
                k1_hist[f'd{d}'] += 1; agg['k1'][f'd{d}'] += 1
                continue
            found = False
            found_detail = None
            for a in range(1, 512):
                opts = nonzero_tag_options_for_A(tagged_basis, a)
                if opts:
                    tag, b = next(iter(opts.items()))
                    vr = build_final_and_verify(seed_terms, block, [a], [b])
                    found_detail = {'block': list(block), 'rank_L': rank_L, 'd': d, 'A_choice': a, 'B_choice': b, 'tag': tag, 'verify_status': vr['status'], 'brent_diff': vr.get('brent_diff')}
                    if vr['status'] == 'VERIFIED':
                        wp = OUTDIR / f'rank22_{source_name}_del{del_idx}_k1_slot{block[0]}_A{a}_B{b}.json'
                        wp.write_text(json.dumps({'source':source_name,'delete_index':del_idx,'block':list(block),**vr}, indent=2, sort_keys=True)+'\n')
                        out['witness_paths'].append(str(wp)); source_witness_count += 1
                    found = True
                    break
            key = 'found' if found else 'none'
            k1_hist[key] += 1; agg['k1'][key] += 1
            if found_detail and len(k1_examples) < 20:
                k1_examples.append(found_detail)
            if source_witness_count >= max_witnesses:
                break
        del_rec['k1'] = {'hist': dict(k1_hist), 'examples': k1_examples}
        if source_witness_count >= max_witnesses:
            out['delete_records'].append(del_rec); break

        # k=2 scan: exact if d=2. Precompute options per slot for each block.
        k2_hist = Counter(); k2_examples=[]; block_count=0
        for block in itertools.combinations(range(22), 2):
            retained_cols = [rg.vec_mask9_to_outer81(a,b) for i,(a,b,_c) in enumerate(seed_terms) if i not in block]
            tagged_basis, E_reps, rank_L, d = rg.build_quotient_basis(retained_cols, D_cols)
            block_count += 1
            if d != 2:
                k2_hist[f'd{d}'] += 1; agg['k2'][f'd{d}'] += 1
                continue
            # For each slot, classify all A choices by attainable nonzero tags.
            slot_opts: List[List[Tuple[int, Dict[int,int]]]] = []
            for _slot in block:
                opts_for_slot=[]
                for a in range(1,512):
                    mp = nonzero_tag_options_for_A(tagged_basis, a)
                    if mp:
                        opts_for_slot.append((a, mp))
                slot_opts.append(opts_for_slot)
            if not slot_opts[0] or not slot_opts[1]:
                k2_hist['d2_empty_H'] += 1; agg['k2']['d2_empty_H'] += 1
                if len(k2_examples) < 20:
                    k2_examples.append({'block':list(block),'rank_L':rank_L,'d':d,'counts':[len(x) for x in slot_opts],'status':'empty_H'})
                continue
            found=False; detail=None
            # E dimension 2: need tags with rank 2.
            for a1, mp1 in slot_opts[0]:
                for tag1,b1 in mp1.items():
                    for a2, mp2 in slot_opts[1]:
                        for tag2,b2 in mp2.items():
                            if rg.tags_rank([tag1,tag2]) == 2:
                                vr = build_final_and_verify(seed_terms, block, [a1,a2], [b1,b2])
                                detail={'block':list(block),'rank_L':rank_L,'d':d,'A_choices':[a1,a2],'B_choices':[b1,b2],'tags':[tag1,tag2],'verify_status':vr['status'],'brent_diff':vr.get('brent_diff'),'option_counts':[len(x) for x in slot_opts]}
                                if vr['status'] == 'VERIFIED':
                                    wp = OUTDIR / f'rank22_{source_name}_del{del_idx}_k2_slots{block[0]}_{block[1]}_A{a1}_{a2}_B{b1}_{b2}.json'
                                    wp.write_text(json.dumps({'source':source_name,'delete_index':del_idx,'block':list(block),**vr}, indent=2, sort_keys=True)+'\n')
                                    out['witness_paths'].append(str(wp)); source_witness_count += 1
                                found=True
                                break
                        if found: break
                    if found: break
                if found: break
            key='found_independent' if found else 'no_independent_tags'
            k2_hist[key]+=1; agg['k2'][key]+=1
            if len(k2_examples)<30 and (found or key!='d2_empty_H'):
                k2_examples.append(detail if detail else {'block':list(block),'rank_L':rank_L,'d':d,'status':key,'option_counts':[len(x) for x in slot_opts]})
            if source_witness_count >= max_witnesses:
                break
        del_rec['k2'] = {'hist': dict(k2_hist), 'block_count': block_count, 'examples': k2_examples}
        out['delete_records'].append(del_rec)
        if source_witness_count >= max_witnesses:
            break
    out['aggregate'] = {k:dict(v) for k,v in agg.items()}
    return out


def main():
    global OUTDIR
    ap=argparse.ArgumentParser()
    ap.add_argument('--sources', default='cn122_qmm,flip_rank23_text,pivot17_transformed_rank23')
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    ap.add_argument('--max-witnesses', type=int, default=1)
    args=ap.parse_args()
    OUTDIR = args.outdir
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0=time.time()
    sources=rg.load_sources()
    names=[x.strip() for x in args.sources.split(',') if x.strip()]
    D_cols=rg.D_columns_as_ints()
    out={'schema':'s0908_ab_residual_block_search_v1','meaning':'Exact local A/B repair scan near verified rank-23 decompositions. A verified witness is a full rank-22 decomposition; absence only excludes scanned one/two-slot retained neighborhoods.','sources':names,'results':{},'witness_paths':[]}
    for name in names:
        if name not in sources:
            print(f'missing source {name}', flush=True); continue
        print(f'=== scanning {name} ===', flush=True)
        res=scan_source(name, sources[name], D_cols, args.max_witnesses)
        out['results'][name]=res
        out['witness_paths'].extend(res['witness_paths'])
        print(json.dumps({'source':name,'aggregate':res['aggregate'],'witnesses':res['witness_paths']}, indent=2), flush=True)
        if out['witness_paths']:
            break
    out['elapsed_sec']=time.time()-t0
    op=OUTDIR/'ab_residual_block_search.json'
    op.write_text(json.dumps(out, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(op),'witness_paths':out['witness_paths'],'elapsed_sec':out['elapsed_sec']}, indent=2, sort_keys=True))

if __name__=='__main__':
    main()
