#!/usr/bin/env python3
"""analysis: optimized free A/B residual search for k=3 retained neighborhoods.

For each verified rank-23 scheme, delete one term and choose three of the
remaining 22 slots as a repair block.  The other 19 old columns form L.  If
E=pi(col(D)) has dim d=3, completion is possible exactly when the image in E
of rank-one 9x9 matrices (a\otimes b) contains three independent tags.  This
script computes that image without enumerating B^3: for each A=a, reduce the
9 columns a\otimes e_beta modulo L+E; the kernel of the outside-rem map gives
all B whose a\otimes B lies in L+E, and the induced tag map gives attainable
E-directions.

If a rank-3 tag basis is found, the script solves for C and verifies all Brent
equations before saving the witness.
"""
from __future__ import annotations
import argparse, itertools, json, sys, time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
import residual_repair_geometry as rg  # type: ignore
from ab_residual_block_search import build_final_and_verify  # type: ignore

OUTDIR = Path('data/free_ab_k3')


def reduce_with_expr_basis(cols: Sequence[int]) -> List[int]:
    """Return a basis of dependencies among columns represented as 9-bit masks."""
    basis: Dict[int, Tuple[int, int]] = {}
    deps: List[int] = []
    for j, col in enumerate(cols):
        x = int(col); expr = 1 << j
        while x:
            p = x.bit_length() - 1
            if p not in basis:
                basis[p] = (x, expr)
                break
            bv, be = basis[p]
            x ^= bv; expr ^= be
        if x == 0:
            deps.append(expr)
    return deps


def tag_rank(tags: Sequence[int]) -> int:
    return rg.tags_rank(tags)


def add_tag_to_basis(tag_basis: List[Tuple[int, int, int]], tag: int, a: int, b: int, target_d: int) -> bool:
    old = tag_rank([t for t,_a,_b in tag_basis])
    new = tag_rank([t for t,_a,_b in tag_basis] + [tag])
    if new > old:
        tag_basis.append((int(tag), int(a), int(b)))
        return new >= target_d
    return False


def attainable_rankone_tag_basis(tagged_basis, d: int) -> Tuple[int, List[Tuple[int,int,int]], int]:
    """Return rank and representative (tag,A,B) basis for attainable tags."""
    tag_basis: List[Tuple[int,int,int]] = []
    a_examined = 0
    for a in range(1, 512):
        a_examined += 1
        rem_cols=[]; tag_cols=[]
        for beta in range(9):
            v = rg.vec_mask9_to_outer81(a, 1 << beta)
            rem, tag = rg.reduce_by_basis(tagged_basis, v)
            rem_cols.append(rem); tag_cols.append(tag)
        deps = reduce_with_expr_basis(rem_cols)  # B masks with outside remainder zero
        for bmask in deps:
            tag = 0
            for beta in range(9):
                if (bmask >> beta) & 1:
                    tag ^= tag_cols[beta]
            if tag != 0:
                if add_tag_to_basis(tag_basis, tag, a, bmask, d):
                    return d, tag_basis, a_examined
    return tag_rank([t for t,_a,_b in tag_basis]), tag_basis, a_examined


def scan_source(name: str, terms: Sequence[Tuple[int,int,int]], D_cols: Sequence[int], stop_on_witness: bool = True) -> dict:
    res={'source':name,'delete_records':[],'aggregate':Counter(),'witness_paths':[]}
    for del_idx in range(len(terms)):
        seed_terms=list(terms[:del_idx]+terms[del_idx+1:])
        rec={'delete_index':del_idx,'deleted_A':int(terms[del_idx][0]),'hist':Counter(),'examples':[],'blocks_tested':0}
        for block in itertools.combinations(range(22),3):
            retained_cols=[rg.vec_mask9_to_outer81(a,b) for i,(a,b,_c) in enumerate(seed_terms) if i not in block]
            tagged,E,rank_L,d=rg.build_quotient_basis(retained_cols,D_cols)
            rec['blocks_tested'] += 1
            if d > 3:
                rec['hist']['d_gt_3'] += 1; res['aggregate']['d_gt_3'] += 1
                continue
            tag_r, tag_basis, a_examined = attainable_rankone_tag_basis(tagged, d)
            if d == 3:
                if tag_r < 3:
                    key=f'd3_tagrank{tag_r}'
                    rec['hist'][key]+=1; res['aggregate'][key]+=1
                    if len(rec['examples']) < 12:
                        rec['examples'].append({'block':list(block),'d':d,'rank_L':rank_L,'tag_rank':tag_r,'tag_basis':tag_basis,'a_examined':a_examined})
                    continue
                # exact success: construct using the 3 basis vectors.
                A_choices=[a for _tag,a,b in tag_basis[:3]]
                B_choices=[b for _tag,a,b in tag_basis[:3]]
                vr=build_final_and_verify(seed_terms, block, A_choices, B_choices)
                detail={'block':list(block),'d':d,'rank_L':rank_L,'tag_rank':tag_r,'tag_basis':tag_basis[:3],'verify_status':vr['status'],'brent_diff':vr.get('brent_diff')}
                if vr['status']=='VERIFIED':
                    wp=OUTDIR/f'rank22_freeAB_{name}_del{del_idx}_block_{block[0]}_{block[1]}_{block[2]}.json'
                    wp.write_text(json.dumps({'source':name,'delete_index':del_idx,'block':list(block),**vr},indent=2,sort_keys=True)+'\n')
                    res['witness_paths'].append(str(wp))
                    rec['hist']['verified_witness']+=1; res['aggregate']['verified_witness']+=1
                    rec['examples'].append(detail)
                    if stop_on_witness:
                        res['delete_records'].append({**rec,'hist':dict(rec['hist'])})
                        return {**res,'aggregate':dict(res['aggregate'])}
                else:
                    # This should not happen if the theory and C solve agree; record loudly.
                    rec['hist']['tag_full_but_verify_failed']+=1; res['aggregate']['tag_full_but_verify_failed']+=1
                    rec['examples'].append(detail)
            elif d < 3:
                # Sufficient test: if tag_r reaches d, construct with d basis columns and fill rest with old block columns.
                if tag_r >= d:
                    A_choices=[]; B_choices=[]
                    for i in range(3):
                        if i < d:
                            _tag,a,b=tag_basis[i]; A_choices.append(a); B_choices.append(b)
                        else:
                            slot=block[i]; A_choices.append(seed_terms[slot][0]); B_choices.append(seed_terms[slot][1])
                    vr=build_final_and_verify(seed_terms, block, A_choices, B_choices)
                    detail={'block':list(block),'d':d,'rank_L':rank_L,'tag_rank':tag_r,'tag_basis':tag_basis[:d],'verify_status':vr['status'],'brent_diff':vr.get('brent_diff')}
                    if vr['status']=='VERIFIED':
                        wp=OUTDIR/f'rank22_freeAB_dlt_{name}_del{del_idx}_block_{block[0]}_{block[1]}_{block[2]}.json'
                        wp.write_text(json.dumps({'source':name,'delete_index':del_idx,'block':list(block),**vr},indent=2,sort_keys=True)+'\n')
                        res['witness_paths'].append(str(wp))
                        rec['hist']['dlt_verified_witness']+=1; res['aggregate']['dlt_verified_witness']+=1
                        rec['examples'].append(detail)
                        if stop_on_witness:
                            res['delete_records'].append({**rec,'hist':dict(rec['hist'])})
                            return {**res,'aggregate':dict(res['aggregate'])}
                    else:
                        rec['hist']['dlt_sufficient_failed']+=1; res['aggregate']['dlt_sufficient_failed']+=1
                        if len(rec['examples']) < 12: rec['examples'].append(detail)
                else:
                    key=f'd{d}_tagrank{tag_r}'
                    rec['hist'][key]+=1; res['aggregate'][key]+=1
        res['delete_records'].append({**rec,'hist':dict(rec['hist'])})
    res['aggregate']=dict(res['aggregate'])
    return res


def main():
    global OUTDIR
    ap=argparse.ArgumentParser()
    ap.add_argument('--sources', default='cn122_qmm')
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    ap.add_argument('--no-stop', action='store_true')
    args=ap.parse_args()
    OUTDIR=args.outdir
    OUTDIR.mkdir(parents=True,exist_ok=True)
    t0=time.time(); sources=rg.load_sources(); D_cols=rg.D_columns_as_ints()
    names=[x.strip() for x in args.sources.split(',') if x.strip()]
    out={'schema':'s0908_free_ab_k3_scan_v1','meaning':'Exact residual-space free A/B scan for three-slot retained-column neighborhoods; verified witnesses solve rank<=22, failures are local only.','results':{},'witness_paths':[]}
    for name in names:
        print(f'=== free A/B k=3 scan {name} ===', flush=True)
        rr=scan_source(name,sources[name],D_cols,stop_on_witness=not args.no_stop)
        out['results'][name]=rr; out['witness_paths'].extend(rr['witness_paths'])
        print(json.dumps({'source':name,'aggregate':rr['aggregate'],'witnesses':rr['witness_paths']},indent=2),flush=True)
        if out['witness_paths'] and not args.no_stop:
            break
    out['elapsed_sec']=time.time()-t0
    op=OUTDIR/'free_ab_k3_scan.json'
    op.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(op),'witness_paths':out['witness_paths'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__':
    main()
