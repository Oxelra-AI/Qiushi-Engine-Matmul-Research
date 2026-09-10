#!/usr/bin/env python3
"""Export all conditional re-pivoted rank-2 lift-obstruction cuts.

This is a compact reproducibility artifact for analysis.  It imports the
canonical generator/evaluator in conditional_repivot_cuts.py, which in
turn reads the two replay-certified pivot-17 transported cut binaries.
"""
from __future__ import annotations
import json, sys, time, hashlib
from pathlib import Path

ROOT=Path('research/research_record')
SCRIPTS=ROOT/'workspace/scripts'
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))
from conditional_repivot_cuts import load_all_cuts, build_conditional_cut_masks  # type: ignore

OUT=ROOT/'workspace/data/quotient_lift/conditional_cuts/conditional_rank2_cut_masks_from_two_orbits.json'


def sha_text(s:str)->str:
    return hashlib.sha256(s.encode()).hexdigest()


def main():
    t0=time.time()
    cuts,manifests=load_all_cuts()
    cond,stats=build_conditional_cut_masks(cuts)
    compact=[]
    for cc in cond:
        compact.append({
            'pivot_a':cc['pivot_a'],
            'B_mask_hex':cc['B_mask_hex'],
            'source_file':cc['source_file'],
            'source_index':cc['source_index'],
            'cut_index':cc['cut_index'],
            'normalizer':cc['normalizer'],
        })
    # deterministic order
    compact.sort(key=lambda r:(r['pivot_a'], int(r['B_mask_hex'],16), r['source_file'], r['source_index']))
    payload={'schema':'s0908_conditional_rank2_cut_masks_v1',
             'meaning':'For n=20 full A-side supports: for every rank-2 full direction a, if z_a=1 then at most 11 selected full directions may lie in B(a,C), where C is one of the two certified pivot-17 obstruction cut orbits. Encoded linearly as sum_{b in B} z_b + 9 z_a <= 20 with Boolean full-direction variables.',
             'cut_inputs':manifests,
             'unique_quotient_cuts':len(cuts),
             'generation_stats':stats,
             'conditional_cuts':compact,
             'elapsed_sec':time.time()-t0}
    txt=json.dumps(payload,indent=2,sort_keys=True)+'\n'
    payload['self_sha256_if_written_without_this_field']=sha_text(txt)
    txt=json.dumps(payload,indent=2,sort_keys=True)+'\n'
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(txt)
    print(json.dumps({'out':str(OUT),'conditional_cut_count':len(compact),'unique_quotient_cuts':len(cuts),'sha256':hashlib.sha256(OUT.read_bytes()).hexdigest(),'elapsed_sec':payload['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__': main()
