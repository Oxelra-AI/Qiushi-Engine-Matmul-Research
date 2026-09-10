#!/usr/bin/env python3
"""Validate analysis conditional re-pivoted cut export."""
from __future__ import annotations
import json, sys, time, hashlib
from collections import Counter
from pathlib import Path
ROOT=Path('research/research_record')
SCRIPTS=ROOT/'workspace/scripts'
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))
import conditional_repivot_cuts as gen  # type: ignore

COND=ROOT/'workspace/data/quotient_lift/conditional_cuts/conditional_rank2_cut_masks_from_two_orbits.json'
OUT=ROOT/'workspace/data/quotient_lift/conditional_cuts/conditional_rank2_cut_masks_validation.json'

def sha(path:Path):
    h=hashlib.sha256();
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()

def points_from_mask(mask:int, maxbit:int=512):
    return [i for i in range(1,maxbit) if (mask>>i)&1]

def main():
    t0=time.time(); data=json.loads(COND.read_text())
    errors=[]; B_hist=Counter(); pivot_seen=Counter(); checked=0
    for i,r in enumerate(data['conditional_cuts']):
        a=int(r['pivot_a']); Bmask=int(r['B_mask_hex'],16); B=set(points_from_mask(Bmask,512))
        norm=r['normalizer']; P=gen.bits_to_mat(int(norm['Pmask'])); QinvT=gen.bits_to_mat(int(norm['QinvTmask']))
        if gen.rank_of_mask(a)!=2: errors.append({'i':i,'error':'pivot_not_rank2','a':a})
        if gen.full_action(P,QinvT,a)!=17: errors.append({'i':i,'error':'normalizer_does_not_send_a_to_17','a':a})
        cut_pts=None
        # recover quotient cut points from source file/index
        source=Path(r['source_file']); cuts=gen.parse_cut_binary(source); cut_pts=set(cuts[int(r['source_index'])]['points'])
        recomputed=set()
        bad=[]
        for b in range(1,512):
            if b==a: continue
            gb=gen.full_action(P,QinvT,b)
            qp=gen.quotient_point_from_full(gb,17)
            if qp is None:
                bad.append({'b':b,'gb':gb,'kind':'maps_to_pivot_or_zero'}); continue
            if qp[0] in cut_pts: recomputed.add(b)
        if recomputed!=B:
            errors.append({'i':i,'error':'B_mismatch','a':a,'missing':sorted(recomputed-B)[:20],'extra':sorted(B-recomputed)[:20],'missing_count':len(recomputed-B),'extra_count':len(B-recomputed)})
        B_hist[len(B)]+=1; pivot_seen[a]+=1; checked+=1
    # Known obstruction supports, lifted with section eps=0 plus pivot, should violate at pivot 17.
    cuts,_=gen.load_all_cuts(); cond,_=gen.build_conditional_cut_masks(cuts)
    known=[]
    for name,supp in [('support1',[1,3,9,33,99,128,132,144,148,160,184,189,192,198,209,215,224,249,254]),('support2',[1,3,9,128,132,144,148,160,165,184,189,192,198,209,215,224,231,249,254])]:
        fullA=[17]+[gen.section_lift(p,17) for p in supp]
        ev=gen.eval_candidate(fullA,cond)
        known.append({'name':name,'violations':ev['violations'],'violating_pivot_count':ev['violating_pivot_count'],'max_lhs':ev['max_lhs'],'max_occ_B_when_active':ev['max_occ_B_when_active']})
    out={'schema':'s0908_validate_conditional_cuts_v1','conditional_file':str(COND),'conditional_file_sha256':sha(COND),'checked':checked,'errors':errors[:50],'error_count':len(errors),'B_size_hist':dict(sorted(B_hist.items())),'pivot_count':len(pivot_seen),'per_pivot_cut_count_hist':dict(sorted(Counter(pivot_seen.values()).items())),'known_obstruction_lift_tests':known,'elapsed_sec':time.time()-t0}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
