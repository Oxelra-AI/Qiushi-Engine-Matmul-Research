#!/usr/bin/env python3
"""Classify whether rank-3 tight sources add leakage contradictions on same-W survivors."""
from __future__ import annotations
import collections, json, sys
from pathlib import Path
SCRIPTS=Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0,str(SCRIPTS))
import contraction_weight_excess_search as s  # type: ignore

out_path=Path('data/contraction_weight_excess/samew_rank3_contribution.json')
stats=collections.Counter()
examples=[]
survivors=0
for idx, rec in enumerate(s.same_w_deletion_lists()):
    us=[int(u) for u in rec['u_masks']]
    if not (s.shadow_consistent(us) is True and s.coord_purity_pass(us) is True):
        continue
    survivors += 1
    r12=s.check_a_list(us, source_ranks=(1,2), target_ranks=(1,2), scalar_ranks=(1,2), head_limit=1000)
    allr=s.check_a_list(us, source_ranks=(1,2,3), target_ranks=(1,2), scalar_ranks=(1,2,3), head_limit=1000)
    full_scalar_clean = allr['scalar_violation_count']==0
    has_rank3_leak=False
    has_rank3_new_target=False
    r12_bad_lams={z['lambda'] for z in r12['leakage_violations_head']}
    rank3_leak_head=[]
    for lv in allr['leakage_violations_head']:
        rb=None if lv.get('srcB') is None else lv['srcB']['rank_lambda']
        rc=None if lv.get('srcC') is None else lv['srcC']['rank_lambda']
        if rb==3 or rc==3:
            has_rank3_leak=True
            if lv['lambda'] not in r12_bad_lams:
                has_rank3_new_target=True
            if len(rank3_leak_head)<5:
                rank3_leak_head.append(lv)
    stats[(full_scalar_clean, r12['leakage_violation_count']>0, allr['leakage_violation_count']>0, has_rank3_leak, has_rank3_new_target)] += 1
    if has_rank3_leak and len(examples)<10:
        examples.append({'index': idx, 'source': rec, 'full_scalar_clean': full_scalar_clean,
                         'r12_scalar': r12['scalar_violation_count'], 'all_scalar': allr['scalar_violation_count'],
                         'r12_leak': r12['leakage_violation_count'], 'all_leak': allr['leakage_violation_count'],
                         'has_rank3_new_target': has_rank3_new_target, 'rank3_leak_head': rank3_leak_head})
result={'schema':'s0908_samew_rank3_contribution_v1',
        'survivors':survivors,
        'tuple_meaning':'(full_rank123_scalar_clean, rank12_has_leak, allsource_has_leak, allsource_has_rank3_leak, rank3_source_creates_new_bad_target)',
        'stats':{str(k):int(v) for k,v in sorted(stats.items(), key=lambda kv: str(kv[0]))},
        'examples':examples,
        'interpretation':'Same-W survivors are local calibration only. This separates rank-3 scalar-cleanliness and rank-3-source contributions within that local family.'}
out_path.parent.mkdir(parents=True, exist_ok=True)
out_path.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
print(json.dumps({'out':str(out_path),'survivors':survivors,'stats':result['stats'],'examples':len(examples)}, indent=2, sort_keys=True))
