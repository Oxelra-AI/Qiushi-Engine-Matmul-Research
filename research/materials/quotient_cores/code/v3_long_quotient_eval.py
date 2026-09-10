#!/usr/bin/env python3
"""Evaluate analysis v3 long distinct E11-core supports against analysis quotient-rank cuts."""
from __future__ import annotations
import json, sys, time
from collections import Counter
from pathlib import Path
import numpy as np
SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
from complete_core_and_transversal import ROOT
from candidate_quotient_cut_scan import eval_candidate
from quotient_rank_cuts import build_contractions, point_mask_for_q

OUT = ROOT / 'workspace/data/quotient_rank_cuts/v3_long_quotient_eval.json'
SRC = ROOT / 'workspace/data/core_complete_transversal/core_e11_saturation_v3_complete_long.json'

def main():
    t0=time.time()
    T_core=np.load(ROOT/'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8)%2
    contractions=build_contractions(T_core)
    masks={q: point_mask_for_q(q) for q in contractions}
    d=json.loads(SRC.read_text())
    rows=[]
    for r in d['rounds']:
        if r.get('status') not in ('OPTIMAL','FEASIBLE') or 'support' not in r:
            continue
        ev=eval_candidate(f"v3_long_round{r['round']}", [int(x) for x in r['support']], contractions, masks, max_store=60)
        rows.append({
            'round': r['round'],
            'complete_violations': r['complete_wang_scan']['complete_violation_count'],
            'max_excess': r['complete_wang_scan']['max_excess'],
            'zero_domain_term_count': r['saturation']['zero_domain_term_count'],
            'linear_passed': r['saturation']['linear_passed'],
            'linear_affine_dim': r['saturation']['linear_affine_dim'],
            'transversal_failure_count_reported': r['saturation']['transversal_failure_count_reported'],
            'domain_hist': r['saturation']['term_domain_dims_hist'],
            'support': r['support'],
            'quotient_cut_eval': {k:v for k,v in ev.items() if k!='violations_head'},
            'quotient_cut_violations_head': ev['violations_head'][:20],
        })
        print(json.dumps({'round': r['round'], 'viol': rows[-1]['complete_violations'], 'zero': rows[-1]['zero_domain_term_count'], 'linear': rows[-1]['linear_passed'], 'trans': rows[-1]['transversal_failure_count_reported'], 'qviol': ev['violated_guarded_instances']}, sort_keys=True))
    result={
        'schema':'v3_long_quotient_eval_v1',
        'source': str(SRC),
        'field':'F2',
        'core':'E11',
        'round_count': len(rows),
        'best_by_complete_violations': sorted([{'round':r['round'],'complete_violations':r['complete_violations'],'zero':r['zero_domain_term_count'],'linear':r['linear_passed'],'trans':r['transversal_failure_count_reported'],'qviol':r['quotient_cut_eval']['violated_guarded_instances']} for r in rows], key=lambda x:x['complete_violations'])[:10],
        'rows': rows,
        'elapsed_sec': round(time.time()-t0,3),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(f'Saved {OUT}')
if __name__=='__main__':
    main()
