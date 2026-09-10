#!/usr/bin/env python3
"""Export compact corrected-shadow certificates and verify them independently.

The compact certificate stores only: source support, saturated lambda guard, row indices
from the labelled 3x3 shadow system, and the derived support-family classification.
The verifier rebuilds the shadow system from the support and guard, XORs the indicated
rows, and checks that the coefficient vector is zero and RHS is one.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path
from collections import Counter
import numpy as np

S0908=Path('scripts')
if str(S0908) not in sys.path: sys.path.insert(0,str(S0908))
from shadow_certificate_analysis import build_labelled_shadow_system, weights_for_guard, apply_classification_to_support, L15, TRACE_INCONSISTENT_9V, TRACE_CONSISTENT_9V  # type: ignore

BUNDLE=Path('data/shadow_certificate/shadow_certificate_extended_bundle.json')
OUT=Path('data/shadow_certificate/compact_shadow_certificates.json')
VERIFY_OUT=Path('data/shadow_certificate/compact_shadow_certificate_verification.json')


def source_support_for(entry):
    cert=entry['certificate']
    name=cert.get('name','')
    if name.startswith('analysis') or cert.get('source_support_label')=='trace_inconsistent_9v':
        return TRACE_INCONSISTENT_9V
    return L15


def compact_entry(entry):
    cert=entry['certificate']; cls=entry['classification']
    source=source_support_for(entry)
    records=cls['records']
    free=[int(r['p']) for r in records if r['class']=='free']
    local=[{'p':int(r['p']),'odd_dependency_qs':[int(q) for q in r.get('odd_dependency_qs',[]) or r.get('witness',[])]} for r in records if r['class']=='local_inconsistent']
    forced1=[int(r['p']) for r in records if r['class']=='forced' and int(r.get('forced_value',0))==1]
    forced0=[int(r['p']) for r in records if r['class']=='forced' and int(r.get('forced_value',0))==0]
    return {
        'name': cert['name'],
        'source_support': [int(x) for x in source],
        'lambda_guard': [int(x) for x in cert.get('lambda_guard', cert.get('guard_lambdas_used', []))],
        'used_guard_lambdas': [int(x) for x in cert.get('guard_lambdas_used', [])],
        'row_indices': [int(i) for i in cert.get('certificate_row_indices', [])],
        'row_count': int(cert.get('certificate_row_count', 0)),
        'type_counts': cert.get('type_counts', {}),
        'tensor_rhs': int(cls.get('tensor_rhs', cert.get('tensor_rhs',0))),
        'derived_guarded_relation': {
            'free_directions': free,
            'local_inconsistent_directions': local,
            'forced_1_directions': forced1,
            'forced_0_directions': forced0,
            'classification_counts': cls.get('class_counts', {}),
            'forced_value_counts': cls.get('forced_value_counts', {}),
            'relation_text': 'If all used_guard_lambdas are saturated at weight 9, no selected point is free or locally inconsistent, then parity of selected forced_1_directions must equal tensor_rhs. Local-inconsistent points are forbidden under their odd-dependency saturation witnesses. This is a shadow linear necessary condition only.',
        }
    }


def verify_compact(compact):
    source=compact['source_support']; guard=compact['lambda_guard']; rows=compact['row_indices']
    A,b,labels=build_labelled_shadow_system(source, guard)
    vx=np.zeros(A.shape[1], dtype=np.uint8); rb=0; used=[]
    ok_range=all(0 <= r < len(labels) for r in rows)
    if not ok_range:
        return {'name':compact['name'],'status':'invalid_row_index','row_count':len(rows),'system_rows':len(labels)}
    for r in rows:
        vx ^= A[r]
        rb ^= int(b[r])
        used.append(labels[r])
    guard_weights=weights_for_guard(source, compact['used_guard_lambdas'])
    # Rebuild relation self-application from compact classes to ensure source is actually excluded.
    free=set(compact['derived_guarded_relation']['free_directions'])
    local=set(int(x['p']) for x in compact['derived_guarded_relation']['local_inconsistent_directions'])
    forced1=set(compact['derived_guarded_relation']['forced_1_directions'])
    sel=set(source)
    forced1_parity=len(sel & forced1) & 1
    tensor_rhs=int(compact['tensor_rhs'])
    return {
        'name': compact['name'],
        'status': 'verified' if (ok_range and not vx.any() and rb==1) else 'failed',
        'system_rows': len(labels),
        'system_variables': int(A.shape[1]),
        'certificate_row_count': len(rows),
        'xor_coefficients_zero': bool(not vx.any()),
        'xor_rhs': int(rb),
        'used_type_counts': dict(Counter(l['type'] for l in used)),
        'source_guard_weights': guard_weights,
        'source_guard_saturated': all(int(v)==9 for v in guard_weights.values()),
        'source_free_selected': sorted(sel & free),
        'source_local_inconsistent_selected': sorted(sel & local),
        'source_forced1_parity': int(forced1_parity),
        'tensor_rhs': tensor_rhs,
        'source_excluded_by_guarded_relation': bool(all(int(v)==9 for v in guard_weights.values()) and not (sel & free) and not (sel & local) and forced1_parity != tensor_rhs),
    }


def main():
    bundle=json.loads(BUNDLE.read_text())
    entries=[compact_entry(e) for e in bundle['certificates']]
    payload={'schema':'s0908_compact_shadow_certificates_v1','field':'F2','meaning':'Auditable row-combination certificates for guarded corrected 3x3-shadow inconsistency; relation is support-dependent and only applies when guards are saturated.', 'certificates':entries}
    OUT.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    checks=[verify_compact(e) for e in entries]
    VERIFY_OUT.write_text(json.dumps({'schema':'s0908_compact_shadow_certificate_verification_v1','checks':checks,'all_verified':all(c['status']=='verified' for c in checks)}, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'out':str(OUT),'verify_out':str(VERIFY_OUT),'checks':checks,'all_verified':all(c['status']=='verified' for c in checks)},indent=2,sort_keys=True))

if __name__=='__main__': main()
