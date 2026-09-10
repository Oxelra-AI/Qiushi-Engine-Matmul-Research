#!/usr/bin/env python3
"""Assemble concise analysis artifact summary and hashes."""
from __future__ import annotations
import json, hashlib
from pathlib import Path

WS=Path(__file__).resolve().parent.parent
paths=[
'scripts/z4_cyclic_sat_f2.py',
'scripts/z4_cyclic_sat_f2_drat.py',
'scripts/collect_z4_drat_receipts.py',
'scripts/z4xcyclic_general_f2.py',
'scripts/z4xcyclic_general_drat.py',
'data/z4_cyclic_f2/z4_cyclic_positive_control_p4_4_2_1.json',
'data/z4_cyclic_f2/z4_cyclic_f2_results_padded.json',
'data/z4_cyclic_f2_drat/z4_cyclic_drat_receipts_all12.json',
'data/z4_cyclic_f2_drat/tool_versions.json',
'data/z4xcyclic_general_f2/z4xcyclic_general_results.json',
'data/z4xcyclic_general_f2_drat/z4xcyclic_general_drat_results.json',
]
meta={}
for p in paths:
    path=WS/p
    if path.exists():
        h=hashlib.sha256(path.read_bytes()).hexdigest()
        meta[p]={'bytes':path.stat().st_size,'sha256':h}
    else:
        meta[p]={'missing':True}

native=json.load(open(WS/'data/z4_cyclic_f2/z4_cyclic_f2_results_padded.json'))
receipts=json.load(open(WS/'data/z4_cyclic_f2_drat/z4_cyclic_drat_receipts_all12.json'))
pos=json.load(open(WS/'data/z4_cyclic_f2/z4_cyclic_positive_control_p4_4_2_1.json'))
gen=json.load(open(WS/'data/z4xcyclic_general_f2/z4xcyclic_general_results.json'))
gendrat=json.load(open(WS/'data/z4xcyclic_general_f2_drat/z4xcyclic_general_drat_results.json'))
summary={
 'ARTIFACT':40,
 'field':'F2',
 'restricted_family':'fixed BILR a0 conjugation g(X)=a0 X a0^{-1}; one size-12 (g^k plus cyclic) free triple orbit; at most 10 cube terms arranged in g-orbits of nominal lengths 1,2,4; zero/degenerate cube slots allowed',
 'restricted_rank22_partitions_tested':len(native['results']),
 'restricted_native_status_counts':{s:sum(1 for r in native['results'] if r['status']==s) for s in sorted({r['status'] for r in native['results']})},
 'restricted_drat_verified_count':receipts['verified_count'],
 'restricted_drat_patterns':[r['pattern'] for r in receipts['records'] if r.get('drat_status')=='VERIFIED'],
 'positive_control':'BILR rank-23 mod-2 pattern (4,4,2,1) SAT, direct all-729 Brent check zero errors',
 'positive_control_pattern':pos['pattern'],
 'positive_control_status':pos['status'],
 'positive_control_brent_errors':pos['check']['brent_errors'],
 'broader_H_family':'fixed tau(A,B,C)=(gB,gC,gA) orbits of nominal lengths 1,2,3,4,6,12; covers more than cube-residual family but still not all three-sided equivariant or characteristic-zero cases',
 'broader_fixed_dims':gen['fixed_dims'],
 'broader_probe_results':[{k:r[k] for k in ['pattern','status','solve_sec','param_dims'] if k in r} for r in gen['results']],
 'broader_drat_results':[{k:r[k] for k in ['pattern','status','drat_status','solve_sec','drat_verify_sec'] if k in r} for r in gendrat['records']],
 'scope_warning':'This excludes only stated F2 restricted subfamilies; it is not a general F2 rank-22 lower bound and has no direct characteristic-zero consequence.',
 'artifact_hashes':meta,
}
out=WS/'data/z4_cyclic_summary.json'
out.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in summary if k!='artifact_hashes'},indent=2))
print('Saved',out)
