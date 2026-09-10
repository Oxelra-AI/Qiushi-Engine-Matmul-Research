#!/usr/bin/env python3
"""Targeted analysis extraction for the independent analysis 9-violation trace-inconsistent support."""
from __future__ import annotations
import itertools, json, sys
from pathlib import Path
S0908=Path('scripts')
if str(S0908) not in sys.path: sys.path.insert(0,str(S0908))
from shadow_certificate_analysis import (TRACE_INCONSISTENT_9V, TRACE_CONSISTENT_9V, L15, find_tight_rank9, build_labelled_shadow_system, gf2_rref_augmented_with_combo, extract_shadow_certificate, classify_all_directions, apply_classification_to_support, weights_for_guard)
OUT=Path('data/shadow_certificate/target_certificate.json')

def consistent(support, qs):
    A,b,_=build_labelled_shadow_system(support, qs)
    c,r,ra,cert=gf2_rref_augmented_with_combo(A,b)
    return c,r,ra,cert

def first_min(support, tight):
    scan=[]
    for k in range(1,len(tight)+1):
        total=0; bad=[]
        for sub in itertools.combinations(tight,k):
            total+=1
            c,_,_,_=consistent(support, sub)
            if not c:
                bad.append(list(sub))
        scan.append({'k':k,'total':total,'inconsistent':len(bad),'examples':bad[:5]})
        print('k',k,'total',total,'bad',len(bad),flush=True)
        if bad:
            return {'size':k,'examples':bad[:5],'total':total,'total_inconsistent':len(bad),'scan':scan}
    return {'scan':scan}

def main():
    support=TRACE_INCONSISTENT_9V
    tight=find_tight_rank9(support)
    c,r,ra,_=consistent(support,tight)
    mini=first_min(support,tight) if not c else None
    chosen=mini['examples'][0] if mini and mini.get('examples') else tight
    cert=extract_shadow_certificate(support, chosen)
    cert['source_support_label']='trace_inconsistent_9v'
    cert['certificate_label']='trace_inconsistent_9v_minimal'
    cls=classify_all_directions(cert)
    apps=[]
    for lab,sup in [('trace_inconsistent_9v',TRACE_INCONSISTENT_9V),('trace_consistent_9v',TRACE_CONSISTENT_9V),('L15',L15)]:
        app=apply_classification_to_support(cls,sup)
        app['label']=lab
        app['guard_weights']=weights_for_guard(sup,cls['guard_lambdas'])
        app['guard_saturated']=all(v==9 for v in app['guard_weights'].values())
        apps.append(app)
    payload={'schema':'s0908_shadow_target_certificate_v1','field':'F2','support':support,'tight_rank9':tight,'full_shadow_consistent':bool(c),'rank':int(r),'augmented_rank':int(ra),'minimal_subset':mini,'certificate':cert,'classification':{'guard_lambdas':cls['guard_lambdas'],'tensor_rhs':cls['tensor_rhs'],'class_counts':cls['class_counts'],'forced_value_counts':cls['forced_value_counts'],'records':cls['records']},'applications':apps}
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    brief={'out':str(OUT),'tight_count':len(tight),'full_consistent':bool(c),'rank':int(r),'aug':int(ra),'minimal_subset':mini,'cert_brief':{'guard':cert.get('guard_lambdas_used'),'row_count':cert.get('certificate_row_count'),'type_counts':cert.get('type_counts'),'tensor_rhs':cert.get('tensor_rhs'),'trace_rhs':cert.get('trace_rhs'),'classification_counts':cls['class_counts'],'forced_value_counts':cls['forced_value_counts']},'applications':apps}
    print(json.dumps(brief,indent=2,sort_keys=True))
if __name__=='__main__': main()
