#!/usr/bin/env python3
"""analysis: compare the first two certified rank-2 lift-cut obstructions."""
from __future__ import annotations
import hashlib, json
from collections import Counter
from pathlib import Path

ROOT=Path('research/research_record')
OUT=ROOT/'workspace/data/quotient_lift/transport/rank2_two_lift_cut_comparison.json'
ORBIT=ROOT/'workspace/data/quotient_branches/quotient_orbits_independent.json'
CEGAR2=ROOT/'workspace/data/quotient_lift/transport/rank2_support_cut_cegar_cap3.json'
MIN2=ROOT/'workspace/data/quotient_lift/transport/rank2_survivor2_lift_cut_minimized.json'
TRAN1=ROOT/'workspace/data/quotient_lift/transport/rank2_lift_cut_stabilizer_transport.json'
TRAN2=ROOT/'workspace/data/quotient_lift/transport/rank2_survivor2_lift_cut_stabilizer_transport.json'
MIN1=ROOT/'workspace/data/quotient_lift/minimized_lift_cut_peer.json'
PEER1=[1,3,9,33,99,128,132,144,148,160,184,189,192,198,209,215,224,249,254]

def sha(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''):
            h.update(c)
    return h.hexdigest()

def mask(points):
    m=0
    for p in points: m |= 1<<int(p)
    return m

def comp(points, orbit_id):
    c=Counter(orbit_id[int(p)] for p in points)
    return {str(k):int(v) for k,v in sorted(c.items())}

def main():
    od=json.loads(ORBIT.read_text())['pivots']['rank2']
    orbit_id={}
    for i,orb in enumerate(od['orbits']):
        for p in orb: orbit_id[int(p)]=i
    a1=[int(x) for x in json.loads(MIN1.read_text())['cut']['points']]
    d2=json.loads(MIN2.read_text()); a2=[int(x) for x in d2['minimized_points']]
    s2=json.loads(CEGAR2.read_text())['rounds'][0]['support']
    t1=json.loads(TRAN1.read_text()); t2=json.loads(TRAN2.read_text())
    fam1=[tuple(int(x) for x in c['cut_points']) for c in t1['unique_cuts']]
    fam2=[tuple(int(x) for x in c['cut_points']) for c in t2['unique_cuts']]
    set1={mask(c) for c in fam1}; set2={mask(c) for c in fam2}
    inter_hist=Counter()
    max_inter=[]
    for c1 in fam1:
        s1=set(c1)
        for c2 in fam2:
            v=len(s1 & set(c2)); inter_hist[v]+=1
            if not max_inter or v>max_inter[0]['intersection']:
                max_inter=[{'intersection':v,'cut1':list(c1),'cut2':list(c2),'common':sorted(s1&set(c2))}]
            elif v==max_inter[0]['intersection'] and len(max_inter)<10:
                max_inter.append({'intersection':v,'cut1':list(c1),'cut2':list(c2),'common':sorted(s1&set(c2))})
    out={'schema':'s0908_rank2_two_lift_cut_comparison_v1','orbit_file':str(ORBIT),'orbit_file_sha256':sha(ORBIT),'rank2_orbit_representatives':od['representatives'],'first_source_support':PEER1,'second_source_support':s2,'support_overlap':sorted(set(PEER1)&set(s2)),'support_first_minus_second':sorted(set(PEER1)-set(s2)),'support_second_minus_first':sorted(set(s2)-set(PEER1)),'first_minimized_cut':a1,'second_minimized_cut':a2,'base_cut_overlap':sorted(set(a1)&set(a2)),'base_cut_first_minus_second':sorted(set(a1)-set(a2)),'base_cut_second_minus_first':sorted(set(a2)-set(a1)),'first_cut_orbit_composition':comp(a1,orbit_id),'second_cut_orbit_composition':comp(a2,orbit_id),'first_cut_certificate_sha256':json.loads(MIN1.read_text()).get('assignment_certificate_sha256') or json.loads(MIN1.read_text()).get('assignment_certificate',{}).get('certificate_sha256'),'second_cut_certificate_sha256':d2.get('assignment_certificate_sha256'),'transport1_manifest':str(TRAN1),'transport1_sha256':sha(TRAN1),'transport1_row_sha256':t1['row_binary_sha256'],'transport1_unique_cuts':len(fam1),'transport2_manifest':str(TRAN2),'transport2_sha256':sha(TRAN2),'transport2_row_sha256':t2['row_binary_sha256'],'transport2_unique_cuts':len(fam2),'transport_family_intersection_count':len(set1&set2),'transport_family_union_count':len(set1|set2),'pairwise_cut_intersection_hist':{str(k):int(v) for k,v in sorted(inter_hist.items())},'max_pairwise_intersection_examples':max_inter,'interpretation':'The two source supports differ only by exchanging {33,99} for {165,231}, but their minimized 12-point obstructions are not stabilizer-equivalent as support sets under pivot-17; their 48-cut transport orbits are disjoint. This suggests several obstruction orbits may be needed for rank-2 coverage even when quotient supports are close.'}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:out[k] for k in ['support_first_minus_second','support_second_minus_first','base_cut_overlap','base_cut_first_minus_second','base_cut_second_minus_first','first_cut_orbit_composition','second_cut_orbit_composition','transport_family_intersection_count','transport_family_union_count','pairwise_cut_intersection_hist']},indent=2,sort_keys=True))
    print('saved',OUT)

if __name__=='__main__': main()
