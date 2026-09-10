#!/usr/bin/env python3
"""Build corrected quotient branch specs for rank-2/rank-3 quotient searches.

The full Wang row binary must remain unchanged.  Branch k forbids all points in
orbits 0..k-1 and forces the representative of orbit k.  This script compares
research_record's independently computed orbit partition with the peer partition and
then writes branch specs in the peer/discovery order for easier cross-research
comparison.
"""
from __future__ import annotations
import json, hashlib
from pathlib import Path

ROOT=Path('research/research_record')
PEER=Path('data/quotient_orbits/quotient_stabilizer_orbits.json')
MINE=ROOT/'workspace/data/quotient_branches/quotient_orbits_independent.json'
OUT=ROOT/'workspace/data/quotient_branches/corrected_branch_specs.json'

def sha(p):
    h=hashlib.sha256();
    with Path(p).open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()

def norm_sets(orbits):
    return sorted([tuple(sorted(o)) for o in orbits])

def main():
    peer=json.loads(PEER.read_text())
    mine=json.loads(MINE.read_text())
    out={'schema':'s0908_corrected_quotient_branch_specs_v1','peer_orbit_path':str(PEER),'peer_orbit_sha256':sha(PEER),'independent_orbit_path':str(MINE),'independent_orbit_sha256':sha(MINE),'pivots':{}}
    bin_paths={
        'rank2':'data/quotient_dfs/rank2_cap5_n19.bin',
        'rank3':'data/quotient_dfs/rank3_cap5_n19.bin',
    }
    pair_paths={
        'rank2':'data/quotient_dfs/rank2_cap7_first32.bin',
        'rank3':'data/quotient_dfs/rank3_cap7_first32.bin',
    }
    for name in ['rank2','rank3']:
        porbs=peer[name]['orbits']['orbits']
        morbs=mine['pivots'][name]['orbits']
        same = norm_sets(porbs)==norm_sets(morbs)
        prev=[]; branches=[]
        for idx,orb in enumerate(porbs):
            rep=min(orb)
            branches.append({'branch':idx,'representative':rep,'orbit_size':len(orb),'orbit':orb,'forbid':sorted(prev),'forbid_count':len(prev),'force':[rep],'constraints':bin_paths[name],'pair_rows_first32':pair_paths[name]})
            prev.extend(orb)
            prev=sorted(set(prev))
        out['pivots'][name]={'pivot':peer[name]['pivot'],'stabilizer_size_peer':peer[name]['stabilizer_size'],'stabilizer_size_independent':mine['pivots'][name]['stabilizer_size'],'orbit_partition_matches_independent':same,'num_orbits':len(porbs),'coverage_ok':sorted(prev)==list(range(1,256)),'branches':branches}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({name:{'num_orbits':out['pivots'][name]['num_orbits'],'match':out['pivots'][name]['orbit_partition_matches_independent'],'coverage_ok':out['pivots'][name]['coverage_ok'],'reps':[b['representative'] for b in out['pivots'][name]['branches']]} for name in ['rank2','rank3']},indent=2,sort_keys=True))
    print('saved',OUT)
if __name__=='__main__': main()
