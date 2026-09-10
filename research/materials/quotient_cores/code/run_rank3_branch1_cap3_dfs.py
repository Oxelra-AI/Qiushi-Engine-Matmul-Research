#!/usr/bin/env python3
"""analysis: replay rank-3 branch-1 infeasibility with the corrected DFS engine."""
from __future__ import annotations
import hashlib, json, subprocess, time
from pathlib import Path
ROOT=Path('research/research_record')
SPECS=ROOT/'workspace/data/quotient_branches/corrected_branch_specs.json'
DFS=str(ROOT/'workspace/scripts/pair_prop_dfs')
CONSTRAINTS=ROOT/'workspace/data/quotient_lift/rank3/rank3_cap3_n19.bin'
PAIR=ROOT/'workspace/data/quotient_dfs/rank3_cap7_first32.bin'
OUT=ROOT/'workspace/data/quotient_lift/rank3/rank3_branch1_cap3_pair32_dfs.json'
MAN=ROOT/'workspace/data/quotient_lift/rank3/rank3_branch1_cap3_pair32_dfs_manifest.json'

def sha(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''):
            h.update(c)
    return h.hexdigest()

def parse(stdout:str):
    for line in stdout.splitlines():
        line=line.strip()
        if line.startswith('{') and '"target"' in line:
            return json.loads(line)
    return None

def main():
    import argparse
    ap=argparse.ArgumentParser(); ap.add_argument('--timeout',type=int,default=600)
    args=ap.parse_args()
    br=json.loads(SPECS.read_text())['pivots']['rank3']['branches'][1]
    force=','.join(map(str,br['force'])); forbid=','.join(map(str,br['forbid']))
    cmd=[DFS,'--constraints',str(CONSTRAINTS),'--pair-rows',str(PAIR),'--target','19','--force',force,'--exclude',forbid,'--timeout',str(args.timeout),'--output',str(OUT)]
    t0=time.time(); cp=subprocess.run(cmd,text=True,capture_output=True,timeout=args.timeout+60); wall=time.time()-t0
    result=parse(cp.stdout) if cp.returncode==0 else None
    out={'schema':'s0908_rank3_branch1_cap3_pair32_dfs_manifest_v1','branch_spec_file':str(SPECS),'branch_spec_sha256':sha(SPECS),'branch':{k:br[k] for k in ['branch','representative','orbit_size','force','forbid_count','forbid']},'dfs_executable':DFS,'constraints':str(CONSTRAINTS),'constraints_sha256':sha(CONSTRAINTS),'pair_rows':str(PAIR),'pair_rows_sha256':sha(PAIR),'command':' '.join(cmd),'returncode':cp.returncode,'wall_sec':wall,'stdout_tail':cp.stdout[-2000:],'stderr_tail':cp.stderr[-1000:],'output':str(OUT),'result':result}
    if result:
        out.update({k:result.get(k) for k in ['complete','solutions','recursive_calls','candidate_tests','max_depth','timeout','forced_infeasible','global_shortage','pair_prunes','pair_forces','pair_propagations','saturated_rows','saturation_removed_points']})
    MAN.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:out.get(k) for k in ['returncode','complete','solutions','timeout','forced_infeasible','recursive_calls','candidate_tests','max_depth','global_shortage','pair_prunes','pair_forces','wall_sec','output']},indent=2,sort_keys=True))
    print('saved',MAN)
if __name__=='__main__': main()
