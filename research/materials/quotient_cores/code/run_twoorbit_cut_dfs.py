#!/usr/bin/env python3
"""analysis: run corrected rank-2 branch DFS with two lift-cut orbits."""
from __future__ import annotations
import hashlib, json, subprocess, time
from pathlib import Path

ROOT=Path('research/research_record')
SPECS=ROOT/'workspace/data/quotient_branches/corrected_branch_specs.json'
PAIR_RUN=str(ROOT/'workspace/scripts/pair_prop_dfs')
CONSTRAINTS=ROOT/'workspace/data/quotient_lift/transport/rank2_cap5_plus_two_orbits_lift_cut_orbits.bin'
PAIR_BIN=ROOT/'workspace/data/quotient_dfs/rank2_cap7_first32.bin'
OUTDIR=ROOT/'workspace/data/quotient_lift/transport'
OUTDIR.mkdir(parents=True,exist_ok=True)

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

def run_one(branch,timeout:int):
    force=','.join(map(str,branch['force']))
    forbid=','.join(map(str,branch['forbid']))
    out=OUTDIR/f'rank2_branch{branch["branch"]}_twoorbit_cuts_{timeout}s.json'
    cmd=[PAIR_RUN,'--constraints',str(CONSTRAINTS),'--pair-rows',str(PAIR_BIN),'--target','19','--force',force,'--timeout',str(timeout),'--output',str(out)]
    if forbid: cmd += ['--exclude',forbid]
    t0=time.time(); cp=subprocess.run(cmd,text=True,capture_output=True,timeout=timeout+30); wall=time.time()-t0
    r=parse(cp.stdout) if cp.returncode==0 else None
    rec={'branch':branch['branch'],'rep':branch['representative'],'orbit_size':branch['orbit_size'],'forbid_count':branch['forbid_count'],'returncode':cp.returncode,'wall_sec':wall,'output':str(out),'stdout_tail':cp.stdout[-1000:],'stderr_tail':cp.stderr[-500:],'result':r}
    if r:
        rec.update({k:r.get(k) for k in ['complete','solutions','recursive_calls','candidate_tests','max_depth','global_shortage','pair_prunes','pair_forces','pair_propagations','saturated_rows','saturation_removed_points']})
    return rec

def main():
    import argparse
    ap=argparse.ArgumentParser(); ap.add_argument('--timeout',type=int,default=90); ap.add_argument('--branches',default='0,1,2,3,5')
    args=ap.parse_args()
    specs=json.loads(SPECS.read_text())['pivots']['rank2']['branches']
    wanted={int(x) for x in args.branches.split(',') if x.strip()}
    out={'schema':'s0908_twoorbit_cut_dfs_v1','timeout':args.timeout,'branches':sorted(wanted),'dfs_executable':PAIR_RUN,'constraints':str(CONSTRAINTS),'constraint_sha256':sha(CONSTRAINTS),'pair_rows':str(PAIR_BIN),'pair_rows_sha256':sha(PAIR_BIN),'runs':[]}
    for b in specs:
        if b['branch'] not in wanted: continue
        print(f'branch {b["branch"]}...', flush=True)
        rec=run_one(b,args.timeout); out['runs'].append(rec)
        print(json.dumps({k:rec.get(k) for k in ['branch','complete','solutions','recursive_calls','max_depth','pair_prunes','pair_forces','wall_sec']},sort_keys=True),flush=True)
    out['summary']=[{k:r.get(k) for k in ['branch','complete','solutions','recursive_calls','candidate_tests','max_depth','global_shortage','pair_prunes','pair_forces','pair_propagations','wall_sec']} for r in out['runs']]
    out['all_wanted_closed']=all(r.get('complete') and r.get('solutions')==0 for r in out['runs'])
    path=OUTDIR/f'twoorbit_cut_open_branch_impact_{args.timeout}s.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('saved',path)
    print(json.dumps({'all_wanted_closed':out['all_wanted_closed'],'summary':out['summary']},indent=2,sort_keys=True))

if __name__=='__main__': main()
