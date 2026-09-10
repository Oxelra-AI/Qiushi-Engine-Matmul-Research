#!/usr/bin/env python3
"""analysis quotient branch pilots using corrected symmetry semantics.

Do NOT remove earlier-orbit points from row masks.  Each branch keeps the full
quotient Wang binary, forbids all earlier orbit points in the initial domain,
and forces the branch representative.  This wrapper runs selected cap-only and
pair-propagation searches and summarizes complete zero-support closures versus
timeouts.
"""
from __future__ import annotations
import argparse, json, subprocess, time
from pathlib import Path

ROOT=Path('research/research_record')
SPECS=ROOT/'workspace/data/quotient_branches/corrected_branch_specs.json'
CAP_BIN={
    'rank2': str(ROOT/'workspace/data/quotient_dfs/rank2_cap5_n19.bin'),
    'rank3': str(ROOT/'workspace/data/quotient_dfs/rank3_cap5_n19.bin'),
}
PAIR32={
    'rank2': str(ROOT/'workspace/data/quotient_dfs/rank2_cap7_first32.bin'),
    'rank3': str(ROOT/'workspace/data/quotient_dfs/rank3_cap7_first32.bin'),
}
CAP_RUNNER=str(ROOT/'workspace/scripts/sound_bitset_dfs')
PAIR_RUNNER=str(ROOT/'workspace/scripts/pair_prop_dfs')
OUTDIR=ROOT/'workspace/data/quotient_branches'

def run_one(cmd, timeout):
    t0=time.time()
    cp=subprocess.run(cmd,text=True,capture_output=True,timeout=timeout+10)
    elapsed=time.time()-t0
    if cp.returncode!=0:
        return {'ok':False,'returncode':cp.returncode,'elapsed_wall':elapsed,'stdout':cp.stdout[-1000:],'stderr':cp.stderr[-1000:]}
    # Runner prints one result line plus summary file; parse first JSON object line from stdout.
    result=None
    for line in cp.stdout.splitlines():
        line=line.strip()
        if line.startswith('{') and '"target"' in line:
            try:
                result=json.loads(line); break
            except json.JSONDecodeError:
                pass
    return {'ok':True,'elapsed_wall':elapsed,'result':result,'stdout_tail':cp.stdout[-500:],'stderr_tail':cp.stderr[-500:]}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--timeout',type=int,default=45); ap.add_argument('--mode',choices=['selected','all'],default='selected'); args=ap.parse_args()
    specs=json.loads(SPECS.read_text())
    plan=[]
    if args.mode=='selected':
        plan=[('rank3',4),('rank3',5),('rank2',13),('rank3',0),('rank2',0)]
    else:
        plan=[]
        for name in ['rank3','rank2']:
            for b in specs['pivots'][name]['branches']:
                plan.append((name,b['branch']))
    out={'schema':'s0908_corrected_quotient_branch_pilots_v1','semantics':'full row masks unchanged; initial domain forbids earlier orbit points; representative forced','timeout_per_run':args.timeout,'plan':plan,'runs':[]}
    for name,bidx in plan:
        b=specs['pivots'][name]['branches'][bidx]
        force=','.join(map(str,b['force']))
        forbid=','.join(map(str,b['forbid']))
        for method in ['cap_only','pair32']:
            outpath=OUTDIR/f'{name}_branch{bidx}_{method}_{args.timeout}s.json'
            if method=='cap_only':
                cmd=[CAP_RUNNER,'--constraints',CAP_BIN[name],'--target','19','--force',force,'--timeout',str(args.timeout),'--output',str(outpath)]
            else:
                cmd=[PAIR_RUNNER,'--constraints',CAP_BIN[name],'--pair-rows',PAIR32[name],'--target','19','--force',force,'--timeout',str(args.timeout),'--output',str(outpath)]
            if forbid:
                cmd += ['--exclude',forbid]
            r=run_one(cmd,args.timeout)
            rec={'pivot':name,'branch':bidx,'representative':b['representative'],'orbit_size':b['orbit_size'],'forbid_count':b['forbid_count'],'method':method,'cmd':cmd,'output':str(outpath),**r}
            if r.get('result'):
                rr=r['result']; rec.update({'complete':rr.get('complete'),'solutions':rr.get('solutions'),'recursive_calls':rr.get('recursive_calls'),'max_depth':rr.get('max_depth'),'global_shortage':rr.get('global_shortage'),'pair_prunes':rr.get('pair_prunes'),'pair_forces':rr.get('pair_forces'),'pair_propagations':rr.get('pair_propagations')})
            out['runs'].append(rec)
            print(json.dumps({k:rec.get(k) for k in ['pivot','branch','method','complete','solutions','recursive_calls','max_depth','pair_prunes','pair_forces','output']},sort_keys=True))
    OUTDIR.mkdir(parents=True,exist_ok=True)
    summary=OUTDIR/f'corrected_quotient_branch_pilots_{args.mode}_{args.timeout}s_summary.json'
    summary.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('saved',summary)
if __name__=='__main__': main()
