#!/usr/bin/env python3
"""Run a corrected-semantics rank-3 quotient branch overview.

Full row masks unchanged; each branch forbids earlier orbit points and forces its
representative.  Intended as a matched short comparison of cap-only versus the
patched pair-propagation runner over the 6 rank-3 stabilizer branches.
"""
from __future__ import annotations
import json, subprocess, time
from pathlib import Path
ROOT=Path('research/research_record')
SPECS=ROOT/'workspace/data/quotient_branches/corrected_branch_specs.json'
CAP_BIN=str(ROOT/'workspace/data/quotient_dfs/rank3_cap5_n19.bin')
PAIR_BIN=str(ROOT/'workspace/data/quotient_dfs/rank3_cap7_first32.bin')
CAP_RUN=str(ROOT/'workspace/scripts/sound_bitset_dfs')
PAIR_RUN=str(ROOT/'workspace/scripts/pair_prop_dfs')
OUTDIR=ROOT/'workspace/data/quotient_branches'

def parse(stdout):
    for line in stdout.splitlines():
        line=line.strip()
        if line.startswith('{') and '"target"' in line:
            try: return json.loads(line)
            except Exception: pass
    return None

def main():
    import argparse
    ap=argparse.ArgumentParser(); ap.add_argument('--timeout',type=int,default=30); args=ap.parse_args()
    specs=json.loads(SPECS.read_text())['pivots']['rank3']['branches']
    out={'schema':'s0908_rank3_branch_overview_v1','timeout':args.timeout,'runs':[]}
    for b in specs:
        force=','.join(map(str,b['force'])); forbid=','.join(map(str,b['forbid']))
        for method,runner in [('cap_only',CAP_RUN),('pair32',PAIR_RUN)]:
            outfile=OUTDIR/f'rank3_overview_branch{b["branch"]}_{method}_{args.timeout}s.json'
            cmd=[runner,'--constraints',CAP_BIN,'--target','19','--force',force,'--timeout',str(args.timeout),'--output',str(outfile)]
            if method=='pair32': cmd[1:1]=['--pair-rows',PAIR_BIN]  # wrong position repaired below
            if method=='pair32':
                cmd=[PAIR_RUN,'--constraints',CAP_BIN,'--pair-rows',PAIR_BIN,'--target','19','--force',force,'--timeout',str(args.timeout),'--output',str(outfile)]
            if forbid: cmd += ['--exclude',forbid]
            t0=time.time(); cp=subprocess.run(cmd,text=True,capture_output=True,timeout=args.timeout+15); wall=time.time()-t0
            r=parse(cp.stdout) if cp.returncode==0 else None
            rec={'branch':b['branch'],'rep':b['representative'],'orbit_size':b['orbit_size'],'forbid_count':b['forbid_count'],'method':method,'returncode':cp.returncode,'wall_sec':wall,'output':str(outfile),'result':r,'stderr_tail':cp.stderr[-300:]}
            if r: rec.update({k:r.get(k) for k in ['complete','solutions','recursive_calls','max_depth','global_shortage','pair_prunes','pair_forces','pair_propagations']})
            out['runs'].append(rec)
            print(json.dumps({k:rec.get(k) for k in ['branch','method','complete','solutions','recursive_calls','max_depth','pair_prunes','pair_forces']},sort_keys=True))
    path=OUTDIR/f'rank3_branch_overview_{args.timeout}s_summary.json'; path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('saved',path)
if __name__=='__main__': main()
