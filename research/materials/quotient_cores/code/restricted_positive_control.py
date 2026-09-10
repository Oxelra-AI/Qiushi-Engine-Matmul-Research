#!/usr/bin/env python3
"""Positive-control scan for a safe-DFS solution recorded in a ladder file."""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
SCRIPT=Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path: sys.path.insert(0,str(SCRIPT))
from coset_certificate_tools import load_lut, scan_multiset_full  # type: ignore


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--ladder',type=Path,required=True)
    ap.add_argument('--case-index',type=int,default=0)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    args=ap.parse_args()
    ladder=json.loads(args.ladder.read_text())
    case=ladder['cases'][args.case_index]
    meta=case['meta']; dfs=case['dfs']['result']
    if not dfs.get('solutions_head'):
        raise ValueError('no safe-DFS solution in selected ladder case')
    supp=[int(x) for x in dfs['solutions_head'][0]]
    H=[int(x) for x in meta['H']]
    length=int(meta['length'])
    scan=scan_multiset_full(load_lut(args.lut), H+supp, length)
    rec={'schema':'restricted_positive_control_v1','ladder':str(args.ladder),'case_index':args.case_index,'length':length,'H':H,'rank_one_support':supp,'A_multiset':H+supp,'dfs_complete':dfs.get('complete'),'dfs_solutions':dfs.get('solutions'),'full_lut_scan':scan}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(rec,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(args.out),'length':length,'support_size':len(H)+len(supp),'violations':scan['violation_count'],'max_excess':scan['max_excess']},indent=2,sort_keys=True))

if __name__=='__main__': main()
