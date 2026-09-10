#!/usr/bin/env python3
"""Summarize native DFS branch runs for E11 Wang cap<=5 enumeration."""
import json, glob
from pathlib import Path

ROOT=Path("data/wang_native")
files=sorted(ROOT.glob("native_fast_cap5_branch*_1800s.json"))
branches=[]
for p in files:
    try:
        data=json.loads(p.read_text())
        br=data['branches'][0] if 'branches' in data else data.get('result', data)
    except Exception as e:
        br={'parse_error':str(e)}
    br['file']=str(p)
    branches.append(br)
complete=[b for b in branches if b.get('complete')]
timeouts=[b for b in branches if b.get('timeout')]
out={
    'status':'ok',
    'file_count':len(files),
    'complete_count':len(complete),
    'timeout_count':len(timeouts),
    'solutions_total':sum(int(b.get('solutions',0)) for b in branches),
    'max_depth_by_branch':{str(b.get('branch')):b.get('max_depth') for b in branches},
    'node_count_by_branch':{str(b.get('branch')):b.get('node_count_by_depth') for b in branches},
    'branches':branches,
}
path=ROOT/'native_fast_cap5_1800s_summary.json'
path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps({'complete_count':out['complete_count'],'timeout_count':out['timeout_count'],'solutions_total':out['solutions_total'],'max_depth_by_branch':out['max_depth_by_branch'],'out':str(path)},indent=2,sort_keys=True))
