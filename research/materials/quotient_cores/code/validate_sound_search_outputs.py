#!/usr/bin/env python3
"""Summarize analysis sound search outputs and rescan any stored solutions."""
from __future__ import annotations
import json, struct, hashlib
from pathlib import Path
from collections import Counter

OUT = Path('data/domain_dfs_soundness')
CAP5 = OUT/'e11_wang_cap5_rebuilt.bin'


def load_wang_bin(path):
    data=path.read_bytes(); assert data[:8]==b'E11WANG1'
    n=struct.unpack_from('<I', data, 8)[0]
    rows=[]; off=12
    for _ in range(n):
        cap,dim,_res,w0,w1,w2,w3=struct.unpack_from('<BBHQQQQ', data, off); off += 36
        rows.append((cap,dim,(w0,w1,w2,w3)))
    return rows, hashlib.sha256(data).hexdigest()


def contains(words,p): return (words[p>>6]>>(p&63))&1

def violations(sol, rows, head=10):
    ans=[]; s=set(sol)
    for i,(cap,dim,words) in enumerate(rows):
        occ=sum(1 for p in s if contains(words,p))
        if occ>cap:
            ans.append({'row_index':i,'cap':cap,'dim':dim,'occ':occ})
            if len(ans)>=head: break
    return ans


def load(path):
    try: return json.loads(path.read_text())
    except Exception as e: return {'error':str(e)}


def main():
    rows,sha=load_wang_bin(CAP5)
    files=(sorted(OUT.glob('sound_cap5_branch*_*.json')) + sorted(OUT.glob('sound_mixed_gap6_branch*.json')) + sorted(OUT.glob('sound_repeat_*.json')) + sorted(OUT.glob('bitset_cap5_branch*.json')) + sorted(OUT.glob('bitset_mixed_gap6_branch*.json')))
    summaries=[]; complete_no_solution=[]; incomplete=[]; solution_rescans=[]
    for p in files:
        data=load(p); results=data.get('results') or [data]
        for r in results:
            item={'file':str(p),'branch':r.get('branch'),'rep':r.get('rep'),'target':r.get('target'), 'complete':r.get('complete'), 'timeout':r.get('timeout'), 'solutions':r.get('solutions'), 'max_depth':r.get('max_depth'), 'elapsed_sec':r.get('elapsed_sec'), 'calls':r.get('recursive_calls'), 'mixed_prunes':r.get('mixed_prunes')}
            summaries.append(item)
            if r.get('complete') and r.get('solutions')==0: complete_no_solution.append(item)
            if not r.get('complete'): incomplete.append(item)
            for sol in r.get('solutions_head',[]):
                solution_rescans.append({'file':str(p),'solution':sol,'wang_violations_head':violations(sol,rows)})
    result={
        'schema':'s0908_sound_search_summary_v1',
        'cap5_binary':str(CAP5),'cap5_sha256':sha,'cap5_rows':len(rows),
        'files_scanned':len(files),'result_records':len(summaries),
        'complete_no_solution_count':len(complete_no_solution),'incomplete_count':len(incomplete),
        'complete_no_solution':complete_no_solution,
        'incomplete':incomplete,
        'solution_rescans':solution_rescans,
        'branch_status_hist':{str(k): int(v) for k,v in Counter((str(x.get('branch')), bool(x.get('complete')), int(x.get('solutions') or 0)) for x in summaries).items()},
    }
    out=OUT/'sound_search_summary.json'
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()
