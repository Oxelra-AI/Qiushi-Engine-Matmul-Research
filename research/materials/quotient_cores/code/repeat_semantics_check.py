#!/usr/bin/env python3
"""analysis: exact repeat-direction bookkeeping and forced-preload checks.

A 19-term E11 A-multiset has multiplicity at most two because all quotient-line
Wang caps are 1 except the six listed directions, whose line caps are 2.  If D
is the set of doubled directions, write the multiset as a distinct support S
plus one extra copy of each p in D.  Then |S|+|D|=19, hence |S|=19-|D|, and
D must be a subset of S.  The residual Wang rows subtract only the extra copy
|D∩U| from every cap; the search must still force one selected copy of each p
in D.

This script checks the immediate preload condition D⊂S against the residual
rows: for every residual row U, |D∩U| (the forced distinct copy) must be <=
residual cap. It also reports the peer --exclude mismatch.
"""
from __future__ import annotations
import json, struct, hashlib
from pathlib import Path
from collections import Counter

MANIFEST = Path('data/wang_native/repeats/residual_cap5_manifest.json')
OUT = Path('data/domain_dfs_soundness')


def load_bin(path: Path):
    data=path.read_bytes(); assert data[:8]==b'E11WANG1'
    n=struct.unpack_from('<I',data,8)[0]; rows=[]; off=12
    for i in range(n):
        cap,dim,_res,w0,w1,w2,w3=struct.unpack_from('<BBHQQQQ',data,off); off+=36
        rows.append((cap,dim,(w0,w1,w2,w3)))
    return rows, hashlib.sha256(data).hexdigest()

def bit(words,p): return (words[p>>6]>>(p&63))&1

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    manifest=json.loads(MANIFEST.read_text())
    records=[]; hist=Counter()
    for e in manifest['summaries']:
        D=tuple(e['repeat_subset']); target=e['target_distinct_support_size']
        path=Path(e['binary_path']) if e.get('binary_path') else None
        if not path or not path.exists():
            records.append({'D':D,'target_distinct_support_size':target,'status':'missing_binary'}); continue
        rows,sha=load_bin(path)
        fails=[]; worst=None
        for idx,(cap,dim,words) in enumerate(rows):
            occ=sum(bit(words,p) for p in D)
            margin=cap-occ
            if worst is None or margin < worst['margin']:
                worst={'row_index':idx,'cap':cap,'dim':dim,'forced_occ':occ,'margin':margin,'inside':[p for p in D if bit(words,p)]}
            if occ>cap and len(fails)<10:
                fails.append({'row_index':idx,'cap':cap,'dim':dim,'forced_occ':occ,'inside':[p for p in D if bit(words,p)]})
        status='preload_ok' if not fails else 'forced_D_violates_residual_rows'
        hist[(len(D),status)] += 1
        records.append({
            'D':D,'repeat_size':len(D),'target_distinct_support_size':target,'required_relation':'multiset_size=|S|+|D|=19 and D subset S',
            'peer_old_runner_used':'--exclude '+','.join(map(str,D))+' (searches S disjoint from D)',
            'correct_runner_should_use':'--target '+str(target)+' --force '+','.join(map(str,D)),
            'row_count':len(rows),'binary_sha256':sha,'status':status,'worst_margin':worst,'fail_head':fails,
        })
    result={'schema':'s0908_repeat_semantics_v1','manifest':str(MANIFEST),'summary_by_repeat_size_and_status':{str(k):int(v) for k,v in sorted(hist.items())},'records':records}
    out=OUT/'repeat_semantics_check.json'
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='records'}|{'records_head':records[:20]},indent=2,sort_keys=True))

if __name__=='__main__': main()
