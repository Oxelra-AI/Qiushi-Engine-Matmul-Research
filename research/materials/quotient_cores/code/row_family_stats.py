#!/usr/bin/env python3
"""analysis: summarize E11 Wang rows by residual capacity and dimension.

This helps choose which omitted Wang rows may be useful for the new global-size
one-row residual-capacity bound without loading all rows into the DFS state.
"""
from __future__ import annotations
import json, sys
from collections import Counter, defaultdict
from pathlib import Path
S04=Path('scripts')
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from core_capacity_from_wang_lut import load_lut  # type: ignore
from wang_capacity_lazy import unpack_basis, rref_basis # type: ignore
LUT=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
OUT=Path('data/domain_dfs_soundness/row_family_stats.json')
MASK9=(1<<9)-1
N=19

def contains_e11(key:int)->bool:
    d=key&0xF
    return d>0 and (((key>>(4+9*(d-1)))&MASK9)==1)

def key9_to_basis8(key9:int):
    raw=[]
    for b in unpack_basis(key9):
        if b==1: continue
        q=int(b)
        if q&1: q^=1
        q8=0
        for bit in range(1,9):
            if (q>>bit)&1: q8 |= 1<<(bit-1)
        if q8: raw.append(q8)
    return tuple(rref_basis(raw,n=8)) if raw else tuple()

def main():
    lut,_=load_lut(LUT)
    cap_dim=Counter(); cap_inc=Counter(); cap_rows=Counter(); cap_size_hist=defaultdict(Counter)
    examples=defaultdict(list)
    for key,lb0 in lut.items():
        key=int(key); lb=int(lb0)
        if not contains_e11(key): continue
        cap=N-lb
        basis=key9_to_basis8(key)
        dim=len(basis)
        size=(1<<dim)-1 if dim>=0 else 0
        cap_dim[(cap,dim)] += 1
        cap_rows[cap]+=1; cap_inc[cap]+=size; cap_size_hist[cap][size]+=1
        if len(examples[cap])<3:
            examples[cap].append({'key9':key,'dim8':dim,'size':size,'lb':lb})
    out={
        'schema':'s0908_row_family_stats_v1',
        'source_lut':str(LUT),
        'N':N,
        'cap_rows':{str(k):int(v) for k,v in sorted(cap_rows.items())},
        'cap_total_point_incidences':{str(k):int(v) for k,v in sorted(cap_inc.items())},
        'cap_avg_row_size':{str(k):cap_inc[k]/cap_rows[k] for k in sorted(cap_rows)},
        'cap_dim_counts':{f'cap{c}_dim{d}':int(v) for (c,d),v in sorted(cap_dim.items())},
        'cap_size_hist':{str(c):{str(s):int(v) for s,v in sorted(h.items())} for c,h in sorted(cap_size_hist.items())},
        'examples':{str(c):examples[c] for c in sorted(examples)},
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
