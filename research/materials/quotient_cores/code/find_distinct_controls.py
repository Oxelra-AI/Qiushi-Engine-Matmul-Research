#!/usr/bin/env python3
"""Find rank-21 E11 pool rows with many/all distinct A masks."""
import json
from pathlib import Path
import numpy as np
POOL = Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
OUT = Path("data/wang_native/controls")
OUT.mkdir(parents=True, exist_ok=True)
pool = np.load(POOL)
hist = {}
examples = {}
for i,row in enumerate(pool):
    R = row.shape[0]//3
    us = [int(row[3*t]) & 0xFF for t in range(R) if (int(row[3*t]) & 0xFF)]
    dc = len(set(us))
    hist[dc] = hist.get(dc,0)+1
    examples.setdefault(dc, i)
    if dc == R:
        data={"kind":"E11 core rank-21 all-distinct A support","source":str(POOL),"row":i,"rank":R,"a_multiset":us,"distinct_a_support":sorted(set(us)),"distinct_count":dc,"duplicate_count":0}
        path=OUT/f"e11_poolrow{i}_distinct21_support.json"
        path.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")
        print(json.dumps({"hist":hist,"first_distinct_row":i,"path":str(path)},indent=2,sort_keys=True))
        break
else:
    print(json.dumps({"hist":hist,"examples":examples,"first_distinct_row":None},indent=2,sort_keys=True))
