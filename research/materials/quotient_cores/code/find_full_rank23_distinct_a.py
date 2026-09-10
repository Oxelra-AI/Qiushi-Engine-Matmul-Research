#!/usr/bin/env python3
"""Search available rank-23 scheme files for a full T333 scheme with distinct A factors.

This is only for positive-control calibration of support enumerators.  It tries
simple flat mask triples in .npy files and verifies them against the canonical
T[3i+j,3j+k,3i+k] convention over F2 before recording A-duplicate statistics.
"""
from __future__ import annotations
import json, subprocess
from pathlib import Path
import numpy as np

OUT = Path("data/wang_native/controls/full_rank23_corpus_scan.json")
ROOTS = [
    Path("data"),
]

def build_t333():
    T=np.zeros((9,9,9),dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3): T[3*i+j,3*j+k,3*i+k]=1
    return T

def vec(m,n=9): return np.array([(int(m)>>i)&1 for i in range(n)],dtype=np.uint8)

def verify_terms(terms):
    T=np.zeros((9,9,9),dtype=np.uint8)
    for u,v,w in terms:
        if not (0 <= int(u) < 512 and 0 <= int(v) < 512 and 0 <= int(w) < 512): return None
        T ^= (vec(u).reshape(9,1,1)*vec(v).reshape(1,9,1)*vec(w).reshape(1,1,9)).astype(np.uint8)
    return int(np.sum(T ^ build_t333()))

def iter_candidate_terms(arr):
    a=np.asarray(arr)
    if a.ndim==1 and a.size%3==0:
        R=a.size//3
        if R==23: yield [[int(a[3*t]),int(a[3*t+1]),int(a[3*t+2])] for t in range(R)]
    if a.ndim==2:
        for row in a:
            if row.size%3==0 and row.size//3==23:
                yield [[int(row[3*t]),int(row[3*t+1]),int(row[3*t+2])] for t in range(23)]

def main():
    files=[]
    for r in ROOTS:
        files.extend(r.glob("**/*rank23*.npy"))
    records=[]
    found=None
    for p in files:
        try:
            arr=np.load(p,allow_pickle=True)
        except Exception as e:
            records.append({"path":str(p),"load_error":str(e)}); continue
        checked=0
        for terms in iter_candidate_terms(arr):
            checked += 1
            diff=verify_terms(terms)
            if diff is None: continue
            us=[u for u,v,w in terms]
            rec={"path":str(p),"candidate_index":checked-1,"diff":diff,"a_distinct":len(set(us)),"a_duplicate":len(us)-len(set(us)),"a_multiset":us}
            records.append(rec)
            if diff==0 and len(set(us))==23 and found is None:
                found=rec | {"terms":terms}
                sp=OUT.parent/"full_rank23_distinct_a_support.json"
                sp.write_text(json.dumps({"kind":"Full T333 rank-23 all-distinct A support","source":str(p),"rank":23,"a_multiset":us,"distinct_a_support":sorted(set(us)),"distinct_count":23,"duplicate_count":0,"terms":terms},indent=2,sort_keys=True)+"\n")
        if checked==0:
            records.append({"path":str(p),"candidate_count":0,"shape":list(np.asarray(arr).shape),"dtype":str(np.asarray(arr).dtype)})
    out={"files_scanned":len(files),"records_head":records[:100],"verified_candidates":sum(1 for r in records if r.get('diff')==0),"found_distinct":found is not None,"found":found}
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps({k:out[k] for k in ['files_scanned','verified_candidates','found_distinct']},indent=2,sort_keys=True))

if __name__=='__main__': main()
