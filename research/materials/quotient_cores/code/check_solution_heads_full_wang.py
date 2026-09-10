#!/usr/bin/env python3
"""Check solution_head supports from native DFS against complete full Wang LUT."""
from __future__ import annotations
import argparse, json, sys
from collections import Counter
from pathlib import Path

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")

def points_from_basis(basis):
    pts=[]
    d=len(basis)
    for m in range(1,1<<d):
        v=0
        for i,b in enumerate(basis):
            if (m>>i)&1: v ^= int(b)
        pts.append(v)
    return pts

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, required=True)
    ap.add_argument("--length", type=int, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args=ap.parse_args()
    data=json.loads(args.input.read_text())
    sols=data.get("solutions_head", [])
    lut,_=load_lut(LUT)
    row_info=[]
    point_to_rows=[[] for _ in range(512)]
    for idx,(key9,lb0) in enumerate(lut.items()):
        key9=int(key9); lb=int(lb0); cap=args.length-lb
        basis=list(unpack_basis(key9)); pts=points_from_basis(basis)
        row_info.append((key9,lb,cap,len(basis),pts))
        for p in pts:
            if 1 <= p <= 511: point_to_rows[p].append(idx)
    results=[]
    for si,sol in enumerate(sols):
        counts=[0]*len(row_info)
        for p in sol:
            for ri in point_to_rows[int(p)]: counts[ri]+=1
        bad=[]
        for ri,c in enumerate(counts):
            key9,lb,cap,dim,pts=row_info[ri]
            if c>cap:
                bad.append((ri,key9,lb,cap,dim,c))
        bh=[]
        for rec in bad[:10]:
            ri,key9,lb,cap,dim,c=rec
            bh.append({"row_index":ri,"key9":key9,"lb":lb,"cap":cap,"dim":dim,"occ":c})
        results.append({"solution_index":si,"support":sol,"violations":len(bad),"first_violation_dim":(bad[0][4] if bad else None),"first_violation_lb":(bad[0][2] if bad else None),"violation_head":bh})
    out={
        "input":str(args.input),"length":args.length,"solutions_checked":len(sols),
        "accepted_count":sum(1 for r in results if r["violations"]==0),
        "violation_count_hist":dict(sorted(Counter(r["violations"] for r in results).items())),
        "first_violation_dim_hist":dict(sorted(Counter(r["first_violation_dim"] for r in results if r["first_violation_dim"] is not None).items())),
        "results_head":results[:20],
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__': main()
