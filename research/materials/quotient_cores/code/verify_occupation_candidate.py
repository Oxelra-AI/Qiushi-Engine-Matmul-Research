#!/usr/bin/env python3
"""Stream-check a candidate F2 first-factor point set against Wang restrictions.

This does not build the full subspace table.  It closes each certificate orbit
representative under GL3 x GL3 x transpose x GL3, checks whether the candidate
point set violates |P∩S| <= r-L(S), and records the first/minimal violations.
"""
from __future__ import annotations
import argparse, json, ast, re, time
from pathlib import Path
from wang_occupation_search import rref_key, gl3, mat_mul, act


def parse_cert_all_reps(cert:Path):
    text=cert.read_text(errors='replace')
    reps=[]
    for block in text.split('constrained_tensors {')[1:]:
        block=block.split('\n}\n',1)[0]
        mi=re.search(r'\n\s*index:\s*(\d+)', '\n'+block)
        ml=re.search(r'\n\s*rank_lower_bound:\s*(-?\d+)', '\n'+block)
        mc=re.search(r'\n\s*constraints:\s*(".*")', '\n'+block)
        idx=int(mi.group(1)) if mi else -1
        lb=int(ml.group(1)) if ml else -1
        vals=[]
        if mc:
            b=ast.literal_eval(mc.group(1)).encode('latin1')
            vals=[b[i] | (b[i+1]<<8) for i in range(0,len(b),2)]
        reps.append((tuple(vals),lb,idx))
    return reps


def in_span(x:int, key:tuple[int,...]) -> bool:
    y=x
    for row in key:
        hb=row.bit_length()-1
        if (y>>hb)&1:
            y ^= row
    return y==0


def count_intersection(points, key):
    return sum(1 for p in points if in_span(p,key))


def load_points(path:Path):
    data=json.loads(path.read_text())
    return data.get('escape_points') or data.get('points') or data


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('points_json', type=Path)
    ap.add_argument('--cert', type=Path, default=Path('data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--max-dim', type=int, default=9)
    ap.add_argument('--max-violations', type=int, default=50)
    ap.add_argument('--json-out', type=Path)
    args=ap.parse_args()
    points=load_points(args.points_json)
    points=[int(x) for x in points]
    GL=gl3(); actions=[(g,h,t) for g in GL for h in GL for t in (0,1)]
    reps=[r for r in parse_cert_all_reps(args.cert) if len(r[0])<=args.max_dim]
    seen=set(); violations=[]; tight_by_dim={}; checked_unique=0; worst_margin=999; worst=[]
    t0=time.time()
    for vals,lb,idx in reps:
        d0=len(rref_key(vals))
        for g,h,t in actions:
            key=rref_key([act(g,h,x,t) for x in vals])
            if key in seen: continue
            seen.add(key); checked_unique+=1
            d=len(key); cap=args.rank-lb
            cnt=count_intersection(points,key)
            margin=cap-cnt
            if margin<0 and len(violations)<args.max_violations:
                violations.append({'rep_index':idx,'dim':d,'lb':lb,'cap':cap,'count':cnt,'margin':margin,'key':list(key)})
            if margin==0:
                tight_by_dim[str(d)]=tight_by_dim.get(str(d),0)+1
            if margin<worst_margin:
                worst_margin=margin; worst=[{'rep_index':idx,'dim':d,'lb':lb,'cap':cap,'count':cnt,'margin':margin,'key':list(key)}]
            elif margin==worst_margin and len(worst)<10:
                worst.append({'rep_index':idx,'dim':d,'lb':lb,'cap':cap,'count':cnt,'margin':margin,'key':list(key)})
    out={'points_json':str(args.points_json),'rank':args.rank,'point_count':len(points),'max_dim':args.max_dim,'rep_count':len(reps),'unique_subspaces_checked':checked_unique,'violation_count_recorded':len(violations),'has_violation':bool(violations),'first_violations':violations,'tight_by_dim':tight_by_dim,'worst_margin':worst_margin,'worst_examples':worst,'elapsed_sec':time.time()-t0}
    txt=json.dumps(out,indent=2,sort_keys=True)
    print(txt)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True,exist_ok=True); args.json_out.write_text(txt+'\n')

if __name__=='__main__': main()
