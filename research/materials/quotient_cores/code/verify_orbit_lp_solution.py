#!/usr/bin/env python3
"""Expand an orbit LP solution to full point variables and rescan WANG512 rows."""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path
SCRIPT=Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path: sys.path.insert(0,str(SCRIPT))
from pivot_fixed_orbit_lp import load_binary_rows, bit_in, full_point_orbits_under_stabilizer  # type: ignore


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lp-json',type=Path,required=True); ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args(); d=json.loads(args.lp_json.read_text())
    pivot=int(d['pivot']); pivot_mult=int(d['pivot_mult']); binary=Path(d['binary']['path'])
    orbit_data=full_point_orbits_under_stabilizer(pivot)
    values=[0.0]*(512)
    sol=d['lp']['solution']
    for var_i,orb_i in enumerate(d['var_orbits']):
        val=float(sol[var_i])
        for p in orbit_data['orbits'][int(orb_i)]: values[int(p)]=val
    values[pivot]=float(pivot_mult)
    t0=time.time(); viol=0; max_excess=0.0; min_slack=1e100; head=[]; rows=0
    for idx,cap,dim,words in load_binary_rows(binary):
        occ=0.0
        for p in range(1,512):
            v=values[p]
            if v and bit_in(words,p): occ+=v
        slack=float(cap)-occ
        if slack<min_slack: min_slack=slack
        if occ>cap+1e-7:
            viol+=1; max_excess=max(max_excess,occ-cap)
            if len(head)<20: head.append({'row_index':idx,'cap':cap,'dim':dim,'occ':occ,'excess':occ-cap})
        rows+=1
    rec={'schema':'verify_orbit_lp_solution_v1','source':str(args.lp_json),'pivot':pivot,'binary':str(binary),'rows':rows,'violation_count':viol,'max_excess':max_excess,'min_slack':min_slack,'violation_head':head,'elapsed_sec':time.time()-t0,'total_mass':sum(values[p] for p in range(1,512))}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(rec,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(args.out),'violations':viol,'min_slack':min_slack,'total_mass':rec['total_mass'],'elapsed_sec':rec['elapsed_sec']},indent=2,sort_keys=True))
if __name__=='__main__': main()
