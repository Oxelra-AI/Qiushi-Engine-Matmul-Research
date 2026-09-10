#!/usr/bin/env python3
"""Project a verified full rank-23 T333 scheme to quotient tensors for all pivots."""
from __future__ import annotations
import json, os, sys, time
from pathlib import Path
from collections import Counter
import numpy as np

SCRIPT_DIR=Path(os.path.dirname(os.path.abspath(__file__)))
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
S04=Path("scripts")
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from extract_known_supports import parse_rank23_txt
from core_capacity_from_wang_lut import load_lut
from quotient_line_caps_and_controls import build_t333, recon_full, quotient_project, quotient_tensor, vec, wang_check_exact

SRC=Path("data/flip_cpd_inspect/src/khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt")
LUT_PATH=Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR=Path("data/wang_native/three_orbit_controls")
PIVOTS={"rank1":1,"rank2":17,"rank3":273}

def recon_q_terms(qterms):
    R=np.zeros((8,9,9),dtype=np.uint8)
    for q,b,c in qterms:
        R ^= (vec(q,8).reshape(8,1,1)*vec(b,9).reshape(1,9,1)*vec(c,9).reshape(1,1,9)).astype(np.uint8)
    return R

def main():
    OUTDIR.mkdir(parents=True,exist_ok=True)
    terms=[tuple(map(int,t)) for t in parse_rank23_txt(SRC)]
    assert int(np.count_nonzero(recon_full(terms)!=build_t333()))==0
    lut,_=load_lut(LUT_PATH)
    records={}
    for name,p in PIVOTS.items():
        qterms=[]; zero=[]
        for i,(a,b,c) in enumerate(terms):
            q=quotient_project(a,p)
            if q==0: zero.append(i)
            else: qterms.append((int(q),int(b),int(c)))
        diff=int(np.count_nonzero(recon_q_terms(qterms)!=quotient_tensor(p)))
        qlist=[q for q,_,_ in qterms]
        wang=wang_check_exact(lut,p,qlist,target=len(qterms))
        rec={"pivot_name":name,"pivot":p,"source":str(SRC),"source_rank":len(terms),"zero_projected_term_indices":zero,"quotient_rank_terms":len(qterms),"quotient_terms_full":[[int(q),int(b),int(c)] for q,b,c in qterms],"quotient_a_multiset":[int(q) for q in qlist],"quotient_a_distinct_count":len(set(qlist)),"quotient_a_duplicate_count":len(qlist)-len(set(qlist)),"duplicate_values":{str(k):v for k,v in Counter(qlist).items() if v>1},"quotient_reconstruction_diff":diff,"quotient_reconstruction_verified":diff==0,"wang_at_own_length":wang}
        records[name]=rec
        (OUTDIR/f"{name}_projected_rank23_control.json").write_text(json.dumps(rec,indent=2,sort_keys=True)+"\n")
    summary={"status":"ok","controls":records}
    sp=OUTDIR/"projected_rank23_quotient_controls_summary.json"
    sp.write_text(json.dumps(summary,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":"ok","out":str(sp),"summary":{k:{"terms":v['quotient_rank_terms'],"dup":v['quotient_a_duplicate_count'],"diff":v['quotient_reconstruction_diff'],"wang_pass":v['wang_at_own_length']['passed']} for k,v in records.items()}},indent=2,sort_keys=True))
if __name__=='__main__': main()
