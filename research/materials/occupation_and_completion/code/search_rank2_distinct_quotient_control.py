#!/usr/bin/env python3
"""Search all GL3xGL3 A-side mappings of the verified rank-23 scheme to pivot 17.

The earlier control script used only the first mapping sending a chosen rank-2 A
factor to the pivot. This searches all mappings and records the minimum duplicate
count of the 22 projected quotient A-factors. It verifies full and quotient tensor
identities for best candidates and, when possible, exact Wang admissibility at n=22.
"""
from __future__ import annotations
import json, os, sys, time
from pathlib import Path
from collections import Counter
import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0, str(SCRIPT_DIR))
S04 = Path("scripts")
if str(S04) not in sys.path: sys.path.insert(0, str(S04))
from extract_known_supports import parse_rank23_txt
from core_capacity_from_wang_lut import load_lut
from wang_capacity_lazy import unpack_basis
from quotient_line_caps_and_controls import (bits_to_mat, mat_to_bits, gf2_rank_mat, gf2_inv, gl3, build_t333, recon_full, quotient_project, quotient_tensor, recon_quotient, wang_check_exact)

SRC = Path("data/flip_cpd_inspect/src/khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt")
LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUT = Path("data/wang_native/three_orbit_controls/rank2_all_mapping_search.json")
PIVOT = 17

def transform_term_Aonly(term, P, Q):
    # same as full stabilizer with R=I, copied for speed from quotient_line_caps...
    A=bits_to_mat(term[0]); B=bits_to_mat(term[1]); C=bits_to_mat(term[2])
    Pinv=gf2_inv(P); Qinv=gf2_inv(Q)
    A2=(P.T @ A @ Qinv.T)&1
    B2=(Q.T @ B)&1
    C2=(Pinv @ C)&1
    return mat_to_bits(A2), mat_to_bits(B2), mat_to_bits(C2)

def main():
    t0=time.time()
    terms=[tuple(map(int,t)) for t in parse_rank23_txt(SRC)]
    assert np.array_equal(recon_full(terms), build_t333())
    G=gl3(); targetM=bits_to_mat(PIVOT)
    rank2_terms=[(i,t[0]) for i,t in enumerate(terms) if gf2_rank_mat(bits_to_mat(t[0]))==2]
    best=[]; best_dup=99; mappings_tested=0; exact_verified=0
    for idx,a in rank2_terms:
        A=bits_to_mat(a)
        # precompute A Q^{-T}
        AQs=[]
        for qi,Q in enumerate(G):
            AQs.append((qi,Q,(A @ gf2_inv(Q).T)&1))
        for pi,P in enumerate(G):
            PT=P.T
            for qi,Q,AQ in AQs:
                if not np.array_equal((PT @ AQ)&1,targetM):
                    continue
                mappings_tested += 1
                trans=[transform_term_Aonly(t,P,Q) for t in terms]
                qlist=[quotient_project(t[0],PIVOT) for t in trans]
                if qlist.count(0)!=1 or qlist[idx]!=0:
                    continue
                qnz=[q for q in qlist if q]
                dup=len(qnz)-len(set(qnz))
                if dup<best_dup:
                    best_dup=dup; best=[]
                if dup==best_dup and len(best)<20:
                    q_terms=[(quotient_project(t[0],PIVOT), t[1], t[2]) for t in trans if quotient_project(t[0],PIVOT)!=0]
                    rec={"term_index":idx,"original_a":int(a),"P_index":pi,"Q_index":qi,"duplicate_count":dup,"distinct_count":len(set(qnz)),"q_multiset":[int(x) for x in qnz],"quotient_terms_full":[[int(q),int(b),int(c)] for q,b,c in q_terms],"duplicate_values":{str(k):v for k,v in Counter(qnz).items() if v>1}}
                    best.append(rec)
                    print(f"new/best dup={dup} term={idx} P={pi} Q={qi}")
                    if dup==0:
                        break
            if best_dup==0: break
        if best_dup==0: break
    # Verify identities and Wang for stored best records.
    lut,_=load_lut(LUT_PATH)
    verified=[]
    for rec in best:
        P=G[rec['P_index']]; Q=G[rec['Q_index']]
        trans=[transform_term_Aonly(t,P,Q) for t in terms]
        full_ok=bool(np.array_equal(recon_full(trans), build_t333()))
        q_ok=bool(np.array_equal(recon_quotient(trans,PIVOT), quotient_tensor(PIVOT)))
        wang=wang_check_exact(lut,PIVOT,rec['q_multiset'],target=22)
        r2=dict(rec); r2.update({"full_tensor_still_verified":full_ok,"quotient_reconstruction_verified":q_ok,"wang_n22":wang})
        verified.append(r2)
        if full_ok and q_ok and wang['passed']: exact_verified+=1
    out={"status":"ok","source":str(SRC),"pivot":PIVOT,"rank2_terms":rank2_terms,"mappings_tested":mappings_tested,"best_duplicate_count":best_dup,"best_records":verified,"exact_verified_best_records":exact_verified,"elapsed_sec":time.time()-t0}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":"ok","mappings_tested":mappings_tested,"best_duplicate_count":best_dup,"best_records":len(verified),"exact_verified_best_records":exact_verified,"out":str(OUT)},indent=2,sort_keys=True))

if __name__=='__main__': main()
