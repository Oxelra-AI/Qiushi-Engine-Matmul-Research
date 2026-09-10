#!/usr/bin/env python3
"""Save a separate BILR rank-23 positive control for the broader fixed-H encoder."""
from __future__ import annotations
import json, time
from pathlib import Path
import z4xcyclic_general_f2 as gen

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'z4xcyclic_general_f2'
OUT.mkdir(parents=True,exist_ok=True)
pat=[12,4,4,2,1]
t0=time.time(); enc,_=gen.encode(pat,sym_break=True); enc_sec=time.time()-t0
cnf=OUT/'z4xcyc_general_positive_p12_4_4_2_1.cnf'
enc.write(cnf)
status,assign,sec,stdout,stderr=gen.run_cms(cnf,300)
rec={'pattern':pat,'vars':enc.nv,'regular_clauses':len(enc.reg),'xor_clauses':len(enc.xors),
     'linear_aux_vars':len(enc.lin_cache),'encode_sec':round(enc_sec,3),'status':status,'solve_sec':round(sec,3),'cnf':str(cnf)}
if status=='SAT':
    chk=gen.direct_verify(assign,pat)
    # Keep only compact terms in this separate positive-control record.
    chk_small={k:v for k,v in chk.items() if k!='terms'}
    rec['check']=chk_small
    rec['true_vars']=[v for v,b in sorted(assign.items()) if b][:2000]
if stdout.strip(): rec['solver_stdout_tail']=stdout[-1000:]
if stderr.strip(): rec['solver_stderr_tail']=stderr[-1000:]
out=OUT/'z4xcyclic_positive_control_p12_4_4_2_1.json'
out.write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({k:v for k,v in rec.items() if k!='true_vars'},indent=2)[:4000])
print('Saved',out)
