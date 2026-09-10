#!/usr/bin/env python3
"""Run the BILR rank-23 mod-2 positive control for analysis Z4-cyclic encoder."""
from __future__ import annotations
import json, time
from pathlib import Path
import z4_cyclic_sat_f2 as z4

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'z4_cyclic_f2'
OUT.mkdir(parents=True,exist_ok=True)
pat=[4,4,2,1]
t0=time.time(); enc,_=z4.encode(pat,sym_break=True,require_nonzero=False); enc_sec=time.time()-t0
cnf=OUT/'z4_cyclic_positive_p4_4_2_1.cnf'
enc.write(cnf)
status,assign,sec,stdout,stderr=z4.run_cms(cnf,300)
rec={'pattern':pat,'vars':enc.nv,'regular_clauses':len(enc.reg),'xor_clauses':len(enc.xors),
     'linear_aux_vars':len(enc.lin_cache),'encode_sec':round(enc_sec,3),'status':status,'solve_sec':round(sec,3),'cnf':str(cnf)}
if status=='SAT':
    rec['check']=z4.direct_verify_record(assign,pat,require_nonzero=False)
    rec['true_vars']=[v for v,b in sorted(assign.items()) if b][:2000]
if stdout.strip(): rec['solver_stdout_tail']=stdout[-1000:]
if stderr.strip(): rec['solver_stderr_tail']=stderr[-1000:]
out=OUT/'z4_cyclic_positive_control_p4_4_2_1.json'
out.write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({k:v for k,v in rec.items() if k not in ('true_vars',)},indent=2)[:4000])
print('Saved',out)
