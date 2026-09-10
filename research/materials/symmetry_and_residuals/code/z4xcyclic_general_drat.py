#!/usr/bin/env python3
"""Pure-CNF/Kissat/DRAT runner for the broader fixed-a0 H=<tau> F2 equivariant family."""
from __future__ import annotations
import argparse, json, subprocess, time
from pathlib import Path
import z4xcyclic_general_f2 as gen
import z4_cyclic_sat_f2_drat as dratutil

SCRIPT_DIR=Path(__file__).resolve().parent
WS=SCRIPT_DIR.parent
OUT=WS/'data'/'z4xcyclic_general_f2_drat'

def run_kissat(cnf,proof,timeout):
    t0=time.time()
    try:
        r=subprocess.run(['kissat',str(cnf),str(proof)],capture_output=True,text=True,timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT',time.time()-t0,'',''
    if r.returncode==20: return 'UNSAT',time.time()-t0,r.stdout,r.stderr
    if r.returncode==10: return 'SAT',time.time()-t0,r.stdout,r.stderr
    return f'RC{r.returncode}',time.time()-t0,r.stdout,r.stderr

def verify(cnf,proof,timeout):
    if not proof.exists(): return 'NO_PROOF',0.0,''
    t0=time.time()
    try:
        r=subprocess.run(['drat-trim',str(cnf),str(proof)],capture_output=True,text=True,timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT',time.time()-t0,''
    out=r.stdout+r.stderr
    status='VERIFIED' if 'VERIFIED' in out else f'RC{r.returncode}'
    lines=[ln.strip() for ln in out.splitlines() if 'clauses in core' in ln or 'lemmas in core' in ln or 'resolution steps' in ln or 's VERIFIED' in ln or 'verification time' in ln]
    return status,time.time()-t0,'\n'.join(lines)+('\n'+out[-1000:] if status!='VERIFIED' else '')

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--patterns',default='12,6,4')
    ap.add_argument('--timeout',type=int,default=600)
    ap.add_argument('--verify-timeout',type=int,default=900)
    args=ap.parse_args()
    OUT.mkdir(parents=True,exist_ok=True)
    pats=gen.parse_patterns(args.patterns)
    _,_,_,dims=gen.build_group_data()
    records=[]
    print('general H DRAT patterns',pats,'fixed dims',dims)
    for pat in pats:
        tag='p'+'_'.join(map(str,pat))
        print('\n',tag,pat)
        t0=time.time(); enc,_=gen.encode(pat,sym_break=True); enc_sec=time.time()-t0
        cnf=OUT/f'z4xcyc_general_tseitin_{tag}.cnf'; proof=OUT/f'z4xcyc_general_tseitin_{tag}.drat'
        nv,nc=dratutil.write_pure_cnf(enc,cnf)
        print('  cnf',nv,nc,'native',enc.nv,'reg',len(enc.reg),'xor',len(enc.xors),'lin',len(enc.lin_cache),'enc',round(enc_sec,3))
        status,sec,stdout,stderr=run_kissat(cnf,proof,args.timeout)
        print(' ',status,round(sec,2),'s')
        rec={'pattern':pat,'tag':tag,'vars':nv,'clauses':nc,'native_vars':enc.nv,'regular_clauses':len(enc.reg),
             'xor_equations':len(enc.xors),'linear_aux_vars':len(enc.lin_cache),'encode_sec':round(enc_sec,3),
             'status':status,'solve_sec':round(sec,3),'cnf':str(cnf),'proof':str(proof)}
        if status=='UNSAT':
            vst,vt,vout=verify(cnf,proof,args.verify_timeout)
            rec.update(drat_status=vst,drat_verify_sec=round(vt,3),proof_bytes=proof.stat().st_size if proof.exists() else 0,drat_summary=vout)
            print('  drat',vst,round(vt,2),'s')
        if stdout.strip(): rec['solver_stdout_tail']=stdout[-2000:]
        if stderr.strip(): rec['solver_stderr_tail']=stderr[-2000:]
        records.append(rec)
        (OUT/'z4xcyclic_general_drat_partial.json').write_text(json.dumps({'fixed_dims':dims,'records':records},indent=2)+'\n')
    out=OUT/'z4xcyclic_general_drat_results.json'
    out.write_text(json.dumps({'field':'F2','fixed_dims':dims,'records':records},indent=2)+'\n')
    print('Saved',out)
if __name__=='__main__': main()
