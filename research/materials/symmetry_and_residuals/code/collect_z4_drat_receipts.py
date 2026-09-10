#!/usr/bin/env python3
"""Collect and replay existing DRAT proofs for analysis Z4-cyclic F2 patterns."""
from __future__ import annotations
import hashlib, json, subprocess, time
from pathlib import Path

WS=Path(__file__).resolve().parent.parent
D=WS/'data'/'z4_cyclic_f2_drat'
PATTERNS=[[4,4,2],[4,4,1,1],[4,2,2,2],[4,2,2,1,1],[4,2,1,1,1,1],[4,1,1,1,1,1,1],
          [2,2,2,2,2],[2,2,2,2,1,1],[2,2,2,1,1,1,1],[2,2,1,1,1,1,1,1],[2,1,1,1,1,1,1,1,1],[1,1,1,1,1,1,1,1,1,1]]

def sha256(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for b in iter(lambda:f.read(1<<20), b''):
            h.update(b)
    return h.hexdigest()

def parse_dimacs_header(path):
    with open(path,'r') as f:
        for line in f:
            if line.startswith('p cnf'):
                _,_,nv,nc=line.split()[:4]
                return int(nv),int(nc)
    return None,None

def run_verify(cnf,drat):
    t0=time.time()
    r=subprocess.run(['drat-trim',str(cnf),str(drat)],capture_output=True,text=True,timeout=900)
    dt=time.time()-t0
    out=r.stdout+r.stderr
    status='VERIFIED' if 's VERIFIED' in out or 'VERIFIED' in out else f'RC{r.returncode}'
    # Extract core/lemma line if present
    lines=[ln.strip() for ln in out.splitlines() if 'clauses in core' in ln or 'lemmas in core' in ln or 'resolution steps' in ln or 's VERIFIED' in ln or 'verification time' in ln]
    return status,dt,lines,out[-2000:]

def main():
    records=[]
    for pat in PATTERNS:
        tag='p'+'_'.join(map(str,pat))
        cnf=D/f'z4_cyclic_tseitin_{tag}.cnf'
        drat=D/f'z4_cyclic_tseitin_{tag}.drat'
        print(tag, 'exists', cnf.exists(), drat.exists())
        rec={'pattern':pat,'tag':tag,'cnf':str(cnf),'proof':str(drat),'cnf_exists':cnf.exists(),'proof_exists':drat.exists()}
        if cnf.exists():
            nv,nc=parse_dimacs_header(cnf); rec.update(vars=nv,clauses=nc,cnf_bytes=cnf.stat().st_size,cnf_sha256=sha256(cnf))
        if drat.exists():
            rec.update(proof_bytes=drat.stat().st_size,proof_sha256=sha256(drat))
        if cnf.exists() and drat.exists():
            status,dt,lines,tail=run_verify(cnf,drat)
            rec.update(drat_status=status,drat_verify_sec=round(dt,3),drat_summary_lines=lines,drat_tail=tail)
            print(' ',status,round(dt,2),'s')
        records.append(rec)
        (D/'z4_cyclic_drat_receipts_partial.json').write_text(json.dumps({'records':records},indent=2)+'\n')
    ok=sum(1 for r in records if r.get('drat_status')=='VERIFIED')
    out=D/'z4_cyclic_drat_receipts_all12.json'
    out.write_text(json.dumps({'field':'F2','scope':'fixed BILR a0 conjugation; one size-12 free orbit plus <=10 cube terms in h-orbits of sizes 1,2,4','require_nonzero':False,'patterns':PATTERNS,'verified_count':ok,'records':records},indent=2)+'\n')
    print('Saved',out,'verified',ok,'/',len(records))
if __name__=='__main__': main()
