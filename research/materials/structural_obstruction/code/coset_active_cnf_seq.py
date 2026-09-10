#!/usr/bin/env python3
"""Compact sequential-counter CNF for a surviving-coset active row system.

This replaces the first pairwise/subset CNF exporter.  It encodes exactly the
active finite 0/1 system reconstructed from a CEGAR run:
  choose 16 allowed rank-one A-directions, per-left/right caps <=5, and the
  active Wang inequalities.  CaDiCaL can emit a DRAT proof for UNSAT.
"""
from __future__ import annotations
import argparse, json, subprocess, sys, time
from pathlib import Path
from typing import Dict, List, Sequence
SCRIPT=Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path: sys.path.insert(0,str(SCRIPT))
from coset_active_constraint_audit import reconstruct_active_rows  # type: ignore
from surviving_coset_ansatz import load_lut, analyze_H, canonical_coset_points, rank_one_uv_map  # type: ignore

class CNF:
    def __init__(self): self.nv=0; self.clauses:List[List[int]]=[]
    def new_var(self): self.nv+=1; return self.nv
    def add_clause(self, cl:Sequence[int]): self.clauses.append([int(x) for x in cl])
    def add_at_most(self, lits:Sequence[int], k:int):
        lits=list(lits); n=len(lits)
        if k<0: self.add_clause([]); return
        if k>=n: return
        if k==0:
            for x in lits: self.add_clause([-x])
            return
        # Sinz sequential counter. s[i][j] for prefix 0..i has >=j+1 true, i=0..n-2.
        s=[[self.new_var() for _ in range(k)] for __ in range(n-1)]
        self.add_clause([-lits[0], s[0][0]])
        for j in range(1,k): self.add_clause([-s[0][j]])
        for i in range(1,n-1):
            self.add_clause([-lits[i], s[i][0]])
            self.add_clause([-s[i-1][0], s[i][0]])
            for j in range(1,k):
                self.add_clause([-lits[i], -s[i-1][j-1], s[i][j]])
                self.add_clause([-s[i-1][j], s[i][j]])
            self.add_clause([-lits[i], -s[i-1][k-1]])
        self.add_clause([-lits[n-1], -s[n-2][k-1]])
    def add_exactly(self,lits:Sequence[int],k:int):
        lits=list(lits)
        self.add_at_most(lits,k)
        self.add_at_most([-x for x in lits], len(lits)-k)
    def write(self,path:Path,comments:Sequence[str]=()):
        path.parent.mkdir(parents=True,exist_ok=True)
        with path.open('w') as f:
            for c in comments: f.write('c '+str(c).replace('\n',' ')+'\n')
            f.write(f'p cnf {self.nv} {len(self.clauses)}\n')
            for cl in self.clauses: f.write(' '.join(map(str,cl))+' 0\n')

def build(cegar_path:Path,binary:Path,lut_path:Path,out_cnf:Path)->Dict:
    cegar=json.loads(cegar_path.read_text())
    lut=load_lut(lut_path)
    hrec=analyze_H(lut, cegar['H'], canonical_coset_points()[0])
    allowed=[int(x) for x in hrec['allowed_rank_one']]
    active, meta = reconstruct_active_rows(cegar, allowed, binary)
    F=CNF(); var={x:F.new_var() for x in allowed}
    F.add_exactly([var[x] for x in allowed],16)
    exactly_clauses=len(F.clauses); exactly_aux=F.nv-len(allowed)
    uv=rank_one_uv_map(); cap_constraints=0
    for side in ['left','right']:
        for val in range(1,8):
            pts=[x for x in allowed if (uv[x][0] if side=='left' else uv[x][1])==val]
            if pts:
                F.add_at_most([var[x] for x in pts],5); cap_constraints+=1
    cap_clauses=len(F.clauses)-exactly_clauses; cap_aux=F.nv-len(allowed)-exactly_aux
    active_constraints=0; active_taut=0; active_impossible=0
    support_hist={}
    for r in active:
        rhs=int(r['rhs']); pts=[allowed[j] for j in r['vars']]
        support_hist[len(pts)]=support_hist.get(len(pts),0)+1
        if rhs<0:
            F.add_clause([]); active_impossible+=1; active_constraints+=1
        elif rhs>=len(pts):
            active_taut+=1
        else:
            F.add_at_most([var[x] for x in pts],rhs); active_constraints+=1
    active_clauses=len(F.clauses)-exactly_clauses-cap_clauses
    active_aux=F.nv-len(allowed)-exactly_aux-cap_aux
    F.write(out_cnf, comments=[
        'surviving coset active-row sequential-counter CNF',
        'cegar='+str(cegar_path),
        'H='+','.join(map(str,cegar['H'])),
        'allowed_order='+','.join(map(str,allowed)),
    ])
    return {'schema':'coset_active_cnf_seq_v1','cegar_path':str(cegar_path),'H':[int(x) for x in cegar['H']],'allowed':allowed,'allowed_count':len(allowed),'active_reconstruction':meta,'active_constraints_encoded':active_constraints,'active_taut':active_taut,'active_impossible':active_impossible,'support_hist':dict(sorted(support_hist.items())),'cnf_path':str(out_cnf),'cnf_vars':F.nv,'cnf_clauses':len(F.clauses),'base_vars':len(allowed),'exactly_clauses':exactly_clauses,'exactly_aux':exactly_aux,'cap_constraints':cap_constraints,'cap_clauses':cap_clauses,'cap_aux':cap_aux,'active_clauses':active_clauses,'active_aux':active_aux}

def run(cmd:List[str], timeout:int)->Dict:
    t=time.time(); p=subprocess.run(cmd,capture_output=True,text=True,timeout=timeout+20)
    return {'command':cmd,'returncode':int(p.returncode),'elapsed_sec':time.time()-t,'stdout_tail':'\n'.join(p.stdout.splitlines()[-80:]),'stderr_tail':'\n'.join(p.stderr.splitlines()[-80:])}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--cegar',type=Path,required=True)
    ap.add_argument('--outdir',type=Path,required=True)
    ap.add_argument('--binary',type=Path,default=Path('data/wang_native/full_tensor/full_wang512_cap19_len20_all_dim9_allbinding.bin'))
    ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--timeout',type=int,default=300)
    ap.add_argument('--proof',action='store_true')
    ap.add_argument('--check-proof',action='store_true')
    args=ap.parse_args(); args.outdir.mkdir(parents=True,exist_ok=True)
    cnf=args.outdir/'active_seq.cnf'; info=build(args.cegar,args.binary,args.lut,cnf)
    drat=args.outdir/'active_seq.drat'
    cmd=['cadical','-n','-t',str(args.timeout),str(cnf)]
    if args.proof: cmd.append(str(drat))
    sol=run(cmd,args.timeout); sol['sat']=False if sol['returncode']==20 else True if sol['returncode']==10 else None
    sol['proof_path']=str(drat) if args.proof else None; sol['proof_size']=drat.stat().st_size if args.proof and drat.exists() else None
    chk=None
    if args.check_proof and sol['sat'] is False and args.proof:
        chk=run(['drat-trim',str(cnf),str(drat)],40000)
    out={'encoding':info,'solver':sol,'proof_check':chk}
    outp=args.outdir/'active_seq_result.json'; outp.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(outp),'sat':sol['sat'],'returncode':sol['returncode'],'vars':info['cnf_vars'],'clauses':info['cnf_clauses'],'proof_size':sol['proof_size'],'proof_check_returncode':None if chk is None else chk['returncode'],'elapsed_sec':sol['elapsed_sec']},indent=2,sort_keys=True))
if __name__=='__main__': main()
