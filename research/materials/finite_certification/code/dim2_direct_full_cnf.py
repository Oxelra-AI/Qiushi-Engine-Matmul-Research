#!/usr/bin/env python3
"""Direct full occurrence-slot CNF for one original-LUT dim-2 raise.

This bypasses CEGAR core extraction: encode all reconstructed quotient
occupation rows for a selected dim-2 orbit into SAT.  Variables y_{slot,point}
choose one quotient point in each of L slots.  This is larger but proof-producing
with CaDiCaL/DRAT if tractable.
"""
from __future__ import annotations
import argparse, hashlib, json, subprocess, sys, time
from pathlib import Path
from pysat.card import CardEnc, EncType  # type: ignore
from pysat.formula import CNF  # type: ignore
SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
import dim2_replay_compat_graph as dg  # type: ignore
OUTDIR=Path('data/dim2_full_cnf')

def sha(path:Path):
 h=hashlib.sha256();
 with path.open('rb') as f:
  for ch in iter(lambda:f.read(1<<20),b''): h.update(ch)
 return h.hexdigest()

def vid(s:int,p:int,npts:int)->int: return s*npts+p+1

def encode(rows,k,L,path):
 npts=(1<<k)-1; cnf=CNF(); top=L*npts; stats={'slot_exactly_one_clauses':0,'row_constraints_encoded':0,'row_constraints_skipped':0,'row_empty_conflicts':0}
 for s in range(L):
  lits=[vid(s,p,npts) for p in range(npts)]
  cnf.append(lits); stats['slot_exactly_one_clauses'] += 1
  enc=CardEnc.atmost(lits=lits,bound=1,top_id=top,encoding=EncType.seqcounter)
  cnf.extend(enc.clauses); stats['slot_exactly_one_clauses'] += len(enc.clauses); top=enc.nv
 for mask,cap in rows:
  pop=mask.bit_count(); lits=[]
  if cap >= L or pop == 0:
   stats['row_constraints_skipped'] += 1; continue
  for s in range(L):
   base=s*npts+1
   for p in range(npts):
    if (mask>>p)&1: lits.append(base+p)
  if cap < 0:
   cnf.append([]); stats['row_empty_conflicts'] += 1
  elif cap == 0:
   for lit in lits: cnf.append([-lit])
   stats['row_constraints_encoded'] += 1
  elif cap < len(lits):
   enc=CardEnc.atmost(lits=lits,bound=int(cap),top_id=top,encoding=EncType.seqcounter)
   cnf.extend(enc.clauses); top=enc.nv; stats['row_constraints_encoded'] += 1
  else:
   stats['row_constraints_skipped'] += 1
 cnf.to_file(str(path)); stats.update({'vars':cnf.nv,'clauses':len(cnf.clauses),'npts':npts,'slots':L}); return stats

def run(args,timeout):
 t=time.time(); p=subprocess.run(args,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=timeout); return {'args':args,'returncode':p.returncode,'stdout_tail':p.stdout[-6000:],'stderr_tail':p.stderr[-6000:],'elapsed_sec':time.time()-t}

def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--index',type=int,default=479); ap.add_argument('--outdir',type=Path,default=OUTDIR); ap.add_argument('--solve',action='store_true'); ap.add_argument('--cadical-timeout',type=int,default=900); ap.add_argument('--drat-timeout',type=int,default=900); args=ap.parse_args(); args.outdir.mkdir(parents=True,exist_ok=True)
 lut,cache=dg.load_lut_cache(); raw=dg.orbit_lbs_from_cache(cache,{})
 prof=json.loads(dg.PROFILE.read_text()); rec=[r for r in prof['dimension_2_orbits'] if int(r['index'])==args.index][0]
 W=[int(x) for x in rec['constraint_values']]; L=int(rec['rank_lower_bound']); k=9-len(dg.rref_basis(W,9)); rows,meta=dg.node_rows(W,lut,cache,raw,L)
 cnf_path=args.outdir/f'orbit{args.index}_full.cnf'; drat_path=args.outdir/f'orbit{args.index}_full.drat'; log_path=args.outdir/f'orbit{args.index}_full_log.json'
 t0=time.time(); encmeta=encode(rows,k,L,cnf_path); encmeta['elapsed_sec']=time.time()-t0; encmeta['cnf_path']=str(cnf_path); encmeta['cnf_sha256']=sha(cnf_path); encmeta['row_count']=len(rows); encmeta['row_meta']=meta; encmeta['index']=args.index; encmeta['basis']=W; encmeta['old_lb']=L; encmeta['quotient_dim']=k
 cad=dr=None
 if args.solve:
  cad=run(['cadical',str(cnf_path),str(drat_path)],args.cadical_timeout); encmeta['cadical_returncode']=cad['returncode']; encmeta['drat_path']=str(drat_path); encmeta['drat_sha256']=sha(drat_path) if drat_path.exists() else None
  if cad['returncode']==20 and drat_path.exists():
   dr=run(['drat-trim',str(cnf_path),str(drat_path)],args.drat_timeout); encmeta['drat_returncode']=dr['returncode']; encmeta['drat_verified']='s VERIFIED' in dr['stdout_tail']
 log_path.write_text(json.dumps({'meta':encmeta,'cadical':cad,'drat_trim':dr},indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':'ok','log':str(log_path),'meta':{k:v for k,v in encmeta.items() if k not in ['row_meta']},'cadical':None if cad is None else cad['returncode'],'drat':None if dr is None else dr['returncode'],'verified':encmeta.get('drat_verified')},indent=2,sort_keys=True))
if __name__=='__main__': main()
