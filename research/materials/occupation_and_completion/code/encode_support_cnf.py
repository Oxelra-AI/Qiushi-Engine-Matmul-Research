#!/usr/bin/env python3
"""analysis: encode a quotient Wang support branch as DIMACS CNF.

Variables x_p (1 <= p <= 255) mean quotient point p is selected.  The CNF
contains the corrected branch force/forbid units, exactly target selected points,
and every Wang row in an E11WANG1 binary as an at-most-cardinality constraint.
This is a proof-facing alternative backend for selected row sets; it deliberately
operates on focused binaries rather than indiscriminately translating every
available consequence.
"""
from __future__ import annotations
import argparse, hashlib, json, struct, time
from collections import Counter
from pathlib import Path
from pysat.card import CardEnc, EncType

MAGIC=b'E11WANG1'; REC='<BBHQQQQ'; SZ=struct.calcsize(REC)
ROOT=Path('research/research_record')
SPECS=ROOT/'workspace/data/quotient_branches/corrected_branch_specs.json'
OUTDIR=ROOT/'workspace/data/quotient_lift/sat'
OUTDIR.mkdir(parents=True,exist_ok=True)

def sha(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): h.update(c)
    return h.hexdigest()

def load_rows(path:Path):
    d=path.read_bytes(); assert d[:8]==MAGIC, (path,d[:8])
    n=struct.unpack('<I',d[8:12])[0]; assert len(d)==12+n*SZ, (len(d),12+n*SZ)
    rows=[]; off=12
    for idx in range(n):
        cap,dim,pad,w0,w1,w2,w3=struct.unpack_from(REC,d,off); off+=SZ
        mask=int(w0)|(int(w1)<<64)|(int(w2)<<128)|(int(w3)<<192)
        pts=[p for p in range(1,256) if (mask>>p)&1]
        rows.append({'idx':idx,'cap':int(cap),'dim':int(dim),'points':pts})
    return rows

def get_branch(pivot:str, branch:int):
    specs=json.loads(SPECS.read_text())['pivots'][pivot]['branches']
    return next(b for b in specs if int(b['branch'])==branch)

def parse_list(s:str): return [int(x) for x in s.split(',') if x.strip()]

def write_dimacs(path:Path,nv:int,clauses:list[list[int]], comments:list[str]):
    with path.open('w') as f:
        for c in comments: f.write('c '+c+'\n')
        f.write(f'p cnf {nv} {len(clauses)}\n')
        for cl in clauses:
            f.write(' '.join(map(str,cl))+' 0\n')

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--rows',type=Path,required=True)
    ap.add_argument('--pivot',choices=['rank2','rank3'],required=True)
    ap.add_argument('--branch',type=int,required=True)
    ap.add_argument('--target',type=int,default=19)
    ap.add_argument('--label',default='')
    ap.add_argument('--encoding',choices=['seqcounter','totalizer'],default='seqcounter')
    args=ap.parse_args(); t0=time.time()
    br=get_branch(args.pivot,args.branch)
    force=set(map(int,br['force'])); forbid=set(map(int,br['forbid']))
    rows=load_rows(args.rows)
    clauses=[]; top=255
    for p in sorted(force): clauses.append([p])
    for p in sorted(forbid): clauses.append([-p])
    enc = EncType.seqcounter if args.encoding=='seqcounter' else EncType.totalizer
    eq=CardEnc.equals(lits=list(range(1,256)), bound=args.target, top_id=top, encoding=enc)
    clauses.extend(eq.clauses); top=max(top,eq.nv)
    row_clause_count=0; skipped=Counter(); cap_hist=Counter(); dim_hist=Counter(); aux_before_rows=top
    for r in rows:
        pts=r['points']; cap=int(r['cap'])
        if cap < 0:
            clauses.append([]); row_clause_count += 1; continue
        if cap >= len(pts):
            skipped['tautological'] += 1; continue
        if cap < 0 or cap >= args.target:
            skipped['bad_or_irrelevant'] += 1; continue
        cn=CardEnc.atmost(lits=pts, bound=cap, top_id=top, encoding=enc)
        clauses.extend(cn.clauses); row_clause_count += len(cn.clauses); top=max(top,cn.nv)
        cap_hist[cap]+=1; dim_hist[r['dim']]+=1
    label=args.label or f'{args.pivot}_branch{args.branch}_{args.rows.stem}'
    cnf=OUTDIR/f'{label}.cnf'
    comments=[f'schema=s0908_support_cnf_v1',f'pivot={args.pivot}',f'branch={args.branch}',f'target={args.target}',f'rows={args.rows}',f'rows_sha256={sha(args.rows)}',f'force={sorted(force)}',f'forbid={sorted(forbid)}',f'encoding={args.encoding}']
    write_dimacs(cnf,top,clauses,comments)
    meta={'schema':'s0908_support_cnf_v1','pivot':args.pivot,'branch':args.branch,'target':args.target,'rows':str(args.rows),'rows_sha256':sha(args.rows),'row_count':len(rows),'force':sorted(force),'forbid':sorted(forbid),'encoding':args.encoding,'variables':top,'base_variables':255,'aux_variables':top-255,'aux_variables_after_exactly':aux_before_rows-255,'clauses':len(clauses),'row_cardinality_clauses':row_clause_count,'cap_hist_encoded':{str(k):int(v) for k,v in sorted(cap_hist.items())},'dim_hist_encoded':{str(k):int(v) for k,v in sorted(dim_hist.items())},'skipped':dict(skipped),'cnf':str(cnf),'cnf_sha256':sha(cnf),'elapsed_sec':time.time()-t0}
    mp=OUTDIR/f'{label}.manifest.json'; mp.write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps(meta,indent=2,sort_keys=True))
if __name__=='__main__': main()
