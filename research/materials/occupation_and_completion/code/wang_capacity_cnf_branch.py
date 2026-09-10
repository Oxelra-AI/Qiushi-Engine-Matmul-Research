#!/usr/bin/env python3
"""Generate proof-checkable CNF for selected Wang capacity branches.

The CP-SAT branch infeasibilities from analysis are scientifically useful but not
proof objects.  This script emits a DIMACS CNF for a branch of the T-level
rank-s occupation problem using selected Wang subspace dimensions, after
restricting the point variables to the branch.  Small subspace cardinalities are
encoded by direct forbidden-subset clauses; the global exactly-s condition uses
PySAT cardinality encoding.

Branch semantics for s=20:
  branch 1: at least one rank-1 point; by symmetry fix E11.
  branch 2: no rank-1 points and at least one rank-2 point; fix E11+E22.
  branch 3: only rank-3 points; fix identity.
"""
from __future__ import annotations
import argparse, itertools, json, pickle, sys, time
from collections import Counter
from pathlib import Path

SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))
from wang_capacity_lazy import unpack_basis, subspace_points_from_basis, matrix_rank_of_mask

CANON_BY_RANK={1:1,2:1|16,3:1|16|256}


def load_lut(path):
    with open(path,'rb') as f: payload=pickle.load(f)
    return payload['lut'], payload.get('meta',{})


def parse_dims(s):
    out=[]
    for part in s.split(','):
        part=part.strip()
        if not part: continue
        if '-' in part:
            a,b=map(int,part.split('-',1)); out.extend(range(a,b+1))
        else: out.append(int(part))
    return sorted(set(out))


def allowed_points(branch_rank:int):
    pts=[]
    for p in range(1,512):
        r=matrix_rank_of_mask(p)
        if branch_rank==0: pts.append(p)
        elif branch_rank==1: pts.append(p)  # fixed rank1 only; other ranks allowed
        elif branch_rank==2:
            if r>=2: pts.append(p)
        elif branch_rank==3:
            if r==3: pts.append(p)
    return pts


def write_dimacs(path, clauses, nv):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('w') as f:
        f.write(f'p cnf {nv} {len(clauses)}\n')
        for cl in clauses:
            f.write(' '.join(map(str,cl))+' 0\n')


def generate(lut, s, dims, branch_rank, cnf_path, meta_path):
    from pysat.card import CardEnc, EncType
    t0=time.time()
    pts=allowed_points(branch_rank)
    p_to_var={p:i+1 for i,p in enumerate(pts)}
    clauses=[]; by_dim=Counter(); by_L=Counter(); rows_seen=0; rows_used=0; direct_clause_count=0; row_var_hist=Counter(); cap_hist=Counter()
    # Branch fixed canonical point.
    if branch_rank:
        canon=CANON_BY_RANK[branch_rank]
        if canon not in p_to_var: raise ValueError('canonical point not in branch')
        clauses.append([p_to_var[canon]])
    # Total exactly s over allowed variables.
    top_id=len(pts)
    enc=CardEnc.equals(lits=list(p_to_var.values()), bound=s, top_id=top_id, encoding=EncType.seqcounter)
    clauses.extend(enc.clauses); top_id=enc.nv
    global_card_clauses=len(enc.clauses)
    for key in sorted(lut):
        d=key&0xF
        if d not in dims: continue
        rows_seen+=1; L=lut[key]; cap=s-L; by_dim[d]+=1; by_L[L]+=1; cap_hist[cap]+=1
        row=[p_to_var[p] for p in subspace_points_from_basis(unpack_basis(key)) if p in p_to_var]
        row_var_hist[len(row)] += 1
        if cap < 0:
            clauses.append([]); rows_used+=1; continue
        if len(row) <= cap:
            continue
        rows_used += 1
        for comb in itertools.combinations(row, cap+1):
            clauses.append([-v for v in comb]); direct_clause_count += 1
    write_dimacs(cnf_path, clauses, top_id)
    meta={'problem':'T-level Wang occupation branch CNF','field':'F2','rank_s':s,'dims':list(dims),'branch_rank':branch_rank,'branch_meaning':'0 unbranched; 1 fixes E11; 2 fixes rank2 and excludes rank1; 3 fixes identity and excludes rank1/rank2','allowed_points':len(pts),'allowed_rank_hist':dict(Counter(matrix_rank_of_mask(p) for p in pts)),'fixed_point':CANON_BY_RANK.get(branch_rank),'cnf_path':str(cnf_path),'num_vars':top_id,'num_clauses':len(clauses),'global_cardinality_clauses':global_card_clauses,'direct_capacity_clauses':direct_clause_count,'rows_seen':rows_seen,'rows_used':rows_used,'rows_by_dim':dict(by_dim),'rows_by_L':dict(by_L),'row_var_count_hist':dict(row_var_hist),'cap_hist':dict(cap_hist),'elapsed_sec':time.time()-t0}
    meta_path.parent.mkdir(parents=True,exist_ok=True); meta_path.write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps(meta,indent=2,sort_keys=True))


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',type=Path,default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')); ap.add_argument('--rank',type=int,default=20); ap.add_argument('--dims',default='1,2,3'); ap.add_argument('--branch-rank',type=int,choices=[0,1,2,3],required=True); ap.add_argument('--cnf',type=Path,required=True); ap.add_argument('--meta',type=Path,required=True); args=ap.parse_args(); lut,meta=load_lut(args.lut); print(f'loaded {len(lut):,} coverage={meta.get("coverage_ok")}'); generate(lut,args.rank,parse_dims(args.dims),args.branch_rank,args.cnf,args.meta)
if __name__=='__main__': main()
