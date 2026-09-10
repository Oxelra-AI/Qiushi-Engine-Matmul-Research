#!/usr/bin/env python3
"""analysis: corrected branch-restricted rank-3 quotient Wang CEGAR.

Searches open pivot-273 branches with x variables, full quotient Wang rows, and
analysis branch semantics: keep all row masks unchanged; initially forbid earlier
orbit points and force the branch representative.  A found support is only a
quotient-Wang support and must be tested by full lift-bit constraints.
"""
from __future__ import annotations
import argparse, hashlib, json, struct, time
from collections import Counter
from pathlib import Path

ROOT=Path('research/research_record')
QALL=Path('data/wang_native/quotient_binaries/rank3_all_n19.bin')
SPECS=ROOT/'workspace/data/quotient_branches/corrected_branch_specs.json'
OUTDIR=ROOT/'workspace/data/quotient_lift/rank3'
OUTDIR.mkdir(parents=True, exist_ok=True)
MAGIC=b'E11WANG1'


def sha(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''):
            h.update(c)
    return h.hexdigest()


def load_rows(path:Path):
    d=path.read_bytes(); assert d[:8]==MAGIC, path
    n=struct.unpack('<I',d[8:12])[0]; off=12; sz=struct.calcsize('<BBHQQQQ'); rows=[]
    for idx in range(n):
        cap,dim,pad,w0,w1,w2,w3=struct.unpack_from('<BBHQQQQ',d,off); off+=sz
        pts=[]
        for wi,w in enumerate((w0,w1,w2,w3)):
            for b in range(64):
                p=64*wi+b
                if p and ((w>>b)&1): pts.append(p)
        rows.append({'idx':idx,'cap':int(cap),'dim':int(dim),'points':pts})
    return rows


def check_support(supp:set[int], rows, target=19):
    viol=[]
    for r in rows:
        c=r['cap']
        if c<=0 or c>=target: continue
        occ=sum(1 for p in r['points'] if p in supp)
        if occ>c: viol.append((r['idx'],c,r['dim'],occ))
    return viol


def solve_round(rows, active:set[int], branch, prev_supports, time_limit:float, seed:int):
    from ortools.sat.python import cp_model
    model=cp_model.CpModel(); x={p:model.NewBoolVar(f'x_{p}') for p in range(1,256)}
    model.Add(sum(x[p] for p in range(1,256))==19)
    for p in branch['force']:
        model.Add(x[int(p)]==1)
    for p in branch['forbid']:
        model.Add(x[int(p)]==0)
    for idx in sorted(active):
        r=rows[idx]; model.Add(sum(x[p] for p in r['points']) <= r['cap'])
    for s in prev_supports:
        model.Add(sum(x[p] for p in s) <= len(s)-1)
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(time_limit); solver.parameters.num_search_workers=8; solver.parameters.random_seed=int(seed)
    st=solver.Solve(model)
    rec={'status':solver.StatusName(st),'wall_time':solver.WallTime(),'conflicts':solver.NumConflicts(),'branches':solver.NumBranches(),'active_constraints':len(active),'branch':branch['branch'],'rep':branch['representative'],'forbid_count':branch['forbid_count']}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        rec['support']=sorted(p for p in range(1,256) if solver.Value(x[p]))
    return rec


def run_branch(rows, branch, args):
    t0=time.time(); active={r['idx'] for r in rows if 0<r['cap']<=args.initial_cap and r['cap']<19}; rounds=[]; found=[]
    for rnd in range(args.rounds):
        elapsed=time.time()-t0
        if elapsed>=args.total_time: break
        tl=min(float(args.time_per_round), args.total_time-elapsed)
        print(f'rank3 branch {branch["branch"]} round {rnd} active={len(active)} tl={tl:.1f}', flush=True)
        rec=solve_round(rows,active,branch,found if args.exclude_found else [],tl,args.seed+100*branch['branch']+rnd)
        if 'support' not in rec:
            print(f"  status={rec['status']} no support", flush=True); rounds.append(rec); break
        supp=set(rec['support'])
        # sanity branch semantics
        assert all(int(p) in supp for p in branch['force'])
        assert all(int(p) not in supp for p in branch['forbid'])
        viol=check_support(supp,rows)
        rec['full_quotient_violation_count']=len(viol)
        rec['full_quotient_violation_head']=[{'idx':i,'cap':c,'dim':d,'occ':o} for i,c,d,o in viol[:50]]
        print(f"  status={rec['status']} qviol={len(viol)} supp={rec['support']}", flush=True)
        if not viol:
            rec['fully_quotient_wang_admissible']=True; found.append(rec['support']); rounds.append(rec); break
        new=0
        for i,c,d,o in viol:
            if i not in active: active.add(i); new+=1
        rec['violations_added']=new
        rec['violation_cap_hist']={str(k):int(v) for k,v in sorted(Counter(c for i,c,d,o in viol).items())}
        rounds.append(rec)
    return {'branch':branch['branch'],'representative':branch['representative'],'orbit_size':branch['orbit_size'],'force':branch['force'],'forbid_count':branch['forbid_count'],'rounds':rounds,'final_active_constraints':len(active),'fully_quotient_wang_admissible':any(r.get('fully_quotient_wang_admissible') for r in rounds),'final_status':rounds[-1]['status'] if rounds else 'no_rounds','elapsed_sec':time.time()-t0}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--branches',default='0,1'); ap.add_argument('--initial-cap',type=int,default=3); ap.add_argument('--rounds',type=int,default=10); ap.add_argument('--time-per-round',type=int,default=120); ap.add_argument('--total-time',type=int,default=600); ap.add_argument('--seed',type=int,default=22300); ap.add_argument('--exclude-found',action='store_true')
    args=ap.parse_args(); t0=time.time(); rows=load_rows(QALL); specs=json.loads(SPECS.read_text())['pivots']['rank3']['branches']; wanted={int(x) for x in args.branches.split(',') if x.strip()}
    branch_recs=[]
    for br in specs:
        if br['branch'] in wanted:
            branch_recs.append(run_branch(rows,br,args))
    out={'schema':'s0908_rank3_branch_cegar_v1','quotient_all_binary':str(QALL),'quotient_all_binary_sha256':sha(QALL),'branch_specs':str(SPECS),'branch_specs_sha256':sha(SPECS),'initial_cap':args.initial_cap,'branches':branch_recs,'any_fully_quotient_wang_admissible':any(b['fully_quotient_wang_admissible'] for b in branch_recs),'elapsed_sec':time.time()-t0}
    path=OUTDIR/f'rank3_branch_cegar_b{args.branches.replace(",","_")}_cap{args.initial_cap}.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('saved',path,flush=True); print(json.dumps({'any_survivor':out['any_fully_quotient_wang_admissible'],'branches':[{k:b.get(k) for k in ['branch','fully_quotient_wang_admissible','final_status','final_active_constraints','elapsed_sec']} for b in branch_recs],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True),flush=True)

if __name__=='__main__': main()
