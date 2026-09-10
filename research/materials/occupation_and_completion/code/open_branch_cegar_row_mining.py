#!/usr/bin/env python3
"""analysis: corrected open-branch quotient-Wang CEGAR with violation-row logging.

This is a row-selection instrument, not proof by itself.  It uses the corrected
E11WANG1 36-byte binary format, starts from a chosen capacity prefix (usually
cap<=3), solves one branch of a quotient occupation problem, and after each
candidate support records every violated full quotient Wang row.  The logged row
indices are intended to select consequential extra rows and pair-propagation rows
instead of blindly passing all cap-7 rows to a quadratic pair builder.
"""
from __future__ import annotations
import argparse, hashlib, json, struct, time
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model

ROOT = Path('research/research_record')
SPECS = ROOT / 'workspace/data/quotient_branches/corrected_branch_specs.json'
QALL = {
    'rank2': Path('data/wang_native/quotient_binaries/rank2_all_n19.bin'),
    'rank3': Path('data/wang_native/quotient_binaries/rank3_all_n19.bin'),
}
OUTDIR = ROOT / 'workspace/data/quotient_lift/mining'
OUTDIR.mkdir(parents=True, exist_ok=True)
MAGIC = b'E11WANG1'; REC = '<BBHQQQQ'; RECSZ = struct.calcsize(REC)

def sha(path: Path) -> str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20), b''):
            h.update(c)
    return h.hexdigest()

def load_rows(path: Path):
    d = path.read_bytes()
    if d[:8] != MAGIC:
        raise ValueError(f'{path}: bad magic {d[:8]!r}')
    n = struct.unpack('<I', d[8:12])[0]
    if len(d) != 12 + n*RECSZ:
        raise ValueError(f'{path}: size mismatch {len(d)} vs {12+n*RECSZ}')
    rows=[]; off=12
    for idx in range(n):
        cap,dim,pad,w0,w1,w2,w3 = struct.unpack_from(REC, d, off); off += RECSZ
        mask = int(w0) | (int(w1)<<64) | (int(w2)<<128) | (int(w3)<<192)
        rows.append({'idx':idx,'cap':int(cap),'dim':int(dim),'mask':mask,'popcount':mask.bit_count()})
    return rows

def row_points(mask:int):
    return [p for p in range(1,256) if (mask>>p)&1]

def solve_round(rows, active, force, forbid, target:int, time_limit:float, seed:int):
    model=cp_model.CpModel()
    x={p:model.NewBoolVar(f'x_{p}') for p in range(1,256)}
    for p in force: model.Add(x[p] == 1)
    for p in forbid: model.Add(x[p] == 0)
    model.Add(sum(x[p] for p in range(1,256)) == target)
    # Cache point lists only for active rows to reduce Python rebuild overhead.
    for idx in sorted(active):
        r=rows[idx]
        pts=row_points(r['mask'])
        if pts:
            model.Add(sum(x[p] for p in pts) <= r['cap'])
    solver=cp_model.CpSolver()
    solver.parameters.max_time_in_seconds=float(time_limit)
    solver.parameters.num_search_workers=8
    solver.parameters.random_seed=int(seed)
    t0=time.time(); st=solver.Solve(model); elapsed=time.time()-t0
    rec={'status':solver.StatusName(st),'solve_elapsed_sec':elapsed,'wall_time':solver.WallTime(),'conflicts':solver.NumConflicts(),'branches':solver.NumBranches(),'active_rows':len(active)}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        supp=sorted(p for p in range(1,256) if solver.Value(x[p]))
        rec['support']=supp
    return rec

def check_support(supp, rows):
    smask=0
    for p in supp: smask |= 1<<p
    viol=[]
    for r in rows:
        cap=r['cap']
        if cap <= 0 or cap >= 19:
            continue
        occ=(smask & r['mask']).bit_count()
        if occ > cap:
            viol.append({'idx':r['idx'],'cap':cap,'dim':r['dim'],'occ':occ,'excess':occ-cap,'popcount':r['popcount']})
    viol.sort(key=lambda v:(-v['excess'], v['cap'], -v['occ'], v['dim'], v['idx']))
    return viol

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--pivot', required=True, choices=['rank2','rank3'])
    ap.add_argument('--branch', type=int, required=True)
    ap.add_argument('--initial-cap', type=int, default=3)
    ap.add_argument('--rounds', type=int, default=8)
    ap.add_argument('--time-per-round', type=float, default=90.0)
    ap.add_argument('--total-time', type=float, default=600.0)
    ap.add_argument('--target', type=int, default=19)
    ap.add_argument('--seed', type=int, default=24000)
    ap.add_argument('--label', default='')
    args=ap.parse_args(); t0=time.time()
    specs=json.loads(SPECS.read_text())['pivots'][args.pivot]['branches']
    br=next(b for b in specs if int(b['branch'])==args.branch)
    rows=load_rows(QALL[args.pivot])
    active={r['idx'] for r in rows if 0 < r['cap'] <= args.initial_cap and r['cap'] < args.target}
    force=set(map(int, br['force'])); forbid=set(map(int, br['forbid']))
    rounds=[]; added_all=[]
    print(f'{args.pivot} branch {args.branch}: rows={len(rows)} initial_active={len(active)} force={sorted(force)} forbid_count={len(forbid)}', flush=True)
    for rnd in range(args.rounds):
        if time.time()-t0 >= args.total_time:
            break
        tl=min(args.time_per_round, args.total_time-(time.time()-t0))
        print(f'round {rnd}: active={len(active)} tl={tl:.1f}', flush=True)
        rec=solve_round(rows,active,force,forbid,args.target,tl,args.seed+rnd)
        if 'support' not in rec:
            rounds.append(rec)
            print(f"  {rec['status']} no support", flush=True)
            break
        viol=check_support(rec['support'], rows)
        rec['violation_count']=len(viol)
        rec['violation_cap_hist']={str(k):int(v) for k,v in sorted(Counter(vv['cap'] for vv in viol).items())}
        rec['violation_dim_hist']={str(k):int(v) for k,v in sorted(Counter(vv['dim'] for vv in viol).items())}
        rec['violation_excess_hist']={str(k):int(v) for k,v in sorted(Counter(vv['excess'] for vv in viol).items())}
        rec['violation_rows']=[vv['idx'] for vv in viol]
        rec['violation_head']=viol[:50]
        print(f"  {rec['status']} qviol={len(viol)} cap_hist={rec['violation_cap_hist']} supp={rec['support']}", flush=True)
        rounds.append(rec)
        if not viol:
            rec['fully_quotient_wang_admissible']=True
            break
        new=0
        for vv in viol:
            if vv['idx'] not in active:
                active.add(vv['idx']); added_all.append(vv['idx']); new+=1
        rec['new_rows_added']=new
        if new==0:
            break
    viol_counter=Counter()
    for rr in rounds:
        for idx in rr.get('violation_rows',[]): viol_counter[int(idx)] += 1
    top=[]
    for idx,cnt in viol_counter.most_common(200):
        r=rows[idx]; top.append({'idx':idx,'count':cnt,'cap':r['cap'],'dim':r['dim'],'popcount':r['popcount']})
    out={'schema':'s0908_open_branch_cegar_row_mining_v1','pivot':args.pivot,'branch':args.branch,'branch_force':sorted(force),'branch_forbid':sorted(forbid),'target':args.target,'initial_cap':args.initial_cap,'rows_path':str(QALL[args.pivot]),'rows_sha256':sha(QALL[args.pivot]),'rows_count':len(rows),'rounds':rounds,'final_active_rows':len(active),'unique_violated_rows':len(viol_counter),'top_violated_rows':top,'final_status':rounds[-1]['status'] if rounds else 'no_rounds','found_fully_admissible':any(r.get('fully_quotient_wang_admissible') for r in rounds),'elapsed_sec':time.time()-t0}
    lab = args.label or f'{args.pivot}_branch{args.branch}_cap{args.initial_cap}'
    path=OUTDIR/f'{lab}_mining.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('saved',path,flush=True)
    print(json.dumps({'final_status':out['final_status'],'rounds':len(rounds),'found_fully_admissible':out['found_fully_admissible'],'unique_violated_rows':out['unique_violated_rows'],'final_active_rows':out['final_active_rows'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True), flush=True)

if __name__=='__main__': main()
