#!/usr/bin/env python3
"""analysis: rank-2 quotient CEGAR with certified lift relations.

This tests whether the compact lift-bit relation family transported from the
analysis 12-point obstruction eliminates quotient-Wang survivors, while preserving
lift-bit variables instead of projecting everything to support-only cuts.

Variables y0_p,y1_p mean quotient point p is selected with lift bit 0/1.  The
support variable is x_p=y0_p+y1_p.  The model contains:
  * target sum_p x_p = 19;
  * active quotient Wang rows, grown by CEGAR from the complete rank2_all_n19.bin;
  * 1296 transported lift-bit relation rows from full Wang source subspaces;
  * optional 48 transported support cuts |S cap A_g|<=11.

After each solve, the candidate support is checked against ALL quotient rows; if
fully quotient-Wang admissible, the lift assignment is checked against the compact
relations and returned for full all-row lift testing.
"""
from __future__ import annotations
import argparse, hashlib, json, struct, time
from collections import Counter
from pathlib import Path

ROOT=Path('research/research_record')
QALL=Path('data/wang_native/quotient_binaries/rank2_all_n19.bin')
REL=ROOT/'workspace/data/quotient_lift/transport/rank2_lift_relation_rows_from_cut33.json'
TRANSPORT=ROOT/'workspace/data/quotient_lift/transport/rank2_lift_cut_stabilizer_transport.json'
OUTDIR=ROOT/'workspace/data/quotient_lift/transport'
OUTDIR.mkdir(parents=True,exist_ok=True)
MAGIC=b'E11WANG1'

def sha(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''):
            h.update(c)
    return h.hexdigest()

def load_rows(path:Path):
    d=path.read_bytes(); assert d[:8]==MAGIC, path
    n=struct.unpack('<I',d[8:12])[0]; off=12; rec=struct.calcsize('<BBHQQQQ'); rows=[]
    for idx in range(n):
        cap,dim,pad,w0,w1,w2,w3=struct.unpack_from('<BBHQQQQ',d,off); off+=rec
        pts=[]
        for wi,w in enumerate((w0,w1,w2,w3)):
            for b in range(64):
                p=64*wi+b
                if p and ((w>>b)&1): pts.append(p)
        rows.append({'idx':idx,'cap':int(cap),'dim':int(dim),'points':pts})
    return rows

def check_support(supp:set[int], rows, target:int=19):
    viol=[]
    for r in rows:
        c=r['cap']
        if c<=0 or c>=target: continue
        occ=sum(1 for p in r['points'] if p in supp)
        if occ>c:
            viol.append((r['idx'],c,r['dim'],occ))
    return viol

def load_relations(path:Path):
    data=json.loads(path.read_text())
    rel=[]
    for i,r in enumerate(data['relation_rows']):
        rel.append({'idx':i,'cap':int(r['cap']),'eps0':list(map(int,r['eps0_points'])),'eps1':list(map(int,r['eps1_points'])),'source_dim':int(r['source_dim']),'source_lb':int(r['source_lb'])})
    return data,rel

def load_support_cuts(path:Path):
    data=json.loads(path.read_text())
    cuts=[]
    for i,r in enumerate(data['unique_cuts']):
        cuts.append({'idx':i,'points':list(map(int,r['cut_points'])),'rhs':int(data['base_rhs'])})
    return data,cuts

def check_rel_assignment(supp:set[int], assign:dict[int,int], rels):
    viol=[]
    for r in rels:
        occ=sum(1 for p in r['eps0'] if p in supp and assign[p]==0)+sum(1 for p in r['eps1'] if p in supp and assign[p]==1)
        if occ>r['cap']:
            viol.append((r['idx'],r['cap'],occ))
    return viol

def solve_round(qrows, active:set[int], rels, cuts, prev_supports, time_limit:float, seed:int, use_cuts:bool=True):
    from ortools.sat.python import cp_model
    model=cp_model.CpModel()
    y0={p:model.NewBoolVar(f'y0_{p}') for p in range(1,256)}
    y1={p:model.NewBoolVar(f'y1_{p}') for p in range(1,256)}
    # exactly 19 selected; point cannot be selected with both lift bits.
    for p in range(1,256):
        model.Add(y0[p]+y1[p] <= 1)
    model.Add(sum(y0[p]+y1[p] for p in range(1,256)) == 19)
    for idx in active:
        r=qrows[idx]
        model.Add(sum(y0[p]+y1[p] for p in r['points']) <= r['cap'])
    for r in rels:
        model.Add(sum(y0[p] for p in r['eps0']) + sum(y1[p] for p in r['eps1']) <= r['cap'])
    if use_cuts:
        for c in cuts:
            model.Add(sum(y0[p]+y1[p] for p in c['points']) <= c['rhs'])
    for s in prev_supports:
        model.Add(sum(y0[p]+y1[p] for p in s) <= len(s)-1)
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(time_limit); solver.parameters.num_search_workers=8; solver.parameters.random_seed=int(seed)
    t0=time.time(); st=solver.Solve(model); elapsed=time.time()-t0
    status=solver.StatusName(st)
    rec={'status':status,'elapsed_sec':elapsed,'active_quotient_constraints':len(active),'relation_constraints':len(rels),'support_cuts':len(cuts) if use_cuts else 0,'conflicts':solver.NumConflicts(),'branches':solver.NumBranches(),'wall_time':solver.WallTime()}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        supp=sorted(p for p in range(1,256) if solver.Value(y0[p])+solver.Value(y1[p])==1)
        assign={p:int(solver.Value(y1[p])) for p in supp}
        rec['support']=supp; rec['lift_bits_in_support_order']=[assign[p] for p in supp]; rec['assignment']=assign
    return rec

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--initial-cap',type=int,default=3); ap.add_argument('--rounds',type=int,default=12); ap.add_argument('--time-per-round',type=int,default=180); ap.add_argument('--total-time',type=int,default=1200); ap.add_argument('--no-support-cuts',action='store_true'); ap.add_argument('--seed',type=int,default=2100)
    args=ap.parse_args()
    t0=time.time(); print('Loading quotient rows...',flush=True); qrows=load_rows(QALL)
    print('Loading relations/cuts...',flush=True); rel_data,rels=load_relations(REL); cut_data,cuts=load_support_cuts(TRANSPORT)
    active={r['idx'] for r in qrows if 0<r['cap']<=args.initial_cap and r['cap']<19}
    rounds=[]; prev=[]
    print(f'rows={len(qrows)} active={len(active)} rels={len(rels)} cuts={len(cuts)}',flush=True)
    for rnd in range(args.rounds):
        elapsed=time.time()-t0
        if elapsed>=args.total_time:
            break
        tl=min(args.time_per_round,args.total_time-elapsed)
        print(f'round {rnd}: active={len(active)} tl={tl:.1f}',flush=True)
        rec=solve_round(qrows,active,rels,cuts,prev,tl,args.seed+rnd,use_cuts=not args.no_support_cuts)
        if 'assignment' in rec:
            # convert assignment keys to int after json round? currently int.
            supp=set(rec['support']); assign={int(k):int(v) for k,v in rec['assignment'].items()}
            viol=check_support(supp,qrows)
            rviol=check_rel_assignment(supp,assign,rels)
            cviol=[]
            for c in cuts:
                occ=sum(1 for p in c['points'] if p in supp)
                if occ>c['rhs']: cviol.append((c['idx'],c['rhs'],occ))
            rec['full_quotient_violation_count']=len(viol); rec['full_quotient_violation_head']=[{'idx':i,'cap':c,'dim':d,'occ':o} for i,c,d,o in viol[:50]]; rec['relation_violation_count']=len(rviol); rec['support_cut_violation_count']=len(cviol)
            print(f"  status={rec['status']} qviol={len(viol)} relviol={len(rviol)} cutviol={len(cviol)} support={rec['support']}", flush=True)
            if rviol or cviol:
                raise AssertionError('solver returned assignment violating encoded relation/cut')
            if not viol:
                rec['fully_quotient_wang_admissible']=True
                rounds.append(rec)
                print('FULLY QUOTIENT-WANG ADMISSIBLE survivor under compact lift relations found.', flush=True)
                break
            new=0
            for i,c,d,o in viol:
                if i not in active:
                    active.add(i); new+=1
            rec['violations_added']=new; rec['violation_cap_hist']={str(k):int(v) for k,v in sorted(Counter(c for i,c,d,o in viol).items())}
            # Do not add candidate as prev support; a stricter model may return same support until violated rows are active, but after adding all violations it won't.
        else:
            print(f"  status={rec['status']} no solution", flush=True)
            rounds.append(rec); break
        rounds.append(rec)
    out={'schema':'s0908_rank2_lift_relation_cegar_v1','quotient_all_binary':str(QALL),'quotient_all_binary_sha256':sha(QALL),'relation_file':str(REL),'relation_file_sha256':sha(REL),'relation_rows_sha256':rel_data['relation_rows_sha256'],'support_cut_transport_file':str(TRANSPORT),'support_cut_transport_sha256':sha(TRANSPORT),'initial_cap':args.initial_cap,'use_support_cuts':not args.no_support_cuts,'rounds':rounds,'final_active_constraints':len(active),'fully_quotient_wang_admissible':any(r.get('fully_quotient_wang_admissible') for r in rounds),'final_status':rounds[-1]['status'] if rounds else 'no_rounds','elapsed_sec':time.time()-t0}
    path=OUTDIR/f'rank2_lift_relation_cegar_cap{args.initial_cap}_{"cuts" if not args.no_support_cuts else "nocuts"}.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('saved',path,flush=True)
    print(json.dumps({'final_status':out['final_status'],'rounds':len(rounds),'fully_quotient_wang_admissible':out['fully_quotient_wang_admissible'],'final_active_constraints':len(active),'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True),flush=True)

if __name__=='__main__': main()
