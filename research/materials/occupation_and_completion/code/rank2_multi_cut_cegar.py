#!/usr/bin/env python3
"""analysis: rank-2 quotient support CEGAR with multiple lift-cut orbits.

Uses x variables only.  Adds all transported monotone support cuts from a list of
rank-2 lift-cut transport manifests, then searches for a 19-point support that
satisfies all quotient Wang rows and avoids all cuts.  A found support is not a
full tensor candidate; it is a target for all-row lift-bit feasibility.
"""
from __future__ import annotations
import argparse, hashlib, json, struct, time
from collections import Counter
from pathlib import Path

ROOT=Path('research/research_record')
QALL=Path('data/wang_native/quotient_binaries/rank2_all_n19.bin')
DEFAULT_MANIFESTS=[
    ROOT/'workspace/data/quotient_lift/transport/rank2_lift_cut_stabilizer_transport.json',
    ROOT/'workspace/data/quotient_lift/transport/rank2_survivor2_lift_cut_stabilizer_transport.json',
]
OUTDIR=ROOT/'workspace/data/quotient_lift/transport'
OUTDIR.mkdir(parents=True, exist_ok=True)
MAGIC=b'E11WANG1'


def sha(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''):
            h.update(c)
    return h.hexdigest()


def sha_obj(o)->str:
    return hashlib.sha256(json.dumps(o,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def load_rows(path:Path):
    d=path.read_bytes(); assert d[:8]==MAGIC, path
    n=struct.unpack('<I',d[8:12])[0]; rec=struct.calcsize('<BBHQQQQ'); off=12; rows=[]
    for idx in range(n):
        cap,dim,pad,w0,w1,w2,w3=struct.unpack_from('<BBHQQQQ',d,off); off+=rec
        pts=[]
        for wi,w in enumerate((w0,w1,w2,w3)):
            for b in range(64):
                p=64*wi+b
                if p and ((w>>b)&1): pts.append(p)
        rows.append({'idx':idx,'cap':int(cap),'dim':int(dim),'points':pts})
    return rows


def load_cut_manifests(paths:list[Path]):
    cuts=[]; manifests=[]; seen={}
    for mp in paths:
        d=json.loads(mp.read_text())
        rhs=int(d.get('base_rhs',11))
        local=[]
        for c in d['unique_cuts']:
            pts=tuple(sorted(int(x) for x in c['cut_points']))
            mask=sum(1<<p for p in pts)
            if mask not in seen:
                seen[mask]=len(cuts)
                cuts.append({'idx':len(cuts),'rhs':rhs,'points':list(pts),'source_manifest':str(mp)})
            local.append(seen[mask])
        manifests.append({'path':str(mp),'sha256':sha(mp),'unique_cuts_in_manifest':len(d['unique_cuts']),'rhs':rhs,'new_cuts_added':len(set(local))})
    return manifests,cuts


def check_support(supp:set[int], rows, target=19):
    viol=[]
    for r in rows:
        c=r['cap']
        if c<=0 or c>=target: continue
        occ=sum(1 for p in r['points'] if p in supp)
        if occ>c: viol.append((r['idx'],c,r['dim'],occ))
    return viol


def check_cuts(supp:set[int], cuts):
    viol=[]
    for c in cuts:
        occ=sum(1 for p in c['points'] if p in supp)
        if occ>c['rhs']: viol.append((c['idx'],c['rhs'],occ,c['points']))
    return viol


def solve_round(rows, active:set[int], cuts, prev_supports, time_limit:float, seed:int):
    from ortools.sat.python import cp_model
    model=cp_model.CpModel(); x={p:model.NewBoolVar(f'x_{p}') for p in range(1,256)}
    model.Add(sum(x[p] for p in range(1,256))==19)
    for idx in sorted(active):
        r=rows[idx]; model.Add(sum(x[p] for p in r['points']) <= r['cap'])
    for c in cuts:
        model.Add(sum(x[p] for p in c['points']) <= c['rhs'])
    for s in prev_supports:
        model.Add(sum(x[p] for p in s) <= len(s)-1)
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(time_limit); solver.parameters.num_search_workers=8; solver.parameters.random_seed=int(seed)
    st=solver.Solve(model)
    rec={'status':solver.StatusName(st),'wall_time':solver.WallTime(),'conflicts':solver.NumConflicts(),'branches':solver.NumBranches(),'active_constraints':len(active),'support_cuts':len(cuts)}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        rec['support']=sorted(p for p in range(1,256) if solver.Value(x[p]))
    return rec


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--cut-manifest', action='append', type=Path, default=[])
    ap.add_argument('--initial-cap',type=int,default=3)
    ap.add_argument('--rounds',type=int,default=20)
    ap.add_argument('--time-per-round',type=int,default=120)
    ap.add_argument('--total-time',type=int,default=900)
    ap.add_argument('--seed',type=int,default=22000)
    ap.add_argument('--exclude-found',action='store_true')
    ap.add_argument('--label',default='two_orbits')
    args=ap.parse_args(); t0=time.time()
    manifests=args.cut_manifest or DEFAULT_MANIFESTS
    print('Loading quotient rows...', flush=True)
    rows=load_rows(QALL)
    print('Loading cuts...', flush=True)
    manifest_recs,cuts=load_cut_manifests(manifests)
    active={r['idx'] for r in rows if 0<r['cap']<=args.initial_cap and r['cap']<19}
    rounds=[]; found=[]
    print(f'rows={len(rows)} active={len(active)} cuts={len(cuts)}', flush=True)
    for rnd in range(args.rounds):
        elapsed=time.time()-t0
        if elapsed>=args.total_time: break
        tl=min(float(args.time_per_round), args.total_time-elapsed)
        print(f'round {rnd} active={len(active)} tl={tl:.1f}', flush=True)
        rec=solve_round(rows,active,cuts,found if args.exclude_found else [],tl,args.seed+rnd)
        if 'support' not in rec:
            print(f"  status={rec['status']} no support", flush=True); rounds.append(rec); break
        supp=set(rec['support']); viol=check_support(supp,rows); cviol=check_cuts(supp,cuts)
        rec['full_quotient_violation_count']=len(viol)
        rec['full_quotient_violation_head']=[{'idx':i,'cap':c,'dim':d,'occ':o} for i,c,d,o in viol[:50]]
        rec['support_cut_violation_count']=len(cviol)
        rec['support_cut_violation_head']=[{'idx':i,'rhs':rhs,'occ':occ,'points':pts} for i,rhs,occ,pts in cviol[:20]]
        print(f"  status={rec['status']} qviol={len(viol)} cviol={len(cviol)} supp={rec['support']}", flush=True)
        if cviol:
            raise AssertionError('CP-SAT returned cut-violating support')
        if not viol:
            rec['fully_quotient_wang_admissible']=True; found.append(rec['support']); rounds.append(rec); break
        new=0
        for i,c,d,o in viol:
            if i not in active: active.add(i); new+=1
        rec['violations_added']=new
        rec['violation_cap_hist']={str(k):int(v) for k,v in sorted(Counter(c for i,c,d,o in viol).items())}
        rounds.append(rec)
    out={'schema':'s0908_rank2_multi_cut_cegar_v1','quotient_all_binary':str(QALL),'quotient_all_binary_sha256':sha(QALL),'cut_manifests':manifest_recs,'support_cut_count':len(cuts),'support_cuts_sha256':sha_obj(cuts),'initial_cap':args.initial_cap,'rounds':rounds,'final_active_constraints':len(active),'fully_quotient_wang_admissible':any(r.get('fully_quotient_wang_admissible') for r in rounds),'final_status':rounds[-1]['status'] if rounds else 'no_rounds','elapsed_sec':time.time()-t0}
    path=OUTDIR/f'rank2_multi_cut_cegar_{args.label}_cap{args.initial_cap}.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('saved',path,flush=True)
    print(json.dumps({'final_status':out['final_status'],'rounds':len(rounds),'fully_quotient_wang_admissible':out['fully_quotient_wang_admissible'],'support_cut_count':len(cuts),'elapsed_sec':out['elapsed_sec'],'final_active_constraints':len(active)},indent=2,sort_keys=True), flush=True)

if __name__=='__main__':
    main()
