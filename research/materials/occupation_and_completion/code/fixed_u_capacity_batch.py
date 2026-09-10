#!/usr/bin/env python3
"""Test all A-support candidates recorded in a Wang core-capacity lazy run.

The capacity run only reasons about A-factor multiplicities.  This script asks,
for each recorded A multiset, whether there actually exist B and C factors for
an exact core CPD with those fixed A factors.  It uses the fixed-U SAT encoding
from fixed_u_core_sat.py and verifies any SAT model.
"""
from __future__ import annotations
import argparse, json, subprocess, re, time, sys
from collections import Counter
from pathlib import Path
import numpy as np

SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0,str(SCRIPT_DIR))
from fixed_u_core_sat import build_cnf, verify_cpd, vec_from_mask  # noqa: E402


def load_core(path): return np.load(path).astype(np.uint8)&1


def u_rank(us):
    basis={}
    for u in us:
        x=int(u)
        while x:
            p=x.bit_length()-1
            if p in basis: x^=basis[p]
            else: basis[p]=x; break
    return len(basis)


def parse_model(stdout):
    vals={}
    for line in stdout.splitlines():
        if not line.startswith('v'): continue
        for tok in line.split()[1:]:
            lit=int(tok)
            if lit: vals[abs(lit)]=lit>0
    return vals


def decode_solution(core,us,maps,stdout):
    vals=parse_model(stdout); vs=[]; ws=[]
    for t in range(maps['r']):
        v=0; w=0
        for b in range(maps['nv']):
            if vals.get(maps['v'][f'{t},{b}'],False): v|=1<<b
        for c in range(maps['nw']):
            if vals.get(maps['w'][f'{t},{c}'],False): w|=1<<c
        vs.append(v); ws.append(w)
    ok,diff=verify_cpd(core,us,vs,ws)
    return {'verified':ok,'diff_count':diff,'u_masks':list(map(int,us)),'v_masks':vs,'w_masks':ws}


def run_solver(cnf_path,solver,timeout):
    try:
        proc=subprocess.run([solver,str(cnf_path)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=timeout)
        out=proc.stdout; err=proc.stderr
        if 's UNSATISFIABLE' in out: st='UNSAT'
        elif 's SATISFIABLE' in out: st='SAT'
        else: st='UNKNOWN'
        return st,proc.returncode,out,err
    except subprocess.TimeoutExpired as exc:
        out=exc.stdout or ''; err=exc.stderr or ''
        if isinstance(out,bytes): out=out.decode('utf-8','replace')
        if isinstance(err,bytes): err=err.decode('utf-8','replace')
        return 'TIMEOUT',None,out,err


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--core',default='data/restricted_cores/mask_001_E11_core.npy')
    ap.add_argument('--capacity-json',required=True)
    ap.add_argument('--outdir',required=True)
    ap.add_argument('--json-out',required=True)
    ap.add_argument('--timeout',type=int,default=60)
    ap.add_argument('--solver',default='kissat')
    ap.add_argument('--keep-cnf',action='store_true')
    args=ap.parse_args()
    t0=time.time(); outdir=Path(args.outdir); outdir.mkdir(parents=True,exist_ok=True)
    core=load_core(args.core)
    cap=json.loads(Path(args.capacity_json).read_text())
    candidates=[]; seen=set()
    for it in cap.get('iterations',[]):
        sol=it.get('solution')
        if not sol: continue
        us=[]
        for k,v in sorted(((int(k),int(v)) for k,v in sol.items())):
            us += [k]*v
        key=tuple(sorted(us))
        if key in seen: continue
        seen.add(key)
        candidates.append({'iteration':it.get('iteration'),'solver_status':it.get('solver_status'),
                           'support_size':len(sol),'max_mult':max(sol.values()),'u_masks':us,
                           'check_stats':it.get('check_stats')})
    records=[]; status_counter=Counter(); found=None
    print('capacity candidates',len(candidates),'from',args.capacity_json)
    for ci,cand in enumerate(candidates):
        cnf,maps=build_cnf(core,cand['u_masks'])
        cnf_path=outdir/f'capacity_iter{cand["iteration"]}_cand{ci}.cnf'
        cnf.write(cnf_path,[f"capacity iteration={cand['iteration']} support={cand['support_size']} maxmult={cand['max_mult']}"])
        st=time.time(); status,rc,stdout,stderr=run_solver(cnf_path,args.solver,args.timeout); elapsed=time.time()-st
        status_counter[status]+=1
        rec={k:cand[k] for k in cand if k!='u_masks'}
        rec.update({'candidate_index':ci,'u_rank':u_rank(cand['u_masks']),'u_masks':cand['u_masks'],
                    'status':status,'returncode':rc,'elapsed_sec':elapsed,'vars':cnf.next-1,'clauses':len(cnf.clauses),
                    'stdout_tail':stdout[-1200:] if status!='SAT' else stdout[-2000:], 'stderr_tail':stderr[-500:]})
        print(f"{ci+1}/{len(candidates)} iter={cand['iteration']} {status} {elapsed:.2f}s support={cand['support_size']} maxmult={cand['max_mult']} u_rank={rec['u_rank']}")
        if status=='SAT':
            sol=decode_solution(core,cand['u_masks'],maps,stdout)
            rec['solution']=sol
            if sol['verified']:
                path=outdir/f'capacity_cand{ci}_solution.npz'
                r=len(sol['u_masks']); U=np.zeros((r,core.shape[0]),dtype=np.uint8); V=np.zeros((r,core.shape[1]),dtype=np.uint8); W=np.zeros((r,core.shape[2]),dtype=np.uint8)
                for i,(u,v,w) in enumerate(zip(sol['u_masks'],sol['v_masks'],sol['w_masks'])):
                    U[i]=vec_from_mask(u,core.shape[0]); V[i]=vec_from_mask(v,core.shape[1]); W[i]=vec_from_mask(w,core.shape[2])
                np.savez(path,U=U,V=V,W=W); rec['solution_npz']=str(path); found=rec
                records.append(rec); break
        records.append(rec)
        if not args.keep_cnf:
            try: cnf_path.unlink()
            except FileNotFoundError: pass
    result={'core':args.core,'capacity_json':args.capacity_json,'candidate_count':len(candidates),'tested':len(records),
            'status_counter':dict(status_counter),'found':found,'records':records,'elapsed_sec':time.time()-t0,
            'interpretation':'Each UNSAT excludes a recorded Wang A-factor multiset as the support of an exact rank-19 E11 CPD, with all B/C factors free. This does not exclude unrecorded A supports.'}
    Path(args.json_out).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('summary', {k:result[k] for k in ['tested','status_counter','found','elapsed_sec']})
    print('wrote',args.json_out)

if __name__=='__main__': main()
