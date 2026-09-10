#!/usr/bin/env python3
"""Orbit-normalized fixed-U search from E11 rank-21 pool deletions.

For each rank-21 E11 CPD in the flip-cpd pool and each two-term deletion, keep
only the resulting 19 A-factor multiset.  Canonicalize that multiset under the
E11-core A-mode stabilizer induced by matrix-multiplication isotropy.  Then test
one representative per canonical class with a fixed-U SAT problem in which all
B and C factors are free.

This avoids imposing the sampled equal-W law on a future rank-19 solution: W is
not fixed and not used in the SAT instances; equal/different deleted W is only a
label describing where the A support came from.
"""
from __future__ import annotations

import argparse, itertools, json, re, subprocess, sys, time
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0,str(SCRIPT_DIR))
from e11_orbit_search import (generate_gl3, stabilizer_col0_e0, mat_inv, apply_e11_action_to_q, compute_e11_orbits)  # noqa: E402
from fixed_u_core_sat import build_cnf, verify_cpd, vec_from_mask  # noqa: E402


def load_core(path):
    return np.load(path).astype(np.uint8)&1


def row_terms(row,rank):
    vals=[int(x) for x in row.tolist()]
    return [tuple(vals[3*i:3*i+3]) for i in range(rank)]


def build_a_perms():
    gl=generate_gl3()
    e0=np.array([1,0,0],dtype=np.uint8)
    Ps=stabilizer_col0_e0(gl)
    Qs=[Q for Q in gl if np.array_equal(mat_inv(Q).T[:,0], e0)]
    perms=[]
    for P in Ps:
        for Q in Qs:
            perm=[0]*256
            for q in range(1,256):
                perm[q]=apply_e11_action_to_q(q,P,Q)
            perms.append(perm)
    return perms


def canonical_multiset(us,perms):
    best=None
    for perm in perms:
        tup=tuple(sorted(perm[int(u)] for u in us))
        if best is None or tup<best:
            best=tup
    return best


def parse_model(stdout:str):
    vals={}
    for line in stdout.splitlines():
        if not line.startswith('v'):
            continue
        for tok in line.split()[1:]:
            lit=int(tok)
            if lit==0: continue
            vals[abs(lit)]=lit>0
    return vals


def decode_solution(core, us, maps, stdout):
    vals=parse_model(stdout)
    r=maps['r']; nv=maps['nv']; nw=maps['nw']
    vs=[]; ws=[]
    for t in range(r):
        v=0; w=0
        for b in range(nv):
            if vals.get(maps['v'][f'{t},{b}'],False): v |= 1<<b
        for c in range(nw):
            if vals.get(maps['w'][f'{t},{c}'],False): w |= 1<<c
        vs.append(v); ws.append(w)
    ok,diff=verify_cpd(core,us,vs,ws)
    return {'verified':ok,'diff_count':diff,'u_masks':list(map(int,us)),'v_masks':vs,'w_masks':ws}


def save_solution_npz(path, core, sol):
    r=len(sol['u_masks'])
    U=np.zeros((r,core.shape[0]),dtype=np.uint8)
    V=np.zeros((r,core.shape[1]),dtype=np.uint8)
    W=np.zeros((r,core.shape[2]),dtype=np.uint8)
    for i,(u,v,w) in enumerate(zip(sol['u_masks'],sol['v_masks'],sol['w_masks'])):
        U[i]=vec_from_mask(u,core.shape[0]); V[i]=vec_from_mask(v,core.shape[1]); W[i]=vec_from_mask(w,core.shape[2])
    path.parent.mkdir(parents=True,exist_ok=True)
    np.savez(path,U=U,V=V,W=W)


def run_solver(cnf_path, solver, timeout):
    try:
        proc=subprocess.run([solver,str(cnf_path)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=timeout)
        out=proc.stdout; err=proc.stderr
        if 's UNSATISFIABLE' in out: status='UNSAT'
        elif 's SATISFIABLE' in out: status='SAT'
        else: status='UNKNOWN'
        return status,proc.returncode,out,err
    except subprocess.TimeoutExpired as exc:
        out=exc.stdout or ''; err=exc.stderr or ''
        if isinstance(out,bytes): out=out.decode('utf-8','replace')
        if isinstance(err,bytes): err=err.decode('utf-8','replace')
        return 'TIMEOUT',None,out,err


def u_rank(us):
    basis={}
    for u in us:
        x=int(u)
        while x:
            p=x.bit_length()-1
            if p in basis: x^=basis[p]
            else: basis[p]=x; break
    return len(basis)


def collect_candidates(pool_path, perms, max_schemes=0):
    arr=np.load(pool_path); rank21=arr.shape[1]//3
    if max_schemes:
        arr=arr[:max_schemes]
    classes={}
    raw_counter=Counter(); class_counter=Counter(); class_pair_types=defaultdict(Counter)
    for si,row in enumerate(arr):
        terms=row_terms(row,rank21)
        for i,j in itertools.combinations(range(rank21),2):
            ptype='same-w' if terms[i][2]==terms[j][2] else 'diff-w'
            raw_counter[ptype]+=1
            us=[terms[k][0] for k in range(rank21) if k not in (i,j)]
            canon=canonical_multiset(us,perms)
            if canon not in classes:
                classes[canon]={'canonical':canon,'representative_us':us,'scheme_index':si,'deleted':[i,j],
                                'pair_type_first':ptype,'u_rank':u_rank(us),'raw_occurrences':0}
            classes[canon]['raw_occurrences']+=1
            class_pair_types[canon][ptype]+=1
    for canon,rec in classes.items():
        rec['pair_type_counts']=dict(class_pair_types[canon])
        rec['dominant_pair_type']=class_pair_types[canon].most_common(1)[0][0]
        class_counter[rec['dominant_pair_type']]+=1
    return list(classes.values()), {'raw_pair_type_counts':dict(raw_counter),'canonical_class_type_counts':dict(class_counter),
                                   'schemes_used':int(len(arr)),'rank21':rank21}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--core',default='data/restricted_cores/mask_001_E11_core.npy')
    ap.add_argument('--pool',default='data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy')
    ap.add_argument('--outdir',required=True)
    ap.add_argument('--json-out',required=True)
    ap.add_argument('--max-schemes',type=int,default=0)
    ap.add_argument('--selection',choices=['same-w','diff-w','all'],default='all')
    ap.add_argument('--max-tests',type=int,default=0,help='0 means analyze only')
    ap.add_argument('--timeout',type=int,default=10)
    ap.add_argument('--solver',default='kissat')
    ap.add_argument('--keep-cnf',action='store_true')
    args=ap.parse_args()
    t0=time.time(); outdir=Path(args.outdir); outdir.mkdir(parents=True,exist_ok=True)
    print('building E11 A-stabilizer permutations...')
    perms=build_a_perms()
    print('perms',len(perms))
    orbit_info=compute_e11_orbits(); orbit_of=orbit_info['point_orbit']
    classes, stats=collect_candidates(args.pool,perms,args.max_schemes)
    for rec in classes:
        rec['orbit_mult']=dict(Counter(orbit_of[u] for u in rec['representative_us']))
    classes.sort(key=lambda r:(-r['raw_occurrences'], r['dominant_pair_type'], r['canonical']))
    selected=[]
    for rec in classes:
        if args.selection!='all' and rec['dominant_pair_type']!=args.selection and args.selection not in rec['pair_type_counts']:
            continue
        selected.append(rec)
    print('classes total',len(classes),'selected',len(selected),'stats',stats)
    result={'pool':args.pool,'core':args.core,'canonicalization_group_size':len(perms),
            'orbit_info':{k:v for k,v in orbit_info.items() if k!='point_orbit'},
            'stats':stats,'class_count':len(classes),'selected_count':len(selected),
            'class_summaries_head':[{k:(list(v) if k in ('canonical','representative_us') else v) for k,v in rec.items() if k!='canonical' or True} for rec in selected[:100]],
            'test_selection':args.selection,'max_tests':args.max_tests,'records':[],'status_counter':{},'found':None}
    if args.max_tests:
        core=load_core(args.core)
        status_counter=Counter()
        for ti,rec in enumerate(selected[:args.max_tests]):
            us=rec['representative_us']
            cnf,maps=build_cnf(core,us)
            cnf_path=outdir/f'orbitrep_{ti:04d}.cnf'
            cnf.write(cnf_path,[f"canonical rep raw_occ={rec['raw_occurrences']} types={rec['pair_type_counts']} scheme={rec['scheme_index']} deleted={rec['deleted']} orbit_mult={rec['orbit_mult']}"])
            st=time.time(); status,rc,stdout,stderr=run_solver(cnf_path,args.solver,args.timeout); elapsed=time.time()-st
            status_counter[status]+=1
            testrec={'test_index':ti,'status':status,'returncode':rc,'elapsed_sec':elapsed,
                     'vars':cnf.next-1,'clauses':len(cnf.clauses),'raw_occurrences':rec['raw_occurrences'],
                     'scheme_index':rec['scheme_index'],'deleted':rec['deleted'],'pair_type_counts':rec['pair_type_counts'],
                     'dominant_pair_type':rec['dominant_pair_type'],'u_rank':rec['u_rank'],'orbit_mult':rec['orbit_mult'],
                     'representative_us':rec['representative_us'],'stdout_tail':stdout[-1200:] if status!='SAT' else stdout[-2000:],
                     'stderr_tail':stderr[-500:]}
            print(f"{ti+1}/{min(args.max_tests,len(selected))} {status} {elapsed:.2f}s raw_occ={rec['raw_occurrences']} types={rec['pair_type_counts']} scheme={rec['scheme_index']} del={rec['deleted']}")
            if status=='SAT':
                sol=decode_solution(core,us,maps,stdout)
                testrec['solution']=sol
                if sol['verified']:
                    solpath=outdir/f'orbitrep_{ti:04d}_rank19_solution.npz'
                    save_solution_npz(solpath,core,sol)
                    testrec['solution_npz']=str(solpath)
                    result['found']=testrec
                    result['records'].append(testrec)
                    break
            result['records'].append(testrec)
            if not args.keep_cnf:
                try: cnf_path.unlink()
                except FileNotFoundError: pass
        result['status_counter']=dict(status_counter)
    result['elapsed_sec']=time.time()-t0
    Path(args.json_out).parent.mkdir(parents=True,exist_ok=True)
    Path(args.json_out).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('summary', {k:result[k] for k in ['class_count','selected_count','status_counter','found','elapsed_sec']})
    print('wrote',args.json_out)

if __name__=='__main__':
    main()
