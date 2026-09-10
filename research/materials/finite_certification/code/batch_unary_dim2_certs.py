#!/usr/bin/env python3
"""Batch unary-count CNF + DRAT verification for analysis dim-2 cores."""
from __future__ import annotations
import argparse, json, subprocess, sys, time
from pathlib import Path

SCRIPT_DIR=Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path: sys.path.insert(0,str(SCRIPT_DIR))


def run(args, timeout):
    t=time.time()
    try:
        p=subprocess.run(args,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=timeout)
        return {'args':args,'returncode':p.returncode,'stdout_tail':p.stdout[-4000:],'stderr_tail':p.stderr[-4000:],'elapsed_sec':time.time()-t,'timeout':False}
    except subprocess.TimeoutExpired as e:
        return {'args':args,'returncode':None,'stdout_tail':(e.stdout or '')[-4000:] if isinstance(e.stdout,str) else '', 'stderr_tail':(e.stderr or '')[-4000:] if isinstance(e.stderr,str) else '', 'elapsed_sec':time.time()-t,'timeout':True}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--cores-root',type=Path,required=True); ap.add_argument('--outdir',type=Path,required=True); ap.add_argument('--indices',default='484,485,486,487,488,489,490,491'); ap.add_argument('--cadical-timeout',type=int,default=300); ap.add_argument('--drat-timeout',type=int,default=300); args=ap.parse_args(); args.outdir.mkdir(parents=True,exist_ok=True)
    records=[]
    for idx in [int(x) for x in args.indices.split(',') if x.strip()]:
        paths=sorted((args.cores_root/f'orbit{idx}').glob(f'orbit{idx}_cap*_core.json'))
        if not paths:
            records.append({'index':idx,'status':'missing_core'}); print('missing',idx,flush=True); continue
        core=paths[0]
        cmd=['python','scripts/unary_count_cnf_from_core.py','--core-json',str(core),'--outdir',str(args.outdir/f'orbit{idx}'),'--name',f'orbit{idx}_unary','--solve','--cadical-timeout',str(args.cadical_timeout),'--drat-timeout',str(args.drat_timeout)]
        rec=run(cmd,args.cadical_timeout+args.drat_timeout+120)
        meta_path=args.outdir/f'orbit{idx}'/f'orbit{idx}_unary_meta.json'
        meta=None
        if meta_path.exists():
            meta=json.loads(meta_path.read_text())
        records.append({'index':idx,'core_json':str(core),'command':cmd,'run':rec,'meta_path':str(meta_path),'verified':None if meta is None else bool(meta.get('drat_verified')),'cnf_vars':None if meta is None else meta.get('cnf_meta',{}).get('vars'),'cnf_clauses':None if meta is None else meta.get('cnf_meta',{}).get('clauses'),'cadical_returncode':None if meta is None else meta.get('cadical_returncode'),'drat_returncode':None if meta is None else meta.get('drat_returncode'),'cnf_sha256':None if meta is None else meta.get('cnf_sha256'),'drat_sha256':None if meta is None else meta.get('drat_sha256'),'elapsed_sec':rec['elapsed_sec']})
        print('orbit',idx,'verified',records[-1]['verified'],'cad',records[-1]['cadical_returncode'],'drat',records[-1]['drat_returncode'],'elapsed',rec['elapsed_sec'],flush=True)
    manifest={'schema':'s0908_batch_unary_dim2_certs_v1','meaning':'Unary-count CNF/DRAT verification for the eight dim-2 raises 484--491 needed by the shortened saturated lower-bound route. Each verified core is a cap-limited subset of original Wang LUT quotient rows.','cores_root':str(args.cores_root),'outdir':str(args.outdir),'records':records,'summary':{'total':len(records),'verified':[r['index'] for r in records if r.get('verified') is True],'failed':[r['index'] for r in records if r.get('verified') is not True]}}
    mpath=args.outdir/'batch_unary_dim2_certs_manifest.json'; mpath.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','manifest':str(mpath),'summary':manifest['summary']},indent=2,sort_keys=True))

if __name__=='__main__': main()
