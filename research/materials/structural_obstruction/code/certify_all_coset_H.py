#!/usr/bin/env python3
"""Certify all 16 normalized surviving-coset H A-side systems.

For each Hxx_constraints.json produced by coset_rankone_fullwang_compress.py,
extract a small active core, encode it as CNF, solve with CaDiCaL emitting DRAT,
and replay with drat-trim.  This certifies the Boolean A-occupation infeasibility
of the compressed full-Wang rows for that fixed H, conditional on the row table
and structural reduction.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from extract_sat_core_and_cnf import extract_core, encode_cnf  # type: ignore

INDIR = Path('data/coset_fullwang')
OUTDIR = Path('data/coset_fullwang_cert_all')


def sha256(path: Path) -> str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda:f.read(1<<20), b''):
            h.update(chunk)
    return h.hexdigest()


def run_cmd(args, timeout=120):
    t0=time.time()
    p=subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    return {'args':args,'returncode':p.returncode,'stdout_tail':p.stdout[-4000:],'stderr_tail':p.stderr[-4000:],'elapsed_sec':time.time()-t0}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--indir', type=Path, default=INDIR)
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    ap.add_argument('--add-per-round', type=int, default=500)
    ap.add_argument('--max-rounds', type=int, default=30)
    ap.add_argument('--solver-sec', type=float, default=10.0)
    ap.add_argument('--cadical-timeout', type=int, default=120)
    ap.add_argument('--drat-timeout', type=int, default=120)
    args=ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    records=[]; t0=time.time()
    for hi in range(16):
        cpath=args.indir/f'H{hi:02d}_constraints.json'
        d=json.loads(cpath.read_text())
        cons=[(int(r['mask']), int(r['rhs'])) for r in d['constraints']]
        start=time.time()
        active, rounds, status = extract_core(cons,args.add_per_round,args.max_rounds,args.solver_sec)
        rec={'h_index':hi,'constraints_path':str(cpath),'constraint_sha256':sha256(cpath),'full_constraint_count':len(cons),'core_status':status,'active_count':len(active),'core_rounds':len(rounds)}
        core_path=args.outdir/f'H{hi:02d}_core.json'
        cnf_path=args.outdir/f'H{hi:02d}_core.cnf'
        drat_path=args.outdir/f'H{hi:02d}_core.drat'
        log_path=args.outdir/f'H{hi:02d}_proof_logs.json'
        core={'schema':'s0908_allH_core_v1','h_index':hi,'source_constraints':str(cpath),'status':status,'active_count':len(active),'active_constraints':[{'mask':m,'rhs':rhs} for m,rhs in active],'rounds':rounds}
        core_path.write_text(json.dumps(core,indent=2,sort_keys=True)+'\n')
        rec['core_path']=str(core_path); rec['core_sha256']=sha256(core_path)
        if status != 'INFEASIBLE':
            rec['verified']=False; rec['reason']='core_not_infeasible'; records.append(rec); continue
        cnf_meta=encode_cnf(active,cnf_path)
        rec['cnf_path']=str(cnf_path); rec['cnf_sha256']=sha256(cnf_path); rec['cnf_meta']=cnf_meta
        cad=run_cmd(['cadical', str(cnf_path), str(drat_path)], timeout=args.cadical_timeout)
        rec['cadical_returncode']=cad['returncode']
        rec['drat_path']=str(drat_path); rec['drat_sha256']=sha256(drat_path) if drat_path.exists() else None
        dr=None
        if cad['returncode'] == 20 and drat_path.exists():
            dr=run_cmd(['drat-trim', str(cnf_path), str(drat_path)], timeout=args.drat_timeout)
            rec['drat_returncode']=dr['returncode']
            rec['drat_verified']='s VERIFIED' in dr['stdout_tail']
        else:
            rec['drat_returncode']=None; rec['drat_verified']=False
        rec['verified']=bool(cad['returncode']==20 and rec.get('drat_returncode')==0 and rec.get('drat_verified'))
        rec['elapsed_sec']=time.time()-start
        log_path.write_text(json.dumps({'cadical':cad,'drat_trim':dr},indent=2,sort_keys=True)+'\n')
        rec['log_path']=str(log_path)
        records.append(rec)
        print('H',hi,'active',len(active),'cad',cad['returncode'],'drat',rec.get('drat_returncode'),'verified',rec['verified'], flush=True)
    manifest={'schema':'s0908_all_coset_H_drat_manifest_v1','meaning':'DRAT replay manifest for the 16 normalized surviving-coset A-side full-Wang compressed systems. This certifies the CNF encodings of the compressed Boolean systems; structural reduction and Wang-row provenance remain separate mathematical premises.','indir':str(args.indir),'outdir':str(args.outdir),'records':records,'summary':{'total':len(records),'verified':[r['h_index'] for r in records if r.get('verified')], 'failed':[r['h_index'] for r in records if not r.get('verified')]},'elapsed_sec':time.time()-t0}
    mpath=args.outdir/'all_coset_H_drat_manifest.json'
    mpath.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','manifest':str(mpath),'summary':manifest['summary'],'elapsed_sec':manifest['elapsed_sec']},indent=2,sort_keys=True))


if __name__=='__main__':
    main()
