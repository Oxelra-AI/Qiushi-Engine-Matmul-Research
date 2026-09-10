#!/usr/bin/env python3
"""Proof-producing fixed-A UNSAT check for E11 core supports.

For a fixed A multiset, build the plain CNF fixed-U encoding from
fixed_u_core_sat.py, run CaDiCaL with a DRAT proof, and verify the proof with
DRAT-trim.  This upgrades a solver UNSAT for a particular A multiset into a
replayable proof artifact.  It proves only the fixed-support statement.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

SCRIPTS_A02 = Path('scripts')
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))

import numpy as np
from fixed_u_core_sat import build_cnf, load_core  # noqa: E402


def sha256_file(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def parse_status(stdout: str) -> str:
    if 's UNSATISFIABLE' in stdout or 'UNSATISFIABLE' in stdout:
        return 'UNSAT'
    if 's SATISFIABLE' in stdout or 'SATISFIABLE' in stdout:
        return 'SAT'
    return 'UNKNOWN'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--core', type=Path, default=Path('data/restricted_cores/mask_001_E11_core.npy'))
    ap.add_argument('--u-list', required=True)
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--name', required=True)
    ap.add_argument('--cadical', default='cadical')
    ap.add_argument('--drat-trim', default='drat-trim')
    ap.add_argument('--timeout', type=int, default=600)
    args = ap.parse_args()

    t_all = time.time()
    args.outdir.mkdir(parents=True, exist_ok=True)
    us = [int(x) for x in args.u_list.split(',') if x.strip()]
    core = load_core(args.core)
    cnf, maps = build_cnf(core, us)
    cnf_path = args.outdir / f'{args.name}.cnf'
    proof_path = args.outdir / f'{args.name}.drat'
    cadical_log = args.outdir / f'{args.name}.cadical.log'
    trim_log = args.outdir / f'{args.name}.drat_trim.log'
    meta_path = args.outdir / f'{args.name}.meta.json'
    cnf.write(cnf_path, [f'E11 fixed-U DRAT proof name={args.name}', f'rank={len(us)} core={args.core}', f'u_masks={us}'])

    cad_cmd = [args.cadical, str(cnf_path), str(proof_path)]
    t0 = time.time()
    cad = subprocess.run(cad_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=args.timeout)
    cad_elapsed = time.time() - t0
    cadical_log.write_text(cad.stdout + ('\n[stderr]\n' + cad.stderr if cad.stderr else ''))
    cad_status = parse_status(cad.stdout + '\n' + cad.stderr)

    trim_status = 'NOT_RUN'
    trim_returncode = None
    trim_elapsed = None
    trim_stdout = ''
    trim_stderr = ''
    if cad_status == 'UNSAT' and proof_path.exists():
        trim_cmd = [args.drat_trim, str(cnf_path), str(proof_path)]
        t1 = time.time()
        trim = subprocess.run(trim_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=args.timeout)
        trim_elapsed = time.time() - t1
        trim_returncode = trim.returncode
        trim_stdout = trim.stdout
        trim_stderr = trim.stderr
        trim_log.write_text(trim.stdout + ('\n[stderr]\n' + trim.stderr if trim.stderr else ''))
        joined = trim.stdout + '\n' + trim.stderr
        trim_status = 'VERIFIED' if ('VERIFIED' in joined or 's VERIFIED' in joined) else 'FAILED_OR_UNKNOWN'

    result = {
        'purpose': 'proof-producing fixed-A E11 UNSAT check',
        'field': 'F2',
        'core': str(args.core),
        'rank': len(us),
        'u_masks': us,
        'cnf_path': str(cnf_path),
        'proof_path': str(proof_path),
        'cadical_log': str(cadical_log),
        'drat_trim_log': str(trim_log),
        'meta_path': str(meta_path),
        'vars': cnf.next - 1,
        'clauses': len(cnf.clauses),
        'cadical': {
            'command': ' '.join(cad_cmd),
            'returncode': cad.returncode,
            'status': cad_status,
            'elapsed_sec': cad_elapsed,
            'stdout_tail': cad.stdout[-4000:],
            'stderr_tail': cad.stderr[-2000:],
        },
        'drat_trim': {
            'returncode': trim_returncode,
            'status': trim_status,
            'elapsed_sec': trim_elapsed,
            'stdout_tail': trim_stdout[-4000:],
            'stderr_tail': trim_stderr[-2000:],
        },
        'sha256': {
            'cnf': sha256_file(cnf_path),
            'drat': sha256_file(proof_path),
            'cadical_log': sha256_file(cadical_log),
            'drat_trim_log': sha256_file(trim_log) if trim_log.exists() else None,
        },
        'fixed_support_unsat_certified': bool(cad_status == 'UNSAT' and trim_status == 'VERIFIED'),
        'meaning': 'If fixed_support_unsat_certified is true, no E11 core CPD exists with this exact fixed A multiset. This does not exclude any other A multiset or orbit unless combined with a complete support enumeration.',
        'elapsed_sec': time.time() - t_all,
    }
    meta_path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'name': args.name,
        'rank': len(us),
        'vars': cnf.next - 1,
        'clauses': len(cnf.clauses),
        'cadical_status': cad_status,
        'drat_trim_status': trim_status,
        'fixed_support_unsat_certified': result['fixed_support_unsat_certified'],
        'elapsed_sec': result['elapsed_sec'],
    }, indent=2, sort_keys=True))
    print(f'wrote {meta_path}')
    if cad_status == 'UNSAT' and trim_status != 'VERIFIED':
        raise SystemExit(2)


if __name__ == '__main__':
    main()
