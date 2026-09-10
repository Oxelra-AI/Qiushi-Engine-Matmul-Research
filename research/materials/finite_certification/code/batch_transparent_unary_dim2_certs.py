#!/usr/bin/env python3
"""Batch transparent unary-count CNF + DRAT verification for orbits 484--491."""
from __future__ import annotations

import argparse
import json
import subprocess
import time
from pathlib import Path


def run(args, timeout):
    t0 = time.time()
    try:
        p = subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
        return {'args': args, 'returncode': p.returncode, 'stdout_tail': p.stdout[-4000:], 'stderr_tail': p.stderr[-4000:], 'elapsed_sec': time.time()-t0, 'timeout': False}
    except subprocess.TimeoutExpired as e:
        return {'args': args, 'returncode': None, 'stdout_tail': (e.stdout or '')[-4000:] if isinstance(e.stdout, str) else '', 'stderr_tail': (e.stderr or '')[-4000:] if isinstance(e.stderr, str) else '', 'elapsed_sec': time.time()-t0, 'timeout': True}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--cores-root', type=Path, default=Path('data/dim2_caplimited_cores_484_491'))
    ap.add_argument('--outdir', type=Path, default=Path('data/transparent_unary_certs_484_491'))
    ap.add_argument('--indices', default='484,485,486,487,488,489,490,491')
    ap.add_argument('--cadical-timeout', type=int, default=600)
    ap.add_argument('--drat-timeout', type=int, default=600)
    args = ap.parse_args(); args.outdir.mkdir(parents=True, exist_ok=True)
    records = []
    for idx in [int(x) for x in args.indices.split(',') if x.strip()]:
        core_paths = sorted((args.cores_root / f'orbit{idx}').glob(f'orbit{idx}_cap*_core.json'))
        if not core_paths:
            records.append({'index': idx, 'status': 'missing_core'}); print('missing core', idx, flush=True); continue
        core = core_paths[0]
        idxdir = args.outdir / f'orbit{idx}'
        cmd = [
            'python', 'scripts/transparent_unary_dim2_cnf.py',
            '--core-json', str(core), '--outdir', str(idxdir), '--name', f'orbit{idx}_transparent',
            '--solve', '--cadical-timeout', str(args.cadical_timeout), '--drat-timeout', str(args.drat_timeout)
        ]
        rec = run(cmd, args.cadical_timeout + args.drat_timeout + 240)
        meta_path = idxdir / f'orbit{idx}_transparent.transparent_meta.json'
        meta = json.loads(meta_path.read_text()) if meta_path.exists() else None
        outrec = {
            'index': idx,
            'core_json': str(core),
            'command': cmd,
            'run': rec,
            'meta_path': str(meta_path),
            'verified': None if meta is None else bool(meta.get('drat_verified')),
            'cnf_vars': None if meta is None else meta.get('vars'),
            'cnf_clauses': None if meta is None else meta.get('clauses'),
            'cnf_sha256': None if meta is None else meta.get('cnf_sha256'),
            'drat_sha256': None if meta is None else meta.get('drat_sha256'),
            'cadical_returncode': None if meta is None else meta.get('cadical_returncode'),
            'drat_returncode': None if meta is None else meta.get('drat_returncode'),
            'elapsed_sec': rec['elapsed_sec'],
        }
        records.append(outrec)
        print('orbit', idx, 'verified', outrec['verified'], 'vars', outrec['cnf_vars'], 'clauses', outrec['cnf_clauses'], 'elapsed', rec['elapsed_sec'], flush=True)
    manifest = {
        'schema': 's0908_batch_transparent_unary_dim2_certs_v1',
        'meaning': 'Transparent unary-count CNF/DRAT verification for the eight dim-2 orbit exclusions 484--491. The encoder has an explicit prefix-counter lifting proof from any legal integer occupation vector to a satisfying assignment.',
        'cores_root': str(args.cores_root),
        'outdir': str(args.outdir),
        'records': records,
        'summary': {'total': len(records), 'verified': [r['index'] for r in records if r.get('verified') is True], 'failed': [r['index'] for r in records if r.get('verified') is not True]},
    }
    mpath = args.outdir / 'batch_transparent_unary_dim2_certs_manifest.json'
    mpath.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'ok', 'manifest': str(mpath), 'summary': manifest['summary']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
