#!/usr/bin/env python3
"""Batch clause-level lifting verification for the eight transparent dim-2 CNFs.

This wraps analysis's per-file verifier.  It reconstructs each actual DIMACS
file from its source occupation core and the transparent prefix-counter clause
families, compares the reconstruction with the file, and records that the
forward lifting from any legal integer occupation vector applies to the same
clauses whose DRAT proof was replayed.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import time
from pathlib import Path

DEFAULT_BATCH = Path('data/transparent_unary_certs_484_491/batch_transparent_unary_dim2_certs_manifest.json')
DEFAULT_OUTDIR = Path('data/transparent_lifting_batch')
VERIFIER = Path('scripts/transparent_cnf_lifting_verifier.py')


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--batch-manifest', type=Path, default=DEFAULT_BATCH)
    ap.add_argument('--outdir', type=Path, default=DEFAULT_OUTDIR)
    ap.add_argument('--timeout', type=int, default=600)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    batch = json.loads(args.batch_manifest.read_text())
    t0 = time.time()
    records = []
    for rec in batch['records']:
        idx = int(rec['index'])
        meta = Path(rec['meta_path'])
        out = args.outdir / f'orbit{idx}_transparent_lifting_verifier.json'
        cmd = ['python', str(VERIFIER), '--meta', str(meta), '--out', str(out)]
        run = subprocess.run(cmd, text=True, capture_output=True, timeout=args.timeout)
        parsed = None
        if out.exists():
            parsed = json.loads(out.read_text())
        records.append({
            'index': idx,
            'meta_path': str(meta),
            'core_json': rec.get('core_json'),
            'cnf_sha256': rec.get('cnf_sha256'),
            'drat_sha256': rec.get('drat_sha256'),
            'cadical_returncode': rec.get('cadical_returncode'),
            'drat_returncode': rec.get('drat_returncode'),
            'transparent_verified': bool(rec.get('verified')),
            'verifier_command': cmd,
            'verifier_returncode': run.returncode,
            'verifier_stdout_tail': run.stdout[-2000:],
            'verifier_stderr_tail': run.stderr[-2000:],
            'verifier_out': str(out),
            'clauses_match_actual_file': None if parsed is None else bool(parsed.get('clauses_match_actual_file')),
            'auxiliary_ranges_disjoint_ordered': None if parsed is None else bool(parsed.get('auxiliary_ranges_disjoint_ordered')),
            'forward_lifting_established_for_file': None if parsed is None else bool(parsed.get('forward_lifting_established_for_file')),
            'vars': None if parsed is None else parsed.get('reconstructed_var_count'),
            'clauses': None if parsed is None else parsed.get('reconstructed_clause_count'),
            'source_row_sha256': None if parsed is None else parsed.get('source', {}).get('row_sha256'),
            'sample_total_failures': None if parsed is None else len(parsed.get('sample_checks', {}).get('total_clause_sample_failures', [])),
            'sample_row_failures': None if parsed is None else len(parsed.get('sample_checks', {}).get('local_row_zero_sample_failures', [])),
        })
    ok = [r['index'] for r in records if r['verifier_returncode'] == 0 and r['forward_lifting_established_for_file']]
    failed = [r['index'] for r in records if r['index'] not in ok]
    manifest = {
        'schema': 's0908_batch_transparent_lifting_verifier_v1',
        'meaning': 'Batch reconstruction and forward-lifting verification for the actual transparent unary-count CNF/DRAT files excluding dim-2 orbits 484--491.',
        'batch_manifest': str(args.batch_manifest),
        'per_file_verifier': str(VERIFIER),
        'records': records,
        'summary': {'total': len(records), 'ok': ok, 'failed': failed, 'all_ok': not failed},
        'elapsed_sec': time.time() - t0,
    }
    outpath = args.outdir / 'batch_transparent_lifting_verifier_manifest.json'
    outpath.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'ok', 'out': str(outpath), 'summary': manifest['summary'], 'elapsed_sec': manifest['elapsed_sec']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
