#!/usr/bin/env python3
"""Verify a regenerated seed witness-subset CNF against a seed run directory.

Use when an external solver run was performed on a copy/regeneration of a
witness-subset formula whose original run summary did not contain a final CNF
suitable for the hardened checker.  The script checks the same local proof
interface as verify_witness_subset_cnf.py: structure, base row
provenance, learned-row provenance, exact CNF sequence, and optional DRAT replay.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
import time
from typing import List, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from graph_coloring_certificate import load_lut  # noqa:E402
from verify_witness_subset_cnf import (  # noqa:E402
    read_jsonl, read_cnf, verify_structure, verify_base, verify_learned, regenerate_cnf,
)


def run_drat_trim(cnf: pathlib.Path, drat: pathlib.Path, timeout: int) -> dict:
    log_path = cnf.with_suffix('.seed_verify_drat_trim.log')
    t0 = time.time()
    try:
        with log_path.open('w') as f:
            proc = subprocess.run(['drat-trim', str(cnf), str(drat)], stdout=f, stderr=subprocess.STDOUT, text=True, timeout=timeout)
        text = log_path.read_text(errors='ignore')
        return {'exit': proc.returncode, 'elapsed_sec': round(time.time() - t0, 2), 'verified': proc.returncode == 0 and 'VERIFIED' in text, 'log': str(log_path)}
    except subprocess.TimeoutExpired:
        return {'exit': None, 'elapsed_sec': timeout, 'verified': False, 'timeout': True, 'log': str(log_path)}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed-run-dir', required=True)
    ap.add_argument('--cnf', required=True)
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--drat', default='')
    ap.add_argument('--drat-time', type=int, default=1800)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()

    seed_dir = pathlib.Path(args.seed_run_dir)
    cnf_path = pathlib.Path(args.cnf)
    base = json.loads((seed_dir / 'base_metadata.json').read_text())
    learned = read_jsonl(seed_dir / 'learned_clauses.jsonl')
    lut = load_lut(pathlib.Path(args.lut))

    structure_check = verify_structure(base, lut)
    base_check = verify_base(base, lut)
    learned_check = verify_learned(base, learned, lut)
    regen_top, regen_clauses = regenerate_cnf(base, learned)
    cnf_top, cnf_clauses = read_cnf(cnf_path)
    exact = cnf_top == regen_top and cnf_clauses == regen_clauses
    first_mismatch = None
    if not exact:
        for i, (a, b) in enumerate(zip(cnf_clauses, regen_clauses)):
            if a != b:
                first_mismatch = {'index': i, 'cnf': a, 'regen': b}
                break
        if first_mismatch is None:
            first_mismatch = {'index': min(len(cnf_clauses), len(regen_clauses)), 'reason': 'length or top mismatch'}

    drat_check = None
    if args.drat:
        drat_path = pathlib.Path(args.drat)
        drat_check = run_drat_trim(cnf_path, drat_path, args.drat_time) if drat_path.exists() else {'verified': False, 'reason': 'drat not found'}

    ok = (structure_check.get('structure_ok', False) and
          base_check['base_edge_bad_count'] == 0 and
          base_check['vertex_bad_count'] == 0 and
          learned_check['learned_bad_count'] == 0 and exact)
    if args.drat:
        ok = ok and bool(drat_check and drat_check.get('verified'))
    result = {
        'schema': 'verify_seed_cnf_v1',
        'seed_run_dir': str(seed_dir),
        'cnf': str(cnf_path),
        'status': 'verified' if ok else 'failed',
        'structure_check': structure_check,
        'base_check': base_check,
        'learned_check': learned_check,
        'cnf_check': {
            'cnf_variables': cnf_top,
            'cnf_clauses': len(cnf_clauses),
            'regenerated_variables': regen_top,
            'regenerated_clauses': len(regen_clauses),
            'exact_sequence_match': exact,
            'first_mismatch': first_mismatch,
        },
        'drat_replay': drat_check,
    }
    out_path = pathlib.Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'status': result['status'],
        'learned_checked': learned_check['learned_checked'],
        'exact_sequence_match': exact,
        'drat_verified': None if drat_check is None else drat_check.get('verified'),
        'cnf_clauses': len(cnf_clauses),
    }, sort_keys=True))
    if not ok:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
