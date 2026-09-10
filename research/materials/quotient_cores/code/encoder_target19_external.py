#!/usr/bin/env python3
"""External-CaDiCaL SAT witnesses for target-19 analysis CNF encoder.

This is the positive-direction check for the same Boolean-copy + PySAT
sequential-counter encoder used in the target-18 DRAT proof bundle.  For each
orbit, it builds the target-19 CNF through dim2_cnf_cert.py with
run_solver=False, solves it by external CaDiCaL with a witness file, decodes the
main copy variables back to integer multiplicities, and scans those counts
against independently regenerated occupation rows.
"""
from __future__ import annotations

import argparse
import json
import pickle
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))

from dim2_cnf_cert import build_cnf_for_orbit  # type: ignore
from dim2_independent_semantics import (  # type: ignore
    LUT_PATH, CACHE_PATH, rref_ind, independent_rows, popcount, file_sha256
)

INDICES = [484,485,486,487,488,489,490,491]
OUTDIR = Path('data/encoder_target19_external')


def load_lut_orbits():
    with LUT_PATH.open('rb') as f:
        data = pickle.load(f)
    lut = data['lut'] if isinstance(data, dict) and 'lut' in data else data
    with CACHE_PATH.open('rb') as f:
        cache = pickle.load(f)
    return lut, {int(o['cert_index']): o for o in cache['orbits']}


def singleton_ubs(rows: Sequence[Tuple[int,int]], target: int, npts: int) -> List[int]:
    ub = [target]*(npts+1)
    for mask, cap in rows:
        if popcount(mask) == 1:
            q = int(mask).bit_length()
            if int(cap) < ub[q]: ub[q] = int(cap)
    return ub


def var_to_q_from_ubs(ub: Sequence[int], target: int, npts: int) -> Dict[int,int]:
    out = {}
    vid = 1
    for q in range(1, npts+1):
        for _ in range(max(0, min(int(ub[q]), target))):
            out[vid] = q
            vid += 1
    return out


def parse_solution(path: Path) -> List[int]:
    vals = []
    text = path.read_text(errors='replace')
    for line in text.splitlines():
        line = line.strip()
        if not line or line[0] not in 'vV':
            continue
        for tok in line.split()[1:]:
            try:
                x = int(tok)
            except ValueError:
                continue
            if x == 0: continue
            vals.append(x)
    return vals


def scan_counts(counts: Sequence[int], rows: Sequence[Tuple[int,int]]) -> Dict:
    violations = []
    tight = 0
    max_excess = -10**9
    for ri,(mask,cap) in enumerate(rows):
        lhs = 0; m = int(mask)
        while m:
            low = m & -m
            i = low.bit_length()-1
            lhs += int(counts[i])
            m ^= low
        excess = lhs - int(cap)
        if excess > 0 and len(violations) < 20:
            violations.append({'row_index': ri, 'lhs': int(lhs), 'cap': int(cap), 'excess': int(excess), 'mask_popcount': popcount(mask)})
        if excess == 0: tight += 1
        if excess > max_excess: max_excess = excess
    return {'violations': len(violations), 'tight_rows': int(tight), 'max_excess': int(max_excess), 'violations_head': violations}


def solve_orbit(idx: int, target: int, outdir: Path, timeout: int, reuse_cnf: bool) -> Dict:
    lut, orbit_by_idx = load_lut_orbits()
    orb = orbit_by_idx[idx]
    W = rref_ind([int(x) for x in orb['basis']], 9)
    rows, row_meta = independent_rows(W, lut, target)
    npts = (1 << row_meta['quotient_dim']) - 1
    ub = singleton_ubs(rows, target, npts)
    var_to_q = var_to_q_from_ubs(ub, target, npts)
    outdir.mkdir(parents=True, exist_ok=True)
    rec_path = outdir / f'orbit_{idx}_target_{target}_certificate.json'
    if reuse_cnf and rec_path.exists():
        rec = json.loads(rec_path.read_text())
    else:
        rec = build_cnf_for_orbit(idx, target, outdir, False, timeout, 60)
    if rec.get('copy_variables') != len(var_to_q):
        raise AssertionError(f'copy variable mismatch orbit {idx}: record {rec.get("copy_variables")} mapping {len(var_to_q)}')
    cadical = shutil.which('cadical')
    if not cadical: raise RuntimeError('cadical not found')
    sol_path = outdir / f'orbit_{idx}_target_{target}.sol'
    log_path = outdir / f'orbit_{idx}_target_{target}_cadical_sat.log'
    cmd = [cadical, '-q', '--sat', '--binary=false', '-t', str(timeout), '-w', str(sol_path), str(rec['cnf_path'])]
    t0 = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout+60)
    elapsed = time.time() - t0
    log_path.write_text('CMD: '+' '.join(cmd)+'\n\nSTDOUT:\n'+proc.stdout+'\nSTDERR:\n'+proc.stderr)
    counts = None; witness = None
    if proc.returncode == 10 and sol_path.exists():
        vals = parse_solution(sol_path)
        true_main = [x for x in vals if x > 0 and x in var_to_q]
        counts = [0]*npts
        for x in true_main:
            counts[var_to_q[x]-1] += 1
        nz = [(i+1,int(c)) for i,c in enumerate(counts) if c]
        witness = {
            'solution_path': str(sol_path),
            'solution_sha256': file_sha256(sol_path),
            'positive_main_copy_count': len(true_main),
            'weight': int(sum(counts)),
            'nonzero_count': len(nz),
            'max_multiplicity': int(max(counts) if counts else 0),
            'support': nz,
            'scan_against_independent_rows': scan_counts(counts, rows),
        }
    out = {
        'schema': 'encoder_target19_external_orbit_v1',
        'cert_index': idx,
        'target': target,
        'W_basis': [int(x) for x in orb['basis']],
        'W_rref': list(W),
        'raw_lb': int(orb['raw_lb']),
        'row_meta': row_meta,
        'singleton_upper_bound_hist': {str(k): int(v) for k,v in sorted(__import__('collections').Counter(ub[1:]).items())},
        'cnf_path': rec['cnf_path'],
        'cnf_sha256': rec['cnf_sha256'],
        'cnf_variables': rec['cnf_variables'],
        'cnf_clauses': rec['cnf_clauses'],
        'copy_variables': rec['copy_variables'],
        'cadical': {'command': cmd, 'returncode': proc.returncode, 'elapsed_sec': elapsed, 'log_path': str(log_path), 'stdout_tail': proc.stdout[-2000:], 'stderr_tail': proc.stderr[-2000:]},
        'sat': proc.returncode == 10,
        'witness': witness,
        'ok': proc.returncode == 10 and witness is not None and witness['weight'] == target and witness['scan_against_independent_rows']['violations'] == 0,
    }
    out_path = outdir / f'orbit_{idx}_target19_external_sat_witness.json'
    out['record_path'] = str(out_path)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True)+'\n')
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--indices', default=','.join(map(str,INDICES)))
    ap.add_argument('--target', type=int, default=19)
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    ap.add_argument('--timeout', type=int, default=240)
    ap.add_argument('--reuse-cnf', action='store_true')
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    results = []
    t0 = time.time()
    for idx in [int(x) for x in args.indices.split(',') if x.strip()]:
        print(f'=== external target-{args.target} SAT orbit {idx} ===', flush=True)
        rec = solve_orbit(idx, args.target, args.outdir / f'orbit_{idx}', args.timeout, args.reuse_cnf)
        results.append(rec)
        print(json.dumps({'idx': idx, 'ok': rec['ok'], 'sat': rec['sat'], 'rc': rec['cadical']['returncode'], 'vars': rec['cnf_variables'], 'clauses': rec['cnf_clauses'], 'solve_sec': rec['cadical']['elapsed_sec'], 'weight': (rec['witness'] or {}).get('weight'), 'max_mult': (rec['witness'] or {}).get('max_multiplicity'), 'violations': ((rec['witness'] or {}).get('scan_against_independent_rows') or {}).get('violations')}, indent=2), flush=True)
    summary = {
        'schema': 'encoder_target19_external_summary_v1',
        'purpose': 'positive-direction SAT witnesses for the exact same target-18 certificate encoder, decoded and checked outside the CNF',
        'indices': [r['cert_index'] for r in results],
        'target': args.target,
        'all_ok': all(r['ok'] for r in results),
        'all_sat': all(r['sat'] for r in results),
        'all_decoded_witnesses_pass_rows': all(((r.get('witness') or {}).get('scan_against_independent_rows') or {}).get('violations') == 0 for r in results),
        'max_multiplicities': {str(r['cert_index']): (r.get('witness') or {}).get('max_multiplicity') for r in results},
        'result_paths': [r['record_path'] for r in results],
        'elapsed_sec': time.time() - t0,
    }
    out = args.outdir / 'summary.json'
    out.write_text(json.dumps(summary, indent=2, sort_keys=True)+'\n')
    print('SUMMARY')
    print(json.dumps(summary, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
