#!/usr/bin/env python3
"""Extract and map DRAT unsat cores for the eight dim-2 CNF certificates.

For each stored CNF/DRAT pair, drat-trim can emit an input-clause core.  This
script regenerates the CNF clauses together with their mathematical origins:
  * global cardinality sum x_q <= target / >= target;
  * one encoded Wang occupation row (mask, cap) from the independently rebuilt
    quotient row system.
It then maps the emitted core clauses back to these origins and writes a compact
manifest of which Wang rows are actually used by the checked proof.

The core is the drat-trim backward core, not guaranteed irreducible.  It is still
a much smaller auditable manifest of the finite nodes touched by the proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from dim2_independent_semantics import (  # type: ignore
    LUT_PATH, CACHE_PATH, rref_ind, independent_rows, popcount, file_sha256
)
from dim2_cnf_cert import atmost_clauses, atleast_clauses  # type: ignore
from pysat.formula import IDPool  # type: ignore

CERT_DIR = Path("data/dim2_cnf_cert_all")
OUTDIR = Path("data/dim2_core_manifests")
INDICES = [484,485,486,487,488,489,490,491]


def load_lut_orbits():
    with LUT_PATH.open('rb') as f:
        data = pickle.load(f)
    lut = data['lut'] if isinstance(data, dict) and 'lut' in data else data
    with CACHE_PATH.open('rb') as f:
        cache = pickle.load(f)
    return lut, {int(o['cert_index']): o for o in cache['orbits']}


def clause_key(clause: Sequence[int]) -> Tuple[int,...]:
    # drat-trim may print core clauses with literals reordered.  Use the
    # sorted literal set; duplicate identical clauses are still tracked by a
    # queue.
    return tuple(sorted(int(x) for x in clause))


def parse_dimacs_clauses(path: Path) -> List[Tuple[int,...]]:
    clauses = []
    with path.open() as f:
        acc = []
        for line in f:
            line = line.strip()
            if not line or line[0] in 'cp':
                continue
            for tok in line.split():
                lit = int(tok)
                if lit == 0:
                    clauses.append(tuple(acc)); acc = []
                else:
                    acc.append(lit)
        if acc:
            raise ValueError(f"unterminated clause in {path}")
    return clauses


def regenerate_with_origins(idx: int, target: int):
    lut, orbit_by_idx = load_lut_orbits()
    orb = orbit_by_idx[idx]
    W = rref_ind([int(x) for x in orb['basis']], 9)
    rows, row_meta = independent_rows(W, lut, target)
    k = row_meta['quotient_dim']
    npts = (1 << k) - 1
    ub = [target] * (npts + 1)
    for row_i, (mask, cap) in enumerate(rows):
        if popcount(mask) == 1:
            q = int(mask).bit_length()
            if int(cap) < ub[q]:
                ub[q] = int(cap)
    pool = IDPool()
    copies = {q: [pool.id(f"x_{q}_{j}") for j in range(1, max(0, min(ub[q], target)) + 1)] for q in range(1, npts+1)}
    clauses: List[List[int]] = []
    origins: List[dict] = []
    all_lits = [lit for q in range(1,npts+1) for lit in copies[q]]
    for c in atmost_clauses(all_lits, target, pool):
        clauses.append(c); origins.append({'kind': 'global_atmost_sum_le_target'})
    for c in atleast_clauses(all_lits, target, pool):
        clauses.append(c); origins.append({'kind': 'global_atleast_sum_ge_target'})
    seen = set()
    encoded_rows = []
    for row_i, (mask, cap) in enumerate(rows):
        lits = []
        m = int(mask)
        while m:
            low = m & -m
            q = low.bit_length()
            lits.extend(copies[q])
            m ^= low
        lits = sorted(set(lits))
        if cap < 0:
            clauses.append([])
            origins.append({'kind': 'wang_row', 'row_index': row_i, 'mask': int(mask), 'cap': int(cap), 'quotient_popcount': popcount(mask), 'expanded_lits': len(lits), 'empty': True})
            continue
        if len(lits) <= int(cap):
            continue
        key = (tuple(lits), int(cap))
        if key in seen:
            continue
        seen.add(key)
        generated = atmost_clauses(lits, int(cap), pool)
        row_origin = {'kind': 'wang_row', 'row_index': row_i, 'mask': int(mask), 'cap': int(cap), 'quotient_popcount': popcount(mask), 'quotient_subspace_dim': popcount(mask).bit_length(), 'expanded_lits': len(lits), 'n_clauses': len(generated)}
        encoded_rows.append(row_origin)
        for c in generated:
            clauses.append(c); origins.append(row_origin)
    nvars = pool.top
    h = hashlib.sha256()
    header = f"p cnf {nvars} {len(clauses)}\n".encode()
    h.update(header)
    for c in clauses:
        h.update((" ".join(str(int(x)) for x in c) + " 0\n").encode())
    return clauses, origins, {'nvars': nvars, 'nclauses': len(clauses), 'cnf_sha256': h.hexdigest(), 'row_meta': row_meta, 'encoded_rows': len(encoded_rows)}


def write_core_for_orbit(idx: int, timeout: int, outdir: Path) -> dict:
    rec_path = CERT_DIR / f'orbit_{idx}' / f'orbit_{idx}_target_18_certificate.json'
    cert = json.loads(rec_path.read_text())
    cnf = Path(cert['cnf_path']); proof = Path(cert['cadical']['proof_path'])
    orbit_out = outdir / f'orbit_{idx}'
    orbit_out.mkdir(parents=True, exist_ok=True)
    core_cnf = orbit_out / f'orbit_{idx}_core.cnf'
    core_lemmas = orbit_out / f'orbit_{idx}_core_lemmas.drat'
    log_path = orbit_out / f'orbit_{idx}_drat_core.log'
    drat_trim = shutil.which('drat-trim')
    cmd = [drat_trim, str(cnf), str(proof), '-c', str(core_cnf), '-l', str(core_lemmas)]
    t0 = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    elapsed = time.time() - t0
    log_path.write_text('CMD: ' + ' '.join(cmd) + '\n\nSTDOUT:\n' + proc.stdout + '\nSTDERR:\n' + proc.stderr)

    clauses, origins, regen = regenerate_with_origins(idx, 18)
    if regen['cnf_sha256'] != cert['cnf_sha256']:
        raise AssertionError(f"regenerated CNF hash mismatch orbit {idx}: {regen['cnf_sha256']} vs {cert['cnf_sha256']}")
    origin_queues: Dict[Tuple[int,...], deque] = defaultdict(deque)
    for i, c in enumerate(clauses):
        origin_queues[clause_key(c)].append((i+1, origins[i]))  # DIMACS clauses are 1-indexed
    core_clauses = parse_dimacs_clauses(core_cnf) if core_cnf.exists() else []
    mapped = []
    missing = 0
    kind_counts = Counter()
    row_clause_counts = Counter()
    row_details = {}
    for c in core_clauses:
        q = origin_queues.get(c)
        if not q:
            # Try normalized clause as fallback; should not be needed.
            missing += 1
            continue
        clause_no, origin = q.popleft()
        kind_counts[origin['kind']] += 1
        if origin['kind'] == 'wang_row':
            ri = int(origin['row_index'])
            row_clause_counts[ri] += 1
            if ri not in row_details:
                row_details[ri] = origin
        mapped.append(clause_no)
    row_manifest_path = orbit_out / f'orbit_{idx}_core_wang_rows.jsonl'
    with row_manifest_path.open('w') as f:
        for ri in sorted(row_details):
            item = dict(row_details[ri])
            item['core_clause_count'] = int(row_clause_counts[ri])
            f.write(json.dumps(item, sort_keys=True) + '\n')
    summary = {
        'cert_index': idx,
        'target': 18,
        'certificate_record': str(rec_path),
        'cnf_path': str(cnf),
        'proof_path': str(proof),
        'cnf_sha256': cert['cnf_sha256'],
        'proof_sha256': cert['cadical']['proof_sha256'],
        'drat_core_command': cmd,
        'drat_trim_returncode': proc.returncode,
        'drat_verified': proc.returncode == 0 and ('VERIFIED' in proc.stdout or 'VERIFIED' in proc.stderr),
        'elapsed_sec': elapsed,
        'core_cnf_path': str(core_cnf),
        'core_cnf_sha256': file_sha256(core_cnf) if core_cnf.exists() else None,
        'core_cnf_size_bytes': core_cnf.stat().st_size if core_cnf.exists() else 0,
        'core_lemmas_path': str(core_lemmas),
        'core_lemmas_sha256': file_sha256(core_lemmas) if core_lemmas.exists() else None,
        'core_lemmas_size_bytes': core_lemmas.stat().st_size if core_lemmas.exists() else 0,
        'log_path': str(log_path),
        'regenerated_cnf_sha256': regen['cnf_sha256'],
        'regenerated_nvars': regen['nvars'],
        'regenerated_nclauses': regen['nclauses'],
        'core_input_clause_count': len(core_clauses),
        'mapped_core_clauses': len(mapped),
        'missing_core_clause_mappings': missing,
        'core_kind_counts': dict(kind_counts),
        'core_wang_row_count': len(row_details),
        'core_wang_rows_manifest': str(row_manifest_path),
        'core_wang_row_dim_hist': dict(Counter(str(row_details[ri].get('quotient_subspace_dim')) for ri in row_details)),
        'core_wang_row_cap_hist': dict(Counter(str(row_details[ri].get('cap')) for ri in row_details)),
        'ok': proc.returncode == 0 and ('VERIFIED' in proc.stdout or 'VERIFIED' in proc.stderr) and missing == 0,
    }
    (orbit_out / f'orbit_{idx}_core_summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    return summary


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--indices', default=','.join(map(str, INDICES)))
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    ap.add_argument('--timeout', type=int, default=900)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    results = []
    for idx in [int(x) for x in args.indices.split(',') if x.strip()]:
        print(f"=== core manifest orbit {idx} ===", flush=True)
        rec = write_core_for_orbit(idx, args.timeout, args.outdir)
        results.append(rec)
        print(json.dumps({
            'idx': idx,
            'ok': rec['ok'],
            'core_input_clauses': rec['core_input_clause_count'],
            'core_wang_rows': rec['core_wang_row_count'],
            'core_kind_counts': rec['core_kind_counts'],
            'elapsed_sec': rec['elapsed_sec'],
        }, indent=2), flush=True)
    summary = {
        'schema': 'dim2_core_manifest_summary_v1',
        'indices': [r['cert_index'] for r in results],
        'all_ok': all(r['ok'] for r in results),
        'results': results,
    }
    out = args.outdir / 'core_manifest_summary.json'
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print('SUMMARY')
    print(json.dumps({'out': str(out), 'all_ok': summary['all_ok'], 'indices': summary['indices']}, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
