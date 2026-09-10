#!/usr/bin/env python3
"""Augment the rep2 Wang-support CNF with transported ruling-line clauses.

The analysis proof excludes the fixed prefix [1,2,3].  By the Segre-grid ruling
geometry and Wang-LUT equivariance, this gives 98 forbidden rank-1 triples
(ruling lines).  For the rep2 adjacent-pair prefix [1,2], these simplify to
1 unit, 10 binary, and 87 ternary clauses on the 509 candidate A-points.

This script imports an existing rep2 witness-subset CNF/provenance seed,
revalidates it through the repaired analysis validator, adds ruling-line clauses
that are not already present, and solves the augmented CNF.  It records clause
counts and, for SAT, scans the full Wang LUT for residual violations.

The output is an execution artifact for the finite-field support route.  UNSAT
would need DRAT replay and semantic binding before becoming a proof leaf.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import subprocess
import sys
import time
from typing import Dict, Iterable, List, Sequence, Set, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))

from witness_subset_separation import (  # noqa:E402
    load_lut,
    process_rep2,
    build_base_cnf,
    validate_and_reencode_learned_record,
    full_lut_violations,
    write_cnf,
    sha256_file,
    run_drat_trim,
)
from ruling_line_transport import all_ruling_triples, simplify_ruling, all_rank1_set  # noqa:E402


def run_cadical(cnf: pathlib.Path, proof: pathlib.Path | None, timeout_sec: int) -> dict:
    cmd = ['cadical', str(cnf)]
    if proof is not None:
        cmd.append(str(proof))
    t0 = time.time()
    try:
        cp = subprocess.run(cmd, text=True, capture_output=True, timeout=timeout_sec)
        return {
            'exit': int(cp.returncode),
            'elapsed_sec': round(time.time() - t0, 3),
            'stdout_tail': cp.stdout[-4000:],
            'stderr_tail': cp.stderr[-2000:],
        }
    except subprocess.TimeoutExpired as e:
        return {
            'exit': -1,
            'elapsed_sec': round(time.time() - t0, 3),
            'stdout_tail': (e.stdout or '')[-4000:] if isinstance(e.stdout, str) else '',
            'stderr_tail': (e.stderr or '')[-2000:] if isinstance(e.stderr, str) else '',
            'timeout': True,
        }


def parse_model_points(stdout: str, survivors: Sequence[int]) -> List[int]:
    inv = {i + 1: int(p) for i, p in enumerate(survivors)}
    selected: Set[int] = set()
    for line in stdout.splitlines():
        if line.startswith('v '):
            for x in line.split()[1:]:
                lit = int(x)
                if lit > 0 and lit in inv:
                    selected.add(inv[lit])
    return sorted(selected)


def load_seed_records(path: pathlib.Path, lut: Dict[int, int], fixed_prefix: Sequence[int],
                      survivors: Sequence[int], var_map: Dict[int, int]) -> List[dict]:
    records: List[dict] = []
    seen_points: Set[Tuple[int, ...]] = set()
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            raw = json.loads(line)
            rec = validate_and_reencode_learned_record(raw, lut, fixed_prefix, survivors, var_map, path)
            pts = tuple(sorted(int(p) for p in rec['points']))
            # The existing separator deduplicates by point subset; preserve that semantics.
            if pts in seen_points:
                continue
            seen_points.add(pts)
            records.append(rec)
    return records


def ruling_clauses_for_prefix(prefix: Sequence[int], var_map: Dict[int, int]) -> Tuple[List[List[int]], dict]:
    triples = all_ruling_triples()
    assert len(triples) == 98
    assert frozenset([1, 2, 3]) in triples
    r1 = all_rank1_set()
    assert len(r1) == 49
    for t in triples:
        assert t <= r1
    rc = simplify_ruling(triples, set(int(x) for x in prefix))
    clauses: List[List[int]] = []
    kind_counts = {'unit': 0, 'binary': 0, 'ternary': 0, 'skipped_not_variable': 0}
    for p in rc['unit']:
        if p in var_map:
            clauses.append([-var_map[p]])
            kind_counts['unit'] += 1
        else:
            kind_counts['skipped_not_variable'] += 1
    for a, b in rc['binary']:
        if a in var_map and b in var_map:
            clauses.append([-var_map[a], -var_map[b]])
            kind_counts['binary'] += 1
        else:
            kind_counts['skipped_not_variable'] += 1
    for a, b, c in rc['ternary']:
        if a in var_map and b in var_map and c in var_map:
            clauses.append([-var_map[a], -var_map[b], -var_map[c]])
            kind_counts['ternary'] += 1
        else:
            kind_counts['skipped_not_variable'] += 1
    meta = {
        'ruling_triples_total': 98,
        'simplified_counts': {
            'unit': len(rc['unit']),
            'binary': len(rc['binary']),
            'ternary': len(rc['ternary']),
            'contradictions': rc['contradictions'],
        },
        'encoded_counts': kind_counts,
        'unit_points': rc['unit'],
        'binary_pairs': [list(x) for x in rc['binary']],
        'ternary_clause_count': len(rc['ternary']),
    }
    return clauses, meta


def normalize_clause(cl: Sequence[int]) -> Tuple[int, ...]:
    return tuple(sorted(int(x) for x in cl))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed-learned-jsonl', required=True)
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--solve-time', type=int, default=900)
    ap.add_argument('--with-drat', action='store_true', help='write a CaDiCaL proof and replay if UNSAT')
    ap.add_argument('--drat-time', type=int, default=900)
    args = ap.parse_args()

    out = pathlib.Path(args.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    seed_path = pathlib.Path(args.seed_learned_jsonl)

    print(f'Loading LUT {args.lut}...')
    lut = load_lut(pathlib.Path(args.lut))
    print(f'  rows: {len(lut):,}')

    prefix = [1, 2]
    candidates = [p for p in range(1, 512) if p not in set(prefix)]
    info = process_rep2(lut, prefix, candidates)
    base_clauses, var_map, top_id, base_meta = build_base_cnf(info)
    survivors = [int(x) for x in info['survivors']]
    print(f'Base rep2: survivors={len(survivors)} target={info["target"]} clauses={len(base_clauses)} vars={top_id}')

    print(f'Importing and revalidating seed {seed_path}...')
    seed_records = load_seed_records(seed_path, lut, prefix, survivors, var_map)
    seed_clauses = [[int(x) for x in rec['lits']] for rec in seed_records]
    print(f'  seed records imported: {len(seed_records):,}')

    ruling_clauses, ruling_meta = ruling_clauses_for_prefix(prefix, var_map)
    existing = {normalize_clause(cl) for cl in base_clauses}
    existing.update(normalize_clause(cl) for cl in seed_clauses)
    new_ruling = [cl for cl in ruling_clauses if normalize_clause(cl) not in existing]
    duplicate_ruling = len(ruling_clauses) - len(new_ruling)
    print(f'Ruling clauses encoded={len(ruling_clauses)} new={len(new_ruling)} duplicate={duplicate_ruling}')

    clauses = list(base_clauses) + list(seed_clauses) + list(new_ruling)
    cnf = out / 'rep2_ruling_augmented.cnf'
    write_cnf(clauses, top_id, cnf)

    proof = out / 'rep2_ruling_augmented.drat' if args.with_drat else None
    print(f'Solving CNF: vars={top_id} clauses={len(clauses):,} proof={bool(proof)}')
    sol = run_cadical(cnf, proof, args.solve_time)
    if sol['exit'] == 10:
        status = 'SAT'
    elif sol['exit'] == 20:
        status = 'UNSAT'
    else:
        status = 'UNKNOWN'
    print(json.dumps({'status': status, 'exit': sol['exit'], 'elapsed_sec': sol['elapsed_sec']}, sort_keys=True))

    model_points = None
    viol_summary = None
    if status == 'SAT':
        model_points = parse_model_points(sol.get('stdout_tail', ''), survivors)
        # stdout_tail can omit a long model; rerun without proof and no timeout is not necessary if tail is enough for small CNF, but check size.
        if len(model_points) != int(info['target']):
            # Save stdout and parse from full? run_cadical retained only tail. Rerun quickly with full stdout capture.
            cp = subprocess.run(['cadical', str(cnf)], text=True, capture_output=True, timeout=max(60, args.solve_time))
            model_points = parse_model_points(cp.stdout, survivors)
        violations = list(full_lut_violations(lut, prefix, model_points, survivors))
        viol_summary = {
            'model_size': len(model_points),
            'support_size': len(set(prefix) | set(model_points)),
            'violation_count': len(violations),
            'max_excess': max([int(v['excess']) for v in violations], default=0),
            'by_residual_head': {},
            'first_violations': [],
        }
        counts = {}
        for v in violations:
            r = str(int(v['residual']))
            counts[r] = counts.get(r, 0) + 1
        viol_summary['by_residual_head'] = dict(sorted(counts.items(), key=lambda kv: int(kv[0]))[:20])
        viol_summary['first_violations'] = [
            {k: (list(val) if isinstance(val, tuple) else val) for k, val in v.items() if k != 'row_survivors'}
            for v in violations[:10]
        ]
        (out / 'sat_model_points.json').write_text(json.dumps(model_points, indent=2) + '\n')
        print(json.dumps({'model_size': len(model_points), 'violations': len(violations), 'max_excess': viol_summary['max_excess']}, sort_keys=True))

    drat = None
    if status == 'UNSAT' and proof is not None:
        print('Replaying DRAT...')
        drat = run_drat_trim(cnf, proof, timeout_sec=args.drat_time)
        print(json.dumps({'drat_exit': drat.get('exit'), 'drat_verified': drat.get('verified'), 'drat_sec': drat.get('elapsed_sec')}, sort_keys=True))

    seed_copy = out / 'seed_learned_clauses.jsonl'
    shutil.copyfile(seed_path, seed_copy)

    result = {
        'schema': 'rep2_ruling_augmented_v1',
        'status': status,
        'prefix': prefix,
        'target': int(info['target']),
        'candidate_count': len(candidates),
        'survivor_count': len(survivors),
        'base_meta': base_meta,
        'base_row_counts': {str(k): int(v) for k, v in info['row_counts'].items()},
        'base_clause_count': len(base_clauses),
        'seed_learned_jsonl': str(seed_path),
        'seed_learned_sha256': sha256_file(seed_path),
        'seed_imported_records': len(seed_records),
        'ruling_meta': ruling_meta,
        'ruling_total_clauses': len(ruling_clauses),
        'ruling_new_clause_count': len(new_ruling),
        'ruling_duplicate_clause_count': duplicate_ruling,
        'final_cnf': str(cnf),
        'final_cnf_sha256': sha256_file(cnf),
        'final_variables': top_id,
        'final_clauses': len(clauses),
        'cadical': sol,
        'model_points_path': str(out / 'sat_model_points.json') if model_points is not None else None,
        'violation_summary': viol_summary,
        'drat': drat,
        'proof_path': str(proof) if proof is not None else None,
        'proof_sha256': sha256_file(proof) if proof is not None and proof.exists() else None,
        'meaning': 'Rep2 adjacent-pair Wang-support CNF augmented by transported ruling-line exclusions from the verified [1,2,3] local branch. SAT means the partial constraints remain open and the model must still be full-LUT scanned; UNSAT with DRAT would be a proof-producing support exclusion candidate.',
    }
    (out / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'Saved {out / "summary.json"}')


if __name__ == '__main__':
    main()
