#!/usr/bin/env python3
"""Fairly solve a stored witness-subset seed CNF and bind the result to provenance.

This script is for the Wang-F2 support proof pipeline.  Some analysis runs ended
as SOLVER_UNKNOWN at a final round CNF that already contains all learned clauses
from the preceding SAT-separated rounds, but the summary did not expose that CNF
as current_cnf.  The k=5 idx13 case showed that such a seed can already be
UNSAT if CaDiCaL is given a longer fair solve.

For a fixed seed run directory, this script:
  * loads base_metadata.json and learned_clauses.jsonl;
  * selects an input CNF (explicit --cnf, current/final CNF from summary, or the
    last round CNF named in round_log);
  * verifies exact regeneration of the CNF from base + learned clauses;
  * solves the same CNF with CaDiCaL without adding mathematical constraints;
  * if SAT, scans the decoded support against the complete Wang LUT;
  * if UNSAT, reruns CaDiCaL with proof tracing and replays DRAT with drat-trim.

A verified UNSAT result closes only the fixed anchored stratum encoded by the
seed run; the external proof layers (Wang LUT, branch universe, orbit cover) are
not re-proved here.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import sys
import time
from collections import defaultdict
from typing import List, Optional, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))

from graph_coloring_certificate import load_lut  # noqa:E402
from verify_witness_subset_cnf import (  # noqa:E402
    read_jsonl, read_cnf, verify_structure, verify_base, verify_learned, regenerate_cnf,
)
from witness_subset_separation import (  # noqa:E402
    write_cnf, run_cadical, run_drat_trim, parse_model_from_log, full_lut_violations, sha256_file,
)


def resolve_seed_cnf(seed_dir: pathlib.Path, summary: dict, explicit: str) -> pathlib.Path:
    if explicit:
        p = pathlib.Path(explicit)
        if not p.exists():
            raise FileNotFoundError(p)
        return p
    for key in ('current_cnf', 'final_cnf'):
        v = summary.get(key)
        if v:
            p = pathlib.Path(v)
            if p.exists():
                return p
    # analysis SOLVER_UNKNOWN summaries retain the final attempted CNF in the
    # last round_log item, even though current_cnf is absent.
    round_log = summary.get('round_log') or []
    if round_log:
        v = round_log[-1].get('cnf')
        if v:
            p = pathlib.Path(v)
            if p.exists():
                return p
    raise FileNotFoundError(f'could not infer CNF in {seed_dir}')


def compact_violations(violations: List[dict]) -> Tuple[dict, List[dict]]:
    by_res = defaultdict(int)
    by_excess = defaultdict(int)
    for v in violations:
        by_res[str(int(v['residual']))] += 1
        by_excess[str(int(v['excess']))] += 1
    head = []
    for v in violations[:20]:
        rec = {}
        for k, vv in v.items():
            if k == 'row_survivors':
                continue
            if isinstance(vv, tuple):
                rec[k] = list(vv)[:30]
            else:
                rec[k] = vv
        head.append(rec)
    return {
        'count': len(violations),
        'max_excess': max((int(v['excess']) for v in violations), default=0),
        'by_residual': dict(sorted(by_res.items(), key=lambda kv: int(kv[0]))),
        'by_excess': dict(sorted(by_excess.items(), key=lambda kv: int(kv[0]))),
    }, head


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed-run-dir', required=True)
    ap.add_argument('--cnf', default='', help='optional explicit seed CNF path')
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--solve-time', type=int, default=1200)
    ap.add_argument('--drat-solve-time', type=int, default=1200)
    ap.add_argument('--drat-time', type=int, default=1800)
    ap.add_argument('--copy-cnf', action='store_true', help='deprecated: the script always solves a writable copy in out-dir')
    ap.add_argument('--use-regenerated-cnf', action='store_true',
                    help='solve a freshly regenerated CNF from base_metadata.json + learned_clauses.jsonl instead of requiring an existing seed CNF; useful for partial runs killed after a SAT-separated round')
    args = ap.parse_args()

    seed_dir = pathlib.Path(args.seed_run_dir)
    out_dir = pathlib.Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    base_path = seed_dir / 'base_metadata.json'
    learned_path = seed_dir / 'learned_clauses.jsonl'
    summary_path = seed_dir / 'summary.json'
    base = json.loads(base_path.read_text())
    learned = read_jsonl(learned_path)
    summary = json.loads(summary_path.read_text()) if summary_path.exists() else {}
    seed_cnf = None if args.use_regenerated_cnf else resolve_seed_cnf(seed_dir, summary, args.cnf)

    print(f'Loading LUT {args.lut}...')
    lut = load_lut(pathlib.Path(args.lut))
    print(f'  rows: {len(lut):,}')

    # Bind the CNF to the mathematical/provenance records before interpreting any solve.
    structure_check = verify_structure(base, lut)
    base_check = verify_base(base, lut)
    learned_check = verify_learned(base, learned, lut)
    regen_top, regen_clauses = regenerate_cnf(base, learned)

    # Always solve a writable CNF in out_dir.  run_cadical writes logs and DRATs
    # beside the CNF; the seed directory may be read-only inside bg_task.
    solve_cnf = out_dir / 'seed.cnf'
    first_mismatch = None
    if args.use_regenerated_cnf:
        cnf_top, cnf_clauses = regen_top, regen_clauses
        exact = True
        write_cnf(regen_clauses, regen_top, solve_cnf)
        cnf_source = 'regenerated_from_base_and_learned_jsonl'
        seed_cnf_path = None
        seed_cnf_hash = None
    else:
        if seed_cnf is None:
            raise FileNotFoundError(f'no seed CNF for {seed_dir}')
        cnf_top, cnf_clauses = read_cnf(seed_cnf)
        exact = cnf_top == regen_top and cnf_clauses == regen_clauses
        if not exact:
            for i, (a, b) in enumerate(zip(cnf_clauses, regen_clauses)):
                if a != b:
                    first_mismatch = {'index': i, 'cnf': a, 'regen': b}
                    break
            if first_mismatch is None:
                first_mismatch = {'index': min(len(cnf_clauses), len(regen_clauses)), 'reason': 'length or top mismatch'}
        shutil.copyfile(seed_cnf, solve_cnf)
        cnf_source = 'copied_existing_seed_cnf'
        seed_cnf_path = str(seed_cnf)
        seed_cnf_hash = sha256_file(seed_cnf)

    provenance_ok = (structure_check.get('structure_ok', False) and
                     base_check['base_edge_bad_count'] == 0 and
                     base_check['vertex_bad_count'] == 0 and
                     learned_check['learned_bad_count'] == 0 and exact)

    result = {
        'schema': 'fair_seed_solve_v1',
        'seed_run_dir': str(seed_dir),
        'seed_summary_status': summary.get('status'),
        'seed_cnf': seed_cnf_path,
        'seed_cnf_sha256': seed_cnf_hash,
        'solve_cnf': str(solve_cnf),
        'solve_cnf_sha256': sha256_file(solve_cnf),
        'cnf_source': cnf_source,
        'copy_cnf': True,
        'branch': base.get('branch'),
        'idx': base.get('idx'),
        'k': base.get('k'),
        'fixed_prefix': [int(x) for x in base.get('fixed_prefix', [])],
        'target': int(base.get('target')),
        'survivor_count': int(base.get('survivor_count')),
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
        'provenance_ok': provenance_ok,
    }
    if not provenance_ok:
        result['status'] = 'PROVENANCE_FAILED'
        (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
        print(json.dumps({'status': result['status'], 'exact_sequence_match': exact}, sort_keys=True))
        raise SystemExit(1)

    sol = run_cadical(solve_cnf, args.solve_time, with_drat=False)
    result['initial_solve'] = {
        'cadical_exit': sol['exit'],
        'cadical_sec': round(sol['elapsed_sec'], 2),
        'log': sol.get('log'),
        'sat': sol.get('sat'),
        'unsat': sol.get('unsat'),
        'has_model': sol.get('has_model'),
    }

    if sol['sat'] and sol['has_model']:
        survivors = [int(x) for x in base['base']['survivors']]
        var_map = {p: i + 1 for i, p in enumerate(survivors)}
        selected = parse_model_from_log(pathlib.Path(sol['log']), var_map)
        fixed_prefix = [int(x) for x in base['fixed_prefix']]
        t0 = time.time()
        violations = list(full_lut_violations(lut, fixed_prefix, selected or [], survivors))
        scan_summary, head = compact_violations(violations)
        result.update({
            'status': 'SAT',
            'selected_size': None if selected is None else len(selected),
            'support_size': None if selected is None else len(set(fixed_prefix) | set(selected)),
            'selected': selected,
            'full_lut_violations': scan_summary,
            'violations_head': head,
            'scan_sec': round(time.time() - t0, 2),
            'meaning': 'SAT model is a support satisfying only the encoded seed CNF; listed violations show why it is not Wang-admissible if count>0.',
        })
    elif sol['unsat']:
        result['status'] = 'UNSAT_NO_PROOF_YET'
        drat_sol = run_cadical(solve_cnf, args.drat_solve_time, with_drat=True)
        trim = {'verified': False, 'reason': 'drat-producing solve did not return UNSAT'}
        if drat_sol['unsat'] and drat_sol.get('drat'):
            trim = run_drat_trim(solve_cnf, pathlib.Path(drat_sol['drat']), args.drat_time)
        result.update({
            'status': 'UNSAT_VERIFIED' if trim.get('verified') else 'UNSAT_UNVERIFIED_DRAT',
            'drat_cadical_exit': drat_sol['exit'],
            'drat_cadical_sec': round(drat_sol['elapsed_sec'], 2),
            'drat': drat_sol.get('drat'),
            'drat_sha256': sha256_file(pathlib.Path(drat_sol['drat'])) if drat_sol.get('drat') else None,
            'drat_trim': trim,
            'meaning': 'Verified UNSAT closes the fixed encoded stratum only; it does not by itself prove the global rank lower bound.',
        })
    else:
        result['status'] = 'SOLVER_UNKNOWN'

    (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'status': result['status'],
        'idx': result.get('idx'),
        'k': result.get('k'),
        'cnf_clauses': len(cnf_clauses),
        'initial_cadical_exit': result['initial_solve']['cadical_exit'],
        'initial_cadical_sec': result['initial_solve']['cadical_sec'],
        'drat_verified': result.get('drat_trim', {}).get('verified'),
        'violations': result.get('full_lut_violations', {}).get('count'),
    }, sort_keys=True))
    if result['status'] in ('PROVENANCE_FAILED', 'UNSAT_UNVERIFIED_DRAT'):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
