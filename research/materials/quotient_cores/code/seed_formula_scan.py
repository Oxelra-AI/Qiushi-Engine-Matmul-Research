#!/usr/bin/env python3
"""Solve and full-LUT scan a seed witness-subset CNF without extra promotion."""
from __future__ import annotations
import argparse, json, pathlib, shutil, sys, time
from collections import defaultdict

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from graph_coloring_certificate import load_lut  # noqa:E402
from witness_subset_separation import run_cadical, parse_model_from_log, full_lut_violations, sha256_file  # noqa:E402


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--run-dir', required=True)
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--solve-time', type=int, default=300)
    args = ap.parse_args()
    run_dir = pathlib.Path(args.run_dir)
    out_dir = pathlib.Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    base = json.loads((run_dir / 'base_metadata.json').read_text())
    summary = json.loads((run_dir / 'summary.json').read_text())
    cnf_path = pathlib.Path(summary.get('current_cnf') or summary.get('final_cnf'))
    if not cnf_path.exists():
        raise FileNotFoundError(cnf_path)
    solve_cnf_path = out_dir / 'seed_current_copy.cnf'
    shutil.copyfile(cnf_path, solve_cnf_path)
    survivors = [int(x) for x in base['base']['survivors']]
    var_map = {p: i + 1 for i, p in enumerate(survivors)}
    lut = load_lut(pathlib.Path(args.lut))
    sol = run_cadical(solve_cnf_path, args.solve_time, with_drat=False)
    result = {
        'schema': 'seed_formula_scan_v1',
        'seed_run_dir': str(run_dir),
        'seed_cnf': str(cnf_path),
        'solve_cnf_copy': str(solve_cnf_path),
        'seed_cnf_sha256': sha256_file(cnf_path),
        'cadical_exit': sol['exit'],
        'cadical_sec': round(sol['elapsed_sec'], 2),
    }
    if sol['sat'] and sol['has_model']:
        selected = parse_model_from_log(pathlib.Path(sol['log']), var_map)
        fixed_prefix = [int(x) for x in base['fixed_prefix']]
        t0 = time.time()
        violations = list(full_lut_violations(lut, fixed_prefix, selected or [], survivors))
        by_res = defaultdict(int)
        for v in violations:
            by_res[str(int(v['residual']))] += 1
        result.update({
            'status': 'SAT',
            'target': int(base['target']),
            'selected_size': None if selected is None else len(selected),
            'support_size': None if selected is None else len(set(fixed_prefix) | set(selected)),
            'selected': selected,
            'full_lut_violation_count': len(violations),
            'max_excess': max((int(v['excess']) for v in violations), default=0),
            'violations_by_residual': dict(sorted(by_res.items(), key=lambda kv: int(kv[0]))),
            'scan_sec': round(time.time() - t0, 2),
            'violations_head': [
                {k: (list(vv)[:20] if isinstance(vv, tuple) else vv) for k, vv in v.items() if k != 'row_survivors'}
                for v in violations[:20]
            ],
        })
    elif sol['unsat']:
        result['status'] = 'UNSAT'
    else:
        result['status'] = 'SOLVER_UNKNOWN'
    (out_dir / 'summary.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'status': result['status'],
        'selected_size': result.get('selected_size'),
        'violations': result.get('full_lut_violation_count'),
        'max_excess': result.get('max_excess'),
        'cadical_sec': result['cadical_sec'],
    }, sort_keys=True))

if __name__ == '__main__':
    main()
