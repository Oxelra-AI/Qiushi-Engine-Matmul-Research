#!/usr/bin/env python3
"""Profile symmetry-marked subbranches of the rep2 adjacent-pair branch.

Rep2 fixes the adjacent rank-1 pair {E11,E12} = {1,2}.  The stabilizer of this
set has 17 orbits on the remaining 509 projective A-points.  Any completion of
rep2 selects 18 such points; marking one selected point and applying the pair
stabilizer puts it into one of these 17 representatives.  Thus, if every branch
with prefix {1,2,rep} is excluded, rep2 is excluded.

This script profiles those marked branches using the same Wang residual-0/1 base
encoding as the witness-subset separator.  It can also solve the base graph CNF
and scan the returned model against the complete LUT.  SAT scans are candidate
information only; UNSAT without DRAT is not counted as a closed branch.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys
import time
from collections import defaultdict
from typing import Dict, List

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))

from graph_coloring_certificate import load_lut  # noqa:E402
from witness_subset_separation import (  # noqa:E402
    process_rep2, build_base_cnf, write_cnf, run_cadical, run_drat_trim,
    parse_model_from_log, full_lut_violations, sha256_file,
)


def load_orbit_reps(path: pathlib.Path) -> List[dict]:
    data = json.loads(path.read_text())
    return [{
        'rep': int(o['rep']),
        'size': int(o['size']),
        'rank': int(o['rank']),
        'members_head': [int(x) for x in o.get('members', [])[:20]],
    } for o in data['orbits']]


def viol_summary(violations: List[dict]) -> dict:
    by_res = defaultdict(int)
    by_excess = defaultdict(int)
    for v in violations:
        by_res[str(int(v['residual']))] += 1
        by_excess[str(int(v['excess']))] += 1
    return {
        'count': len(violations),
        'max_excess': max((int(v['excess']) for v in violations), default=0),
        'by_residual': dict(sorted(by_res.items(), key=lambda kv: int(kv[0]))),
        'by_excess': dict(sorted(by_excess.items(), key=lambda kv: int(kv[0]))),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--orbit-analysis', default='workspace/data/matching/rep2_orbit_analysis.json')
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--reps', default='', help='comma-separated orbit representatives; empty means all 17')
    ap.add_argument('--solve-time', type=int, default=60)
    ap.add_argument('--with-drat', action='store_true', help='for base-graph UNSAT, rerun CaDiCaL with proof and replay')
    ap.add_argument('--drat-solve-time', type=int, default=600)
    ap.add_argument('--drat-time', type=int, default=900)
    args = ap.parse_args()

    out_dir = pathlib.Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    orbits = load_orbit_reps(pathlib.Path(args.orbit_analysis))
    wanted = None
    if args.reps.strip():
        wanted = {int(x) for x in args.reps.replace(';', ',').split(',') if x.strip()}
        orbits = [o for o in orbits if o['rep'] in wanted]
        if {o['rep'] for o in orbits} != wanted:
            raise SystemExit(f'missing reps {sorted(wanted - {o["rep"] for o in orbits})}')

    print(f'Loading LUT {args.lut}...')
    lut = load_lut(pathlib.Path(args.lut))
    print(f'  rows: {len(lut):,}')

    results = []
    for oi, orb in enumerate(orbits):
        rep = int(orb['rep'])
        prefix = [1, 2, rep]
        candidates = sorted(m for m in range(1, 512) if m not in set(prefix))
        sub = out_dir / f'rep_{rep:03d}'
        sub.mkdir(parents=True, exist_ok=True)
        print(f'\n[{oi+1}/{len(orbits)}] prefix={prefix} orbit_size={orb["size"]} rank={orb["rank"]}')
        t0 = time.time()
        info = process_rep2(lut, prefix, candidates)
        profile_sec = time.time() - t0
        rec = {
            'schema': 'rep2_marked_branch_profile_item_v1',
            'rep': rep,
            'orbit_size': orb['size'],
            'rep_matrix_rank': orb['rank'],
            'prefix': prefix,
            'candidate_count': len(candidates),
            'target': int(info['target']),
            'survivor_count': len(info.get('survivors', [])),
            'edge_count': len(info.get('edge_key', {})),
            'vertex_exclusion_count': len(info.get('vertex_key', {})),
            'impossible_row_count': len(info.get('impossible_rows', [])),
            'row_counts': info.get('row_counts', {}),
            'profile_sec': round(profile_sec, 2),
        }
        if info.get('impossible_rows'):
            rec['status'] = 'FIXED_PREFIX_VIOLATES'
            rec['violating_row'] = info['impossible_rows'][0]
            print(f'  direct fixed-prefix violation after {profile_sec:.1f}s')
            (sub / 'profile.json').write_text(json.dumps(rec, indent=2, sort_keys=True) + '\n')
            results.append(rec)
            continue
        clauses, var_map, top_id, base_meta = build_base_cnf(info)
        base_payload = {
            'schema': 'rep2_marked_branch_base_v1',
            'prefix': prefix,
            'rep': rep,
            'orbit_size': orb['size'],
            'rep_matrix_rank': orb['rank'],
            'rank_budget': 20,
            'candidate_count': len(candidates),
            'candidate_universe': candidates,
            'target': int(info['target']),
            'survivor_count': len(info['survivors']),
            'base': base_meta,
        }
        (sub / 'base_metadata.json').write_text(json.dumps(base_payload, indent=2, sort_keys=True) + '\n')
        cnf_path = sub / 'base_graph.cnf'
        write_cnf(clauses, top_id, cnf_path)
        rec.update({
            'base_variables': top_id,
            'base_clauses': len(clauses),
            'base_cnf': str(cnf_path),
            'base_cnf_sha256': sha256_file(cnf_path),
        })
        sol = run_cadical(cnf_path, args.solve_time, with_drat=False)
        rec['base_solve'] = {
            'exit': sol['exit'],
            'elapsed_sec': round(sol['elapsed_sec'], 2),
            'sat': sol['sat'],
            'unsat': sol['unsat'],
            'has_model': sol['has_model'],
            'log': sol['log'],
        }
        if sol['unsat']:
            rec['status'] = 'BASE_GRAPH_UNSAT'
            if args.with_drat:
                drat_sol = run_cadical(cnf_path, args.drat_solve_time, with_drat=True)
                trim = {'verified': False, 'reason': 'drat-producing solve did not return UNSAT'}
                if drat_sol['unsat'] and drat_sol.get('drat'):
                    trim = run_drat_trim(cnf_path, pathlib.Path(drat_sol['drat']), args.drat_time)
                rec['drat_cadical_exit'] = drat_sol['exit']
                rec['drat_cadical_sec'] = round(drat_sol['elapsed_sec'], 2)
                rec['drat'] = drat_sol.get('drat')
                rec['drat_trim'] = trim
                rec['status'] = 'BASE_GRAPH_UNSAT_DRAT' if trim.get('verified') else 'BASE_GRAPH_UNSAT_NO_VERIFIED_DRAT'
            print(f'  base graph UNSAT; clauses={len(clauses)}')
        elif sol['sat'] and sol['has_model']:
            selected = parse_model_from_log(pathlib.Path(sol['log']), var_map)
            violations = list(full_lut_violations(lut, prefix, selected or [], info['survivors']))
            rec['status'] = 'BASE_GRAPH_SAT_SCANNED'
            rec['selected_size'] = None if selected is None else len(selected)
            rec['support_size'] = None if selected is None else len(set(prefix) | set(selected))
            rec['selected'] = selected
            rec['full_lut_violations'] = viol_summary(violations)
            rec['violations_head'] = [
                {k: (list(vv)[:20] if isinstance(vv, tuple) else vv) for k, vv in v.items() if k != 'row_survivors'}
                for v in violations[:10]
            ]
            print(f'  base graph SAT; survivors={rec["survivor_count"]} target={rec["target"]} violations={len(violations)}')
        else:
            rec['status'] = 'BASE_GRAPH_SOLVER_UNKNOWN'
            print(f'  base graph solver unknown')
        (sub / 'profile.json').write_text(json.dumps(rec, indent=2, sort_keys=True) + '\n')
        results.append(rec)
        summary = {'schema': 'rep2_marked_branch_profile_v1', 'records': results}
        (out_dir / 'summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')

    summary = {'schema': 'rep2_marked_branch_profile_v1', 'records': results}
    (out_dir / 'summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    closed_direct = sum(1 for r in results if r['status'] == 'FIXED_PREFIX_VIOLATES')
    closed_base = sum(1 for r in results if r['status'].startswith('BASE_GRAPH_UNSAT'))
    print(json.dumps({
        'records': len(results),
        'direct_fixed_prefix_violations': closed_direct,
        'base_graph_unsat': closed_base,
        'sat_or_unknown': len(results) - closed_direct - closed_base,
        'summary': str(out_dir / 'summary.json'),
    }, sort_keys=True))


if __name__ == '__main__':
    main()
