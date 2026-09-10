#!/usr/bin/env python3
"""Rank-1 geometry profile for the rep2 branch with ruling-line exclusions.

The verified local prefix [1,2,3] exclusion transports to every Fano ruling line
in the 7x7 rank-1 Segre grid.  For the adjacent-pair prefix [1,2], this gives
rank-1-only unit/binary/ternary clauses.  This script computes how much these
constraints reduce the possible rank-1 part of a rep2 support, alone and when
combined with residual-0/1 Wang graph edges among rank-1 candidates.

It also reports orbits of maximal patterns under Stab({1,2}) using the stored
analysis orbit partition; this is route-shaping evidence for possible rep2
stratification.
"""
from __future__ import annotations

import argparse
import itertools
import json
import pathlib
import pickle
import subprocess
import sys
import time
from typing import Dict, List, Sequence, Set, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))

from ruling_line_transport import all_ruling_triples, simplify_ruling, all_rank1_set  # noqa:E402
from witness_subset_separation import load_lut, process_rep2  # noqa:E402


def write_wcnf_hard_soft(path: pathlib.Path, nvars: int, hard: Sequence[Sequence[int]], soft_units: Sequence[int]) -> int:
    """Write weighted CNF: hard clauses weight top, soft unit x weight 1. Return top."""
    top = len(soft_units) + 1
    with path.open('w') as f:
        f.write(f'p wcnf {nvars} {len(hard) + len(soft_units)} {top}\n')
        for cl in hard:
            f.write(str(top) + ' ' + ' '.join(str(int(x)) for x in cl) + ' 0\n')
        for x in soft_units:
            f.write(f'1 {int(x)} 0\n')
    return top


def run_rc2(path: pathlib.Path, timeout_sec: int = 300) -> Tuple[str, int | None, List[int], str]:
    """Run PySAT RC2 on WCNF; return status, optimum selected count, positive vars, log."""
    code = r'''
import sys, json
from pysat.formula import WCNF
from pysat.examples.rc2 import RC2
w = WCNF(from_file=sys.argv[1])
with RC2(w, adapt=True, exhaust=True) as rc2:
    model = rc2.compute()
    if model is None:
        print(json.dumps({'status':'UNSAT'}))
    else:
        cost = int(rc2.cost)
        pos = sorted([int(x) for x in model if int(x)>0 and int(x)<=w.nv])
        print(json.dumps({'status':'OPTIMUM','cost':cost,'selected_count':w.nv-cost,'positive':pos}))
'''
    try:
        cp = subprocess.run([sys.executable, '-B', '-c', code, str(path)], text=True, capture_output=True, timeout=timeout_sec)
    except subprocess.TimeoutExpired as e:
        return 'TIMEOUT', None, [], (e.stdout or '') if isinstance(e.stdout, str) else ''
    log = (cp.stdout or '') + (cp.stderr or '')
    if cp.returncode != 0:
        return f'ERROR_{cp.returncode}', None, [], log[-4000:]
    lines = [ln for ln in cp.stdout.splitlines() if ln.strip().startswith('{')]
    if not lines:
        return 'NO_JSON', None, [], log[-4000:]
    data = json.loads(lines[-1])
    if data['status'] != 'OPTIMUM':
        return data['status'], None, [], log[-4000:]
    return 'OPTIMUM', int(data['selected_count']), [int(x) for x in data['positive']], log[-4000:]


def run_cadical_cnf(clauses: Sequence[Sequence[int]], nvars: int, timeout_sec: int = 60) -> bool:
    # Return True if SAT.
    import tempfile, os
    with tempfile.NamedTemporaryFile('w', suffix='.cnf', delete=False) as f:
        path = f.name
        f.write(f'p cnf {nvars} {len(clauses)}\n')
        for cl in clauses:
            f.write(' '.join(map(str, cl)) + ' 0\n')
    try:
        cp = subprocess.run(['cadical', path], text=True, capture_output=True, timeout=timeout_sec)
        return cp.returncode == 10
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


def max_with_rc2(var_points: Sequence[int], hard_point_clauses: Sequence[Sequence[int]], out_prefix: pathlib.Path, timeout: int) -> dict:
    var_map = {int(p): i + 1 for i, p in enumerate(var_points)}
    hard_vars = [[lit_sign * var_map[abs_lit]
                  for abs_lit, lit_sign in [(abs(int(x)), 1 if int(x) > 0 else -1) for x in cl]]
                 for cl in hard_point_clauses]
    # Simpler convert: input hard_point_clauses use signed point IDs.
    hard_vars = []
    for cl in hard_point_clauses:
        vc = []
        for x in cl:
            x = int(x)
            p = abs(x)
            if p in var_map:
                vc.append((1 if x > 0 else -1) * var_map[p])
            else:
                # A unit on non-variable point is either already fixed false or irrelevant; ignore satisfied none.
                pass
        if not vc:
            # Empty hard clause means impossible under the variable universe.
            hard_vars.append([])
        else:
            hard_vars.append(vc)
    wcnf = out_prefix.with_suffix('.wcnf')
    write_wcnf_hard_soft(wcnf, len(var_points), hard_vars, list(range(1, len(var_points) + 1)))
    status, opt, pos, log = run_rc2(wcnf, timeout)
    selected_points = [var_points[v - 1] for v in pos] if pos else []
    return {
        'wcnf': str(wcnf),
        'status': status,
        'opt_selected_candidates': opt,
        'opt_total_rank1_including_prefix': (opt + 2 if opt is not None else None),
        'selected_points': selected_points,
        'solver_log_tail': log,
        'hard_clause_count': len(hard_vars),
    }


def feasible_at_least(var_points: Sequence[int], hard_point_clauses: Sequence[Sequence[int]], bound: int, timeout: int = 60) -> bool:
    # Sinz/cardinality via PySAT for an exact check that >= bound is feasible.
    from pysat.card import CardEnc, EncType
    var_map = {int(p): i + 1 for i, p in enumerate(var_points)}
    clauses: List[List[int]] = []
    for cl in hard_point_clauses:
        vc = []
        for x in cl:
            x = int(x); p = abs(x)
            if p in var_map:
                vc.append((1 if x > 0 else -1) * var_map[p])
        clauses.append(vc)
    top = len(var_points)
    enc = CardEnc.atleast(lits=list(range(1, len(var_points) + 1)), bound=bound, top_id=top, encoding=EncType.seqcounter)
    clauses.extend([list(c) for c in enc.clauses])
    return run_cadical_cnf(clauses, int(enc.nv), timeout)


def rank1_ruling_clauses(prefix: Sequence[int], rank1_candidates: Set[int]) -> Tuple[List[List[int]], dict]:
    rc = simplify_ruling(all_ruling_triples(), set(prefix))
    clauses: List[List[int]] = []
    # signed point literals: -p means point p not selected
    for p in rc['unit']:
        if p in rank1_candidates:
            clauses.append([-p])
    for a, b in rc['binary']:
        if a in rank1_candidates and b in rank1_candidates:
            clauses.append([-a, -b])
    for a, b, c in rc['ternary']:
        if a in rank1_candidates and b in rank1_candidates and c in rank1_candidates:
            clauses.append([-a, -b, -c])
    return clauses, {
        'simplified': {'unit': len(rc['unit']), 'binary': len(rc['binary']), 'ternary': len(rc['ternary']), 'contradictions': rc['contradictions']},
        'encoded_rank1_clause_count': len(clauses),
        'unit_points': rc['unit'],
        'binary_pairs': [list(x) for x in rc['binary']],
    }


def orbit_signature(selected: Sequence[int], orbit_analysis: dict) -> Tuple[int, ...]:
    counts = []
    s = set(int(x) for x in selected)
    for o in orbit_analysis['orbits']:
        counts.append(len(s & set(int(x) for x in o['members'])))
    return tuple(counts)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--out-dir', default='data/rep2_rank1_ruling_profile')
    ap.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--orbit-analysis', default='data/matching/rep2_orbit_analysis.json')
    ap.add_argument('--timeout', type=int, default=300)
    args = ap.parse_args()

    out = pathlib.Path(args.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    prefix = [1, 2]
    r1 = all_rank1_set()
    rank1_cands = sorted(r1 - set(prefix))

    line_clauses, line_meta = rank1_ruling_clauses(prefix, set(rank1_cands))
    print(f'Rank1 candidates={len(rank1_cands)} ruling clauses={len(line_clauses)}')
    res_line = max_with_rc2(rank1_cands, line_clauses, out / 'ruling_only', args.timeout)
    print(json.dumps({'ruling_only_status': res_line['status'], 'opt_candidates': res_line['opt_selected_candidates'], 'opt_total': res_line['opt_total_rank1_including_prefix']}, sort_keys=True))

    print('Loading LUT and rep2 base graph for rank1 edge restriction...')
    lut = load_lut(pathlib.Path(args.lut))
    info = process_rep2(lut, prefix, [p for p in range(1, 512) if p not in set(prefix)])
    # Base graph edge clauses among rank1 candidates, point-literal format.
    base_r1_edges = []
    for (a, b), key in info['edge_key'].items():
        if int(a) in r1 and int(b) in r1 and int(a) in rank1_cands and int(b) in rank1_cands:
            base_r1_edges.append([-int(a), -int(b)])
    base_units = [[-int(p)] for p in info['vertex_key'] if int(p) in rank1_cands]
    combined = base_units + base_r1_edges + line_clauses
    print(f'Rank1 base units={len(base_units)} base_edges={len(base_r1_edges)} combined={len(combined)}')
    res_combined = max_with_rc2(rank1_cands, combined, out / 'base_ruling_rank1', args.timeout)
    print(json.dumps({'combined_status': res_combined['status'], 'opt_candidates': res_combined['opt_selected_candidates'], 'opt_total': res_combined['opt_total_rank1_including_prefix']}, sort_keys=True))

    feasible_table = []
    if res_combined['opt_selected_candidates'] is not None:
        opt = int(res_combined['opt_selected_candidates'])
        for b in range(max(0, opt - 2), min(len(rank1_cands), opt + 2) + 1):
            feasible_table.append({'selected_candidates_bound': b, 'feasible': feasible_at_least(rank1_cands, combined, b, timeout=60)})

    with open(args.orbit_analysis) as f:
        orbit_analysis = json.load(f)
    sig_line = orbit_signature(res_line.get('selected_points', []), orbit_analysis) if res_line.get('selected_points') else None
    sig_combined = orbit_signature(res_combined.get('selected_points', []), orbit_analysis) if res_combined.get('selected_points') else None

    result = {
        'schema': 'rep2_rank1_ruling_profile_v1',
        'prefix': prefix,
        'rank1_candidate_count': len(rank1_cands),
        'line_meta': line_meta,
        'ruling_only_max': res_line,
        'base_graph_rank1': {
            'base_rank1_unit_count': len(base_units),
            'base_rank1_edge_count': len(base_r1_edges),
            'base_rep2_total_survivors': len(info['survivors']),
            'base_rep2_total_edges': len(info['edge_key']),
        },
        'base_plus_ruling_max': res_combined,
        'base_plus_ruling_feasible_at_least_table': feasible_table,
        'orbit_signature_order': [{'rep': int(o['rep']), 'rank': int(o['rank']), 'size': int(o['size'])} for o in orbit_analysis['orbits']],
        'ruling_only_orbit_signature': list(sig_line) if sig_line is not None else None,
        'base_plus_ruling_orbit_signature': list(sig_combined) if sig_combined is not None else None,
        'meaning': 'Maximum rank-1 candidates compatible with transported ruling-line triples, optionally with residual-0/1 Wang base graph restricted to rank-1 candidate variables. This profiles rep2 geometry; it is not a full support exclusion because higher-rank points are ignored.',
    }
    out_path = out / 'summary.json'
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'Saved {out_path}')


if __name__ == '__main__':
    main()
