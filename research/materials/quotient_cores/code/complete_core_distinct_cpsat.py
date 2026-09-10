#!/usr/bin/env python3
"""analysis: complete E11-core CP-SAT restricted to distinct projected A-directions.

analysis certified that any rank-19 E11-core decomposition over F2 must have
distinct projected A-directions.  This script therefore solves the remaining
A-side Wang feasibility problem with Boolean variables x_p in {0,1}, all
complete Wang occupation rows (except tautological ambient row), and contraction
lower bounds.  A FEASIBLE result is only an A-support candidate and must still
pass fixed-A B/C completion; an INFEASIBLE result from CP-SAT would still need a
proof-producing encoding for a theorem.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient
from complete_core_and_transversal import ROOT, build_core_constraints, complete_core_wang_scan, saturation_domains, transversal_failures
from quotient_rank_cuts import build_contractions, point_mask_for_q
from candidate_source_qcut_scan import eval_candidate_sources
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis

OUTDIR = ROOT / 'workspace/data/repeat_branch_certificate'
ALLMASK = (1 << 255) - 1


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}, payload.get('meta', {})


def load_hint(path: Path | None, round_index: int | None):
    if path is None or not path.exists():
        return None
    d = json.loads(path.read_text())
    rounds = d.get('rounds', [])
    if round_index is None:
        # choose lowest complete Wang violation distinct support
        best = None
        for r in rounds:
            A = r.get('support') or r.get('A_cols')
            if not A or len(A) != 19 or len(set(A)) != 19:
                continue
            val = r.get('complete_wang_violations', 10**9)
            if best is None or val < best[0]:
                best = (val, A)
        return None if best is None else [int(x) for x in best[1]]
    for r in rounds:
        if r.get('round') == round_index:
            A = r.get('support') or r.get('A_cols')
            return None if not A else [int(x) for x in A]
    return None


def main():
    from ortools.sat.python import cp_model
    ap = argparse.ArgumentParser()
    ap.add_argument('--solver-time', type=float, default=1800.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--seed', type=int, default=4747)
    ap.add_argument('--hint-source', type=Path, default=ROOT / 'workspace/data/unconditional_qcuts/fresh_uncond_sep_10r.json')
    ap.add_argument('--hint-round', type=int, default=None)
    ap.add_argument('--qcut-source', type=Path, default=None, help='optional learned unconditional qcuts to add')
    ap.add_argument('--out', type=Path, default=OUTDIR / 'complete_core_distinct_cpsat.json')
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    s = 19
    core = CoreQuotient(1)
    lut, lut_meta = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records, meta = build_core_constraints(core, lut)
    T = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    contractions = build_contractions(T)
    masks = {q: point_mask_for_q(q) for q in contractions}
    points = list(range(1, 256))

    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f'x_{p}') for p in points}
    model.Add(sum(x[p] for p in points) == s)

    wang_count = 0
    dim_counts = Counter()
    for rec in records:
        L = int(rec['L'])
        cap = s - L
        if cap >= s:
            continue
        pts = subspace_points_from_basis(unpack_basis(int(rec['key8'])))
        # empty dim-0 row is harmless; Add(sum([])<=0) is allowed but skip if no pts.
        if not pts:
            continue
        model.Add(sum(x[p] for p in pts) <= cap)
        wang_count += 1
        dim_counts[int(rec['dim8'])] += 1

    clb = 0
    for q, c in contractions.items():
        rk = int(c['rank'])
        if rk > 0:
            model.Add(sum(x[p] for p in points if ((q & p).bit_count() & 1)) >= rk)
            clb += 1

    qcut_count = 0
    if args.qcut_source and args.qcut_source.exists():
        src = json.loads(args.qcut_source.read_text())
        seen = set()
        for rnd in src.get('rounds', []):
            for c in rnd.get('learned_qcuts', []) or rnd.get('learned_quotient_cuts', []):
                q1, q2 = sorted([int(c['sources'][0]), int(c['sources'][1])])
                target = int(c['target']); side = str(c.get('side','?'))
                key = (side, q1, q2, target)
                if key in seen:
                    continue
                seen.add(key)
                req = int(c['requirement'])
                rhs = req + int(contractions[q1]['rank']) + int(contractions[q2]['rank'])
                source_union = masks[q1] | masks[q2]
                outside_mask = masks[target] & (~source_union) & ALLMASK
                terms = []
                for p in points:
                    coeff = 0
                    if (outside_mask >> (p-1)) & 1: coeff += 1
                    if ((q1 & p).bit_count() & 1): coeff += 1
                    if ((q2 & p).bit_count() & 1): coeff += 1
                    if coeff: terms.append(coeff*x[p])
                model.Add(sum(terms) >= rhs)
                qcut_count += 1

    hint = load_hint(args.hint_source, args.hint_round)
    hint_added = False
    if hint:
        hs = set(hint)
        for p in points:
            model.AddHint(x[p], 1 if p in hs else 0)
        hint_added = True

    build_sec = time.time() - t0
    print(f'Wang rows={wang_count} by_dim={dict(sorted(dim_counts.items()))} clb={clb} qcuts={qcut_count} build={build_sec:.1f}s hint={hint_added}')

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = int(args.workers)
    solver.parameters.random_seed = int(args.seed)
    ts = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - ts
    status_name = solver.StatusName(status)
    print(f'status={status_name} solve_sec={solve_sec:.1f}')

    result = {
        'schema': 'complete_core_distinct_cpsat_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': s,
        'meaning': 'Boolean complete-Wang A-side model after repeated-direction branch was certified impossible. FEASIBLE gives only an A-support candidate needing B/C completion; UNKNOWN leaves distinct branch open.',
        'constraint_summary': {
            'wang_rows': wang_count,
            'wang_by_dim': {str(k): int(v) for k, v in sorted(dim_counts.items())},
            'contraction_lower_bounds': clb,
            'unconditional_qcuts': qcut_count,
        },
        'hint_source': None if args.hint_source is None else str(args.hint_source),
        'hint_added': hint_added,
        'build_sec': round(build_sec, 3),
        'solver': 'OR-Tools CP-SAT',
        'solver_time_limit': args.solver_time,
        'workers': args.workers,
        'seed': args.seed,
        'status': status_name,
        'solve_sec': round(solve_sec, 3),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A = [p for p in points if solver.Value(x[p])]
        scan = complete_core_wang_scan('distinct_complete_solution', A, s, records, max_head=30)
        sat = saturation_domains(T, A)
        trans = transversal_failures(sat['sat_records'], sat['B_domains'], sat['C_domains'], 9, 9, max_report=10)
        qscan = eval_candidate_sources('distinct_complete_solution', A, contractions, masks, max_source_size=2, max_store=20)
        result['solution'] = {
            'A_cols': A,
            'distinct_points': len(A),
            'complete_wang_violations': scan['complete_violation_count'],
            'zero_domain_terms': len(sat['summary']['zero_domain_terms']),
            'linear_pass': sat['summary']['linear_membership']['necessary_linear_test_passed'],
            'affine_dim': sat['summary']['linear_membership']['affine_solution_dimension_if_consistent'],
            'transversal_failures': trans['failure_count_reported'],
            'quotient_rank_violations_size2': qscan['violated_guarded_instances'],
        }
        print('A_cols=', A)
        print('checks=', result['solution'])
    result['total_elapsed_sec'] = round(time.time() - t0, 3)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'Saved {args.out}')

if __name__ == '__main__':
    main()
