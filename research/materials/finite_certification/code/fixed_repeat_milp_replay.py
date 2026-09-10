#!/usr/bin/env python3
"""analysis: independent HiGHS replay for each normalized repeated E11-core direction.

This is a semantic cross-check for the proof-producing CNF.  It rebuilds the
same compact Wang + contraction + unconditional quotient-rank model used in
analysis, but fixes x_p=2 for each of the six one-dimensional capacity-two core
points.  Infeasibility for p=1 is the fixed instance targeted by the DRAT run;
infeasibility for all six also cross-checks the symmetry conclusion directly at
solver level.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient
from complete_core_and_transversal import ROOT, build_core_constraints
from quotient_rank_cuts import build_contractions, point_mask_for_q
from unconditional_milp_replay import build_milp_model, load_lut

OUTDIR = ROOT / 'workspace/data/repeat_branch_certificate'


def extract_constraints(source: Path, records):
    src = json.loads(source.read_text())
    wang_keys = set()
    for r in records:
        if int(r['dim8']) in (1, 2):
            wang_keys.add(int(r['key8']))
    qcuts = []
    for rnd in src.get('rounds', []):
        for w in rnd.get('learned_wang_rows', []):
            wang_keys.add(int(w['key8']))
        for c in rnd.get('learned_quotient_cuts', []):
            q1, q2 = sorted([int(c['sources'][0]), int(c['sources'][1])])
            cc = dict(c)
            cc['sources'] = [q1, q2]
            qcuts.append(cc)
    uniq = {}
    for c in qcuts:
        uniq[(str(c['side']), int(c['sources'][0]), int(c['sources'][1]), int(c['target']))] = c
    return wang_keys, list(uniq.values())


def solve_fixed_repeat(fixed_p: int, base_model: dict, time_limit: float):
    # Copy bounds arrays from the base model and fix x_{fixed_p}=2.
    lb = np.array(base_model['bounds'].lb, dtype=float).copy()
    ub = np.array(base_model['bounds'].ub, dtype=float).copy()
    idx = fixed_p - 1
    lb[idx] = 2
    ub[idx] = 2
    constraints = LinearConstraint(base_model['A'], base_model['lbs'], base_model['ubs'])
    t0 = time.time()
    res = milp(
        c=np.zeros(base_model['nvars']),
        integrality=base_model['integrality'],
        bounds=Bounds(lb, ub),
        constraints=constraints,
        options={'time_limit': time_limit, 'mip_rel_gap': 0.0, 'presolve': True},
    )
    ans = {
        'fixed_repeat_point': fixed_p,
        'status': int(res.status),
        'success': bool(res.success),
        'message': str(res.message),
        'solve_sec': round(time.time() - t0, 3),
    }
    if res.x is not None:
        vals = np.rint(res.x[:255]).astype(int)
        counts = {int(p): int(vals[p - 1]) for p in range(1, 256) if vals[p - 1]}
        ans['counts'] = counts
        ans['distinct_points'] = len(counts)
        ans['max_mult'] = max(counts.values()) if counts else 0
    return ans


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', type=Path, default=ROOT / 'workspace/data/quotient_rank_cuts/core_e11_multiset_quotient_sep_24r_fullstored.json')
    ap.add_argument('--time-limit', type=float, default=120.0)
    ap.add_argument('--out', type=Path, default=OUTDIR / 'fixed_repeat_milp_replay.json')
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    s = 19
    core = CoreQuotient(1)
    lut = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records, meta = build_core_constraints(core, lut)
    record_by_key = {int(r['key8']): r for r in records}
    T = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    contractions = build_contractions(T)
    masks = {q: point_mask_for_q(q) for q in contractions}
    points = list(range(1, 256))
    point_cap = {}
    for p in points:
        key8 = core.key8_from_rows([p])
        key9 = core.key9_from_key8(key8)
        point_cap[p] = max(0, min(s, s - int(lut[key9])))
    cap2 = sorted(p for p, c in point_cap.items() if c >= 2)
    wang_keys, qcuts = extract_constraints(args.source, records)

    print(f'compact constraints: wang={len(wang_keys)} qcuts={len(qcuts)} cap2={cap2}')
    base = build_milp_model(s, points, point_cap, records, record_by_key, lut, core, contractions, masks, wang_keys, qcuts, force_repeat=False)
    print(f'base model vars={base["nvars"]} rows={base["nrows"]} build_sec={base["build_sec"]:.3f}')

    results = []
    for p in cap2:
        r = solve_fixed_repeat(p, base, args.time_limit)
        print(f'p={p} status={r["status"]} success={r["success"]} sec={r["solve_sec"]} msg={r["message"][:80]}')
        results.append(r)

    out = {
        'schema': 'fixed_repeat_milp_replay_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': s,
        'source': str(args.source),
        'point_cap_distribution': {str(k): int(v) for k, v in sorted(Counter(point_cap.values()).items())},
        'capacity_two_points': cap2,
        'compact_constraints': {
            'unique_wang_rows': len(wang_keys),
            'contraction_lower_bounds': base['clb'],
            'unconditional_quotient_cuts': len(qcuts),
            'base_rows_without_fixed_equality': base['nrows'],
            'base_variables': base['nvars'],
        },
        'solver': 'scipy.optimize.milp/HiGHS',
        'time_limit_per_fixed_point': args.time_limit,
        'results': results,
        'all_capacity_two_points_infeasible': all(r['status'] == 2 for r in results),
        'total_elapsed_sec': round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f'Saved {args.out}')


if __name__ == '__main__':
    main()
