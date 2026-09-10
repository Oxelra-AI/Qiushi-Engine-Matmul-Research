#!/usr/bin/env python3
"""CP-SAT search for distinct E11 rank-19 A-supports with Wang + purity 2-SAT.

This is an experimental support generator, not a proof.  It combines:
  * 19 distinct nonzero quotient directions x_p (p=1..255),
  * analysis primitive-retained E11 Wang occupation rows from research_record,
  * direct slice capacity >= 3 and optional total-weight targeting/minimization,
  * purity-side 2-SAT constraints derived from the analysis defect/leak lemma.

Returned FEASIBLE supports are rescanned against the complete 417,199-row Wang
table, the corrected shadow system, and the independent support-level purity
filter.  UNKNOWN/INFEASIBLE from CP-SAT is not a mathematical theorem here.
"""
from __future__ import annotations

import argparse
import collections
import json
import pickle
import sys
import time
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

OLD_SCRIPTS = Path('scripts')
THIS_SCRIPTS = Path('scripts')
for p in [str(OLD_SCRIPTS), str(THIS_SCRIPTS)]:
    if p not in sys.path:
        sys.path.insert(0, p)

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import build_core_constraints, complete_core_wang_scan  # noqa: E402
import e11_shadow_filter as shadow  # noqa: E402
import e11_purity_2sat_filter as purity  # noqa: E402

ROOT_OLD = Path('research/research_record')
LUT_PATH = ROOT_OLD / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl'
REDUCED_PATH = ROOT_OLD / 'workspace/data/reduced_wang/primitive_reduced_rows.pkl'


def points_from_bitset(bs: int) -> List[int]:
    pts = []
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())  # x_p stored at bit p-1; p in 1..255
        bs ^= bit
    return pts


def bitrow(row: Sequence[int]) -> int:
    x = 0
    for i, b in enumerate(row):
        if int(b) & 1:
            x |= 1 << i
    return x


def rank_int(rows: Iterable[int]) -> int:
    basis: Dict[int, int] = {}
    r = 0
    for x0 in rows:
        x = int(x0)
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                r += 1
                break
    return r


def consistent_int(rows: List[int], rhs: List[int], nvars: int):
    rA = rank_int(rows)
    rB = rank_int([row | ((int(b)&1) << nvars) for row, b in zip(rows, rhs)])
    return rA == rB, rA, rB


def shadow_summary_for_support(us: List[int], inv_lams: List[int]) -> dict:
    nvars = 9 * len(us)
    tensor_rows, tensor_rhs = shadow.build_tensor_shadow_rows(us)
    tight = [lam for lam in inv_lams if sum(shadow.dot8(lam, u) for u in us) == 9]
    rows = [bitrow(r) for r in tensor_rows]
    rhs = list(tensor_rhs)
    for lam in tight:
        tr, tb = shadow.add_trace_rows(us, [lam], transpose_coeff=False)
        rows.extend(bitrow(r) for r in tr)
        rhs.extend(tb)
    ok, rA, rB = consistent_int(rows, rhs, nvars)
    return {"ok": ok, "rank": rA, "aug_rank": rB, "tight_count": len(tight), "tight": tight}


def load_reduced(path: Path):
    with path.open('rb') as f:
        return pickle.load(f)


def add_wang_rows(model, x, records, kept_keys: set[int], s_rank: int):
    by_L = collections.Counter(); by_dim = collections.Counter()
    added = 0; skipped = 0
    for rec in records:
        key = int(rec['key8'])
        if key not in kept_keys:
            skipped += 1
            continue
        L = int(rec['L'])
        cap = s_rank - L
        if cap >= s_rank:
            continue
        pts = points_from_bitset(int(rec['point_bitset']))
        if pts:
            model.Add(sum(x[p] for p in pts) <= cap)
            added += 1
            by_L[L] += 1
            by_dim[int(rec['dim8'])] += 1
    return {"added": added, "skipped_not_kept": skipped, "by_L": {str(k): int(v) for k,v in sorted(by_L.items())}, "by_dim": {str(k): int(v) for k,v in sorted(by_dim.items())}}


def add_purity_2sat_constraints(model, x, caps, cap_is, B, C, points: List[int], extended: bool = False):
    # Cap-3: B and C forced.  Cap-4: B or C.
    clause_count = 0
    for s in range(8):
        model.AddImplication(cap_is[(s,3)], B[s]); clause_count += 1
        model.AddImplication(cap_is[(s,3)], C[s]); clause_count += 1
        model.AddBoolOr([B[s], C[s], cap_is[(s,4)].Not()]); clause_count += 1
    # Sharing constraints: for each selected point containing both slices.
    for p in points:
        active = [s for s in range(8) if (p >> s) & 1]
        for s1, s2 in combinations(active, 2):
            j1, i1 = purity.SLICE_BLOCKS[s1]
            j2, i2 = purity.SLICE_BLOCKS[s2]
            if j1 != j2:
                model.AddBoolOr([x[p].Not(), B[s1].Not(), B[s2].Not()]); clause_count += 1
            if i1 != i2:
                model.AddBoolOr([x[p].Not(), C[s1].Not(), C[s2].Not()]); clause_count += 1
    # We deliberately omit the cap-5 extension from the solver model for now: its
    # cleanest support-level encoding needs group-wise sharing lower-bound variables.
    # It is still evaluated after candidate extraction by purity.build_purity_clauses.
    return {"purity_clause_count": clause_count, "extended_in_model": False}


def add_capacity_indicators(model, caps, cap_is):
    # Reify cap == k for k=0..19.  The table form is robust for CP-SAT.
    # cap_is[(s,k)] is exact; exactly one value is selected.
    for s in range(8):
        model.AddAllowedAssignments([caps[s]] + [cap_is[(s,k)] for k in range(20)],
                                    [[k] + [1 if kk == k else 0 for kk in range(20)] for k in range(20)])


def main():
    from ortools.sat.python import cp_model

    ap = argparse.ArgumentParser()
    ap.add_argument('--solver-time', type=float, default=90.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--seed', type=int, default=906)
    ap.add_argument('--max-rounds', type=int, default=4)
    ap.add_argument('--target-weight', type=int, default=None)
    ap.add_argument('--minimize-weight', action='store_true')
    ap.add_argument('--out', type=Path, default=Path('data/support_search/wang_purity_support_search.json'))
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    s_rank = 19
    points = list(range(1, 256))
    lut, lut_meta = load_lut(LUT_PATH)
    records, complete_meta = build_core_constraints(CoreQuotient(1), lut)
    red = load_reduced(REDUCED_PATH)
    kept = set(int(k) for k in red['kept_key8'])
    inv_lams = shadow.invertible_lambda_masks()

    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f'x_{p}') for p in points}
    model.Add(sum(x[p] for p in points) == s_rank)

    # Slice capacities and total A-weight.
    caps = []
    cap_is = {}
    for ss in range(8):
        cap = model.NewIntVar(0, s_rank, f'cap_{ss}')
        caps.append(cap)
        model.Add(cap == sum(x[p] for p in points if (p >> ss) & 1))
        model.Add(cap >= 3)
        for k in range(20):
            cap_is[(ss,k)] = model.NewBoolVar(f'cap_{ss}_is_{k}')
    add_capacity_indicators(model, caps, cap_is)
    total_weight = model.NewIntVar(0, 8*s_rank, 'total_weight')
    model.Add(total_weight == sum(caps))
    model.Add(total_weight >= 27)
    if args.target_weight is not None:
        model.Add(total_weight == int(args.target_weight))

    wang_summary = add_wang_rows(model, x, records, kept, s_rank)

    B = [model.NewBoolVar(f'Bpure_{ss}') for ss in range(8)]
    C = [model.NewBoolVar(f'Cpure_{ss}') for ss in range(8)]
    purity_summary = add_purity_2sat_constraints(model, x, caps, cap_is, B, C, points)

    if args.minimize_weight:
        model.Minimize(total_weight)

    build_sec = time.time() - t0
    print(json.dumps({
        'build_sec': round(build_sec,3),
        'retained_wang_rows': wang_summary['added'],
        'purity_clauses': purity_summary['purity_clause_count'],
        'target_weight': args.target_weight,
        'minimize_weight': args.minimize_weight,
    }, indent=2))

    rounds = []
    included_extra = set()
    for r in range(args.max_rounds):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(args.solver_time)
        solver.parameters.num_search_workers = int(args.workers)
        solver.parameters.random_seed = int(args.seed + r)
        ts = time.time()
        status = solver.Solve(model)
        solve_sec = time.time() - ts
        status_name = solver.StatusName(status)
        rec = {'round': r, 'status': status_name, 'solve_sec': round(solve_sec,3)}
        print(f'round {r}: {status_name} {solve_sec:.2f}s')
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rounds.append(rec)
            break
        A = [p for p in points if solver.Value(x[p])]
        caps_val = [solver.Value(c) for c in caps]
        tw = solver.Value(total_weight)
        scan = complete_core_wang_scan(f'research_record_wang_purity_round_{r}', A, s_rank, records, max_head=20)
        # Add all complete Wang violations whose rows were not retained/included.
        new_rows = []
        if scan['complete_violation_count']:
            # complete_core_wang_scan omits points, so re-evaluate records directly for additions.
            selected = set(A)
            for rec0 in records:
                key = int(rec0['key8'])
                if key in kept or key in included_extra:
                    continue
                cap = s_rank - int(rec0['L'])
                if cap >= s_rank:
                    continue
                pts = points_from_bitset(int(rec0['point_bitset']))
                occ = sum(1 for p in pts if p in selected)
                if occ > cap:
                    new_rows.append({'key8': key, 'L': int(rec0['L']), 'cap': cap, 'dim8': int(rec0['dim8']), 'occ': occ, 'points': pts})
                    included_extra.add(key)
                    model.Add(sum(x[p] for p in pts) <= cap)
            print(f'  added {len(new_rows)} complete-Wang rows')
        sh = shadow_summary_for_support(A, inv_lams)
        pur_base = purity.build_purity_clauses(A, extended=False)
        pur_ext = purity.build_purity_clauses(A, extended=True)
        rec.update({
            'A_cols': A,
            'caps': caps_val,
            'total_weight': tw,
            'B_assignment': [solver.Value(B[ss]) for ss in range(8)],
            'C_assignment': [solver.Value(C[ss]) for ss in range(8)],
            'complete_wang_scan': scan,
            'new_complete_rows_added': len(new_rows),
            'new_rows_head': [{k:v for k,v in z.items() if k != 'points'} for z in new_rows[:10]],
            'shadow': {k: sh[k] for k in ['ok','rank','aug_rank','tight_count','tight']},
            'purity_base': {k: pur_base[k] for k in ['capacity_ok','twosat_sat','rejects_support','cross_cap3_cap4_obstructions','latin_triple_obstructions','n_clauses']},
            'purity_extended': {k: pur_ext[k] for k in ['twosat_sat','rejects_support','hard_reject_reasons','extended_units']},
        })
        print('  support', A)
        print('  checks', json.dumps({
            'caps': caps_val,
            'weight': tw,
            'complete_wang_viol': scan['complete_violation_count'],
            'shadow_ok': sh['ok'],
            'purity_base_reject': pur_base['rejects_support'],
            'purity_ext_reject': pur_ext['rejects_support'],
        }, sort_keys=True))
        rounds.append(rec)
        # Stop only on a real support candidate for B/C completion: complete-Wang, shadow-consistent, purity-pass.
        if scan['complete_violation_count'] == 0 and sh['ok'] and not pur_ext['rejects_support']:
            rec['candidate_for_completion'] = True
            break
        # Avoid returning same failed support.
        model.Add(sum(x[p] for p in A) <= s_rank - 1)

    result = {
        'schema': 'research_record_wang_purity_support_search_v1',
        'meaning': 'Experimental support generation with reduced Wang rows plus purity-side 2-SAT; feasible supports are candidates only and are rescanned against complete Wang and shadow.',
        'parameters': vars(args) | {'out': str(args.out)},
        'lut_coverage_ok': lut_meta.get('coverage_ok'),
        'complete_meta': complete_meta,
        'reduced_counts': {'kept': len(kept), 'dropped': len(red['dropped_key8']), 'kept_hash': red.get('kept_key8_sha256')},
        'constraint_summary': {'retained_wang': wang_summary, 'purity_2sat': purity_summary},
        'build_sec': round(build_sec,3),
        'rounds': rounds,
        'elapsed_sec': round(time.time() - t0,3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'out': str(args.out), 'rounds': len(rounds), 'last': rounds[-1] if rounds else None, 'elapsed_sec': result['elapsed_sec']}, indent=2, sort_keys=True)[:5000])


if __name__ == '__main__':
    main()
