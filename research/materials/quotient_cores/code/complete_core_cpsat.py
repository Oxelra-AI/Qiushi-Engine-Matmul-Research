#!/usr/bin/env python3
r"""analysis: Complete core CP-SAT with all Wang rows + unconditional quotient cuts.

CP-SAT handled smaller models more effectively than HiGHS MILP. Try the 
complete 417K Wang table + contraction bounds + learned unconditional cuts.
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
from complete_core_and_transversal import ROOT, build_core_constraints
from quotient_rank_cuts import build_contractions, point_mask_for_q
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis

OUTDIR = ROOT / "workspace/data/unconditional_qcuts"
ALLMASK = (1 << 255) - 1


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}


def main():
    from ortools.sat.python import cp_model

    ap = argparse.ArgumentParser()
    ap.add_argument('--solver-time', type=float, default=600.0)
    ap.add_argument('--qcut-source', type=Path, default=None,
                    help='JSON with learned unconditional qcuts')
    ap.add_argument('--out', type=Path, default=OUTDIR / 'complete_core_cpsat.json')
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    s = 19
    core = CoreQuotient(1)
    T_core = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    lut = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records, meta = build_core_constraints(core, lut)
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}
    points = list(range(1, 256))

    point_cap = {}
    for p in points:
        key8 = core.key8_from_rows([p])
        key9 = core.key9_from_key8(key8)
        point_cap[p] = max(0, min(s, s - int(lut[key9])))

    model = cp_model.CpModel()
    x = {p: model.NewIntVar(0, point_cap[p], f'x_{p}') for p in points}
    model.Add(sum(x[p] for p in points) == s)

    # ALL Wang rows
    wang_count = 0
    dim_counts = Counter()
    for rec in records:
        key8 = int(rec['key8'])
        L_val = int(rec['L'])
        cap = s - L_val
        if cap >= s:
            continue
        pts = subspace_points_from_basis(unpack_basis(key8))
        model.Add(sum(x[p] for p in pts) <= cap)
        wang_count += 1
        dim_counts[int(rec['dim8'])] += 1
    print(f"Wang rows: {wang_count} by dim: {dict(sorted(dim_counts.items()))}")

    # Contraction lower bounds
    clb = 0
    for q, c in contractions.items():
        rk = int(c['rank'])
        if rk > 0:
            model.Add(sum(x[p] for p in points if ((q & p).bit_count() & 1)) >= rk)
            clb += 1
    print(f"Contraction lower bounds: {clb}")

    # Optional unconditional qcuts
    qcut_count = 0
    if args.qcut_source and args.qcut_source.exists():
        src = json.loads(args.qcut_source.read_text())
        for rnd in src.get('rounds', []):
            for c in rnd.get('learned_qcuts', []):
                q1, q2 = int(c['sources'][0]), int(c['sources'][1])
                target = int(c['target'])
                req = int(c['requirement'])
                rq1 = int(contractions[q1]['rank'])
                rq2 = int(contractions[q2]['rank'])
                source_union = masks[q1] | masks[q2]
                outside_mask = masks[target] & (~source_union) & ALLMASK
                lhs_terms = []
                for p in points:
                    coeff = 0
                    if (outside_mask >> (p - 1)) & 1:
                        coeff += 1
                    if ((q1 & p).bit_count() & 1):
                        coeff += 1
                    if ((q2 & p).bit_count() & 1):
                        coeff += 1
                    if coeff > 0:
                        lhs_terms.append((p, coeff))
                rhs = req + rq1 + rq2
                model.Add(sum(coeff * x[p] for p, coeff in lhs_terms) >= rhs)
                qcut_count += 1
        print(f"Unconditional qcuts: {qcut_count}")

    build_sec = time.time() - t0
    print(f"Build time: {build_sec:.1f}s, total constraints: {wang_count + clb + qcut_count + 1}")

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = 8
    solver.parameters.random_seed = 4646
    ts = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - ts

    status_name = {
        cp_model.OPTIMAL: 'OPTIMAL', cp_model.FEASIBLE: 'FEASIBLE',
        cp_model.INFEASIBLE: 'INFEASIBLE', cp_model.UNKNOWN: 'UNKNOWN',
        cp_model.MODEL_INVALID: 'MODEL_INVALID',
    }.get(status, str(status))

    print(f"\nCP-SAT status: {status_name} solve_sec={solve_sec:.1f}")

    result = {
        "schema": "complete_core_cpsat_v1",
        "field": "F2",
        "core": "E11",
        "rank_s": s,
        "constraint_summary": {
            "wang_rows": wang_count,
            "wang_by_dim": {str(k): int(v) for k, v in sorted(dim_counts.items())},
            "contraction_lower_bounds": clb,
            "unconditional_qcuts": qcut_count,
        },
        "point_cap_distribution": {str(k): int(v) for k, v in sorted(Counter(point_cap.values()).items())},
        "build_sec": round(build_sec, 3),
        "solver": "OR-Tools CP-SAT",
        "solver_time_limit": args.solver_time,
        "status": status_name,
        "solve_sec": round(solve_sec, 3),
    }

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        counts = {p: solver.Value(x[p]) for p in points if solver.Value(x[p])}
        A_cols = []
        for p, c in sorted(counts.items()):
            A_cols.extend([p] * int(c))
        result["solution"] = {
            "distinct_points": len(counts),
            "max_mult": max(counts.values()) if counts else 0,
            "A_cols": A_cols,
            "counts": {str(k): int(v) for k, v in sorted(counts.items())},
        }
        print(f"FEASIBLE: {len(counts)} distinct, max_mult={max(counts.values()) if counts else 0}")
        print(f"A_cols = {A_cols}")

    result["total_elapsed_sec"] = round(time.time() - t0, 3)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Saved {args.out}")


if __name__ == "__main__":
    main()
