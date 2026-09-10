#!/usr/bin/env python3
r"""analysis: Complete core MILP with all 417,199 Wang rows + unconditional cuts.

Instead of iteratively learning constraints, build the ENTIRE core Wang table
at once (dim 1-8, all 417,199 subspaces), add contraction lower bounds and
known unconditional quotient-rank cuts, and test LP relaxation and ILP
feasibility.

If the LP relaxation is INFEASIBLE, we have a dual certificate proving
rank(E11 core) >= 20 over F2, i.e., no 19-point A-support satisfies all
occupancy constraints.  This would be a clean mathematical result.

If the LP is FEASIBLE but ILP is INFEASIBLE, the integrality gap matters
and we need integer proof systems.

If the ILP is FEASIBLE, we have a Wang-admissible A-support for rank-one
completion.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient
from fixed_A_saturation import mat_rank_f2
from complete_core_and_transversal import ROOT, build_core_constraints
from quotient_rank_cuts import build_contractions, point_mask_for_q
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis

OUTDIR = ROOT / "workspace/data/unconditional_qcuts"


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lp-time', type=float, default=120.0)
    ap.add_argument('--ilp-time', type=float, default=300.0)
    ap.add_argument('--max-dim', type=int, default=8, help='Max subspace dimension to include')
    ap.add_argument('--include-qcuts', action='store_true', help='Include stored unconditional qcuts')
    ap.add_argument('--out', type=Path, default=OUTDIR / 'complete_core_milp.json')
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

    p_index = {p: p - 1 for p in points}
    nx = 255

    # Build constraints
    print("Building constraint matrix from ALL core Wang rows...")
    rows = []
    lbs = []
    ubs = []

    def add(coeff, lb=-np.inf, ub=np.inf):
        rows.append(coeff)
        lbs.append(lb)
        ubs.append(ub)

    # Sum = s
    add({p_index[p]: 1 for p in points}, s, s)

    # ALL Wang rows up to max_dim
    wang_count = 0
    dim_counts = Counter()
    for rec in records:
        dim8 = int(rec['dim8'])
        if dim8 > args.max_dim:
            continue
        key8 = int(rec['key8'])
        L_val = int(rec['L'])
        cap = s - L_val
        if cap >= s:
            continue  # trivially satisfied
        pts = subspace_points_from_basis(unpack_basis(key8))
        add({p_index[p]: 1 for p in pts}, -np.inf, cap)
        wang_count += 1
        dim_counts[dim8] += 1
    print(f"  Wang rows: {wang_count} by dimension: {dict(sorted(dim_counts.items()))}")

    # Contraction lower bounds
    clb = 0
    for q, c in contractions.items():
        rk = int(c['rank'])
        if rk > 0:
            add({p_index[p]: 1 for p in points if ((q & p).bit_count() & 1)}, rk, np.inf)
            clb += 1
    print(f"  Contraction lower bounds: {clb}")

    # Optionally add stored unconditional qcuts
    qcut_count = 0
    if args.include_qcuts:
        qcut_src = OUTDIR / 'fresh_uncond_sep_10r.json'
        if qcut_src.exists():
            src = json.loads(qcut_src.read_text())
            for rnd in src.get('rounds', []):
                for c in rnd.get('learned_qcuts', []):
                    q1, q2 = int(c['sources'][0]), int(c['sources'][1])
                    target = int(c['target'])
                    req = int(c['requirement'])
                    rq1 = int(contractions[q1]['rank'])
                    rq2 = int(contractions[q2]['rank'])
                    source_union = masks[q1] | masks[q2]
                    outside_mask = masks[target] & (~source_union) & ((1 << 255) - 1)
                    coeff = {}
                    for p in points:
                        if (outside_mask >> (p - 1)) & 1:
                            coeff[p_index[p]] = coeff.get(p_index[p], 0) + 1
                        if ((q1 & p).bit_count() & 1):
                            coeff[p_index[p]] = coeff.get(p_index[p], 0) + 1
                        if ((q2 & p).bit_count() & 1):
                            coeff[p_index[p]] = coeff.get(p_index[p], 0) + 1
                    rhs = req + rq1 + rq2
                    add(coeff, rhs, np.inf)
                    qcut_count += 1
            print(f"  Unconditional qcuts: {qcut_count}")

    build_sec = time.time() - t0
    print(f"\nTotal: {len(rows)} constraints, {nx} variables. Build time: {build_sec:.1f}s")

    # Assemble sparse matrix
    A = lil_matrix((len(rows), nx), dtype=float)
    for i, coeff in enumerate(rows):
        for j, v in coeff.items():
            A[i, j] = v
    A_csr = A.tocsr()

    lb_vec = np.zeros(nx)
    ub_vec = np.array([point_cap[p] for p in points], dtype=float)

    # 1) LP relaxation
    print("\n=== LP relaxation (continuous) ===")
    ts = time.time()
    res_lp = milp(
        c=np.zeros(nx),
        integrality=np.zeros(nx, dtype=int),
        bounds=Bounds(lb_vec, ub_vec),
        constraints=LinearConstraint(A_csr, np.array(lbs), np.array(ubs)),
        options={'time_limit': args.lp_time, 'presolve': True},
    )
    lp_sec = time.time() - ts
    print(f"  Status: {res_lp.status} Message: {res_lp.message}")
    print(f"  Solve time: {lp_sec:.3f}s")
    lp_result = {"status": int(res_lp.status), "message": str(res_lp.message), "solve_sec": round(lp_sec, 3)}
    if res_lp.x is not None:
        x_lp = res_lp.x[:nx]
        lp_result["x_sum"] = round(float(x_lp.sum()), 6)
        lp_result["x_nonzero"] = int(np.count_nonzero(x_lp > 1e-8))
        lp_result["x_fractional"] = int(np.count_nonzero(np.abs(x_lp - np.rint(x_lp)) >= 1e-8))
        lp_result["x_max"] = round(float(x_lp.max()), 6)
        print(f"  LP solution: sum={lp_result['x_sum']} nonzero={lp_result['x_nonzero']} "
              f"fractional={lp_result['x_fractional']} max={lp_result['x_max']}")

    # 2) ILP (integer)
    print("\n=== ILP (integer) ===")
    ts = time.time()
    res_ilp = milp(
        c=np.zeros(nx),
        integrality=np.ones(nx, dtype=int),
        bounds=Bounds(lb_vec, ub_vec),
        constraints=LinearConstraint(A_csr, np.array(lbs), np.array(ubs)),
        options={'time_limit': args.ilp_time, 'mip_rel_gap': 0.0, 'presolve': True},
    )
    ilp_sec = time.time() - ts
    print(f"  Status: {res_ilp.status} Message: {res_ilp.message}")
    print(f"  Solve time: {ilp_sec:.3f}s")
    ilp_result = {"status": int(res_ilp.status), "message": str(res_ilp.message), "solve_sec": round(ilp_sec, 3)}
    if res_ilp.x is not None:
        x_ilp = np.rint(res_ilp.x[:nx]).astype(int)
        counts = {int(p): int(x_ilp[p - 1]) for p in points if x_ilp[p - 1]}
        ilp_result["distinct_points"] = len(counts)
        ilp_result["max_mult"] = int(max(counts.values())) if counts else 0
        ilp_result["counts"] = {str(k): v for k, v in sorted(counts.items())}
        print(f"  ILP solution: {len(counts)} distinct points, max_mult={ilp_result['max_mult']}")

    result = {
        "schema": "complete_core_milp_v1",
        "field": "F2",
        "core": "E11",
        "rank_s": s,
        "constraint_summary": {
            "total_constraints": len(rows),
            "wang_rows": wang_count,
            "wang_by_dim": {str(k): int(v) for k, v in sorted(dim_counts.items())},
            "contraction_lower_bounds": clb,
            "unconditional_qcuts": qcut_count,
            "max_dim": args.max_dim,
        },
        "point_cap_distribution": {str(k): int(v) for k, v in sorted(Counter(point_cap.values()).items())},
        "build_sec": round(build_sec, 3),
        "lp_relaxation": lp_result,
        "ilp": ilp_result,
        "total_elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"\nSaved {args.out}")


if __name__ == "__main__":
    main()
